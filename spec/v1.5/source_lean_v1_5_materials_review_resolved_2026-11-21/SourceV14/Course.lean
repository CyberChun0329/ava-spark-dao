import SourceV14.Confirmation
import SourceV14.Funding
import SourceV14.CreditEvidence
import SourceV14.Workflow.AttendanceFacts

namespace SourceV14.Course

open Booking Settlement Confirmation CreditEvidence
open Workflow.AttendanceFacts

structure VerifiedLessonRefund where
  form : PartOne
  originalDebit : CreditPosting
  obligation : ObligationId
  settlement : RefundRecord
  payment : PostedPayment
  approval : Option PaymentApproval := none

def VerifiedLessonRefund.matches (refund : VerifiedLessonRefund) (ledger : List CreditPosting)
    (payments : PaymentHistory) (authorities : ReviewAuthorities) (posting : CreditPosting) :
    Prop :=
  let form := refund.form
  let p := form.place
  let debit := refund.originalDebit
  let record := refund.settlement
  let paid := refund.payment.instruction
  form.matches ∧ debit ∈ ledger ∧ debit.kind = .lessonDebit p.lesson p.id ∧
  debit.account = p.account ∧ form.confirmedAt.by debit.point ∧ 0 < debit.amount ∧
  debit.point.by record.trigger ∧ record.trigger.by posting.point ∧
  record.reason ≠ "" ∧ 0 ≤ record.finalFee ∧ 0 ≤ record.amount ∧
  record.amount ≤ debitTotal p ledger record.trigger ∧
  record.matches form ledger posting.point record.reason record.trigger record.due record.amount
    (some refund.obligation) ∧
  LessonRefundPostingMatches p ledger posting refund.obligation ∧
  payments.actualPaymentWithEvidence refund.payment ∧ refund.payment.id = posting.id ∧
  paid.part.lesson = p.lesson ∧ paid.part.purpose = .lessonRefund p.id ∧
  paid.part.obligation = refund.obligation ∧ paid.destination = .account p.account ∧
  paid.amount = posting.amount ∧ paid.atTime = posting.point ∧
  ∀ approval ∈ refund.approval,
    approval.authorisedAtGrant authorities ∧ approval.grantedAt.by posting.point ∧
    ∃ scope ∈ approval.scope, scope.part = paid.part ∧
      scope.destination = paid.destination ∧ 0 < scope.amount

/-- The ledger consists of actual postings. IDs distinguish receipts from copies or reversals. -/
structure CreditRecords where
  topUps : List TopUpReceipt
  grants : List CompensationCreditOrigin
  topUpReturns : List TopUpReturnAuthorisation
  closed : List FullRefundClosure
  ownsAccount : ActorId → AccountId → Prop
  courseProviderAt : ActorId → Moment → Prop
  verifiedRefunds : List VerifiedLessonRefund
  payments : PaymentHistory
  paymentAuthorities : ReviewAuthorities
  lessonFees : LessonFeeAmendments := {}

def ValidCreditHistory (opening : AccountId → Amount) (ledger : List CreditPosting)
    (evidence : CreditRecords) (closureSeen : Moment → Prop := fun _ ↦ True) : Prop :=
  CreditOriginsValid ledger evidence.topUps evidence.grants evidence.topUpReturns
    evidence.closed evidence.ownsAccount evidence.courseProviderAt evidence.lessonFees ∧
  (ledger.map (·.id)).Nodup ∧ (ledger.map (·.point)).Nodup ∧
  evidence.payments.distinctReceipts ∧
  (∀ e ∈ ledger, 0 < e.amount ∧
    match e.kind with
    | .lessonRefund _ _ _ =>
        ∃ refund ∈ evidence.verifiedRefunds,
          refund.matches ledger evidence.payments evidence.paymentAuthorities e
    | .creditReturned receipt =>
        e.amount ≤ balanceBefore opening ledger e.account e.point ∧
        ∃ original ∈ ledger, original.id = receipt ∧ 0 < original.change ∧
          original.account = e.account ∧ original.point.before e.point ∧
          match original.kind with
          | .compensation _ _ => compensationClosureRemovalPosting ledger evidence.closed e
          | _ => ∃ returned ∈ evidence.payments.returned,
              returned.id = e.id ∧ returned.paidReceipt = receipt ∧
                returned.amount = e.amount ∧ returned.returnedAt = e.point
    | .lessonDebit _ _ | .topUpReturn _ =>
        e.amount ≤ balanceBefore opening ledger e.account e.point
    | _ => True) ∧
  (∀ receipt ∈ ledger, ∀ bound, returnedFrom ledger receipt bound ≤ receipt.amount) ∧
  ∀ closure ∈ evidence.closed, closureSeen closure.closedAt →
    closure.creditDispositionsRecorded ledger

structure FormationCheck where
  lesson : LessonId
  provider : ActorId
  terms : String
  point : Moment
  conditionsMet : Bool
  deriving Repr

inductive BookingTermReference where
  | rules (version : String)
  | tutorAgreement (reference : String)
  | materialsTerms (reference : String)
  | other (reference : String)
  deriving DecidableEq, Repr

/-- Reference to the actual version of a document used in the agreed booking terms. -/
structure BookingTermDocument where
  reference : BookingTermReference
  evidence : EvidenceRef
  deriving DecidableEq, Repr

structure BookingTermsProvision where
  form : PartOne
  coordinator : ActorId
  recipient : ActorId
  formProvided : Moment
  referencedTermsProvided : Moment
  documents : List BookingTermDocument
  deriving Repr

def BookingTermsProvision.delivers (provision : BookingTermsProvision) (f : PartOne)
    (recipient : ActorId) (documents : List BookingTermDocument) : Prop :=
  provision.form = f ∧ provision.coordinator = f.lesson.coordinator ∧
    provision.recipient = recipient ∧
    ∀ document ∈ documents, document ∈ provision.documents

structure BookingEvidence where
  signatures : Signatures
  tutorAgreement : TutorAgreement
  formation : FormationCheck
  funding : FundingCheck
  debit : Option CreditPosting
  agreedDocuments : List BookingTermDocument
  provisions : List BookingTermsProvision

def ProvidedBookingTerms (f : PartOne) (a : Signatures) (documents : List BookingTermDocument)
    (provisions : List BookingTermsProvision) (debitAt : Option Moment) : Prop :=
  let required : List BookingTermReference :=
    [.rules f.rulesVersion, .tutorAgreement f.tutorAgreementRef] ++
    f.materialsTermsRef.toList.map BookingTermReference.materialsTerms ++
    f.additionalReferencedTerms.map BookingTermReference.other
  (∀ reference ∈ required, ∃ document ∈ documents, document.reference = reference) ∧
  (∃ provision ∈ provisions,
    provision.delivers f a.providedTo documents ∧
    provision.formProvided = a.formProvided ∧
    provision.referencedTermsProvided = a.referencedTermsProvided) ∧
  ∃ provision ∈ provisions, provision.delivers f f.agreedTutor documents ∧
    TermsProvidedInTime provision.formProvided provision.referencedTermsProvided
      [a.tutorAccepted] debitAt

def BookingEvidence.providedAgreedTerms (booking : BookingEvidence) (f : PartOne) : Prop :=
  ProvidedBookingTerms f booking.signatures booking.agreedDocuments booking.provisions
    (booking.debit.map (·.point))

def FormUsesRoster (f : PartOne) (r : Roster) : Prop :=
  f.place ∈ r.places ∧ f.privateRoster = some r.reference ∧ f.rosterLock = some r.lockedAt

def CanConfirmPlace (f : PartOne) (booking : BookingEvidence) (roster : Option Roster)
    (opening : AccountId → Amount) (ledger : List CreditPosting) (creditRecords : CreditRecords)
    (discounts : List DiscountRecord) (actualTeachingBegan : Option Moment) : Prop :=
  let places := roster.map (·.places) |>.getD [f.place]
  let a := booking.signatures
  let checked := booking.formation
  let before := ledger.filter (fun e ↦ decide (e.point.before f.confirmedAt))
  let through := ledger.filter (fun e ↦ decide (e.point.by f.confirmedAt))
  f.matches ∧
  (match f.lesson.kind, roster with
  | .oneToOne, none => True
  | .group, some r => r.valid f.lesson f.schedule.start ∧ FormUsesRoster f r
  | _, _ => False) ∧
  checked.lesson = f.lesson.id ∧ checked.provider = f.lesson.provider ∧
  checked.terms = f.applicableStartTerms ∧ checked.conditionsMet = true ∧
  checked.point.before f.confirmedAt ∧
  (∀ began, actualTeachingBegan = some began → f.confirmedAt.before began) ∧
  a.valid f (booking.debit.map (·.point)) ∧ booking.tutorAgreement.agreedBeforeAcceptance f a ∧
  a.providerAccepted.by f.confirmedAt ∧ a.tutorAccepted.by f.confirmedAt ∧
  a.customerAccepted.by f.confirmedAt ∧
  (∀ acceptance, a.payerAccepted = some acceptance → acceptance.2.by f.confirmedAt) ∧
  booking.funding.readsForm f ∧
  booking.funding.securedBefore f.lesson places f.confirmedAt ∧
  booking.funding.checkedAt.before a.customerAccepted ∧
  booking.funding.checkedAt.before a.tutorAccepted ∧
  ValidCreditHistory opening through creditRecords (fun t ↦ t.by f.confirmedAt) ∧
  PaymentRecord f through discounts f.confirmedAt (debitTotal f.place through f.confirmedAt) ∧
  (match booking.debit with
  | none => DiscountCoversFullFee f.place ledger discounts f.confirmedAt
  | some row => row ∈ ledger ∧ DebitAtConfirmation f.place opening before row f.confirmedAt) ∧
  booking.providedAgreedTerms f

structure TutorReplacement where
  previous : Schedule
  record : ChangeRecord
  agreedAt : Moment
  effectiveAt : Moment
  agreement : TutorAgreement
  accepted : ScheduleApproval
  providerConsent : ScheduleApproval
  noticeChannel : Option String

/-- The original and replacement schedule, with the Part 2 record of the actual change. -/
structure AgreedScheduleChange where
  previous : Schedule
  record : ChangeRecord
  approvals : List ScheduleApproval
  compliesWithOneToOneTerms : String → Prop

structure RosterCorrection where
  before : Roster
  after : Roster
  original : RecordedSettlementOutcome
  finding : ReviewFinding
  record : SettlementCorrection

structure RosterReviewHistory where
  originalOutcome : EvidenceRef
  corrections : List RosterCorrection
  authorities : ReviewAuthorities
  appointments : List ReviewAppointment
  initialFindings : List InitialFinding
  reviewFindings : List ReviewFinding
  governingForm : ReviewMatter → PartOne → Prop
  /-- The actual review outcome approves precisely these old and corrected members. -/
  approvedChange : ReviewFinding → Roster → Roster → Prop

def RosterReviewHistory.applies (history : RosterReviewHistory) (l : Lesson)
    (forms : List PartOne) (previous : Roster) (outcome : EvidenceRef) (point : Moment)
    (changes : List RosterCorrection) (effective : Roster) : Prop :=
  match changes with
  | [] => effective = previous
  | change :: later =>
    change.before = previous ∧ change.after.reference = previous.reference ∧
    change.after.lockedAt = previous.lockedAt ∧ change.after.valid l previous.lockedAt ∧
    change.original.outcome = outcome ∧ change.original.decidedAt = point ∧
    point.before change.record.recordedAt ∧
    correctionAfterReviewConforms l history.authorities history.appointments [change.original]
      change.finding change.record ∧
    (∃ form ∈ forms, form.lesson = l ∧ form.matches ∧
      form.confirmedAt.by change.finding.decidedAt ∧ history.governingForm change.finding.matter form ∧
      reviewFindingRecordedConforms history.authorities (some form.contacts.reviewer)
        history.appointments history.initialFindings history.reviewFindings change.finding) ∧
    history.approvedChange change.finding change.before change.after ∧
    (∀ p, (p ∈ change.before.places ∧ p ∉ change.after.places) ∨
      (p ∈ change.after.places ∧ p ∉ change.before.places) →
      ∀ actor ∈ [p.customer, p.payer, p.student], actor ∈ change.finding.matter.parties) ∧
    history.applies l forms change.after change.record.correction change.record.recordedAt later effective

structure AfterLessonRecords where
  tutorReports : List TutorDeliveryReport
  attendance : List AttendanceReport
  serviceFeedback : List DeliveryReport
  followUps : List StudentFollowUp
  coordinatorConfirmations : List (ActorId × Moment)
  studentCompletions : List StudentCompletionReport := []
  deriving Repr

structure StudentFaultFinding where
  decision : FaultDecision
  place : PlaceId
  student : ActorId
  atFault : Bool
  evidence : List FaultEvidence

def StudentFaultFinding.decidedAt (finding : StudentFaultFinding) : Moment :=
  finding.decision.decidedAt

structure StudentFaultHistory where
  findings : List StudentFaultFinding
  decisions : DecisionRecords
  /-- Verified contents of the decision, including its explicit student finding. -/
  recordedStudentOutcome : StudentFaultFinding → Prop

def StudentFaultHistory.applies (history : StudentFaultHistory) (f : PartOne)
    (query : Moment) (finding : StudentFaultFinding) : Prop :=
  finding ∈ history.findings ∧ f.place.matches f.lesson ∧ finding.place = f.place.id ∧
  finding.student = f.place.student ∧ history.recordedStudentOutcome finding ∧
  finding.decision.effectiveForForm history.decisions f query ∧
  (finding.atFault = true → sufficientKindOfEvidenceForFault finding.evidence)

def StudentFaultHistory.foundAtFault (history : StudentFaultHistory) (f : PartOne)
    (query : Moment) : Prop :=
  ∃ finding, history.applies f query finding ∧ finding.atFault = true ∧
    ∀ other, history.applies f query other →
      other.decidedAt.by finding.decidedAt ∧
      (other.decidedAt = finding.decidedAt → other.atFault = true)

structure TutorPayTerms where
  reference : String
  normalFee : Amount
  payment : PaymentTerms

/-- Agreed revisions to the pay and payment terms for the same lesson and tutor. -/
structure TutorPayAmendments where
  agreementEvidence : LessonId → ActorId → String → Option EvidenceRef := fun _ _ _ ↦ none
  authenticAgreement : LessonId → ActorId → String → EvidenceRef → Prop := fun _ _ _ _ ↦ False
  amendments : List (PrivateAmendment (LessonId × ActorId) TutorPayTerms) := []
  assents : List PrivateAmendmentAssent := []
  furtherAffected : PrivateAmendment (LessonId × ActorId) TutorPayTerms → ActorId → Prop :=
    fun _ _ ↦ False
  authenticAssent : PrivateAmendment (LessonId × ActorId) TutorPayTerms →
    PrivateAmendmentAssent → Prop := fun _ _ ↦ False

/-- §6.4 retains an existing teaching agreement until a verified change takes effect. -/
def TutorPayAmendments.termsAt (facts : TutorPayAmendments) (l : Lesson) (tutor : ActorId)
    (original : TutorPayTerms) (originalAt query : Moment) (terms : TutorPayTerms) : Prop :=
  let scope := (l.id, tutor)
  let changes := (facts.amendments.filter (fun change ↦ change.replacement.scope == scope)).mergeSort
    (fun first second ↦ decide (first.replacement.effectiveAt.by second.replacement.effectiveAt))
  let originalReference reference :=
    facts.agreementEvidence l.id tutor original.reference = some reference ∧
      facts.authenticAgreement l.id tutor original.reference reference
  originalAt.by query ∧
  ((¬(∃ reference, originalReference reference) ∧ terms = original) ∨
    ∃ reference, originalReference reference ∧ ∃ operative,
      privateArrangementAt
        (fun change person ↦ person = l.provider ∨ person = tutor ∨ facts.furtherAffected change person)
        (fun change assent ↦ change.replacement.terms.reference ≠ "" ∧
          0 ≤ change.replacement.terms.normalFee ∧ change.replacement.terms.payment.valid ∧
          facts.authenticAssent change assent)
        facts.assents query
        { scope, reference, terms := original, effectiveAt := originalAt } changes operative ∧
      terms = operative.terms)

/-- The provider's effective group register at a stated occurrence. A
snapshot taken for an arrangement does not itself lock the settlement roster. -/
structure GroupRegisterSnapshot where
  lesson : LessonId
  atTime : Moment
  forms : List PartOne

def GroupRegisterSnapshot.conforms (snapshot : GroupRegisterSnapshot) (l : Lesson) : Prop :=
  snapshot.lesson = l.id ∧ l.kind = .group ∧
  snapshot.forms ≠ [] ∧ (snapshot.forms.map (·.place.id)).Nodup ∧
  (snapshot.forms.map (·.place.student)).Nodup ∧
  ∀ form ∈ snapshot.forms, form.lesson = l ∧ form.matches ∧ form.confirmedAt.by snapshot.atTime

structure StartEvidence where
  effectiveForms : List PartOne
  groupRoster : Option Roster
  bookings : List (PartOne × BookingEvidence)
  scheduleHistory : List Schedule
  changes : List AgreedScheduleChange
  openingCredit : AccountId → Amount
  creditRecords : CreditRecords
  ledger : List CreditPosting
  discounts : List DiscountRecord
  notices : List Notice
  academicTeamAt : LessonId → ActorId → Moment → Prop
  teachingBegan : Option Moment
  teachingEnded : Option Moment
  verifiedOneToOneAbsence : Option OneToOneAbsence := none
  studentsTakingLesson : List ActorId
  afterLesson : AfterLessonRecords
  studentFaults : StudentFaultHistory
  tutorReplacements : List TutorReplacement := []
  rosterReview : Option RosterReviewHistory := none
  clockBoundaries : List ClockBoundary := []
  tutorPayAmendments : TutorPayAmendments := {}
  groupRegisters : List GroupRegisterSnapshot := []
  /-- Independent evidence from the provider's register at the stated cut.
  A verified snapshot identifies all the effective places and their operative forms. -/
  verifiesGroupRegister : GroupRegisterSnapshot → Prop := fun _ ↦ False
  bookedRosters : List (PartOne × Roster) := []
  oneToOneAbsenceReasons : List OneToOneAbsenceReason := []

def StartEvidence.verifiedOneToOneAbsenceAt (ev : StartEvidence) : Option Moment :=
  ev.verifiedOneToOneAbsence.map (·.start)

def StartEvidence.retainsOneToOneAbsence (ev : StartEvidence) (form : PartOne) (schedule : Schedule)
    (start query : Moment) (facts : AbsenceFacts) : Prop :=
  ∃ row ∈ ev.verifiedOneToOneAbsence,
    row.matchesAt form start query ∧ row.schedule = schedule ∧
    row.factsAt ev.oneToOneAbsenceReasons query = facts

def StartEvidence.roster (ev : StartEvidence) : List Place :=
  (ev.groupRoster.map (·.places)).getD (ev.effectiveForms.map (·.place))

def StartEvidence.formsMatch (ev : StartEvidence) (l : Lesson) : Prop :=
  ev.effectiveForms ≠ [] ∧
  ∀ f ∈ ev.effectiveForms, f.lesson = l ∧ f.matches

def RegisterMatchesForms (r : Roster) (ev : StartEvidence) (l : Lesson) : Prop :=
  l.kind = .group ∧ ev.groupRoster = some r ∧ ev.formsMatch l ∧ r.lesson = l.id ∧
  (∀ p ∈ r.places, ∃ f ∈ ev.effectiveForms, p = f.place) ∧
  ((ev.effectiveForms.map (·.place.id)).Nodup) ∧
  ∀ f ∈ ev.effectiveForms, FormUsesRoster f r

def StartEvidence.rosterMatchesForms (ev : StartEvidence) (l : Lesson) : Prop :=
  match l.kind, ev.groupRoster with
  | .group, some r => RegisterMatchesForms r ev l
  | .oneToOne, none => ev.formsMatch l ∧ ev.effectiveForms.length = 1
  | _, _ => False

def StartEvidence.formForRoster (ev : StartEvidence) (l : Lesson) (r : Roster)
    (f : PartOne) : Prop :=
  f.lesson = l ∧ f.matches ∧ FormUsesRoster f r ∧
  (f ∈ ev.effectiveForms ∨ ∃ booking, (f, booking) ∈ ev.bookings) ∧
  (∀ locked, ev.groupRoster = some locked → f.place ∈ locked.places → f ∈ ev.effectiveForms)

def EffectiveRosterAt (r : Roster) (ev : StartEvidence) (l : Lesson) (query : Moment) : Prop :=
  (∃ locked, RegisterMatchesForms locked ev l ∧ locked.valid l locked.lockedAt ∧
    match ev.rosterReview with
    | none => r = locked
    | some history =>
      history.applies l (ev.effectiveForms ++ ev.bookings.map Prod.fst)
        locked history.originalOutcome locked.lockedAt
        (history.corrections.filter (fun row ↦ decide (row.record.recordedAt.by query))) r) ∧
  ∀ p ∈ r.places, ∃ f, ev.formForRoster l r f ∧ f.place = p

def StartEvidence.rosterFormsAt (ev : StartEvidence) (l : Lesson) (query : Moment)
    (roster : Option Roster) (forms : List PartOne) : Prop :=
  match l.kind, roster with
  | .oneToOne, none => ev.rosterMatchesForms l ∧ forms = ev.effectiveForms
  | .group, some r =>
      EffectiveRosterAt r ev l query ∧ (forms.map (·.place.id)).Nodup ∧
      (∀ f ∈ forms, ev.formForRoster l r f) ∧
      ∀ p ∈ r.places, ∃ f ∈ forms, f.place = p
  | _, _ => False

/-- Arrangement decisions use their own historical register. Settlement and
start checks still use the roster actually fixed for the lesson. -/
def StartEvidence.arrangementFormsAt (ev : StartEvidence) (l : Lesson) (query : Moment)
    (roster : Option Roster) (forms : List PartOne) : Prop :=
  match l.kind, roster with
  | .group, none =>
    (∀ locked ∈ ev.groupRoster, query.before locked.lockedAt) ∧
    ∃ snapshot ∈ ev.groupRegisters,
      snapshot.atTime = query ∧ snapshot.conforms l ∧ ev.verifiesGroupRegister snapshot ∧
      forms = snapshot.forms
  | .group, some locked =>
    (∃ original ∈ ev.groupRoster, original.lockedAt.by query) ∧
    ev.rosterFormsAt l query (some locked) forms
  | _, _ => ev.rosterFormsAt l query roster forms

/-- Prefer the actual roster at confirmation; a later roster does not
retroactively change the class or funding scope of an earlier booking. -/
def StartEvidence.readsBookedRoster (ev : StartEvidence) (f : PartOne)
    (roster : Option Roster) (observed : Moment) (booked : Option Roster) : Prop :=
  (∃ original ∈ booked, (f, original) ∈ ev.bookedRosters) ∨
  ((∀ original, (f, original) ∉ ev.bookedRosters) ∧
    (booked = ev.groupRoster ∨ booked = roster ∨
      ∃ earlier point, booked = some earlier ∧ f.confirmedAt.by point ∧ point.by observed ∧
        EffectiveRosterAt earlier ev f.lesson point))

def StartEvidence.latestReplacement (ev : StartEvidence) (l : Lesson) (visible : Moment → Prop)
    (active : Option TutorReplacement) : Prop :=
  let recorded := fun r : TutorReplacement ↦ r.record.originalLesson = l.id ∧ visible r.effectiveAt
  match active with
  | none => ∀ r ∈ ev.tutorReplacements, ¬ recorded r
  | some r => r ∈ ev.tutorReplacements ∧ recorded r ∧
    ∀ other ∈ ev.tutorReplacements, recorded other → other.effectiveAt.by r.effectiveAt

def TutorReplacement.conforms (r : TutorReplacement) (l : Lesson) (ev : StartEvidence) : Prop :=
  let next := r.record.nextSchedule
  let tutor := r.agreement.tutor
  r.record.originalLesson = l.id ∧ next.lesson = l.id ∧
  next.effectiveAtQuery ev.scheduleHistory r.effectiveAt ∧
  r.previous ∈ ev.scheduleHistory ∧ r.previous.lesson = l.id ∧ r.previous.valid ∧
  (if next.confirmationTarget = r.previous.confirmationTarget then next = r.previous
   else r.previous.effectiveAt.before next.effectiveAt ∧ next.effectiveAt = r.effectiveAt ∧
     next.agreedAt = r.agreedAt ∧ ∃ change ∈ ev.changes, change.previous = r.previous ∧
       change.record = r.record) ∧
  r.agreedAt.by r.effectiveAt ∧
  (∀ began, ev.teachingBegan = some began →
    r.agreedAt.before began ∧ r.effectiveAt.by began) ∧
  r.record.separateBooking = none ∧ r.record.replacementTutor = some tutor ∧
  r.agreement.lesson = l.id ∧ r.agreement.provider = l.provider ∧
  r.agreement.reference ≠ "" ∧ 0 ≤ r.agreement.fee ∧ r.agreement.payment.valid ∧
  r.agreement.tutorResponsibilities ≠ "" ∧ r.agreement.providerResponsibilities ≠ "" ∧
  r.agreement.signed ∧ r.agreement.termsAgreedAt.before r.accepted.point ∧
  r.accepted.forActor tutor next.confirmationTarget r.agreedAt ∧
  r.providerConsent.forActor l.provider (.replacementTutor l.id tutor) r.agreedAt ∧
  (∀ channel, r.noticeChannel = some channel → channel ≠ "") ∧
  ∃ roster forms prior, ev.arrangementFormsAt l r.agreedAt roster forms ∧
    (∀ place ∈ r.record.scope, ∃ f ∈ forms, place = f.place.id) ∧
    ev.latestReplacement l (fun t ↦ t.before r.effectiveAt) prior ∧
    let previousTutor := (prior.map (·.agreement.tutor)).getD l.tutor
    tutor ≠ previousTutor ∧
    ∀ f ∈ forms,
      f.confirmedAt.before r.agreedAt ∧ f.serviceTerms = r.agreement.service ∧
      f.serviceItems = r.agreement.serviceItems ∧
      r.record.matchesFrom f r.previous previousTutor (ev.academicTeamAt l.id) r.agreedAt

def StartEvidence.effectiveReplacement (ev : StartEvidence) (l : Lesson) (query : Moment)
    (active : Option TutorReplacement) : Prop :=
  let sameLesson := ev.tutorReplacements.filter (fun r ↦ r.record.originalLesson == l.id)
  (sameLesson.map (·.effectiveAt)).Nodup ∧
  (∀ r ∈ sameLesson, r.effectiveAt.by query → r.conforms l ev) ∧
  ev.latestReplacement l (fun t ↦ t.by query) active

def EffectiveTutorAt (l : Lesson) (ev : StartEvidence) (query : Moment) (tutor : ActorId) : Prop :=
  ∃ active, ev.effectiveReplacement l query active ∧
    tutor = (active.map (·.agreement.tutor)).getD l.tutor

/-- The signed form uses the teaching assignment and terms in force at its own confirmation. -/
def StartEvidence.readsTutorAtConfirmation (ev : StartEvidence) (f : PartOne) : Prop :=
  ∃ active, ev.effectiveReplacement f.lesson f.confirmedAt active ∧
    match active with
    | none => f.agreedTutor = f.lesson.tutor ∧ f.agreedTutorFee = f.lesson.normalTutorFee
    | some replacement =>
      let agreement := replacement.agreement
      f.agreedTutor = agreement.tutor ∧ f.serviceTerms = agreement.service ∧
      f.serviceItems = agreement.serviceItems ∧
      ev.tutorPayAmendments.termsAt f.lesson agreement.tutor
        ⟨agreement.reference, agreement.fee, agreement.payment⟩ agreement.termsAgreedAt
        f.confirmedAt ⟨f.tutorAgreementRef, f.agreedTutorFee, f.deadlines.tutorPay⟩

def StartEvidence.confirmedBookingFor (ev : StartEvidence) (f : PartOne)
    (roster : Option Roster) (observed : Moment) : Prop :=
  ∃ booking bookedRoster, (f, booking) ∈ ev.bookings ∧
    ev.readsBookedRoster f roster observed bookedRoster ∧
    CanConfirmPlace f booking bookedRoster ev.openingCredit ev.ledger ev.creditRecords
      ev.discounts ev.teachingBegan ∧ ev.readsTutorAtConfirmation f

def EffectiveTutorAgreementAt (f : PartOne) (ev : StartEvidence) (query : Moment)
    (tutor : ActorId) (reference : String) (normalFee : Amount) (payment : PaymentTerms)
    (observed : Moment := query) (termsAt : Moment := query) : Prop :=
  f.matches ∧ query.by termsAt ∧ termsAt.by observed ∧
  (f ∈ ev.effectiveForms ∨ ∃ roster forms, ev.rosterFormsAt f.lesson observed roster forms ∧
    f ∈ forms ∧ ev.confirmedBookingFor f roster observed) ∧
  ∃ active, ev.effectiveReplacement f.lesson query active ∧
    match active with
    | none =>
      tutor = f.lesson.tutor ∧
      let original : TutorPayTerms :=
        ⟨f.tutorAgreementRef, f.lesson.normalTutorFee, f.deadlines.tutorPay⟩
      let selected : TutorPayTerms := ⟨reference, normalFee, payment⟩
      let scope := (f.lesson.id, tutor)
      if f.agreedTutor ≠ tutor ∨ f.agreedTutorFee ≠ f.lesson.normalTutorFee then False
      else if ev.tutorPayAmendments.amendments.any
          (fun change ↦ change.replacement.scope == scope) then
        ∃ signedForm booking, (signedForm, booking) ∈ ev.bookings ∧
          signedForm.lesson = f.lesson ∧ signedForm.tutorAgreementRef = f.tutorAgreementRef ∧
          signedForm.agreedTutor = tutor ∧ signedForm.agreedTutorFee = f.lesson.normalTutorFee ∧
          signedForm.deadlines.tutorPay = f.deadlines.tutorPay ∧
          booking.tutorAgreement.agreedBeforeAcceptance signedForm booking.signatures ∧
          ev.tutorPayAmendments.termsAt f.lesson tutor original booking.tutorAgreement.termsAgreedAt
            termsAt selected
      else
        f.confirmedAt.by termsAt ∧ selected = original
    | some r => tutor = r.agreement.tutor ∧
        ev.tutorPayAmendments.termsAt f.lesson tutor
          ⟨r.agreement.reference, r.agreement.fee, r.agreement.payment⟩ r.agreement.termsAgreedAt
          termsAt ⟨reference, normalFee, payment⟩

/-- Accepting a lesson incurs the duty to provide the agreed teaching.
    Whether it was provided remains a distinct fact. -/
def AgreedTeachingOwed (f : PartOne) (ev : StartEvidence) (tutor : ActorId)
    (atTime : Moment) (serviceItems : List Nat) : Prop :=
  f.matches ∧ ∃ replacement, ev.effectiveReplacement f.lesson atTime replacement ∧
    match replacement with
    | none => tutor = f.lesson.tutor ∧ f.agreedTutor = tutor ∧ serviceItems = f.serviceItems ∧
      ∃ entry ∈ ev.bookings,
        entry.1 = f ∧ entry.2.signatures.tutorSigner = tutor ∧
        entry.2.signatures.tutorAccepted.by atTime ∧
        entry.2.tutorAgreement.agreedBeforeAcceptance f entry.2.signatures
    | some assignment => tutor = assignment.agreement.tutor ∧
      assignment.accepted.point.by atTime ∧ serviceItems = assignment.agreement.serviceItems

def AgreedScheduleChange.records (change : AgreedScheduleChange) (l : Lesson)
    (ev : StartEvidence) (roster : Option Roster) (forms : List PartOne) : Prop :=
  let next := change.record.nextSchedule
  ev.arrangementFormsAt l next.agreedAt roster forms ∧ next.lesson = l.id ∧ next.valid ∧
  change.previous ∈ ev.scheduleHistory ∧ change.previous.lesson = l.id ∧
  change.previous.effectiveAt.by next.agreedAt ∧
  change.previous.effectiveAt.before next.effectiveAt ∧
  change.previous.confirmationTarget ≠ next.confirmationTarget ∧
  (∀ earlier ∈ ev.scheduleHistory, earlier.lesson = l.id →
    earlier.effectiveAt.before next.effectiveAt →
    earlier.effectiveAt.by change.previous.effectiveAt) ∧
  (∀ began, ev.teachingBegan = some began →
    next.agreedAt.before began ∧ next.effectiveAt.by began) ∧
  change.record.separateBooking = none ∧
  (∀ tutor, change.record.replacementTutor = some tutor →
    ∃ r ∈ ev.tutorReplacements, r.record = change.record ∧ r.previous = change.previous ∧
      r.agreedAt = next.agreedAt ∧ r.effectiveAt = next.effectiveAt ∧ r.conforms l ev) ∧
  (∀ place ∈ change.record.scope, ∃ f ∈ forms, place = f.place.id) ∧
  (change.record.replacementTutor = none →
    ∀ f ∈ forms, change.record.matchesFrom f change.previous l.tutor (ev.academicTeamAt l.id))

private def AgreedScheduleChange.priorSchedules (change : AgreedScheduleChange) (l : Lesson)
    (ev : StartEvidence) : List Schedule :=
  ev.scheduleHistory.filter (fun row ↦
    row.lesson == l.id && decide (row.effectiveAt.before change.record.nextSchedule.effectiveAt))

private def groupRescheduleOnPriorSchedules (l : Lesson) (ev : StartEvidence)
    (change : AgreedScheduleChange) : Prop :=
  let next := change.record.nextSchedule
  ∃ roster forms tutor, change.records l ev roster forms ∧
    (∀ f ∈ forms, ∃ window ∈ f.groupRescheduleCutoff,
      window.allowsFrom f.schedule change.previous (change.priorSchedules l ev) next.agreedAt
        f.confirmedAt ev.clockBoundaries) ∧
    EffectiveTutorAt l ev
      (if change.record.replacementTutor.isSome then next.effectiveAt else next.agreedAt) tutor ∧
    GroupReschedule l (forms.map (·.place)) change.record.consents next change.approvals
      ev.teachingBegan tutor

private def AgreedScheduleChange.allowedOnPriorSchedules (change : AgreedScheduleChange) (l : Lesson)
    (ev : StartEvidence) : Prop :=
  let s := change.record.nextSchedule
  groupRescheduleOnPriorSchedules l ev change ∨
    (l.kind = .oneToOne ∧ change.records l ev none ev.effectiveForms ∧
      (∀ f ∈ ev.effectiveForms, change.compliesWithOneToOneTerms f.cancelChangeTerms ∧
        ∀ window ∈ f.oneToOneRescheduleWindow,
          window.allowsFrom f.schedule change.previous (change.priorSchedules l ev) s.agreedAt
            f.confirmedAt ev.clockBoundaries) ∧
      ∃ tutor, EffectiveTutorAt l ev s.effectiveAt tutor ∧
        ∀ actor ∈ [tutor, l.provider], ∃ c ∈ change.approvals,
          c.forActor actor s.confirmationTarget s.agreedAt)

def StartEvidence.verifiedLockedRegister (ev : StartEvidence) (l : Lesson)
    (locked : Roster) : Prop :=
  let register : GroupRegisterSnapshot := ⟨l.id, locked.lockedAt, ev.effectiveForms⟩
  RegisterMatchesForms locked ev l ∧ register.conforms l ∧ ev.verifiesGroupRegister register

/-- The first group's date can come from a retained commitment or a
verified historical register. A later member's form can carry a revised date. -/
def GroupOriginalSchedule (l : Lesson) (ev : StartEvidence) (s : Schedule) : Prop :=
  l.kind = .group ∧
  (∀ row ∈ ev.scheduleHistory, row.lesson = l.id → s.effectiveAt.by row.effectiveAt) ∧
  (((∃ f booking, (f, booking) ∈ ev.bookings ∧ f.matches ∧ f.lesson = l ∧ f.schedule = s ∧
      booking.signatures.valid f (booking.debit.map (·.point)) ∧
      booking.tutorAgreement.agreedBeforeAcceptance f booking.signatures ∧
      booking.signatures.providerAccepted.by f.confirmedAt ∧
      booking.signatures.tutorAccepted.by f.confirmedAt ∧
      booking.signatures.customerAccepted.by f.confirmedAt ∧
      (∀ acceptance ∈ booking.signatures.payerAccepted, acceptance.2.by f.confirmedAt)) ∨
    (∃ locked ∈ ev.groupRoster, ev.verifiedLockedRegister l locked ∧
      ∃ f ∈ ev.effectiveForms, f.schedule = s)) ∨
    ∃ snapshot ∈ ev.groupRegisters, snapshot.conforms l ∧ ev.verifiesGroupRegister snapshot ∧
      ∃ f ∈ snapshot.forms, f.schedule = s)

def ScheduleWasAgreed (l : Lesson) (ev : StartEvidence) (s : Schedule) : Prop :=
  s.lesson = l.id ∧ s.valid ∧
  ((l.kind = .oneToOne ∧ ev.rosterMatchesForms l ∧ ∀ f ∈ ev.effectiveForms, f.schedule = s) ∨
    GroupOriginalSchedule l ev s ∨
    ∃ change ∈ ev.changes, change.record.nextSchedule = s ∧ change.allowedOnPriorSchedules l ev)

def EffectiveSchedule (l : Lesson) (ev : StartEvidence) (s : Schedule) (query : Moment) :
    Prop :=
  s.lesson = l.id ∧ s.effectiveAtQuery ev.scheduleHistory query ∧
  ((ev.scheduleHistory.filter (fun row ↦ row.lesson == l.id)).map (·.effectiveAt)).Nodup ∧
  ∀ row ∈ ev.scheduleHistory, row.lesson = l.id → row.effectiveAt.by query →
    ScheduleWasAgreed l ev row

private def AgreedScheduleChange.priorSchedulesAgreed (change : AgreedScheduleChange) (l : Lesson)
    (ev : StartEvidence) : Prop :=
  let prior := change.priorSchedules l ev
  (prior.map (·.effectiveAt)).Nodup ∧ ∀ row ∈ prior, ScheduleWasAgreed l ev row

def CanRescheduleGroup (l : Lesson) (ev : StartEvidence) (change : AgreedScheduleChange) : Prop :=
  change.priorSchedulesAgreed l ev ∧ groupRescheduleOnPriorSchedules l ev change

def AgreedScheduleChange.allowed (change : AgreedScheduleChange) (l : Lesson)
    (ev : StartEvidence) : Prop :=
  change.priorSchedulesAgreed l ev ∧ change.allowedOnPriorSchedules l ev

/-- The thirty-day clock starts on the first agreed start that actually remains in force
    at that point in the schedule history. -/
def AgreedStartClock (l : Lesson) (ev : StartEvidence) (query base : Moment) : Prop :=
  base.by query ∧
  (∃ s, s.start = base ∧ EffectiveSchedule l ev s base) ∧
  ∀ s ∈ ev.scheduleHistory, EffectiveSchedule l ev s s.start → s.start.by query →
    base.by s.start

def EffectiveLessonPeriod (l : Lesson) (ev : StartEvidence) (current : Schedule)
    (query : Moment) (evidence : PeriodStartEvidence) (selected : Moment) : Prop :=
  EffectiveSchedule l ev current query ∧
  match evidence with
  | .unknown => False
  | .verifiedNotStarted => selected = current.start
  | .verifiedStart began =>
    began.by query ∧ ∃ atStart, EffectiveSchedule l ev atStart began ∧ selected = atStart.start

/-- A start-linked period uses the new start only before its clock has begun. -/
def LessonDeadlineAnchor (l : Lesson) (ev : StartEvidence) (query anchor : Moment) : Prop :=
  ∃ schedule,
    (∃ original, AgreedStartClock l ev query original ∧
      EffectiveLessonPeriod l ev schedule query (.verifiedStart original) anchor) ∨
    ((¬∃ earlier, AgreedStartClock l ev query earlier) ∧
      EffectiveLessonPeriod l ev schedule query .verifiedNotStarted anchor)

def _root_.SourceV14.Confirmation.PaymentDeadline.appliesForLesson (term : PaymentDeadline) (l : Lesson) (ev : StartEvidence)
    (query : Moment) (actual : Option PaymentTrigger) (deadline : Moment) : Prop :=
  term.applies actual deadline ∧
  match term with
  | .after _ _ true =>
    ∃ event ∈ actual, event.boundaries = ev.clockBoundaries ∧ LessonDeadlineAnchor l ev query event.point
  | _ => True

def StartEvidence.noticesFor (ev : StartEvidence) (s : Schedule) : List Notice :=
  ev.notices ++ ev.changes.flatMap
    (fun change ↦ if change.record.nextSchedule = s then change.record.notices else []) ++
  ev.tutorReplacements.flatMap
    (fun change ↦ if change.record.nextSchedule = s then change.record.notices else [])

def StartEvidence.feeAt (ev : StartEvidence) (f : PartOne) (query : Moment)
    (fee : Amount) : Prop :=
  ev.creditRecords.lessonFees.feeAt f query fee

def StartEvidence.paidInFull (ev : StartEvidence) (f : PartOne) (query : Moment) : Prop :=
  ev.creditRecords.lessonFees.paidInFull f ev.ledger ev.discounts query

def StartEvidence.paidAtStart (ev : StartEvidence) (f : PartOne) (start : Moment) : Prop :=
  ev.creditRecords.lessonFees.paidInFull f
    (ev.ledger.filter (fun entry ↦ decide (entry.point.before start)))
    (ev.discounts.filter (fun discount ↦ decide (discount.point.before start))) start

def CanStart (l : Lesson) (ev : StartEvidence) (s : Schedule) (occurred : Moment) : Prop :=
  let notices := ev.noticesFor s
  EffectiveSchedule l ev s occurred ∧ s.start.by occurred ∧
  ∃ roster forms active, ev.rosterFormsAt l occurred roster forms ∧
    (∀ r ∈ roster.toList, r.valid l s.start) ∧
    ValidCreditHistory ev.openingCredit
      (ev.ledger.filter (fun e ↦ decide (e.point.before occurred))) ev.creditRecords
      (fun t ↦ t.before occurred) ∧
    (∀ student ∈ ev.studentsTakingLesson, ∃ f ∈ forms, f.place.student = student) ∧
    (l.kind = .group → ev.studentsTakingLesson ≠ []) ∧
    ev.effectiveReplacement l occurred active ∧
    let tutor := (active.map (·.agreement.tutor)).getD l.tutor
    ∀ f ∈ forms,
      let tutorChannel := (active.map (·.noticeChannel)).getD f.contacts.tutorNotice
      f.confirmedAt.before occurred ∧ ev.confirmedBookingFor f roster occurred ∧
      ev.paidAtStart f occurred ∧
      (∃ n ∈ notices, NoticePerformed n s.confirmationTarget f.place.student f.contacts.studentNotice ∧
        ev.academicTeamAt l.id n.sender n.point ∧ n.point.before occurred) ∧
      (∃ n ∈ notices, n.target = s.confirmationTarget ∧ n.recipient = tutor ∧ n.channel ≠ "" ∧
        (∀ channel, tutorChannel = some channel → n.channel = channel) ∧ n.point.before occurred ∧
        (n.sender = l.provider ∨ ev.academicTeamAt l.id n.sender n.point)) ∧
      -- A place signed after the change uses the operative teaching assignment on its Part 1.
      ∀ replacement ∈ active.toList, f.confirmedAt.before replacement.effectiveAt →
        f.place.id ∈ replacement.record.scope ∧
        ∃ n ∈ replacement.record.notices,
          NoticePerformed n (.replacementTutor l.id tutor) f.place.student f.contacts.studentNotice ∧
          ev.academicTeamAt l.id n.sender n.point ∧
          replacement.agreedAt.by n.point ∧ n.point.before occurred

def CanConfirmSeparateBooking (original next : PartOne) (change : ChangeRecord)
    (booking : BookingEvidence) (ev : StartEvidence) : Prop :=
  original.matches ∧ original.lesson.id ≠ next.lesson.id ∧
  change.separateBooking = some next.lesson.id ∧ change.replacementTutor = none ∧
  change.nextSchedule = next.schedule ∧ change.matches original (ev.academicTeamAt original.lesson.id) ∧
  CanConfirmPlace next booking ev.groupRoster ev.openingCredit ev.ledger ev.creditRecords
    ev.discounts ev.teachingBegan

def StartEvidence.reportedAfterLesson (ev : StartEvidence) (point query : Moment) : Prop :=
  ∃ started ended, ev.teachingBegan = some started ∧ ev.teachingEnded = some ended ∧
    started.by ended ∧ ended.by point ∧ point.by query

/-- §2.4 and Form Part 2 permit a student's report about an agreed occurrence with no teaching. -/
def StartEvidence.reportedStudentOccurrence (ev : StartEvidence) (f : PartOne)
    (point : Moment) : Prop :=
  ev.reportedAfterLesson point point ∨
  (ev.teachingBegan = none ∧ ev.teachingEnded = none ∧
    ∃ schedule, EffectiveSchedule f.lesson ev schedule schedule.start ∧
      f.confirmedAt.by schedule.start ∧ schedule.start.by point)

def AttendanceReportRecorded (ev : StartEvidence) (l : Lesson) (p : Place)
    (query : Moment) (r : AttendanceReport) : Prop :=
  r ∈ ev.afterLesson.attendance ∧ AttendanceConcerns l p r ∧ ev.reportedAfterLesson r.point query

def AttendanceRecorded (ev : StartEvidence) (l : Lesson) (p : Place)
    (query : Moment) (attended : Bool) : Prop :=
  ∃ r, AttendanceReportRecorded ev l p query r ∧ r.attended = attended ∧
    ∀ other, AttendanceReportRecorded ev l p query other →
      other.point.by r.point ∧ (other.point = r.point → other.attended = attended)

def ServiceFeedbackRecorded (ev : StartEvidence) (f : PartOne)
    (query : Moment) (report : DeliveryReport) : Prop :=
  report ∈ ev.afterLesson.serviceFeedback ∧ ServiceFeedbackConcerns f report ∧
    ev.reportedAfterLesson report.point query

def StudentCompletionRecorded (ev : StartEvidence) (f : PartOne) (query : Moment)
    (report : StudentCompletionReport) : Prop :=
  report ∈ ev.afterLesson.studentCompletions ∧ report.lesson = f.lesson.id ∧
    report.place = f.place.id ∧ report.student = f.place.student ∧
    report.coordinator = f.lesson.coordinator ∧ ev.reportedAfterLesson report.point query

def StudentReportingComplete (ev : StartEvidence) (f : PartOne) (query : Moment) : Prop :=
  (∃ attended, AttendanceRecorded ev f.lesson f.place query attended) ∧
    ∀ service ∈ f.serviceItems, ∃ report, ServiceFeedbackRecorded ev f query report ∧
      (service ∈ report.servicesReceived ∨ service ∈ report.servicesNotReceived)

def TutorDeliveryRecorded (ev : StartEvidence) (l : Lesson) (query : Moment)
    (report : TutorDeliveryReport) : Prop :=
  report ∈ ev.afterLesson.tutorReports ∧ report.lesson = l.id ∧
    (∃ began, ev.teachingBegan = some began ∧ EffectiveTutorAt l ev began report.tutor) ∧
    report.coordinator = l.coordinator ∧ report.details ≠ "" ∧
    ev.reportedAfterLesson report.point query

/-- The tutor reports and the coordinator contacts each student who has not replied.
    A partial reply is recorded as such. -/
def TutorAndCoordinatorReported (ev : StartEvidence) (l : Lesson) (query : Moment) : Prop :=
  (∃ report, TutorDeliveryRecorded ev l query report) ∧
  ∃ roster forms, ev.rosterFormsAt l query roster forms ∧
    ∀ f ∈ forms,
      (∃ report, AttendanceReportRecorded ev l f.place query report) ∨
      (∃ report, ServiceFeedbackRecorded ev f query report ∧
        (report.servicesReceived ≠ [] ∨ report.servicesNotReceived ≠ [])) ∨
      (∃ report, StudentCompletionRecorded ev f query report) ∨
      (∃ ended, ev.teachingEnded = some ended ∧ ∃ followUp ∈ ev.afterLesson.followUps,
        FollowUpPerformed followUp l f.place ended query)

def GroupReportsMatch (ev : StartEvidence) (l : Lesson) (r : Roster) (query : Moment)
    (tutorCompleted : Bool) (attendanceConfirmed faultFound : List PlaceId) : Prop :=
  (tutorCompleted = true ↔ ∃ report, TutorDeliveryRecorded ev l query report ∧
    report.completed = true) ∧
  ∀ p ∈ r.places,
    (p.id ∈ attendanceConfirmed ↔ AttendanceRecorded ev l p query true) ∧
    (p.id ∈ faultFound ↔ ∃ f, ev.formForRoster l r f ∧ f.place = p ∧
      ev.studentFaults.foundAtFault f query)

noncomputable def StartEvidence.groupConfirmationCount (ev : StartEvidence)
    (r : Roster) (l : Lesson) (query : Moment) (attendanceConfirmed faultFound : List PlaceId) : Nat := by
  classical
  exact (r.places.filter fun place ↦ decide (
    place.id ∈ attendanceConfirmed ∧ place.id ∉ faultFound ∧
    ∃ f, ev.formForRoster l r f ∧ f.place = place ∧
      ∃ start, ev.teachingBegan = some start ∧ start.by query ∧ ev.paidAtStart f start)).length

/-- §4.2 uses payment measured from actual entries and confirmed attendance per place. -/
def CanSettleGroupNormally (l : Lesson) (ev : StartEvidence) (s : Schedule)
    (r : Roster) (actualStart query : Moment)
    (tutorReportedCompletion : Bool) (attendanceConfirmed faultFound : List PlaceId) : Prop :=
  EffectiveRosterAt r ev l query ∧ ev.teachingBegan = some actualStart ∧ actualStart.by query ∧
  GroupReportsMatch ev l r query tutorReportedCompletion attendanceConfirmed faultFound ∧
  l.kind = .group ∧ r.valid l s.start ∧ CanStart l ev s actualStart ∧
  tutorReportedCompletion = true ∧
  r.places.length < 2 * ev.groupConfirmationCount r l query attendanceConfirmed faultFound

def GroupSettlementAvailable (l : Lesson) (ev : StartEvidence) (s : Schedule)
    (r : Roster) (actualStart expiry query : Moment)
    (tutorReportedCompletion factsVerified : Bool) (handler : Handler)
    (attendanceConfirmed faultFound : List PlaceId) : Prop :=
  let usual := CanSettleGroupNormally l ev s r actualStart query tutorReportedCompletion
    attendanceConfirmed faultFound
  handler.maySettle l ∧
  GroupReportsMatch ev l r query tutorReportedCompletion attendanceConfirmed faultFound ∧
  (usual ∨ (EffectiveRosterAt r ev l query ∧ EffectiveSchedule l ev s query ∧
      ∃ base, AgreedStartClock l ev query base ∧
        ClockBoundary.reachedAfter ev.clockBoundaries base thirtyDays query ∧
        GroupVerified l r usual base expiry query factsVerified))

def OneToOneReportsMatch (ev : StartEvidence) (l : Lesson) (query : Moment)
    (studentConfirmed tutorConfirmed coordinatorConfirmed : Bool) : Prop :=
  (studentConfirmed = true ↔ ∃ f ∈ ev.effectiveForms, f.lesson = l ∧ ∃ report,
    StudentCompletionRecorded ev f query report) ∧
  (tutorConfirmed = true ↔ ∃ report, TutorDeliveryRecorded ev l query report ∧
    report.completed = true) ∧
  (coordinatorConfirmed = true ↔ ∃ confirmation ∈ ev.afterLesson.coordinatorConfirmations,
    confirmation.1 = l.coordinator ∧ ev.reportedAfterLesson confirmation.2 query)

def CanSettleOneToOneNormally (l : Lesson) (ev : StartEvidence) (s : Schedule)
    (actualStart query : Moment)
    (studentConfirmed tutorConfirmed coordinatorConfirmed : Bool) : Prop :=
  ev.teachingBegan = some actualStart ∧ actualStart.by query ∧
  OneToOneReportsMatch ev l query studentConfirmed tutorConfirmed coordinatorConfirmed ∧
  OneToOneUsual l (CanStart l ev s actualStart) studentConfirmed tutorConfirmed coordinatorConfirmed

def OneToOneSettlementAvailable (l : Lesson) (ev : StartEvidence) (s : Schedule)
    (actualStart expiry query : Moment)
    (studentConfirmed tutorConfirmed coordinatorConfirmed factsVerified : Bool)
    (handler : Handler) : Prop :=
  handler.maySettle l ∧
  OneToOneReportsMatch ev l query studentConfirmed tutorConfirmed coordinatorConfirmed ∧
  (CanSettleOneToOneNormally l ev s actualStart query
      studentConfirmed tutorConfirmed coordinatorConfirmed ∨
    (EffectiveSchedule l ev s query ∧ ∃ base, AgreedStartClock l ev query base ∧
      ClockBoundary.reachedAfter ev.clockBoundaries base thirtyDays query ∧
      OneToOneVerified l base expiry query
        studentConfirmed tutorConfirmed coordinatorConfirmed factsVerified))

structure CancellationRequest where
  lesson : LessonId
  place : PlaceId
  customer : ActorId
  coordinator : ActorId
  point : Moment
  deriving Repr

def CancellationRequest.matches (r : CancellationRequest) (f : PartOne) : Prop :=
  r.lesson = f.lesson.id ∧ r.place = f.place.id ∧ r.customer = f.place.customer ∧
    r.coordinator = f.lesson.coordinator

def CanCancelOneToOne (f : PartOne) (r : CancellationRequest)
    (ev : StartEvidence) : Prop :=
  f.matches ∧ r.matches f ∧ f.lesson.kind = .oneToOne ∧
  (∀ began ∈ ev.teachingBegan, r.point.before began) ∧
  ∃ window ∈ f.oneToOneAdvanceCutoff,
    match window with
    | .fixed .. =>
      window.allows f.schedule.start r.point ev.clockBoundaries ∧
      ∃ current, EffectiveSchedule f.lesson ev current r.point ∧ r.point.before current.start
    | .beforeLessonStart .. =>
      f ∈ ev.effectiveForms ∧ ∃ current, EffectiveSchedule f.lesson ev current r.point ∧
        window.allowsFrom f.schedule current ev.scheduleHistory r.point f.confirmedAt ev.clockBoundaries

structure RearrangementContact where
  lesson : LessonId
  coordinator : ActorId
  recipient : ActorId
  point : Moment
  deriving Repr

structure NoFaultCancellationRecord where
  schedule : Schedule
  disruptionVerifiedAt : Moment
  cannotProceed : Bool
  anyPartyAtFault : Bool
  affected : List ActorId
  contacts : List RearrangementContact
  newAcceptance : Option Moment
  cancellation : CancellationRequest
  refundObligation : ObligationId
  underTerms : String → Prop
  noneTaught : Bool
  undeliveredAgreedValue : Amount
  /-- Verified teaching and its undelivered value for the affected place. -/
  undeliveredAt : LessonId → PlaceId → Moment → Bool → Amount → Prop

def NoFaultCancellationRecord.conforms (r : NoFaultCancellationRecord) (f : PartOne)
    (ev : StartEvidence) : Prop :=
  (∃ roster forms, ev.rosterFormsAt f.lesson r.cancellation.point roster forms ∧ f ∈ forms) ∧
  r.cancellation.matches f ∧ r.underTerms f.noFaultTerms ∧
  r.undeliveredAt f.lesson.id f.place.id r.cancellation.point
    r.noneTaught r.undeliveredAgreedValue ∧
  EffectiveSchedule f.lesson ev r.schedule r.disruptionVerifiedAt ∧
  f.place.customer ∈ r.affected ∧
  (∀ actor ∈ r.affected, ∃ contact ∈ r.contacts,
    contact.lesson = f.lesson.id ∧ contact.coordinator = f.lesson.coordinator ∧
    contact.recipient = actor ∧ r.disruptionVerifiedAt.by contact.point ∧
    contact.point.by f.deadlines.noFaultAcceptance) ∧
  NoFaultCancellation r.cannotProceed r.anyPartyAtFault f.deadlines.noFaultAcceptance
    r.cancellation.point r.newAcceptance ∧
  0 ≤ r.undeliveredAgreedValue

def NoFaultCancellationRecord.refundAmount (r : NoFaultCancellationRecord) (f : PartOne)
    (ev : StartEvidence) : Amount :=
  noFaultRefund (debitTotal f.place ev.ledger r.cancellation.point)
    r.undeliveredAgreedValue r.noneTaught

/-- §2.2/4.3. Record the amount under the same no-fault obligation and the return to the
    account actually debited. Timeliness and any hold remain separate from actual receipt. -/
def NoFaultRefundReceipt (f : PartOne) (ev : StartEvidence) (r : NoFaultCancellationRecord)
    (e : CreditPosting) (refund : ObligationId) (record : RefundRecord) : Prop :=
  r.conforms f ev ∧ r.cancellation.point.before e.point ∧
  record.basis = .noFaultCancellation ∧
  (∃ fee, ev.feeAt f r.cancellation.point fee ∧
    record.finalFee = (if r.noneTaught then 0 else fee - r.refundAmount f ev)) ∧
  record.matches f ev.ledger e.point "no-fault cancellation" r.cancellation.point record.due
    (r.refundAmount f ev) (some refund) ∧
  ValidLessonRefund f.place ev.ledger e refund (r.refundAmount f ev) false

end SourceV14.Course
