import SourceV14.Settlement

namespace SourceV14.Confirmation

open Booking Settlement

inductive DeadlineTerms where
  | fixed (due : Moment)
  | after (seconds : Nat)
  deriving DecidableEq, Repr

structure PaymentTrigger where
  reference : String
  point : Moment
  boundaries : List ClockBoundary := []
  deriving DecidableEq, Repr

inductive PaymentDeadline where
  | fixed (deadline : Moment)
  | after (seconds : Nat) (triggerRef : String) (basedOnLessonStart : Bool := false)
  deriving DecidableEq, Repr

def PaymentDeadline.valid (terms : PaymentDeadline) : Prop :=
  match terms with
  | .fixed _ => True
  | .after _ reference _ => reference ≠ ""

def PaymentDeadline.applies (terms : PaymentDeadline) (event : Option PaymentTrigger)
    (deadline : Moment) : Prop :=
  match terms with
  | .fixed specified => deadline = specified
  | .after seconds reference _ =>
    ∃ actual, event = some actual ∧ actual.reference = reference ∧ reference ≠ "" ∧
      ClockBoundary.find actual.boundaries actual.point .after seconds = some deadline

structure PaymentTerms where
  due : PaymentDeadline
  latestExecution : PaymentDeadline
  deriving DecidableEq, Repr

def PaymentTerms.valid (terms : PaymentTerms) : Prop :=
  terms.due.valid ∧ terms.latestExecution.valid

inductive AdvanceOpening where
  | fixed (point : Moment)
  | beforeLessonStart (seconds : Nat)
  | unspecified
  deriving DecidableEq, Repr

inductive AdvanceWindow where
  | fixed (cutoff : Moment) (opens : Option Moment := none)
  | beforeLessonStart (closesBefore : Nat) (opens : AdvanceOpening)
  deriving DecidableEq, Repr

/-- A relative boundary uses the verified cutoff in the actual ordered clock. -/
def AdvanceOpening.onSchedule (opening : AdvanceOpening) (start : Moment)
    (boundaries : List ClockBoundary) : Option Moment :=
  match opening with
  | .fixed point => some point
  | .beforeLessonStart lead => ClockBoundary.find boundaries start .before lead
  | .unspecified => none

private def advanceCutoffCompatible (boundaries : List ClockBoundary) (start : Moment)
    (lead : Nat) (cutoff : Moment) : Prop :=
  match (AdvanceOpening.beforeLessonStart lead).onSchedule start boundaries with
  | some recorded => cutoff = recorded
  | none => cutoff.seconds + lead = start.seconds

def AdvanceWindow.validAt (window : AdvanceWindow) (start : Moment) : Prop :=
  match window with
  | .fixed cutoff opens => ∀ openAt ∈ opens, openAt.by cutoff
  | .beforeLessonStart lead .unspecified => lead ≤ start.seconds
  | .beforeLessonStart lead (.fixed openAt) => openAt.seconds + lead ≤ start.seconds
  | .beforeLessonStart lead (.beforeLessonStart beginsBefore) =>
    lead ≤ beginsBefore ∧ beginsBefore ≤ start.seconds

def AdvanceWindow.allows (window : AdvanceWindow) (start request : Moment)
    (boundaries : List ClockBoundary) : Prop :=
  window.validAt start ∧
  match window with
  | .fixed cutoff opens => (∀ openAt ∈ opens, openAt.by request) ∧ request.by cutoff
  | .beforeLessonStart lead opening =>
    (match opening with
    | .unspecified => True
    | .fixed openAt => openAt.by request
    | .beforeLessonStart opensBefore =>
      ∀ openAt, advanceCutoffCompatible boundaries start opensBefore openAt → openAt.by request) ∧
    ClockBoundary.byBefore boundaries start lead request

/-- An open window keeps its original bounds. An unknown within-second order permits
    a request only if every compatible placement yields permission. -/
def AdvanceWindow.allowsFrom (window : AdvanceWindow) (original current : Schedule)
    (history : List Schedule) (request signedAt : Moment) (boundaries : List ClockBoundary) : Prop :=
  match window with
  | .fixed .. => window.allows original.start request boundaries
  | .beforeLessonStart _ .unspecified =>
    signedAt.by request ∧ current.lesson = original.lesson ∧
    current.effectiveAtQuery history request ∧
    window.allows original.start request boundaries ∧ window.allows current.start request boundaries ∧
    ∀ prior ∈ history, prior.lesson = original.lesson → signedAt.by prior.effectiveAt →
      prior.effectiveAt.by request → window.allows prior.start request boundaries
  | .beforeLessonStart closesBefore opening =>
    current.lesson = original.lesson ∧ current.effectiveAtQuery history request ∧
    ∀ cutoffAt : Moment → Nat → Moment,
      (∀ start lead, lead ≤ start.seconds →
        advanceCutoffCompatible boundaries start lead (cutoffAt start lead)) →
      let openingAt := fun start ↦
        match opening with
        | .fixed point => some point
        | .beforeLessonStart lead => some (cutoffAt start lead)
        | .unspecified => none
      let within := fun start point ↦ window.validAt start ∧
        (∀ openAt ∈ openingAt start, openAt.by point) ∧ point.by (cutoffAt start closesBefore)
      let started := fun (row : Schedule) (began : Moment) ↦
        row.lesson = original.lesson ∧ began.by request ∧
        ∃ nominal ∈ openingAt row.start,
          let available := if nominal.before row.effectiveAt then row.effectiveAt else nominal
          began = (if available.before signedAt then signedAt else available) ∧
          row.effectiveAtQuery history began ∧ within row.start began
      ∃ row began, started row began ∧
        (∀ other point, started other point → began.by point) ∧ within row.start request

structure PayAndReviewTerms where
  remedyAcceptance : PaymentDeadline
  noFaultAcceptance : Moment
  noFaultRefund : Option PaymentTerms
  compensation : PaymentTerms
  refund : PaymentTerms
  tutorPay : PaymentTerms
  materialsShares : PaymentTerms
  finalReply : PaymentDeadline
  finalReview : Moment
  temporaryHoldExpiry : Moment
  reviewerHandoff : Moment
  postLiftPay : DeadlineTerms
  deriving Repr

def PayAndReviewTerms.valid (terms : PayAndReviewTerms) : Prop :=
  terms.compensation.valid ∧ terms.refund.valid ∧ terms.tutorPay.valid ∧
  terms.materialsShares.valid ∧ terms.finalReply.valid ∧ terms.remedyAcceptance.valid ∧
  ∀ separatelyAgreed ∈ terms.noFaultRefund, separatelyAgreed.valid

def PayAndReviewTerms.noFaultRefundTerms (terms : PayAndReviewTerms) : PaymentTerms :=
  terms.noFaultRefund.getD terms.refund

structure Contacts where
  providerName : String
  providerContact : String
  studentNotice : String
  tutorNotice : Option String
  coordinatorContact : String
  leadAcademicTutor : ActorId
  leadContact : String
  substitute : Option ActorId
  substituteContact : Option String
  reviewer : ActorId
  reviewerContact : String
  alternativeContact : ActorId
  alternativeContactDetails : String
  alternativeCanTemporarilyHold : Bool
  escalationContact : ActorId
  escalationContactDetails : String
  deriving Repr

def Contacts.complete (c : Contacts) : Prop :=
  (∀ text ∈ [c.providerName, c.providerContact, c.studentNotice, c.coordinatorContact,
    c.leadContact, c.reviewerContact, c.alternativeContactDetails, c.escalationContactDetails],
    text ≠ "") ∧
  (∀ contact, c.tutorNotice = some contact → contact ≠ "") ∧
  (c.substitute.isSome = true →
    ∃ contact, c.substituteContact = some contact ∧ contact ≠ "")

structure PartOne where
  lesson : Lesson
  place : Place
  contacts : Contacts
  rulesVersion : String
  confirmedAt : Moment
  customerRepresentatives : List ActorId
  /-- The written form uses the declared schedule time zone for each of its times. -/
  schedule : Schedule
  additionalReferencedTerms : List String := []
  serviceTerms : String
  serviceItems : List Nat
  discountBasis : Option String
  privateRoster : Option Nat
  rosterLock : Option Moment
  groupRescheduleCutoff : Option AdvanceWindow
  oneToOneAdvanceCutoff : Option AdvanceWindow
  oneToOneRescheduleWindow : Option AdvanceWindow := none
  cancelChangeTerms : String
  noFaultTerms : String
  applicableStartTerms : String
  tutorAgreementRef : String
  absentGroupPlacePay : Option Amount
  materialsOrBundle : Option String
  materialsTermsRef : Option String
  materialsPayer : Option ActorId
  deadlines : PayAndReviewTerms
  /-- The tutor and fee recorded on this Part 1 when they differ from the original lesson. -/
  tutorAtBooking : Option (ActorId × Amount) := none
  deriving Repr

@[simp] def PartOne.agreedTutor (f : PartOne) : ActorId :=
  (f.tutorAtBooking.map Prod.fst).getD f.lesson.tutor

@[simp] def PartOne.agreedTutorFee (f : PartOne) : Amount :=
  (f.tutorAtBooking.map Prod.snd).getD f.lesson.normalTutorFee

def PartOne.matches (f : PartOne) : Prop :=
  f.rulesVersion = "1.5" ∧ f.place.matches f.lesson ∧ f.place.validFees ∧
  0 ≤ f.agreedTutorFee ∧ f.schedule.lesson = f.lesson.id ∧ f.schedule.valid ∧
  f.contacts.complete ∧ f.deadlines.valid ∧
  (∀ text ∈ [f.serviceTerms, f.cancelChangeTerms, f.noFaultTerms,
    f.applicableStartTerms, f.tutorAgreementRef], text ≠ "") ∧
  f.additionalReferencedTerms.Nodup ∧ (∀ ref ∈ f.additionalReferencedTerms, ref ≠ "") ∧
  f.serviceItems ≠ [] ∧ f.serviceItems.Nodup ∧
  (f.place.feePayable < f.place.normalFee →
    ∃ basis, f.discountBasis = some basis ∧ basis ≠ "") ∧
  (f.lesson.kind = .group →
    ∃ roster lock cutoff absencePay, f.privateRoster = some roster ∧
      f.rosterLock = some lock ∧ lock.by f.schedule.start ∧
      f.groupRescheduleCutoff = some cutoff ∧ f.absentGroupPlacePay = some absencePay ∧
      0 ≤ absencePay ∧ cutoff.validAt f.schedule.start) ∧
  (f.lesson.kind = .oneToOne →
    (∃ window ∈ f.oneToOneAdvanceCutoff, window.validAt f.schedule.start) ∧
    ∀ window ∈ f.oneToOneRescheduleWindow, window.validAt f.schedule.start) ∧
  (match f.materialsOrBundle, f.materialsTermsRef, f.materialsPayer with
  | none, none, none => True
  | some materials, some terms, some _ => materials ≠ "" ∧ terms ≠ ""
  | _, _, _ => False)

structure Signatures where
  providedLesson : LessonId
  providedPlace : PlaceId
  providedBy : ActorId
  providedTo : ActorId
  formProvided : Moment
  referencedTermsProvided : Moment
  providerSigner : ActorId
  providerAccepted : Moment
  tutorSigner : ActorId
  tutorAccepted : Moment
  customerAccepted : Moment
  customerSigner : ActorId
  payerAccepted : Option (ActorId × Moment)
  deriving Repr

def Signatures.valid (f : PartOne) (a : Signatures) (debit : Option Moment) : Prop :=
  a.providedLesson = f.lesson.id ∧ a.providedPlace = f.place.id ∧
  a.providedBy = f.lesson.coordinator ∧
  (a.providedTo = f.place.customer ∨ a.providedTo ∈ f.customerRepresentatives) ∧
  a.providerSigner = f.lesson.provider ∧ a.tutorSigner = f.agreedTutor ∧
  (a.customerSigner = f.place.customer ∨ a.customerSigner ∈ f.customerRepresentatives) ∧
  (f.place.payer ≠ f.place.customer → a.payerAccepted.isSome = true) ∧
  (∀ acceptance, a.payerAccepted = some acceptance → acceptance.1 = f.place.payer) ∧
  TermsProvidedInTime a.formProvided a.referencedTermsProvided
    ([a.providerAccepted, a.tutorAccepted, a.customerAccepted] ++
      (a.payerAccepted.map Prod.snd).toList)
    debit

structure TeachingAgreementSignature where
  signedBy : ActorId
  agreementReference : String
  evidence : String
  deriving Repr

structure TutorAgreement where
  lesson : LessonId
  provider : ActorId
  tutor : ActorId
  reference : String
  termsAgreedAt : Moment
  service : String
  serviceItems : List Nat
  fee : Amount
  payment : PaymentTerms
  tutorResponsibilities : String
  providerResponsibilities : String
  signatures : List TeachingAgreementSignature
  deriving Repr

/-- The signed teaching agreement is distinct from accepting a lesson on its form. -/
def TutorAgreement.signed (agreement : TutorAgreement) : Prop :=
  ∀ actor ∈ [agreement.provider, agreement.tutor],
    ∃ signature ∈ agreement.signatures,
      signature.signedBy = actor ∧ signature.agreementReference = agreement.reference ∧
      signature.evidence ≠ ""

def TutorAgreement.agreedBeforeAcceptance (agreement : TutorAgreement) (f : PartOne)
    (signatures : Signatures) : Prop :=
  agreement.lesson = f.lesson.id ∧ agreement.provider = f.lesson.provider ∧
  agreement.tutor = f.agreedTutor ∧ agreement.reference = f.tutorAgreementRef ∧
  agreement.signed ∧ agreement.termsAgreedAt.before signatures.tutorAccepted ∧
  agreement.service = f.serviceTerms ∧ agreement.serviceItems = f.serviceItems ∧
  agreement.fee = f.agreedTutorFee ∧
  agreement.payment = f.deadlines.tutorPay ∧
  agreement.tutorResponsibilities ≠ "" ∧ agreement.providerResponsibilities ≠ ""

/-- Part 2 records what happened, using the same lesson and place identifiers as Part 1. -/
structure ChangeRecord where
  originalLesson : LessonId
  nextSchedule : Schedule
  contactedCoordinator : ActorId
  contactedAt : Moment
  scope : List PlaceId
  consents : List Confirmation
  notices : List Notice
  previousTutor : Option ActorId
  replacementTutor : Option ActorId
  separateBooking : Option LessonId
  deriving Repr

def ChangeRecord.matchesFrom (r : ChangeRecord) (f : PartOne) (previous : Schedule)
    (previousTutor : ActorId) (academicTeamAt : ActorId → Moment → Prop)
    (agreedAt : Moment := r.nextSchedule.agreedAt) : Prop :=
  let confirmedAndNotified := fun target ↦
    (∃ c ∈ r.consents, DesignatedConfirmation f.place c ∧ c.target = target ∧
      c.point.by agreedAt) ∧
    (∃ n ∈ r.notices, NoticePerformed n target f.place.student f.contacts.studentNotice ∧
      academicTeamAt n.sender n.point ∧ agreedAt.by n.point)
  r.originalLesson = f.lesson.id ∧ r.nextSchedule.valid ∧ f.place.id ∈ r.scope ∧
  r.contactedCoordinator = f.lesson.coordinator ∧ r.contactedAt.by agreedAt ∧
  (r.replacementTutor = none ∨
    r.nextSchedule.confirmationTarget ≠ previous.confirmationTarget →
    confirmedAndNotified r.nextSchedule.confirmationTarget) ∧
  (∀ tutor, r.replacementTutor = some tutor →
    confirmedAndNotified (.replacementTutor r.originalLesson tutor)) ∧
  (r.replacementTutor.isSome = true → r.previousTutor = some previousTutor) ∧
  (r.separateBooking = none → r.nextSchedule.lesson = f.lesson.id) ∧
  (∀ next, r.separateBooking = some next → r.nextSchedule.lesson = next)

def ChangeRecord.matches (r : ChangeRecord) (f : PartOne)
    (academicTeamAt : ActorId → Moment → Prop) : Prop :=
  r.matchesFrom f f.schedule f.agreedTutor academicTeamAt

structure ExtensionRecord where
  oldDeadline : Moment
  newDeadline : Moment
  agreed : List (ActorId × Moment)
  deriving Repr

def ExtensionRecord.valid (r : ExtensionRecord) (requiredConsentActors : List ActorId) :
    Prop :=
  r.oldDeadline.before r.newDeadline ∧
  ∀ actor ∈ requiredConsentActors, ∃ pair ∈ r.agreed,
    pair.1 = actor ∧ pair.2.before r.oldDeadline

def PaymentRecord (f : PartOne) (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (query : Moment) (recordedDebit : Amount) : Prop :=
  f.matches ∧ PaidInFull f.place ledger discounts query ∧
  (f.place.feePayable = 0 → ∃ d ∈ discounts,
    d.covers f.place query ∧ f.discountBasis = some d.basis) ∧
  recordedDebit = debitTotal f.place ledger query

inductive RefundBasis where
  | agreedChange | noFaultCancellation | absence | standardCompensation
  | directRequest | noAgreement | failedDelivery | afterMadeGood
  deriving DecidableEq, Repr

structure RefundRecord where
  lesson : LessonId
  place : PlaceId
  account : AccountId
  reason : String
  basis : RefundBasis
  finalFee : Amount
  trigger : Moment
  due : Moment
  amount : Amount
  returned : Amount
  receiptTimes : List Moment
  closesCase : Bool
  originalWaivedCompensationContinues : Bool
  deriving Repr

def RefundRecord.matches (r : RefundRecord) (f : PartOne)
    (ledger : List CreditPosting) (query : Moment) (reason : String)
    (trigger due : Moment) (amount : Amount) (scope : Option Nat) : Prop :=
  r.lesson = f.lesson.id ∧ r.place = f.place.id ∧ r.account = f.place.account ∧
  r.reason = reason ∧ r.trigger = trigger ∧ r.due = due ∧ r.amount = amount ∧
  r.returned = creditsRestoredFor f.place ledger query scope ∧
  (r.receiptTimes.Nodup) ∧
  (∀ time, time ∈ r.receiptTimes ↔
    ∃ entry ∈ ledger, entry.account = r.account ∧ entry.point = time ∧ time.by query ∧
      ∃ obligation, entry.kind = .lessonRefund r.lesson r.place obligation ∧
        (scope.isNone = true ∨ scope = some obligation)) ∧
  ¬ (r.closesCase = true ∧ r.originalWaivedCompensationContinues = true)

end SourceV14.Confirmation
