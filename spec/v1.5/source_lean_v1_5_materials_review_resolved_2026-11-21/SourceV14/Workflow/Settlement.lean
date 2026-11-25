import SourceV14.Operations
import SourceV14.Workflow.Cancellation
import SourceV14.Workflow.Review

namespace SourceV14.Workflow.Settlement

open Booking Confirmation Course SourceV14.Settlement Operations

/-- §§2.2 and 3.1 identify the events that can invoke the agreed change terms. -/
inductive AgreedChangeCause where
  | advanceCancellation (request : CancellationRequest)
  | reschedule (change : AgreedScheduleChange)
  | goodReasonAbsence (facts : AbsenceFacts) (reason : AbsenceReasonEvidence)

/-- §§3.1, 4.1–4.2. This identifies the decision made for one place; the
class-wide attendance result supplies a gate, rather than a fee decision. -/
inductive FeeBasis where
  | ordinaryOneToOne (student tutor coordinator verified : Bool)
      (agreedTeaching : Prop) (facts : PlaceFeeFacts)
  | ordinaryGroup (roster : Roster) (completed verified wentAhead serviceAvailable : Bool)
      (attendance fault : List PlaceId) (facts : PlaceFeeFacts)
  | absence (facts : AbsenceFacts) (reason : AbsenceReasonEvidence)
  | agreedChange (cause : AgreedChangeCause) (assessment : AgreedChangeAssessment)
  | providerStartedEarly (actuallyWentAhead : Prop)
      (unmet : LessonId → Moment → Prop) (serviceValue tutorPay : Amount)
      (underTerms : PartOne → Amount → Amount → Prop)

structure FeeDecision where
  form : PartOne
  schedule : Schedule
  start : Moment
  expiry : Moment
  decidedAt : Moment
  handler : Handler
  assignment : SettlementAssignment
  holdFacts : HoldFacts
  basis : FeeBasis
  amounts : LessonSettlement

def FeeDecision.agreedCancellation (decision : FeeDecision) : Option CancellationRequest :=
  match decision.basis with
  | .agreedChange (.advanceCancellation request) _ => some request
  | _ => none

/-- The occurrence supporting change terms, distinct from any separately agreed deadline clock. -/
def FeeDecision.agreedChangeAt (decision : FeeDecision) : Option Moment :=
  match decision.basis with
  | .agreedChange (.advanceCancellation request) _ => some request.point
  | .agreedChange (.reschedule change) _ => some change.record.nextSchedule.effectiveAt
  | .agreedChange (.goodReasonAbsence ..) _ => some decision.decidedAt
  | _ => none

/-- Assess an agreed advance cancellation against its original recorded form and request. -/
def FeeDecision.respectsCancellation (decision : FeeDecision)
    (history : Cancellation.History) : Prop :=
  match decision.agreedCancellation with
  | some request => Cancellation.HasOneToOneCancellation history decision.form request
  | none => ¬ Cancellation.PlaceCancelledAt history decision.form.place decision.decidedAt

def FeeDecision.allowed (entry : FeeDecision) (course : StartEvidence)
    (holds : HoldHistory) : Prop :=
  let e := entry
  let authority := entry.assignment.authorities
  match entry.basis with
  | .ordinaryOneToOne student tutor coordinator verified teaching facts =>
    OrdinaryOneToOneCharge e.form course e.schedule e.start e.expiry e.decidedAt e.handler
      e.assignment student tutor coordinator verified teaching facts holds authority e.holdFacts e.amounts
  | .ordinaryGroup roster completed verified wentAhead serviceAvailable attendance fault facts =>
    OrdinaryGroupCharge e.form course e.schedule roster e.start e.expiry e.decidedAt e.handler
      e.assignment completed verified wentAhead serviceAvailable attendance fault facts holds authority
      e.holdFacts e.amounts
  | .absence facts reason =>
    HalfFeeAbsenceRecorded e.form course e.schedule e.start e.decidedAt e.handler e.assignment
      facts reason holds e.holdFacts course.ledger e.amounts
  | .agreedChange cause assessment =>
    let underTerms := fun cancellation reschedule absence ↦
      AgreedChangeSettlementRecorded e.form course e.decidedAt cancellation reschedule absence
        assessment e.amounts e.handler e.assignment holds e.holdFacts
    match cause with
    | .advanceCancellation request => underTerms (some request) none none
    | .reschedule change =>
      e.form.confirmedAt.by change.record.nextSchedule.agreedAt ∧
      e.form.place.id ∈ change.record.scope ∧
      change.previous.start ≠ change.record.nextSchedule.start ∧
      underTerms none (some change) none
    | .goodReasonAbsence facts reason =>
      course.teachingBegan = none ∧
      course.retainsOneToOneAbsence e.form e.schedule e.start e.decidedAt facts ∧
      e.start.by e.decidedAt ∧ underTerms none none (some (facts, reason))
  | .providerStartedEarly actual unmet serviceValue tutorPay underTerms =>
    UnauthorisedStartSettlement e.form course e.schedule e.start e.decidedAt e.handler e.assignment
      actual unmet holds e.holdFacts serviceValue tutorPay underTerms e.amounts

structure AdoptedFee where
  reference : EvidenceRef
  decision : FeeDecision

/-- §4.2 gives a retained §3.1 group absence priority over ordinary settlement for its place. -/
def FeeDecision.respectsRecordedGroupAbsence (entry : FeeDecision) (fees : List AdoptedFee)
    (query : Moment := entry.decidedAt) : Prop :=
  match entry.basis with
  | .ordinaryGroup .. =>
    ¬ ∃ old ∈ fees,
      old.decision.form.lesson.id = entry.form.lesson.id ∧
      old.decision.form.place.id = entry.form.place.id ∧ old.decision.decidedAt.by query ∧
      match old.decision.basis with
      | .absence facts _ =>
        groupAbsenceHalfFee old.decision.form.lesson old.decision.form.place facts
      | _ => False
  | _ => True

/-- Tutor settlement reads verified, operative place accounts. The supplied
agreement, completion history and adjudications remain independent evidence. -/
structure TutorDue where
  form : PartOne
  roster : Option Roster
  forms : List PartOne
  schedule : Schedule
  startedAt : Moment
  settledAt : Moment
  next : TutorLessonRecord
  completionHistory : List TutorLessonRecord
  faultDecisions : List TutorFaultDecisionEvidence
  faults : List TutorFaultCase
  deductions : List NextTutorDeductionRecord
  agreement : AgreedTutorPayment
  terms : PaymentTerms
  basis : TutorSettlementBasis
  handler : Handler
  assignment : SettlementAssignment
  holdFacts : HoldFacts
  agreedFee : Amount
  net : Amount
  /-- A held group place can remain outstanding alongside a separately determined part. -/
  separatePart : Option PaymentPart

/-- Verified completion for §3.4, including the effective tutor. An eligible
one-to-one absence can generate tutor pay without a teaching completion. -/
structure TutorCompletion where
  form : PartOne
  row : TutorLessonRecord
  start : Moment
  verifiedAt : Moment
  agreement : TutorPayTerms
  feeUnderTerms : PartOne → TutorPayTerms → Amount → Prop

abbrev TutorOccurrenceKey := LessonId × ActorId × Option Moment

def tutorOccurrenceKey (row : TutorLessonRecord) : TutorOccurrenceKey :=
  (row.lesson.id, row.lesson.tutor, row.completedAt)

def TutorCompletion.occurrenceKey (entry : TutorCompletion) : TutorOccurrenceKey :=
  tutorOccurrenceKey entry.row

/-- The reviewed fee changes the classification of an already verified occurrence. -/
structure TutorCompletionRevision where
  original : TutorLessonRecord
  correction : Review.Correction
  correctedFee : Amount

def TutorCompletionRevision.recordedAt (change : TutorCompletionRevision) : Moment :=
  change.correction.record.recordedAt

def TutorCompletion.conforms (entry : TutorCompletion) (course : StartEvidence) : Prop :=
  let row := entry.row
  let f := entry.form
  row.lesson = { f.lesson with tutor := row.lesson.tutor, normalTutorFee := entry.agreement.normalFee } ∧
  (∃ roster forms, course.rosterFormsAt f.lesson entry.start roster forms ∧ f ∈ forms) ∧
  EffectiveTutorAgreementAt f course entry.start row.lesson.tutor entry.agreement.reference
    entry.agreement.normalFee entry.agreement.payment entry.verifiedAt entry.verifiedAt ∧
  entry.feeUnderTerms f entry.agreement row.feeOtherwisePayable ∧
  match row.completedAt with
  | some completed =>
    row.completedForSparkDAO = true ∧ course.teachingBegan = some entry.start ∧
    course.teachingEnded = some completed ∧
    ∃ report, TutorDeliveryRecorded course f.lesson entry.verifiedAt report ∧
      report.completed = true ∧ report.tutor = row.lesson.tutor
  | none =>
    row.completedForSparkDAO = false ∧ course.teachingBegan = none ∧
    ∃ absence ∈ course.verifiedOneToOneAbsence, absence.matchesAt f entry.start entry.verifiedAt

structure TutorPayout where
  settlement : TutorDue
  clockBase : Moment
  expiry : Moment
  receipt : PostedPayment
  part : PaymentPart
  authorities : ReviewAuthorities
  holdFacts : HoldFacts
  approval : PaymentApprovalRoute
  schedule : PaymentSchedule
  agreedConditions : PaymentInstruction → Prop
  earlierLaw : Moment → Prop
  afterLift : List PostLiftPaymentRecord

/-- A tutor payment filing consumes an established settlement and the posted receipt.
The hold and payment deadline are checked at the actual payment occurrence. -/
def TutorPayout.checked (row : TutorPayout) (course : StartEvidence) (holds : HoldHistory) : Prop :=
  let due := row.settlement
  (∀ part ∈ due.separatePart, row.part = part) ∧
  TutorPaymentPosted due.form course due.schedule due.startedAt due.settledAt row.clockBase row.expiry
    due.completionHistory due.next due.faults due.deductions due.agreedFee due.net due.faultDecisions
    due.agreement due.basis due.roster due.forms row.receipt row.part holds row.authorities row.holdFacts
    row.approval row.schedule due.terms row.agreedConditions row.earlierLaw row.afterLift
    (FiledPaymentOnTime due.form row.authorities row.holdFacts holds row.part row.schedule row.receipt row.afterLift)
    (FiledPaymentCompletedOnTime due.form row.authorities row.holdFacts holds row.part row.schedule row.afterLift)

structure History where
  fees : List AdoptedFee := []
  filed : List FiledLessonAccount := []
  tutorCompletions : List TutorCompletion := []
  tutors : List TutorDue := []
  tutorPayments : List TutorPayout := []
  tutorCompletionRevisions : List TutorCompletionRevision := []

def History.tutorCompletionRowsAt (h : History) (atTime : Moment) : List TutorLessonRecord :=
  (h.tutorCompletions.filter (fun entry ↦ decide (entry.verifiedAt.by atTime))).map fun entry ↦
    h.tutorCompletionRevisions.foldl (fun row revision ↦
      if revision.recordedAt.by atTime ∧ revision.original = row then
        { row with feeOtherwisePayable := revision.correctedFee }
      else row) entry.row

def TutorCompletionRevision.conforms (change : TutorCompletionRevision) (history : History) : Prop :=
  let key := tutorOccurrenceKey change.original
  change.correction.record.lesson = change.original.lesson.id ∧
  change.original ∈ history.tutorCompletionRowsAt change.recordedAt ∧
  (∃ entry ∈ history.tutorCompletions, entry.occurrenceKey = key ∧
    entry.verifiedAt.before change.recordedAt) ∧
  0 ≤ change.correctedFee ∧ change.correctedFee ≠ change.original.feeOtherwisePayable ∧
  ∀ prior ∈ history.tutorCompletionRevisions, tutorOccurrenceKey prior.original = key →
    prior.recordedAt.before change.recordedAt ∧ prior.correction ≠ change.correction

/-- Preserve original accounts when an authorised correction supersedes them. -/
def History.recordedAt (h : History) (lesson : LessonId) (place : PlaceId) (atTime : Moment)
    (amounts : LessonSettlement) (atDecision : Moment) : Prop :=
  ∃ entry ∈ h.fees, entry.decision.form.lesson.id = lesson ∧
    entry.decision.form.place.id = place ∧ entry.decision.amounts = amounts ∧
    entry.decision.decidedAt = atDecision ∧ atDecision.by atTime ∧
    entry.decision.respectsRecordedGroupAbsence h.fees atTime

/-- A good-reason absence uses the adopted amount under the agreed change terms. -/
def TutorDue.agreedAbsenceRecorded (due : TutorDue) (course : StartEvidence) (h : History) : Prop :=
  course.teachingBegan = none →
  ∀ facts reason, due.basis.absenceWithoutTeaching = some (due.startedAt, facts, reason) →
    oneToOneAbsenceUsesChangeTerms due.form.lesson due.form.place facts →
    ∃ entry ∈ h.fees, ∃ assessment,
      entry.decision.form = due.form ∧ entry.decision.start = due.startedAt ∧
      entry.decision.schedule = due.schedule ∧
      entry.decision.basis = .agreedChange (.goodReasonAbsence facts reason) assessment ∧
      entry.decision.amounts ∈ due.basis.paymentsByPlace ∧
      due.basis.operativeSettlement due.form.place.id due.settledAt =
        some (entry.decision.amounts, entry.decision.decidedAt)

/-- §§4.2–4.3 form the total from the actual place settlement records, including
the documented separate portion in a partially held group. -/
def TutorDue.established (due : TutorDue) (course : StartEvidence) (holds : HoldHistory)
    (h : History) : Prop :=
  let a := due.assignment.authorities
  let f := due.form
  let actual := due.settledAt
  let basis := due.basis
  let agreement := due.agreement
  let tutor := agreement.tutor
  let terms : TutorPayTerms := ⟨agreement.agreementRef, due.next.lesson.normalTutorFee, due.terms⟩
  f ∈ due.forms ∧ course.rosterFormsAt f.lesson actual due.roster due.forms ∧
  due.holdFacts.groupSettlementScopeMatches f.lesson (due.forms.map (·.place)) ∧
  due.assignment.authorised f due.handler actual ∧
  holds.mayCarryOutDecision a due.holdFacts due.assignment.matter due.assignment.decision actual ∧
  due.completionHistory = h.tutorCompletionRowsAt actual ∧
  due.next ∈ due.completionHistory ∧
  due.next.lesson = { f.lesson with tutor := tutor, normalTutorFee := due.next.lesson.normalTutorFee } ∧
  TutorSettlementOccurrence f course due.schedule due.startedAt actual basis due.next ∧
  due.agreedAbsenceRecorded course h ∧
  agreement.lesson = f.lesson.id ∧
  EffectiveTutorAgreementAt f course due.startedAt tutor terms.reference terms.normalFee
    terms.payment actual actual ∧
  basis.debtsReferenced f.lesson tutor actual ∧
  (∀ fault, fault ∈ due.faults ↔ ∃ finding ∈ due.faultDecisions, finding.establishes fault actual) ∧
  (∀ deduction ∈ due.deductions, 0 < deduction.unappliedAmount →
    deduction.shortfallTerms = agreement.shortfallTerms) ∧
  (∀ row ∈ basis.paymentsByPlace, ∃ settled, basis.operativeSettlement row.place actual = some (row, settled) ∧
    h.recordedAt f.lesson.id row.place actual row settled) ∧
  basis.totals f course actual due.forms terms due.agreedFee ∧
  match due.separatePart with
  | none =>
    (f.lesson.kind = .group →
      due.holdFacts.decisionConcernsWholeGroup due.assignment.matter due.assignment.decision) ∧
    (∀ pf ∈ due.forms, ∃ row ∈ basis.paymentsByPlace, row.place = pf.place.id) ∧
    TutorAmountsForSettlement due.completionHistory due.next due.faults due.deductions
      due.agreedFee due.net
  | some part =>
    f.lesson.kind = .group ∧
    basis.hasOtherHeldPlace f.lesson tutor due.forms holds a due.holdFacts actual actual ∧
    (∀ fault ∈ due.faults, fault.originalLesson.id ≠ due.next.lesson.id ∨
      fault.originalLesson.tutor ≠ due.next.lesson.tutor) ∧
    basis.separatePartMatches f.lesson tutor part due.holdFacts ∧
    due.deductions = [] ∧ due.net = part.amount

inductive Event where
  | assessFee (entry : AdoptedFee)
  | fileAccount (form : PartOne) (account : FiledLessonAccount)
  | verifyTutorCompletion (entry : TutorCompletion)
  | reviseTutorCompletion (change : TutorCompletionRevision)
  | assessTutor (due : TutorDue)
  | fileTutorPayment (row : TutorPayout)

def Event.lesson : Event → LessonId
  | .assessFee entry => entry.decision.form.lesson.id
  | .fileAccount form _ => form.lesson.id
  | .verifyTutorCompletion entry => entry.form.lesson.id
  | .reviseTutorCompletion change => change.original.lesson.id
  | .assessTutor due => due.form.lesson.id
  | .fileTutorPayment row => row.settlement.form.lesson.id

inductive Step (course : StartEvidence) (holds : HoldHistory) : History → Event → History → Prop where
  | assessFee {before : History} {entry : AdoptedFee}
      (allowed : entry.decision.allowed course holds)
      (distinct : ∀ old ∈ before.fees, old.reference ≠ entry.reference)
      (absence : entry.decision.respectsRecordedGroupAbsence before.fees) :
    Step course holds before (.assessFee entry) { before with fees := before.fees ++ [entry] }
  | fileAccount {before : History} {form : PartOne} {account : FiledLessonAccount}
      (filed : account.matches form course.ledger)
      (retainedForm : form ∈ course.effectiveForms ∨ form ∈ course.bookings.map Prod.fst) :
    Step course holds before (.fileAccount form account) { before with filed := before.filed ++ [account] }
  | verifyTutorCompletion {before : History} {entry : TutorCompletion}
      (verified : entry.conforms course)
      (fresh : ∀ old ∈ before.tutorCompletions, old.occurrenceKey ≠ entry.occurrenceKey) :
    Step course holds before (.verifyTutorCompletion entry)
      { before with tutorCompletions := before.tutorCompletions ++ [entry] }
  | reviseTutorCompletion {before : History} {change : TutorCompletionRevision}
      (revised : change.conforms before) :
    Step course holds before (.reviseTutorCompletion change)
      { before with tutorCompletionRevisions := before.tutorCompletionRevisions ++ [change] }
  | assessTutor {before : History} {due : TutorDue}
      (established : due.established course holds before) :
    Step course holds before (.assessTutor due) { before with tutors := before.tutors ++ [due] }

  | fileTutorPayment {before : History} {row : TutorPayout}
      (prior : row.settlement ∈ before.tutors)
      (recorded : row.receipt ∈ holds.payments.posted)
      (checked : row.checked course holds)
      (fresh : ∀ old ∈ before.tutorPayments, old.receipt.id ≠ row.receipt.id) :
    Step course holds before (.fileTutorPayment row)
      { before with tutorPayments := before.tutorPayments ++ [row] }

end SourceV14.Workflow.Settlement
