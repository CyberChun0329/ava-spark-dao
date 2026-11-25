import SourceV14.Workflow.Settlement
import SourceV14.Workflow.Review
import SourceV14.Workflow.Redress

/-!
The original tutor-pay outcome (source §§3.2, 3.4 and confirmation form Part 2)
is retained independently of customer redress. Later settlement uses the
operative outcome and the actual course and completion records.
-/

namespace SourceV14.Workflow.TutorFaultHistory

open Confirmation Course CreditEvidence Operations

structure Entry where
  fault : TutorFaultCase
  evidence : TutorFaultDecisionEvidence
  outcome : RecordedSettlementOutcome
  recordedAt : Moment
  fullDeduction : Amount
  originalTutorPay : Amount

/-- Verified meanings of retained review findings for the affected place and pay record. -/
structure ReviewInterpretation where
  faultOutcome : ReviewFinding → PlaceId → Option FindingDisposition := fun _ _ ↦ none
  completionFee : ReviewFinding → Settlement.TutorOccurrenceKey → Option Amount := fun _ _ ↦ none

private def usesReviewedDisposition (interpretation : ReviewInterpretation)
    (decision : FaultDecisionRecord) : Prop :=
  match decision.decision with
  | .initial _ => True
  | .review finding => interpretation.faultOutcome finding decision.place = some decision.disposition

def matchesInitialOutcome (review : Review.History) (finding : InitialFinding)
    (outcome : RecordedSettlementOutcome) : Prop :=
  outcome ∈ review.originalOutcomes ∧ outcome.matter = finding.matter ∧
    outcome.decidedBy = finding.decider ∧ outcome.decidedAt = finding.decidedAt

/-- Link the economic disposition to the actual decision it records. -/
def Entry.matchesOutcome (entry : Entry) (review : Review.History) : Prop :=
  let outcome := entry.outcome
  match entry.evidence.decision.decision with
  | .initial finding => matchesInitialOutcome review finding outcome
  | .review finding =>
    outcome.matter = finding.matter ∧ outcome.outcome = finding.outcome ∧
      outcome.decidedBy = finding.reviewer ∧ outcome.decidedAt = finding.decidedAt

def Entry.conforms (entry : Entry) (course : StartEvidence) (review : Review.History)
    (interpretation : ReviewInterpretation) : Prop :=
  let evidence := entry.evidence
  evidence.lessonEvidence = course ∧
  evidence.records.appointments = review.appointments ∧
  evidence.records.initialFindings = review.initialFindings ∧
  evidence.records.reviewFindings = review.reviewFindings ∧
  entry.matchesOutcome review ∧ usesReviewedDisposition interpretation evidence.decision ∧
  entry.fault.originalLessonAt.by entry.recordedAt ∧
  entry.fault.finding.scope.affects evidence.original.place.id ∧
  evidence.establishes entry.fault entry.recordedAt ∧
  originalFaultTutorSettlement entry.fault entry.fullDeduction entry.originalTutorPay

def correctionFinding : Review.Correction → ReviewFinding
  | .nonmonetary _ finding _ => finding
  | .monetary _ payment => payment.finding

private def correctionOriginalOutcome : Review.Correction → RecordedSettlementOutcome
  | .nonmonetary original _ _ | .monetary original _ => original.outcome

private def reviewedOutcome (finding : ReviewFinding) : RecordedSettlementOutcome :=
  ⟨finding.matter, finding.outcome, finding.reviewer, finding.decidedAt⟩

/-- The correction changes the linked tutor-fault outcome of the original lesson. -/
def Entry.correctedBy (entry : Entry) (interpretation : ReviewInterpretation)
    (correction : Review.Correction) : Prop :=
  correctionOriginalOutcome correction = entry.outcome ∧
  (interpretation.faultOutcome (correctionFinding correction) entry.evidence.original.place.id).isSome

structure Revision where
  original : Entry
  correction : Review.Correction
  decision : FaultDecisionRecord
  replacement : Option Entry

structure History where
  entries : List Entry
  revisions : List Revision

def History.empty : History := ⟨[], []⟩

def History.operativeAt (history : History) (entry : Entry) (query : Moment) : Prop :=
  entry ∈ history.entries ∧ entry.recordedAt.by query ∧
    ¬∃ revision ∈ history.revisions, revision.original = entry ∧
      revision.correction.record.recordedAt.by query

def Revision.conforms (revision : Revision) (history : History)
    (course : LessonId → StartEvidence) (review : Review.History)
    (interpretation : ReviewInterpretation) : Prop :=
  let old := revision.original
  let correctedAt := revision.correction.record.recordedAt
  history.operativeAt old correctedAt ∧
  (∀ prior ∈ history.revisions, prior.original ≠ old) ∧
  revision.correction ∈ review.corrections ∧
  correctionOriginalOutcome revision.correction = old.outcome ∧
  revision.decision.decision = .review (correctionFinding revision.correction) ∧
  revision.decision.place = old.evidence.original.place.id ∧
  match revision.decision.disposition, revision.replacement with
  | .fault (.tutor _ _), some entry =>
    entry.evidence.decision = revision.decision ∧ entry.recordedAt = correctedAt ∧
    entry.conforms (course entry.evidence.original.lesson.id) review interpretation ∧
    entry ∉ history.entries
  | .fault (.tutor _ _), none => False
  | _, none => usesReviewedDisposition interpretation revision.decision
  | _, some _ => False

inductive Event where
  | record (entry : Entry)
  | revise (revision : Revision)

/-- The form also records the original full deduction and zero pay when teaching
did not take place. Neither a completion nor a customer election is required. -/
inductive Step (course : LessonId → StartEvidence) (review : Review.History)
    (interpretation : ReviewInterpretation) :
    History → Event → History → Prop where
  | record {history : History} (entry : Entry)
      (recorded : entry.conforms (course entry.evidence.original.lesson.id) review interpretation)
      (fresh : ∀ old ∈ history.entries, old.outcome ≠ entry.outcome)
      (newCase : ∀ old, history.operativeAt old entry.recordedAt →
        ¬old.outcome.matter.sameCase entry.outcome.matter) :
    Step course review interpretation history (.record entry)
      { history with entries := history.entries ++ [entry] }
  | revise {history : History} (revision : Revision)
      (recorded : revision.conforms history course review interpretation) :
    Step course review interpretation history (.revise revision)
      { entries := history.entries ++ revision.replacement.toList
        revisions := history.revisions ++ [revision] }

def relevant (fault : TutorFaultCase) (next : TutorLessonRecord) : Prop :=
  fault.originalLesson.tutor = next.lesson.tutor ∧
    (fault.originalLesson.id = next.lesson.id ∨
      ∃ completedAt, laterPayableTutorCompletion fault next completedAt)

/-- Read earlier actual completions for this tutor from the same course state.
    A retained completion report in the relevant window requires a verified pay
    classification, which may be zero. -/
def priorCompletionsCovered (course : LessonId → StartEvidence) (rows : List TutorLessonRecord)
    (fault : TutorFaultCase) (next : TutorLessonRecord) (query : Moment) : Prop :=
  ∀ nextAt, laterPayableTutorCompletion fault next nextAt →
    ∀ lesson, lesson ≠ fault.originalLesson.id → lesson ≠ next.lesson.id →
    let file := course lesson
    ∀ form ∈ file.effectiveForms ++ file.bookings.map Prod.fst,
    form.lesson.id = lesson → ∀ completedAt ∈ file.teachingEnded,
    fault.originalLessonAt.before completedAt → completedAt.by nextAt →
    ∀ report, TutorDeliveryRecorded file form.lesson query report →
    report.tutor = fault.originalLesson.tutor → report.completed = true →
    ∃ row ∈ rows, row.lesson.id = lesson ∧ row.lesson.tutor = report.tutor ∧
      row.completedAt = some completedAt ∧ row.completedForSparkDAO = true

/-- An operative outcome is due for the original lesson or that tutor's first
    later completed lesson with otherwise payable fees. -/
def Entry.applies (entry : Entry) (history : History) (rows : List TutorLessonRecord)
    (next : TutorLessonRecord) (query : Moment) : Prop :=
  history.operativeAt entry query ∧ entry.fault.originalLesson.tutor = next.lesson.tutor ∧
    (entry.fault.originalLesson.id = next.lesson.id ∨
      firstPayableLessonAfterFault entry.fault rows next)

private def completionFeeCurrent (review : Review.History)
    (interpretation : ReviewInterpretation) (row : TutorLessonRecord) (query : Moment) : Prop :=
  let key := Settlement.tutorOccurrenceKey row
  ∀ correction ∈ review.corrections, correction.record.lesson = row.lesson.id →
    correction.record.recordedAt.by query →
    ∀ fee ∈ interpretation.completionFee (correctionFinding correction) key,
      (¬∃ later ∈ review.corrections, later.record.lesson = row.lesson.id ∧
        correctionOriginalOutcome later = reviewedOutcome (correctionFinding correction) ∧
        correction.record.recordedAt.before later.record.recordedAt ∧
        later.record.recordedAt.by query ∧
        (interpretation.completionFee (correctionFinding later) key).isSome) →
      fee = row.feeOtherwisePayable

private def originalTimeAtOrAfter (course : StartEvidence) (lesson : Lesson)
    (completed : Moment) : Prop :=
  ∃ schedule,
    let originalAt := course.teachingEnded.getD schedule.start
    EffectiveSchedule lesson course schedule originalAt ∧ ¬originalAt.before completed

private def reviewedFaultCanAffect (course : StartEvidence)
    (fault : TutorFaultFinding) (next : TutorLessonRecord) : Prop :=
  fault.lesson = next.lesson.id ∨
    (next.completedForSparkDAO = true ∧ 0 < next.feeOtherwisePayable ∧
      ∃ completed ∈ next.completedAt,
        ¬∃ form ∈ course.effectiveForms ++ course.bookings.map Prod.fst,
          form.lesson.id = fault.lesson ∧ originalTimeAtOrAfter course form.lesson completed)

/-- A retained tutor-fault finding can require adoption before the corresponding
    economic entry exists. An operative entry suffices for the same tutor and case. -/
def History.reviewFaultsRecordedAt (history : History) (course : LessonId → StartEvidence)
    (review : Review.History) (interpretation : ReviewInterpretation) (next : TutorLessonRecord)
    (query : Moment) : Prop :=
  ∀ finding ∈ review.reviewFindings, finding.decidedAt.by query →
    ∀ place fault facts,
      interpretation.faultOutcome finding place = some (.fault (.tutor fault facts)) →
      fault.lesson = finding.matter.lesson → fault.tutor = next.lesson.tutor →
      reviewedFaultCanAffect (course fault.lesson) fault next →
      (∃ entry, history.operativeAt entry query ∧ entry.outcome.matter.sameCase finding.matter ∧
        entry.fault.originalLesson.id = fault.lesson ∧ entry.fault.originalLesson.tutor = fault.tutor) ∨
      ∃ correction ∈ review.corrections, correction.record.recordedAt.by query ∧
        correctionOriginalOutcome correction = reviewedOutcome finding ∧
        (interpretation.faultOutcome (correctionFinding correction) place).isSome

/-- A verified initial fault needs its economic entry or a retained correction
    of that exact initial outcome for the affected place. -/
def History.initialFaultsRecordedAt (history : History) (course : LessonId → StartEvidence)
    (review : Review.History) (interpretation : ReviewInterpretation) (next : TutorLessonRecord)
    (query : Moment) : Prop :=
  ∀ finding ∈ review.initialFindings, finding.decidedAt.by query →
    let original := course finding.matter.lesson
    let saved := original.studentFaults.decisions
    let records := review.decisionRecords saved.authorities saved
    ∀ (form : PartOne) (schedule : SourceV14.Booking.Schedule) (decision : FaultDecisionRecord)
      (fault : TutorFaultCase),
      decision.decision = .initial finding →
      (TutorFaultDecisionEvidence.mk form original schedule decision records).establishes
        fault finding.decidedAt →
      fault.finding.scope.affects form.place.id → relevant fault next →
      (∃ entry, history.operativeAt entry query ∧
        entry.evidence.decision.decision = .initial finding ∧ entry.matchesOutcome review ∧
        entry.fault.originalLesson = fault.originalLesson ∧
        entry.fault.originalLessonAt = fault.originalLessonAt) ∨
      ∃ correction ∈ review.corrections,
        let revisedFinding := correctionFinding correction
        correction.record.recordedAt.by query ∧
        matchesInitialOutcome review finding (correctionOriginalOutcome correction) ∧
        revisedFinding ∈ review.reviewFindings ∧
        (interpretation.faultOutcome revisedFinding form.place.id).isSome

def History.completeAt (history : History) (course : LessonId → StartEvidence)
    (review : Review.History) (interpretation : ReviewInterpretation) (rows : List TutorLessonRecord)
    (next : TutorLessonRecord) (query : Moment) : Prop :=
  completionFeeCurrent review interpretation next query ∧
  history.reviewFaultsRecordedAt course review interpretation next query ∧
  history.initialFaultsRecordedAt course review interpretation next query ∧
  ∀ entry, history.operativeAt entry query → relevant entry.fault next →
    (∀ correction ∈ review.corrections, correction.record.recordedAt.by query →
      ¬entry.correctedBy interpretation correction) ∧
    priorCompletionsCovered course rows entry.fault next query ∧
    ∀ nextAt, laterPayableTutorCompletion entry.fault next nextAt →
      ∀ row ∈ rows, row.lesson.id ≠ entry.fault.originalLesson.id →
        row.lesson.tutor = next.lesson.tutor →
        ∀ ended ∈ row.completedAt, entry.fault.originalLessonAt.before ended → ended.by nextAt →
          completionFeeCurrent review interpretation row query

/-- Exact case and evidence membership at the dated assessment. -/
def History.reads (history : History) (rows : List TutorLessonRecord) (next : TutorLessonRecord)
    (query : Moment) (faults : List TutorFaultCase) (evidence : List TutorFaultDecisionEvidence) :
    Prop :=
  (∀ fault, fault ∈ faults ↔
    ∃ entry : Entry, entry.applies history rows next query ∧ entry.fault = fault) ∧
  (∀ record, record ∈ evidence ↔
    ∃ entry : Entry, entry.applies history rows next query ∧ entry.evidence = record)

/-- A later filing may have more evidence. Its assessment must still match the
    operative tutor, original lesson and agreed original fee at payment. -/
def History.sameTreatmentAt (history : History) (rows : List TutorLessonRecord)
    (next : TutorLessonRecord) (query : Moment) (assessedFaults : List TutorFaultCase) : Prop :=
  ∀ key fee,
    (∃ fault ∈ assessedFaults, fault.deductionKey = key ∧ originalTutorDeduction fault = fee) ↔
    ∃ entry : Entry, entry.applies history rows next query ∧
      entry.fault.deductionKey = key ∧ entry.fullDeduction = fee

private def changedTutorSettlement (review : Review.History) (due : Settlement.TutorDue)
    (query : Moment) : Prop :=
  ∃ correction ∈ review.paymentCorrections,
    due.settledAt.before correction.finding.decidedAt ∧
    correction.correction.recordedAt.by query ∧
    correction.finding.matter.sameCase due.assignment.matter ∧
    correction.correction.originalOutcome = due.assignment.decision ∧
    correction.money.corrected.ref.purpose = .tutorPay due.agreement.tutor

private def changedCorrectedTutorSettlement (review : Review.History)
    (filed : Review.CorrectedPayout) (query : Moment) : Prop :=
  ∃ correction ∈ review.paymentCorrections,
    filed.correction.correction.recordedAt.before correction.correction.recordedAt ∧
    correction.correction.recordedAt.by query ∧
    correction.finding.matter.sameCase filed.correction.finding.matter ∧
    correction.correction.originalOutcome = filed.correction.finding.outcome ∧
    correction.originalPart = filed.correction.money.corrected

/-- A repeated calculation of the same total can refer to its own deduction.
    An operative record of that key for a different next lesson cannot. -/
def deductionsUsedOnce (review : Review.History) (settlement : Settlement.History)
    (deductions : List NextTutorDeductionRecord) (query : Moment) : Prop :=
  ∀ deduction ∈ deductions,
    (∀ settled ∈ settlement.tutors, settled.settledAt.by query →
      ¬changedTutorSettlement review settled query →
      ∀ old ∈ settled.deductions, old.key = deduction.key → old.nextLesson = deduction.nextLesson) ∧
    (∀ filed ∈ review.correctedPayouts, filed.recordedAt.by query →
      ¬changedCorrectedTutorSettlement review filed query →
      filed.part.ref.purpose = .tutorPay deduction.key.1 →
      ∀ amounts ∈ filed.reviewedTutorAmounts, ∀ old ∈ amounts.deductions,
        old.key = deduction.key → old.nextLesson = deduction.nextLesson)

def settlementUses (course : LessonId → StartEvidence) (review : Review.History)
    (history : History) (settlement : Settlement.History)
    (interpretation : ReviewInterpretation) : Settlement.Event → Prop
  | .verifyTutorCompletion entry =>
    completionFeeCurrent review interpretation entry.row entry.verifiedAt
  | .reviseTutorCompletion change =>
    change.correction ∈ review.corrections ∧
    interpretation.completionFee (correctionFinding change.correction)
      (Settlement.tutorOccurrenceKey change.original) = some change.correctedFee
  | .assessTutor due =>
    let rows := settlement.tutorCompletionRowsAt due.settledAt
    due.completionHistory = rows ∧
    history.completeAt course review interpretation rows due.next due.settledAt ∧
    history.reads rows due.next due.settledAt due.faults due.faultDecisions ∧
    deductionsUsedOnce review settlement due.deductions due.settledAt
  | .fileTutorPayment payout =>
    let due := payout.settlement
    let atTime := payout.receipt.instruction.atTime
    let rows := settlement.tutorCompletionRowsAt atTime
    due.next ∈ rows ∧
    history.completeAt course review interpretation rows due.next atTime ∧
    history.sameTreatmentAt rows due.next atTime due.faults ∧
    deductionsUsedOnce review settlement due.deductions atTime
  | _ => True

def correctedPayoutUses (course : LessonId → StartEvidence) (review : Review.History)
    (history : History) (settlement : Settlement.History) (interpretation : ReviewInterpretation)
    (payout : Review.CorrectedPayout) : Prop :=
  match payout.part.ref.purpose with
  | .tutorPay _ =>
    ∀ amounts ∈ payout.reviewedTutorAmounts,
      let correctedAt := payout.correction.correction.recordedAt
      let paidAt := payout.payment.paid.instruction.atTime
      let assessedRows := settlement.tutorCompletionRowsAt correctedAt
      let paymentRows := settlement.tutorCompletionRowsAt paidAt
      amounts.completionHistory = assessedRows ∧ amounts.nextLesson ∈ paymentRows ∧
      history.completeAt course review interpretation assessedRows amounts.nextLesson correctedAt ∧
      history.reads assessedRows amounts.nextLesson correctedAt amounts.faults
        amounts.faultEvidence ∧
      history.completeAt course review interpretation paymentRows amounts.nextLesson paidAt ∧
      history.sameTreatmentAt paymentRows amounts.nextLesson paidAt amounts.faults ∧
      deductionsUsedOnce review settlement amounts.deductions paidAt
  | _ => True

private def relevantRedress (form : PartOne) (course : StartEvidence)
    (next : TutorLessonRecord) : Prop :=
  form.lesson.id = next.lesson.id ∨
    (next.completedForSparkDAO = true ∧ 0 < next.feeOtherwisePayable ∧
      ∃ completed ∈ next.completedAt, ¬originalTimeAtOrAfter course form.lesson completed)

private def History.retainsRedress (history : History) (course : LessonId → StartEvidence)
    (facts : Redress.FaultFacts) (next : TutorLessonRecord) (query : Moment) : Prop :=
  match facts.fault, facts.authority with
  | .tutor finding _, some decision =>
    finding.tutor = next.lesson.tutor →
    relevantRedress facts.form (course facts.form.lesson.id) next →
    ∃ entry ∈ history.entries, entry.recordedAt.by query ∧
      entry.fault.originalLesson.id = facts.form.lesson.id ∧ entry.fault.finding = finding ∧
      entry.evidence.decision.decision = decision.decision
  | _, _ => True

/-- A retained customer record can already establish knowledge of the tutor
    finding. Tutor settlement then requires its own economic origin record. -/
def redressRecordedAt (course : LessonId → StartEvidence) (history : History)
    (redress : Redress.History) (next : TutorLessonRecord) (query : Moment) : Prop :=
  (∀ remedy ∈ redress.remedies, remedy.agreement.acceptedAt.by query →
    history.retainsRedress course remedy.facts next query) ∧
  ∀ assessment ∈ redress.assessments, assessment.amount.recordedAt.by query →
    match assessment.evidence with
    | .originalCompensation facts _ | .faultRefund facts .. =>
      history.retainsRedress course facts next query
    | _ => True

def retainedRedressUses (course : LessonId → StartEvidence) (history : History)
    (redress : Redress.History) : Settlement.Event → Prop
  | .assessTutor due => redressRecordedAt course history redress due.next due.settledAt
  | .fileTutorPayment payout =>
    redressRecordedAt course history redress payout.settlement.next
      payout.receipt.instruction.atTime
  | _ => True

def retainedRedressCorrectedPayoutUses (course : LessonId → StartEvidence) (history : History)
    (redress : Redress.History) (payout : Review.CorrectedPayout) : Prop :=
  match payout.part.ref.purpose with
  | .tutorPay _ =>
    ∀ amounts ∈ payout.reviewedTutorAmounts,
      redressRecordedAt course history redress amounts.nextLesson
        payout.payment.paid.instruction.atTime
  | _ => True

end SourceV14.Workflow.TutorFaultHistory
