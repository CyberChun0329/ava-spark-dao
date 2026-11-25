import RecognisedV15.Institutional
import SourceV14.Workflow

namespace RecognisedV15.Settlement

open SourceV14 SourceV14.Booking SourceV14.Confirmation SourceV14.Course
  SourceV14.Operations SourceV14.Settlement
open SourceV14.Workflow
open SourceV14.Workflow.Settlement (FeeDecision History TutorDue TutorPayout)

/-- The handler decides the fee for one place against its own evidence and credit history. -/
private def feeAssessment (course : LessonEvidence) (holds : HoldHistory)
    (decision : FeeDecision) : Prop :=
  let form := decision.form
  let atTime := decision.decidedAt
  let assignment := decision.assignment
  let facts := decision.holdFacts
  let amounts := decision.amounts
  let permittedStart := course.openingPermitted form.lesson decision.schedule decision.start
  let withFeeChecks := fun (conditions : Prop) ↦
    assignment.authorised form decision.handler atTime ∧
    FeeHoldTermsMatch form facts ∧
    holds.mayCarryOutDecision assignment.authorities facts assignment.matter assignment.decision
      atTime ∧
    ¬FeeOnHold holds assignment.authorities facts form.place atTime ∧
    amounts.matchesPaymentHistory form.place course.creditFee.ledger atTime ∧ conditions
  match decision.basis with
  | .ordinaryOneToOne student tutor coordinator verified agreedTeaching feeFacts =>
    withFeeChecks <|
    form ∈ course.bookingSchedule.effectiveForms ∧
    OneToOneSettlementAvailable form.lesson course.toDirect decision.schedule decision.start
      decision.expiry atTime student tutor coordinator verified decision.handler ∧
    permittedStart ∧ agreedTeaching ∧ ¬feeFacts.exceptionApplies form course.toDirect atTime ∧
    course.toDirect.feeAt form atTime amounts.feePayable
  | .ordinaryGroup roster completed verified wentAhead serviceAvailable attendance fault feeFacts =>
    withFeeChecks <|
    course.toDirect.formForRoster form.lesson roster form ∧
    course.groupSettlementAllowed form.lesson decision.schedule roster decision.start
      decision.expiry atTime completed verified decision.handler attendance fault ∧
    permittedStart ∧ wentAhead = true ∧ serviceAvailable = true ∧
    course.toDirect.paidInFull form atTime ∧
    ¬feeFacts.exceptionApplies form course.toDirect atTime ∧
    course.toDirect.feeAt form atTime amounts.feePayable
  | .absence absence reason =>
    withFeeChecks <|
    (∃ roster forms, course.toDirect.rosterFormsAt form.lesson atTime roster forms ∧ form ∈ forms) ∧
    permittedStart ∧ decision.start.by atTime ∧
    (∃ fee, course.toDirect.feeAt form decision.start fee ∧
      ((course.teachingOccurred decision.start ∧
        ∃ agreedPay, form.absentGroupPlacePay = some agreedPay ∧
          groupAbsenceAmounts form.lesson form.place absence fee agreedPay
            amounts.feePayable amounts.tutorPay) ∨
      (oneToOneAbsenceHalfFee form.lesson form.place absence ∧ reason.applies form absence atTime ∧
        course.toDirect.retainsOneToOneAbsence form decision.schedule decision.start atTime
          absence ∧
        amounts.feePayable = absenceCustomerFee fee ∧
        ∃ tutor reference normalFee terms,
          EffectiveTutorAgreementAt form course.toDirect decision.start tutor reference
            normalFee terms ∧ amounts.tutorPay = normalFee / 2))) ∧
    amounts.creditDueBack = grossLessonCreditRestoration amounts.debited amounts.feePayable
  | .agreedChange cause assessment =>
    let underTerms := fun cancellation reschedule absence ↦
      AgreedChangeSettlementRecorded form course.toDirect atTime cancellation reschedule absence
        assessment amounts decision.handler assignment holds facts
    match cause with
    | .advanceCancellation request => underTerms (some request) none none
    | .reschedule change =>
      form.confirmedAt.by change.record.nextSchedule.agreedAt ∧
      form.place.id ∈ change.record.scope ∧
      change.previous.start ≠ change.record.nextSchedule.start ∧
      underTerms none (some change) none
    | .goodReasonAbsence absence reason =>
      course.teaching.teachingBegan = none ∧
      course.toDirect.retainsOneToOneAbsence form decision.schedule decision.start atTime absence ∧
      decision.start.by atTime ∧ underTerms none none (some (absence, reason))
  | .providerStartedEarly actual unmet serviceValue tutorPay underTerms =>
    withFeeChecks <|
    (∃ roster forms, course.toDirect.rosterFormsAt form.lesson atTime roster forms ∧ form ∈ forms) ∧
    course.teachingOccurred decision.start ∧
    EffectiveSchedule form.lesson course.toDirect decision.schedule decision.start ∧
    decision.start.by atTime ∧ unmet form.lesson.id decision.start ∧ ¬permittedStart ∧ actual ∧
    underTerms form serviceValue tutorPay ∧
    amounts.feePayable = serviceValue ∧ amounts.tutorPay = tutorPay ∧
    amounts.creditDueBack = grossLessonCreditRestoration amounts.debited amounts.feePayable

/-- Establish tutor pay from the effective agreement, verified completion history and retained
place settlements. In a partially held group, a separately determined part can be recognised. -/
private def tutorAssessment (course : LessonEvidence) (holds : HoldHistory) (before : History)
    (due : TutorDue) : Prop :=
  let form := due.form
  let atTime := due.settledAt
  let assignment := due.assignment
  let basis := due.basis
  let agreement := due.agreement
  let tutor := agreement.tutor
  let terms : TutorPayTerms := ⟨agreement.agreementRef, due.next.lesson.normalTutorFee, due.terms⟩
  assignment.authorised form due.handler atTime ∧
  holds.mayCarryOutDecision assignment.authorities due.holdFacts
    assignment.matter assignment.decision atTime ∧
  form ∈ due.forms ∧ course.toDirect.rosterFormsAt form.lesson atTime due.roster due.forms ∧
  due.holdFacts.groupSettlementScopeMatches form.lesson (due.forms.map (·.place)) ∧
  TutorSettlementOccurrence form course.toDirect due.schedule due.startedAt atTime basis due.next ∧
  due.agreedAbsenceRecorded course.toDirect before ∧
  agreement.lesson = form.lesson.id ∧
  EffectiveTutorAgreementAt form course.toDirect due.startedAt tutor terms.reference terms.normalFee
    terms.payment atTime atTime ∧
  due.completionHistory = before.tutorCompletionRowsAt atTime ∧
  due.next ∈ due.completionHistory ∧
  due.next.lesson = { form.lesson with tutor := tutor, normalTutorFee := terms.normalFee } ∧
  (∀ row ∈ basis.paymentsByPlace, ∃ settled,
    basis.operativeSettlement row.place atTime = some (row, settled) ∧
    before.recordedAt form.lesson.id row.place atTime row settled) ∧
  basis.debtsReferenced form.lesson tutor atTime ∧
  (∀ fault, fault ∈ due.faults ↔
    ∃ finding ∈ due.faultDecisions, finding.establishes fault atTime) ∧
  (∀ deduction ∈ due.deductions, 0 < deduction.unappliedAmount →
    deduction.shortfallTerms = agreement.shortfallTerms) ∧
  basis.totals form course.toDirect atTime due.forms terms due.agreedFee ∧
  match due.separatePart with
  | none =>
    (form.lesson.kind = .group →
      due.holdFacts.decisionConcernsWholeGroup assignment.matter assignment.decision) ∧
    (∀ placeForm ∈ due.forms, ∃ row ∈ basis.paymentsByPlace, row.place = placeForm.place.id) ∧
    TutorAmountsForSettlement due.completionHistory due.next due.faults due.deductions
      due.agreedFee due.net
  | some part =>
    form.lesson.kind = .group ∧
    basis.hasOtherHeldPlace form.lesson tutor due.forms holds assignment.authorities
      due.holdFacts atTime atTime ∧
    (∀ fault ∈ due.faults, fault.originalLesson.id ≠ due.next.lesson.id ∨
      fault.originalLesson.tutor ≠ due.next.lesson.tutor) ∧
    basis.separatePartMatches form.lesson tutor part due.holdFacts ∧
    due.deductions = [] ∧ due.net = part.amount

/-- Check the payable amount and places at the time of the actual instruction. -/
private def tutorPaymentAmount (course : LessonEvidence) (holds : HoldHistory)
    (row : TutorPayout) : Prop :=
  let due := row.settlement
  let form := due.form
  let basis := due.basis
  let tutor := due.agreement.tutor
  let part := row.part
  let paidAt := row.receipt.instruction.atTime
  let observed := row.approval.observedPayment row.authorities row.holdFacts holds part row.receipt
  let terms : TutorPayTerms :=
    ⟨due.agreement.agreementRef, due.next.lesson.normalTutorFee, due.terms⟩
  (basis.totals form course.toDirect due.settledAt due.forms terms due.agreedFee ∧
    (∀ placeForm ∈ due.forms, ∃ amount ∈ basis.paymentsByPlace, amount.place = placeForm.place.id) ∧
    TutorAmountsForSettlement due.completionHistory due.next due.faults due.deductions
      due.agreedFee due.net ∧
    (form.lesson.kind = .group → ∀ placeForm ∈ due.forms,
      FeeHoldTermsMatch placeForm row.holdFacts ∧
      (¬FeeOnHold holds row.authorities row.holdFacts placeForm.place paidAt ∨ observed)) ∧
    row.holdFacts.coversPurpose form.lesson.id (.tutorPay tutor) part.recipient due.net ∧
    row.receipt.instruction.amount ≤ holds.payments.remainingPurposeBefore form.lesson.id
      (.tutorPay tutor) part.recipient due.net paidAt) ∨
  (form.lesson.kind = .group ∧
    basis.hasOtherHeldPlace form.lesson tutor due.forms holds row.authorities
      row.holdFacts due.settledAt paidAt ∧
    (∀ fault ∈ due.faults, fault.originalLesson.id ≠ due.next.lesson.id ∨
      fault.originalLesson.tutor ≠ due.next.lesson.tutor) ∧
    (∃ subtotal, basis.totals form course.toDirect due.settledAt due.forms terms subtotal) ∧
    basis.separatePartMatches form.lesson tutor part row.holdFacts ∧
    due.deductions = [] ∧ due.net = part.amount)

/-- Check the effective payee, payment terms and approval for the retained receipt. -/
private def tutorPaymentFiling (course : LessonEvidence) (holds : HoldHistory)
    (row : TutorPayout) : Prop :=
  let due := row.settlement
  let form := due.form
  let agreement := due.agreement
  let part := row.part
  let paidAt := row.receipt.instruction.atTime
  let observed := row.approval.observedPayment row.authorities row.holdFacts holds part row.receipt
  (∀ selected ∈ due.separatePart, part = selected) ∧
  form ∈ course.bookingSchedule.effectiveForms ∧
  due.next ∈ due.completionHistory ∧
  due.next.lesson = { form.lesson with
    tutor := agreement.tutor, normalTutorFee := due.next.lesson.normalTutorFee } ∧
  TutorSettlementOccurrence form course.toDirect due.schedule due.startedAt due.settledAt
    due.basis due.next ∧
  (∀ fault, fault ∈ due.faults ↔
    ∃ finding ∈ due.faultDecisions, finding.establishes fault due.settledAt) ∧
  (∀ deduction ∈ due.deductions, 0 < deduction.unappliedAmount →
    deduction.shortfallTerms = agreement.shortfallTerms) ∧
  agreement.lesson = form.lesson.id ∧
  EffectiveTutorAgreementAt form course.toDirect due.startedAt agreement.tutor
    agreement.agreementRef due.next.lesson.normalTutorFee due.terms paidAt paidAt ∧
  course.toDirect.rosterFormsAt form.lesson due.settledAt due.roster due.forms ∧
  row.holdFacts.groupSettlementScopeMatches form.lesson (due.forms.map (·.place)) ∧
  (∀ placeForm ∈ due.forms, part.ref ∈ due.basis.tutorPartsForPlace placeForm.place.id →
    FeeHoldTermsMatch placeForm row.holdFacts ∧
    (¬FeeOnHold holds row.authorities row.holdFacts placeForm.place paidAt ∨ observed)) ∧
  due.basis.debtsReferenced form.lesson agreement.tutor paidAt ∧
  due.basis.nowIndependentlyPayable part.ref ∧ HoldFacts.matchesForm row.holdFacts form part.ref ∧
  part.ref.lesson = form.lesson.id ∧ part.ref.purpose = .tutorPay agreement.tutor ∧
  part.recipient = .person agreement.tutor agreement.recipient ∧
  tutorPaymentAmount course holds row ∧
  AgreedStartClock form.lesson course.toDirect paidAt row.clockBase ∧
  row.expiry.seconds = row.clockBase.seconds + thirtyDays ∧
  due.terms.due.appliesForLesson form.lesson course.toDirect paidAt agreement.dueTrigger
    row.schedule.dueAt ∧
  due.terms.latestExecution.appliesForLesson form.lesson course.toDirect paidAt
    agreement.executionTrigger row.schedule.originalExecutionDeadline ∧
  postLiftTermMatches form.deadlines.postLiftPay row.schedule ∧
  due.settledAt.by paidAt ∧
  (row.approval.filedPayment row.authorities row.holdFacts holds part row.schedule
    (fun instruction ↦ due.settledAt.by instruction.atTime ∧ row.agreedConditions instruction ∧
      (ClockBoundary.reachedAfter course.bookingSchedule.clockBoundaries row.clockBase thirtyDays
        instruction.atTime ∨ ∃ earlier ∈ row.schedule.legalDeadline, row.earlierLaw earlier))
    row.receipt row.afterLift ∨ observed)

/-- Each settlement operation reads the evidence for its own decision and appends its own record. -/
def Step (course : LessonEvidence) (holds : HoldHistory) (cancelled : Cancellation.History)
    (debts : Debt.History) (before : History) (event : SourceV14.Workflow.Settlement.Event)
    (after : History) : Prop :=
  match event with
  | .assessFee entry =>
    entry.decision.respectsCancellation cancelled ∧
    feeAssessment course holds entry.decision ∧
    (∀ old ∈ before.fees, old.reference ≠ entry.reference) ∧
    entry.decision.respectsRecordedGroupAbsence before.fees ∧
    after = { before with fees := before.fees ++ [entry] }
  | .fileAccount form account =>
    account.matches form course.creditFee.ledger ∧
    (form ∈ course.bookingSchedule.effectiveForms ∨
      form ∈ course.bookingSchedule.bookings.map Prod.fst) ∧
    after = { before with filed := before.filed ++ [account] }
  | .verifyTutorCompletion entry =>
    entry.conforms course.toDirect ∧
    (∀ old ∈ before.tutorCompletions, old.occurrenceKey ≠ entry.occurrenceKey) ∧
    after = { before with tutorCompletions := before.tutorCompletions ++ [entry] }
  | .reviseTutorCompletion change =>
    change.conforms before ∧
    after = { before with tutorCompletionRevisions := before.tutorCompletionRevisions ++ [change] }
  | .assessTutor due =>
    tutorAssessment course holds before due ∧
    (∀ debt, debt.debtor = due.agreement.tutor → debt.creditor = due.form.lesson.provider →
      debt.recordedAt.by due.settledAt →
      (debt ∈ due.basis.confirmedDebts due.form.lesson.id due.agreement.tutor ↔
        debt ∈ debts.confirmed)) ∧
    after = { before with tutors := before.tutors ++ [due] }
  | .fileTutorPayment row =>
    row.settlement ∈ before.tutors ∧ row.receipt ∈ holds.payments.posted ∧
    tutorPaymentFiling course holds row ∧
    (∀ old ∈ before.tutorPayments, old.receipt.id ≠ row.receipt.id) ∧
    after = { before with tutorPayments := before.tutorPayments ++ [row] }

private theorem feeAssessment_iff (course : LessonEvidence) (holds : HoldHistory)
    (decision : FeeDecision) :
    feeAssessment course holds decision ↔ decision.allowed course.toDirect holds := by
  unfold feeAssessment FeeDecision.allowed
  cases decision.basis with
  | ordinaryOneToOne =>
    unfold OrdinaryOneToOneCharge
    constructor
    · rintro ⟨handler, terms, carryOut, unheld, ledger, form, available, opens, teaching,
        noException, fee⟩
      exact ⟨form, handler, terms, carryOut, available, opens, teaching,
        noException, unheld, ledger, fee⟩
    · rintro ⟨form, handler, terms, carryOut, available, opens, teaching, noException,
        unheld, ledger, fee⟩
      exact ⟨handler, terms, carryOut, unheld, ledger, form, available, opens,
        teaching, noException, fee⟩
  | ordinaryGroup =>
    unfold OrdinaryGroupCharge
    constructor
    · rintro ⟨handler, terms, carryOut, unheld, ledger, form, available, opens, wentAhead, offered,
        paid, noException, fee⟩
      exact ⟨form, handler, terms, carryOut, available, opens, paid, noException, unheld, wentAhead,
        offered, ledger, fee⟩
    · rintro ⟨form, handler, terms, carryOut, available, opens, paid, noException,
        unheld, wentAhead, offered, ledger, fee⟩
      exact ⟨handler, terms, carryOut, unheld, ledger, form, available, opens, wentAhead, offered,
        paid, noException, fee⟩
  | absence =>
    unfold HalfFeeAbsenceRecorded
    constructor
    · rintro ⟨handler, terms, carryOut, unheld, ledger, roster, opens, startsBy, evidence, refund⟩
      exact ⟨roster, rfl, handler, terms, carryOut, unheld, opens, startsBy,
        ledger, evidence, refund⟩
    · rintro ⟨roster, _, handler, terms, carryOut, unheld, opens, startsBy,
        ledger, evidence, refund⟩
      exact ⟨handler, terms, carryOut, unheld, ledger, roster, opens, startsBy, evidence, refund⟩
  | agreedChange cause assessment =>
    cases cause <;> rfl
  | providerStartedEarly =>
    unfold UnauthorisedStartSettlement
    constructor
    · rintro ⟨handler, terms, carryOut, unheld, ledger, roster, teaching, schedule, startsBy, unmet,
        prohibited, wentAhead, providerTerms, fee, pay, refund⟩
      exact ⟨roster, teaching, schedule, startsBy, unmet, prohibited, wentAhead, handler, terms,
        carryOut, unheld, providerTerms, ledger, fee, pay, refund⟩
    · rintro ⟨roster, teaching, schedule, startsBy, unmet, prohibited, wentAhead, handler, terms,
        carryOut, unheld, providerTerms, ledger, fee, pay, refund⟩
      exact ⟨handler, terms, carryOut, unheld, ledger, roster, teaching, schedule, startsBy, unmet,
        prohibited, wentAhead, providerTerms, fee, pay, refund⟩

private theorem tutorAssessment_iff (course : LessonEvidence) (holds : HoldHistory)
    (before : History) (due : TutorDue) :
    tutorAssessment course holds before due ↔ due.established course.toDirect holds before := by
  unfold tutorAssessment TutorDue.established
  constructor
  · rintro ⟨handler, carryOut, form, roster, scope, occurrence, absence, identity, terms,
      completions, next, lesson, records, debts, faults, remainders, totals, pay⟩
    exact ⟨form, roster, scope, handler, carryOut, completions, next, lesson, occurrence, absence,
      identity, terms, debts, faults, remainders, records, totals, pay⟩
  · rintro ⟨form, roster, scope, handler, carryOut, completions, next, lesson, occurrence, absence,
      identity, terms, debts, faults, remainders, records, totals, pay⟩
    exact ⟨handler, carryOut, form, roster, scope, occurrence, absence, identity, terms,
      completions, next, lesson, records, debts, faults, remainders, totals, pay⟩

private theorem tutorPaymentFiling_iff (course : LessonEvidence) (holds : HoldHistory)
    (row : TutorPayout) :
    tutorPaymentFiling course holds row ↔ row.checked course.toDirect holds := by
  unfold tutorPaymentFiling tutorPaymentAmount TutorPayout.checked TutorPaymentPosted
  constructor
  · rintro ⟨separate, form, next, lesson, occurrence, faults, remainders, identity, agreement,
      roster, scope, unheld, debts, payable, partForm, partLesson, purpose, recipient, amount,
      startClock, expiry, dueTerm, executionTerm, liftTerm, settled, approval⟩
    exact ⟨separate, form, next, lesson, occurrence, startClock, expiry, faults, remainders,
      identity, agreement, roster, scope, unheld, debts, payable, partForm, dueTerm, partLesson,
      purpose, recipient, amount, executionTerm, liftTerm, settled, approval, Iff.rfl, Iff.rfl⟩
  · rintro ⟨separate, form, next, lesson, occurrence, startClock, expiry, faults, remainders,
      identity, agreement, roster, scope, unheld, debts, payable, partForm, dueTerm, partLesson,
      purpose, recipient, amount, executionTerm, liftTerm, settled, approval, _, _⟩
    exact ⟨separate, form, next, lesson, occurrence, faults, remainders, identity, agreement,
      roster, scope, unheld, debts, payable, partForm, partLesson, purpose, recipient, amount,
      startClock, expiry, dueTerm, executionTerm, liftTerm, settled, approval⟩

/-- Local settlement preserves the source gates and the exact successor for every event. -/
theorem step_iff (course : LessonEvidence) (holds : HoldHistory) (cancelled : Cancellation.History)
    (debts : Debt.History) (before : History) (event : SourceV14.Workflow.Settlement.Event)
    (after : History) :
    Step course holds cancelled debts before event after ↔
      event.respectsCancellation cancelled ∧ event.readsConfirmedDebts debts ∧
        SourceV14.Workflow.Settlement.Step course.toDirect holds before event after := by
  constructor
  · cases event with
    | assessFee entry =>
      rintro ⟨active, assessed, fresh, absence, rfl⟩
      exact ⟨active, trivial,
        .assessFee ((feeAssessment_iff course holds entry.decision).mp assessed) fresh absence⟩
    | fileAccount form account =>
      rintro ⟨filed, retainedForm, rfl⟩
      exact ⟨trivial, trivial, .fileAccount filed retainedForm⟩
    | verifyTutorCompletion entry =>
      rintro ⟨verified, fresh, rfl⟩
      exact ⟨trivial, trivial, .verifyTutorCompletion verified fresh⟩
    | reviseTutorCompletion change =>
      rintro ⟨revised, rfl⟩
      exact ⟨trivial, trivial, .reviseTutorCompletion revised⟩
    | assessTutor due =>
      rintro ⟨assessed, confirmedDebts, rfl⟩
      exact ⟨trivial, confirmedDebts,
        .assessTutor ((tutorAssessment_iff course holds before due).mp assessed)⟩
    | fileTutorPayment row =>
      rintro ⟨prior, posted, filed, fresh, rfl⟩
      exact ⟨trivial, trivial,
        .fileTutorPayment prior posted ((tutorPaymentFiling_iff course holds row).mp filed) fresh⟩
  · rintro ⟨active, confirmedDebts, rule⟩
    cases rule with
    | assessFee allowed fresh absence =>
      exact ⟨active, (feeAssessment_iff ..).mpr allowed, fresh, absence, rfl⟩
    | fileAccount filed retainedForm => exact ⟨filed, retainedForm, rfl⟩
    | verifyTutorCompletion verified fresh => exact ⟨verified, fresh, rfl⟩
    | reviseTutorCompletion revised => exact ⟨revised, rfl⟩
    | assessTutor established =>
      exact ⟨(tutorAssessment_iff ..).mpr established, confirmedDebts, rfl⟩
    | fileTutorPayment prior posted checked fresh =>
      exact ⟨prior, posted, (tutorPaymentFiling_iff ..).mpr checked, fresh, rfl⟩

end RecognisedV15.Settlement
