import SourceV14.Workflow

/-! Agreed-change checks for a debited one-to-one place. -/

namespace FidelityCancellationChecks

open SourceV14 SourceV14.Booking SourceV14.Confirmation SourceV14.Course
open SourceV14.CreditEvidence SourceV14.Operations SourceV14.Workflow

private def m (seconds : Nat) : Moment := ⟨seconds, 0⟩

private def lesson : Lesson := ⟨17, .oneToOne, 1, 2, 3, 80⟩
private def place : Place := ⟨8, 17, 11, 12, 13, 14, 100, 100⟩
private def schedule : Schedule := ⟨17, m 345600, m 349200, "UTC", m 8, m 9⟩
private def cutoff : Moment := m 259200
private def refundDeadlineAt : Moment := m 180000
private def paymentTerms : PaymentTerms := ⟨.fixed refundDeadlineAt, .fixed refundDeadlineAt⟩

private def form : PartOne where
  lesson := lesson
  place := place
  contacts :=
    ⟨"Provider", "provider", "email", none, "coordinator", 4, "lead", none, none,
      5, "review", 6, "alternative", false, 7, "escalation"⟩
  rulesVersion := "1.5"
  confirmedAt := m 10
  customerRepresentatives := []
  schedule := schedule
  serviceTerms := "one hour of tutoring"
  serviceItems := [1]
  discountBasis := none
  privateRoster := none
  rosterLock := none
  groupRescheduleCutoff := none
  oneToOneAdvanceCutoff := some (.fixed cutoff)
  cancelChangeTerms :=
    "Retain 20 on timely cancellation and restore the excess. Retain 15 and pay the tutor 25 for verified good reason."
  noFaultTerms := "No-fault terms"
  applicableStartTerms := "Start terms"
  tutorAgreementRef := "Tutor agreement"
  absentGroupPlacePay := none
  materialsOrBundle := none
  materialsTermsRef := none
  materialsPayer := none
  deadlines :=
    ⟨.fixed refundDeadlineAt, m 170000, none, paymentTerms, paymentTerms, paymentTerms,
      paymentTerms, .fixed refundDeadlineAt, m 181000, m 181000, m 181000, .fixed (m 182000)⟩

private def reviewTerms : ReviewTerms :=
  ⟨3, 6, 4, .exact refundDeadlineAt, m 181000, m 181000, m 181000, 7⟩

private def noInterest : DirectInterest := ⟨false, false, false, false⟩

private def authorities : ReviewAuthorities where
  corePartner := fun actor _ ↦ actor = 1
  initialFinding := fun _ _ _ ↦ False
  reviewer := fun _ _ _ ↦ False
  approvesPayment := fun ref actor _ ↦ ref.lesson = lesson.id ∧ actor = lesson.provider
  interest := fun _ _ _ ↦ noInterest
  originalDecisionMaker := fun _ ↦ none
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

private def part : PaymentPart := ⟨⟨17, 21, 1, .lessonRefund 8⟩, .lessonRefund 14, 80⟩

private def holdFacts : HoldFacts where
  terms := fun _ ↦ reviewTerms
  termsApply := fun _ ↦ False
  acceptedPaymentConcern := fun _ _ _ _ ↦ False
  reviewerCannotActInTime := fun _ _ ↦ False
  temporaryAuthority := fun _ _ _ _ ↦ False
  allegedFactsWouldChangePayment := fun _ _ _ ↦ False
  separatelyIdentifiable := fun _ _ ↦ False
  establishedParts := fun id purpose ↦
    if id = part.ref.lesson ∧ purpose = part.ref.purpose then [part] else []
  paymentAffected := fun _ _ ↦ False
  decisionPending := fun _ _ _ ↦ False
  partFallsUnderDecision := fun _ _ _ ↦ False
  decisionConcernsWholeGroup := fun _ _ ↦ False
  isGroupLesson := fun _ ↦ False
  affectsWholeSettlement := fun _ ↦ False
  groupSettlementParts := fun _ ↦ []

private def approvalScope : ApprovalScopeEntry := ⟨part.ref, .account 14, 80, none⟩
private def approval : PaymentApproval :=
  ⟨1, 1, 3, m 172803, some (m 185000), none, [approvalScope]⟩

private def holds : HoldHistory where
  payments := ⟨[], [], []⟩
  temporary := []
  formal := []
  lifts := []

private def debit : CreditPosting := ⟨1, 14, .lessonDebit 17 8, 100, m 10⟩

-- The prestate supplies the already confirmed place and its original exact debit.
private def course : StartEvidence where
  effectiveForms := [form]
  groupRoster := none
  bookings := []
  scheduleHistory := [schedule]
  changes := []
  openingCredit := fun account ↦ if account = place.account then 100 else 0
  creditRecords :=
    { topUps := [], grants := [], topUpReturns := [], closed := []
      ownsAccount := fun actor account ↦ actor = place.payer ∧ account = place.account
      courseProviderAt := fun actor _ ↦ actor = lesson.provider
      verifiedRefunds := [], payments := holds.payments, paymentAuthorities := authorities }
  ledger := [debit]
  discounts := []
  notices := []
  academicTeamAt := fun id actor _ ↦ id = lesson.id ∧ actor = lesson.coordinator
  teachingBegan := none
  teachingEnded := none
  verifiedOneToOneAbsence := none
  studentsTakingLesson := []
  afterLesson := ⟨[], [], [], [], [], []⟩
  studentFaults :=
    { findings := []
      decisions :=
        { authorities, terms := reviewTerms, appointments := [], faultOutcomes := []
          faultMatterCovers := fun _ _ ↦ False
          wasResponsibleTutor := fun _ _ ↦ False
          originalAttendanceTime := fun _ _ _ ↦ False }
      recordedStudentOutcome := fun _ ↦ False }

private def initial : State where
  lessons := fun _ ↦ LessonFile.fromEvidence course
  credit := CreditBook.fromEvidence course
  holds := holds
  cancelled := []
  settlement := {}
  redress := {}
  materials := {}
  review := Review.History.empty
  debts := {}
  tutorFaults := ⟨[], []⟩
  activeReserves := []
  paymentRecords := []
  separateBookings := []

private def request : CancellationRequest := ⟨17, 8, 12, 3, m 172800⟩
private def lateRequest : CancellationRequest := { request with point := m 259201 }
private def cancellation : Cancellation.Event := .oneToOne form request
private def cancelled : State := { initial with cancelled := [cancellation] }

private def assignment : SettlementAssignment :=
  ⟨⟨1, 17, [12]⟩, 1, authorities, none, none, fun seat ↦ seat = place.id⟩

private def handler : Handler := ⟨3, false, noInterest⟩

private def assessment : AgreedChangeAssessment where
  termsReference := form.cancelChangeTerms
  finalFee := 20
  tutorPay := 0
  verifiedUnderApplicableTerms := request.point.seconds + 86400 ≤ schedule.start.seconds

private def amounts : SourceV14.Settlement.LessonSettlement := ⟨17, 8, 20, 100, 80, 0, 0, 0⟩

private def fee : Settlement.AdoptedFee where
  reference := 9
  decision :=
    ⟨form, schedule, schedule.start, refundDeadlineAt, m 172801, handler, assignment,
      holdFacts, .agreedChange (.advanceCancellation request) assessment, amounts⟩

private def assessed : State := { cancelled with settlement := { fees := [fee] } }

private theorem formMatches : form.matches := by
  simp [PartOne.matches, form, lesson, place, schedule, m, Contacts.complete,
    Place.matches, Place.validFees, Schedule.valid, Moment.by, Moment.before, PayAndReviewTerms.valid,
    paymentTerms, PaymentTerms.valid, PaymentDeadline.valid, AdvanceWindow.validAt] <;> decide +kernel

private theorem timelyRequestAllowed : CanCancelOneToOne form request course := by
  refine ⟨formMatches, ⟨rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_⟩
  · simp [course]
  · refine ⟨.fixed cutoff, by simp [form], ?_⟩
    refine ⟨?_, schedule, ?_, by decide⟩
    · simp [AdvanceWindow.allows, AdvanceWindow.validAt]
      decide
    · refine ⟨rfl, ?_, ?_, ?_⟩
      · simp [Schedule.effectiveAtQuery, course, schedule, request, Schedule.valid,
          Moment.by, Moment.before, m] <;> decide
      · simp [course, schedule, form, lesson]
      · intro row member _ _
        have eq : row = schedule := by simpa [course] using member
        subst row
        refine ⟨rfl, by simp [schedule, Schedule.valid, Moment.before, m]; decide,
          Or.inl ⟨rfl, ?_, ?_⟩⟩
        · change (course.formsMatch lesson ∧ [form].length = 1)
          simp [StartEvidence.formsMatch, course, show form.lesson = lesson from rfl, formMatches]
        · intro item member
          have eq : item = form := by simpa [course] using member
          subst item
          rfl

theorem fixedCutoffDoesNotPermitCancellationAtStart :
    ¬ CanCancelOneToOne
      { form with oneToOneAdvanceCutoff := some (.fixed (m 400000)) }
      { request with point := schedule.start } course := by
  intro allowed
  obtain ⟨_, _, _, _, window, inForm, windowAllowed⟩ := allowed
  have fixed : window = .fixed (m 400000) := by simpa using inForm.symm
  subst window
  obtain ⟨_, current, effective, before⟩ := windowAllowed
  have member : current ∈ course.scheduleHistory := effective.2.1.1
  have same : current = schedule := by simpa [course] using member
  subst current
  exact (by decide : ¬ schedule.start.before schedule.start) before

theorem advanceCancellationRecorded :
    Step initial (.cancellation cancellation) cancelled := by
  apply Step.cancellation
  · trivial
  · refine ⟨by decide, by simp [initial], ?_, rfl⟩
    exact ⟨by change form ∈ [form]; simp, timelyRequestAllowed⟩

theorem lateCancellationRejected (next : State) :
    ¬ Step initial (.cancellation (.oneToOne form lateRequest)) next := by
  intro step
  cases step with
  | cancellation _ rule =>
    have canCancel : CanCancelOneToOne form lateRequest course := rule.2.2.1.2
    obtain ⟨_, _, _, _, window, inForm, allowed⟩ := canCancel
    have exactWindow : .fixed cutoff = window := by simpa [form] using inForm
    subst window
    exact (by decide : ¬ lateRequest.point.by cutoff) allowed.1.2.2

private theorem feeAllowed : fee.decision.allowed course holds := by
  change AgreedChangeSettlementRecorded form course (m 172801) (some request)
    none none assessment amounts handler assignment holds holdFacts
  refine ⟨?_, ?_, ?_, ?_, ?_, Or.inl ⟨request, by simp, by decide, timelyRequestAllowed⟩,
    rfl, ?_, ?_, rfl, rfl, by decide +kernel⟩
  · refine ⟨none, [form], ?_, by simp⟩
    change (course.formsMatch lesson ∧ [form].length = 1) ∧ [form] = [form]
    simp [StartEvidence.formsMatch, course, show form.lesson = lesson from rfl, formMatches]
  · simp [SettlementAssignment.authorised, assignment, form, handler, Handler.maySettle, lesson,
      place, authorities, ReviewAuthorities.disinterested, noInterest, DirectInterest.affected]
  · simp [FeeHoldTermsMatch, HoldFacts.matchesForm, holdFacts]
  · simp [HoldHistory.mayCarryOutDecision, HoldHistory.distinctFormalDecisions,
      HoldHistory.decisionOnFormalHold, HoldHistory.validFormalHold, holds]
  · simp [FeeOnHold, HoldHistory.paymentOnHold, HoldHistory.formalInForce,
      HoldHistory.temporaryInForce, HoldHistory.validFormalHold, holds]
  · change request.point.seconds + 86400 ≤ schedule.start.seconds
    decide
  · refine ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩

theorem exactCancellationSettled :
    Step cancelled (.settlement (.assessFee fee)) assessed := by
  apply Step.settlement
  · change Cancellation.HasOneToOneCancellation [cancellation] form request
    simp [Cancellation.HasOneToOneCancellation, cancellation]
  all_goals first
    | trivial
    | exact Settlement.Step.assessFee (before := cancelled.settlement) feeAllowed
        (by simp [cancelled, initial]) trivial

theorem unrecordedCancellationCannotSettle (next : State) :
    ¬ Step initial (.settlement (.assessFee fee)) next := by
  intro step
  cases step with
  | settlement active _ _ _ =>
    change Cancellation.HasOneToOneCancellation [] form request at active
    simp [Cancellation.HasOneToOneCancellation] at active

theorem ordinaryChargeStillBlocked (entry : Settlement.AdoptedFee) (next : State)
    (ordinary : entry.decision.agreedCancellation = none)
    (cancelledPlace : Cancellation.PlaceCancelledAt cancelled.cancelled
      entry.decision.form.place entry.decision.decidedAt) :
    ¬ Step cancelled (.settlement (.assessFee entry)) next := by
  intro step
  cases step with
  | settlement active _ _ _ =>
    exact (by
      simpa [Settlement.Event.respectsCancellation, Settlement.FeeDecision.respectsCancellation,
        ordinary] using active :
        ¬Cancellation.PlaceCancelledAt cancelled.cancelled entry.decision.form.place
          entry.decision.decidedAt) cancelledPlace

private def refund : Redress.AssessedRefund where
  amount :=
    ⟨form, part.ref.obligation, .agreedChange, "Agreed advance cancellation",
      request.point, m 172802, ⟨refundDeadlineAt, refundDeadlineAt, none, .date (m 182000)⟩,
      20, 80, [part]⟩
  evidence := .agreedChange fee
  dueEvent := none
  executionEvent := none

private def refundHistory : Redress.History := { assessments := [refund] }

private def refundAssessed : State :=
  { (assessed.withCourse lesson.id course).withHolds holds with redress := refundHistory }

private theorem partsMatch : refund.amount.partsMatch holdFacts := by
  simp [Redress.RefundAssessment.partsMatch, refund, holdFacts, part, form, place, lesson,
    sumAmounts] <;> decide +kernel

private theorem refundConforms : refund.conforms assessed.redress course holds holdFacts := by
  refine ⟨formMatches, by decide, by decide, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_, partsMatch, rfl, ?_, ?_⟩
  · simp [EarlierFeeRefundsFor]
  · simp [assessed, cancelled, initial]
  · simp [refund, fee, Settlement.FeeDecision.agreedChangeAt, paymentTerms,
      PaymentDeadline.appliesForLesson, PaymentDeadline.applies, Redress.RefundTriggerEvidence.applies, form,
      feeAdjustmentRefundPrincipal, earlierOutstanding] <;> decide +kernel

theorem refundFromAdoptedFee :
    Step assessed (.redress (.assessRefund refund holdFacts)) refundAssessed := by
  apply Step.redress (after := course) (holds := holds)
  · simp [Redress.Event.usesRecordedCancellation, refund, assessed, fee,
      Settlement.FeeDecision.respectsCancellation, Settlement.FeeDecision.agreedCancellation,
      Cancellation.HasOneToOneCancellation, cancelled, cancellation]
  · trivial
  · simp [Redress.Event.usesRecordedReviews, Redress.Event.assessmentDecisions, refund]
  · trivial
  · exact ⟨refundConforms, rfl, rfl, rfl⟩

private def unadoptedFee : Settlement.AdoptedFee := { fee with reference := 99 }

private def refundWithUnadoptedFee : Redress.AssessedRefund :=
  { refund with evidence := .agreedChange unadoptedFee }

theorem refundRequiresExactAdoptedFee (next : State) :
    ¬ Step assessed (.redress (.assessRefund refundWithUnadoptedFee holdFacts)) next := by
  intro step
  cases step with
  | redress recorded _ _ _ _ =>
    have present : unadoptedFee ∈ [fee] := recorded.1
    have sameFee : unadoptedFee = fee := List.mem_singleton.mp present
    exact (by decide : ¬ unadoptedFee.reference = fee.reference) (congrArg (·.reference) sameFee)

private def refundWithWrongBasis : Redress.AssessedRefund :=
  { refund with amount := { refund.amount with basis := .absence } }

theorem refundCannotUseAbsenceBasis (next : State) :
    ¬ Step assessed (.redress (.assessRefund refundWithWrongBasis holdFacts)) next := by
  intro step
  cases step with
  | redress _ _ _ _ rule =>
    have conforms : refundWithWrongBasis.conforms assessed.redress course holds holdFacts := rule.1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, basis, _⟩ := conforms
    nomatch basis

private def approvedHolds : HoldHistory := { holds with approvals := [approval] }
private def approved : State :=
  { refundAssessed.withHolds approvedHolds with paymentRecords := [.grantApproval approval] }

theorem approvedRefundPayment :
    Step refundAssessed (.payment (.grantApproval approval)) approved :=
  Step.payment trivial
    (Payment.Step.grantApproval approval (by change approval.id ∉ ([] : List ApprovalId); simp))

private def receipt : CreditPosting := ⟨2, 14, .lessonRefund 17 8 21, 80, m 173000⟩

private def paid : PostedPayment :=
  ⟨receipt.id, ⟨part.ref, .account place.account, approval.executor, receipt.amount, receipt.point⟩,
    some 11⟩

private def filing : VerifiedLessonRefund where
  form := form
  originalDebit := debit
  obligation := part.ref.obligation
  settlement :=
    ⟨lesson.id, place.id, place.account, refund.amount.reason, refund.amount.basis, 20,
      request.point, refundDeadlineAt, 80, 80, [receipt.point], false, false⟩
  payment := paid
  approval := some approval

private def posting : Redress.RefundPosting :=
  ⟨refund, receipt, filing, part, some (.ordinary approval), none⟩

private def paymentConditions (instruction : PaymentInstruction) : Prop :=
  instruction.destination = .account place.account

private def paidHolds : HoldHistory :=
  { approvedHolds with payments := { approvedHolds.payments with posted := [paid] } }

private def restored : State :=
  { (approved.withCourse lesson.id (Redress.receiveRefund course receipt filing paidHolds.payments))
      |>.withHolds paidHolds with redress := refundHistory }

private theorem recordMatches :
    filing.settlement.matches form [debit, receipt] receipt.point refund.amount.reason
      request.point refundDeadlineAt 80 (some part.ref.obligation) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel, by simp [filing], ?_, by decide⟩
  intro time
  constructor
  · intro entered
    have sameTime : time = receipt.point := by simpa [filing] using entered
    subst time
    exact ⟨receipt, by simp, rfl, rfl, by decide, 21, rfl, Or.inr rfl⟩
  · rintro ⟨entry, inLedger, _, timeMatches, _, obligation, kindMatches, _⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inLedger
    rcases inLedger with rfl | rfl
    · cases kindMatches
    · simpa [filing] using timeMatches.symm

private theorem actualPayment : paidHolds.payments.actualPaymentWithEvidence paid := by
  simp [PaymentHistory.actualPaymentWithEvidence, paidHolds, paid]

private theorem grantAuthorised : approval.authorisedAtGrant authorities := by
  simp [PaymentApproval.authorisedAtGrant, approval, approvalScope, authorities, part, lesson]

private theorem verifiedRefundFile :
    filing.matches [debit, receipt] paidHolds.payments authorities receipt := by
  refine ⟨formMatches, by simp [filing], rfl, rfl, by decide, by decide +kernel, by decide,
    by decide, by decide, by decide +kernel, by decide +kernel, by decide +kernel,
    recordMatches, ?_, actualPayment, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · exact ⟨by simp, rfl, rfl, by decide +kernel⟩
  · intro supplied represented
    have same : approval = supplied := by simpa [filing] using represented
    subst supplied
    exact ⟨grantAuthorised, by decide, approvalScope, by simp [approval], rfl, rfl,
      by decide +kernel⟩

private theorem verifiedFiling :
    posting.verifiedFiling refundHistory course [debit, receipt] paidHolds.payments
      holdFacts authorities := by
  refine ⟨by simp [posting, refundHistory], by decide, rfl, rfl,
    by simp [posting, refund], partsMatch, rfl, ?_, rfl, rfl, rfl, ?_,
    recordMatches, verifiedRefundFile⟩
  · simp [course]
  · simp [posting, filing, refund]

private theorem filingApproved :
    PaymentApprovalRoute.filedPayment (.ordinary approval) authorities holdFacts paidHolds part
      refund.amount.schedule paymentConditions paid [] := by
  refine ⟨actualPayment, rfl, ?_, ?_⟩
  · change originalExecutorMayPay authorities holdFacts paidHolds approval part
      refund.amount.schedule paymentConditions paid.instruction
    refine ⟨?_, ?_, grantAuthorised, ?_, ?_, rfl, ?_, rfl, by decide, ?_, ?_⟩
    · simp [HoldFacts.isCanonicalPart, holdFacts] <;> decide +kernel
    · simp [HoldHistory.approvalRecorded, paidHolds, approvedHolds]
    · refine ⟨by decide, ?_, ?_⟩
      · simp [approval]
        decide
      · simp [approval]
    · refine ⟨approvalScope, by simp [approval], rfl, rfl, by simp [approvalScope],
        by decide +kernel⟩
    · refine ⟨rfl, rfl, by decide +kernel, by decide +kernel, ?_, ?_⟩
      · simp [PaymentHistory.distinctReceipts, paidHolds, approvedHolds, holds]
      · simp [PaymentHistory.validReturns, paidHolds, approvedHolds, holds, sumAmounts]
        decide +kernel
    · simp [HoldHistory.distinctFormalDecisions, paidHolds, approvedHolds, holds]
    · simp [HoldHistory.paymentOnHold, HoldHistory.formalInForce, HoldHistory.temporaryInForce,
        HoldHistory.validFormalHold, HoldHistory.remainingPortionBefore, paidHolds, approvedHolds,
        holds] <;> decide +kernel
  · rintro ⟨time, ⟨hold, _, released, _⟩, _⟩
    have recordedHold : hold ∈ [] := released.1.1
    simp at recordedHold

private theorem validFiling :
    posting.validFiling refundHistory course [debit, receipt] paidHolds
      holdFacts authorities paymentConditions := by
  refine ⟨⟨verifiedFiling, ?_⟩, .ordinary approval, by simp [posting], rfl, ?_, rfl, rfl, ?_, ?_,
    rfl, filingApproved⟩
  · refine ⟨[], ?_, ⟨by simp [posting], rfl, rfl, by decide +kernel⟩, by decide +kernel,
      by decide +kernel⟩
    decide +kernel
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, actualPayment⟩
  · simp [HoldFacts.coversObligation, holdFacts, refund, posting] <;> decide +kernel
  · simp [HoldFacts.matchesForm, holdFacts]

theorem refundRestoredToDebitedAccount :
    Step approved (.redress (.postRefund posting holdFacts authorities paymentConditions)) restored := by
  apply Step.redress
    (after := Redress.receiveRefund course receipt filing paidHolds.payments) (holds := paidHolds)
  · trivial
  · trivial
  · simp [Redress.Event.usesRecordedReviews, Redress.Event.assessmentDecisions]
  · trivial
  · refine ⟨⟨by simp [Redress.FreshPosting]; decide, ?_, rfl, rfl, validFiling⟩, rfl, rfl⟩
    change paid.id ∉ ([] : List PaymentId)
    simp

theorem originalAccountRestored :
    SourceV14.Settlement.refundBalanceDue place restored.credit.ledger receipt.point
      80 (some part.ref.obligation) = 0 ∧
    restored.credit.creditRecords.verifiedRefunds = [filing] ∧
    balanceBefore restored.credit.openingCredit restored.credit.ledger place.account (m 173001) =
      80 := by
  exact ⟨by decide +kernel, rfl, by decide +kernel⟩

private def wrongPosting : Redress.RefundPosting :=
  { posting with
    posting := { receipt with account := 99 }
    filing := { filing with
      payment := { paid with instruction := { paid.instruction with destination := .account 99 } } } }

theorem wrongAccountCannotDischargeRefund (next : State) :
    ¬ Step approved (.redress (.postRefund wrongPosting holdFacts authorities paymentConditions))
      next := by
  intro step
  cases step with
  | redress _ _ _ _ rule =>
    obtain ⟨_, _, _, _, valid⟩ := rule.1
    obtain ⟨_, _, _, _, filed⟩ := valid
    have wrongAccountMatches : wrongPosting.posting.account = form.place.account := filed.1.2.1
    exact (by decide : ¬ wrongPosting.posting.account = form.place.account) wrongAccountMatches

private def goodReasonFacts : AbsenceFacts where
  startRequirementsMet := True
  studentNotifiedAsAgreed := True
  teachingAvailableAsAgreed := True
  studentDidNotAttend := True
  providerErrorCausedMissedService := False
  cancelledOrRescheduledUnderTerms := False
  lessonWentAhead := False
  couldNotProceedSolelyForNonattendance := True
  studentWasNotReady := True
  verifiedGoodReason := some true

private def goodReasonEvidence : AbsenceReasonEvidence :=
  ⟨False, course.studentFaults.decisions, []⟩

private def verifiedAbsence : AttendanceFacts.OneToOneAbsence :=
  ⟨form, schedule, schedule.start, m 346000, goodReasonFacts⟩

private def absenceCourse : StartEvidence :=
  { course with verifiedOneToOneAbsence := some verifiedAbsence }

private def absenceState : State := initial.withCourse lesson.id absenceCourse

private def absenceDecisionAt : Moment := m 346100
private def tutorDecisionAt : Moment := m 346200

private def goodReasonAssessment : AgreedChangeAssessment :=
  ⟨form.cancelChangeTerms, 15, 25, goodReasonFacts.verifiedGoodReason = some true⟩

private def goodReasonAmounts : SourceV14.Settlement.LessonSettlement :=
  ⟨17, 8, 15, 100, 85, 0, 25, 0⟩

private def goodReasonFee : Settlement.AdoptedFee where
  reference := 10
  decision :=
    ⟨form, schedule, schedule.start, refundDeadlineAt, absenceDecisionAt, handler, assignment,
      holdFacts, .agreedChange (.goodReasonAbsence goodReasonFacts goodReasonEvidence)
        goodReasonAssessment, goodReasonAmounts⟩

private def absenceSettled : State := { absenceState with settlement := { fees := [goodReasonFee] } }

private theorem goodReasonUsesChangeTerms :
    oneToOneAbsenceUsesChangeTerms lesson place goodReasonFacts := by
  simp [oneToOneAbsenceUsesChangeTerms, verifiedStudentAbsence, lesson, place, Place.matches,
    goodReasonFacts]

private theorem absenceWasVerified (cut : Moment) (verified : verifiedAbsence.checkedAt.by cut) :
    absenceCourse.retainsOneToOneAbsence form schedule schedule.start cut goodReasonFacts :=
  ⟨verifiedAbsence, by simp [absenceCourse], ⟨rfl, rfl, verified⟩, rfl, rfl⟩

private theorem goodReasonFeeAllowed : goodReasonFee.decision.allowed absenceCourse holds := by
  refine ⟨rfl, absenceWasVerified absenceDecisionAt (by decide), by decide, ?_⟩
  change AgreedChangeSettlementRecorded form absenceCourse absenceDecisionAt none none
    (some (goodReasonFacts, goodReasonEvidence)) goodReasonAssessment goodReasonAmounts
    handler assignment holds holdFacts
  refine ⟨?_, ?_, ?_, ?_, ?_,
    Or.inr (Or.inr ⟨(goodReasonFacts, goodReasonEvidence), by simp, goodReasonUsesChangeTerms,
      by intro needed; exact False.elim needed,
      schedule, schedule.start, absenceWasVerified absenceDecisionAt (by decide)⟩),
    rfl, rfl, ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩, rfl, rfl, by decide +kernel⟩
  · refine ⟨none, [form], ?_, by simp⟩
    change (absenceCourse.formsMatch lesson ∧ [form].length = 1) ∧ [form] = [form]
    simp [StartEvidence.formsMatch, absenceCourse, course, show form.lesson = lesson from rfl,
      formMatches]
  · simp [SettlementAssignment.authorised, assignment, form, handler, Handler.maySettle, lesson,
      place, authorities, ReviewAuthorities.disinterested, noInterest, DirectInterest.affected]
  · simp [FeeHoldTermsMatch, HoldFacts.matchesForm, holdFacts]
  · simp [HoldHistory.mayCarryOutDecision, HoldHistory.distinctFormalDecisions,
      HoldHistory.decisionOnFormalHold, HoldHistory.validFormalHold, holds]
  · simp [FeeOnHold, HoldHistory.paymentOnHold, HoldHistory.formalInForce,
      HoldHistory.temporaryInForce, HoldHistory.validFormalHold, holds]

theorem signedGoodReasonFeeAtRoot :
    Step absenceState (.settlement (.assessFee goodReasonFee)) absenceSettled := by
  apply Step.settlement
  · change ¬ Cancellation.PlaceCancelledAt [] form.place absenceDecisionAt
    simp [Cancellation.PlaceCancelledAt]
  all_goals first
    | trivial
    | (change State.absenceReasonCurrentAt absenceState form absenceDecisionAt
       change ∀ prior ∈ AttendanceFacts.OneToOneAbsenceReason.latestAt _ _, ∀ revision ∈
         ([] : List Review.Correction), _
       simp)
    | exact Settlement.Step.assessFee (before := absenceState.settlement) goodReasonFeeAllowed
        (by
          change ∀ old ∈ ([] : List Settlement.AdoptedFee), old.reference ≠ goodReasonFee.reference
          simp) trivial

private def notYetVerified : StartEvidence :=
  { course with
    verifiedOneToOneAbsence := some { verifiedAbsence with checkedAt := m 346101 } }

theorem goodReasonAssessmentWaitsForVerification :
    ¬ goodReasonFee.decision.allowed notYetVerified holds := by
  intro allowed
  have retained : notYetVerified.retainsOneToOneAbsence
      form schedule schedule.start absenceDecisionAt goodReasonFacts := allowed.2.1
  obtain ⟨row, saved, matched, _⟩ := retained
  have exactRow : { verifiedAbsence with checkedAt := m 346101 } = row := by
    simpa [notYetVerified] using saved
  subst row
  exact (by decide : ¬ (m 346101).by absenceDecisionAt) matched.2.2

private def goodReasonBasis : TutorSettlementBasis where
  paymentsByPlace := [goodReasonAmounts]
  hadTutorPayUnderTerms := fun agreement row ↦
    agreement.reference = form.tutorAgreementRef ∧ row.tutorPay = 25
  nowIndependentlyPayable := fun _ ↦ False
  tutorPartsForPlace := fun _ ↦ []
  absenceWithoutTeaching := some (schedule.start, goodReasonFacts, goodReasonEvidence)
  agreedNetPortion := fun _ ↦ none
  operativeSettlement := fun seat cut ↦
    if seat = place.id ∧ absenceDecisionAt.by cut then some (goodReasonAmounts, absenceDecisionAt)
    else none
  confirmedDebts := fun _ _ ↦ []
  separateDebtReferences := []

private def absentTutorRecord : TutorLessonRecord := ⟨lesson, none, false, 25⟩

private def goodReasonDue : Settlement.TutorDue where
  form := form
  roster := none
  forms := [form]
  schedule := schedule
  startedAt := schedule.start
  settledAt := tutorDecisionAt
  next := absentTutorRecord
  completionHistory := [absentTutorRecord]
  faultDecisions := []
  faults := []
  deductions := []
  agreement := ⟨lesson.id, lesson.tutor, form.tutorAgreementRef, none, none, none, none⟩
  terms := form.deadlines.tutorPay
  basis := goodReasonBasis
  handler := handler
  assignment := assignment
  holdFacts := holdFacts
  agreedFee := 25
  net := 25
  separatePart := none

theorem goodReasonTutorUsesAdoptedFee :
    goodReasonDue.agreedAbsenceRecorded absenceCourse absenceSettled.settlement ∧
    goodReasonBasis.paymentsByPlace.map (·.tutorPay) = [25] ∧
    absentTutorRecord.feeOtherwisePayable ≠ lesson.normalTutorFee / 2 := by
  refine ⟨?_, rfl, by decide +kernel⟩
  intro _ facts reason same _
  have pair := Option.some.inj same
  have factsMatch : goodReasonFacts = facts := congrArg (fun row ↦ row.2.1) pair
  have reasonsMatch : goodReasonEvidence = reason := congrArg (fun row ↦ row.2.2) pair
  subst facts
  subst reason
  exact ⟨goodReasonFee, by simp [absenceSettled], goodReasonAssessment, rfl, rfl, rfl, rfl,
    by change goodReasonAmounts ∈ [goodReasonAmounts]; simp, rfl⟩

theorem goodReasonTutorOccurrence (ev : StartEvidence)
    (canStart : CanStart lesson ev schedule schedule.start)
    (noTeaching : ev.teachingBegan = none)
    (retained : ev.retainsOneToOneAbsence form schedule schedule.start tutorDecisionAt
      goodReasonFacts) :
    TutorSettlementOccurrence form ev schedule schedule.start tutorDecisionAt goodReasonBasis
      absentTutorRecord := by
  exact ⟨canStart.1, by decide, Or.inr ⟨noTeaching, rfl, rfl, goodReasonFacts,
    goodReasonEvidence, rfl, retained, canStart, by intro needed; contradiction,
    Or.inl goodReasonUsesChangeTerms⟩⟩

private def absentTutorCompletion : Settlement.TutorCompletion :=
  ⟨form, absentTutorRecord, schedule.start, m 346150,
    ⟨form.tutorAgreementRef, lesson.normalTutorFee, form.deadlines.tutorPay⟩,
    fun _ _ amount ↦ amount = 25⟩

private def laterTutorCompletion : Settlement.TutorCompletion :=
  { absentTutorCompletion with
    row := { absentTutorRecord with lesson := { lesson with id := 18 } }
    verifiedAt := m 346300 }

theorem tutorCompletionCutUsesVerificationTime :
    Settlement.History.tutorCompletionRowsAt
      { tutorCompletions := [absentTutorCompletion, laterTutorCompletion] }
      tutorDecisionAt = [absentTutorRecord] := by
  rfl

#print axioms signedGoodReasonFeeAtRoot
#print axioms goodReasonAssessmentWaitsForVerification
#print axioms goodReasonTutorUsesAdoptedFee
#print axioms goodReasonTutorOccurrence
#print axioms tutorCompletionCutUsesVerificationTime

#print axioms advanceCancellationRecorded
#print axioms exactCancellationSettled
#print axioms refundFromAdoptedFee
#print axioms refundRequiresExactAdoptedFee
#print axioms refundCannotUseAbsenceBasis
#print axioms refundRestoredToDebitedAccount
#print axioms originalAccountRestored
#print axioms lateCancellationRejected
#print axioms ordinaryChargeStillBlocked
#print axioms unrecordedCancellationCannotSettle
#print axioms wrongAccountCannotDischargeRefund

private def accountBeforeReview : FiledLessonAccount where
  lesson := lesson.id
  place := place.id
  account := place.account
  filedBy := lesson.coordinator
  filedAt := m 173001
  settlementEvidence := some fee.reference
  feePayable := some 20
  debited := 100
  refunds := [(part.ref.obligation, some 80)]
  creditDueBack := some 80
  restored := 80
  tutorPay := some 0
  materialShare := 0
  materialsPending := false

private def originalRefundDecision (originalPart : PaymentPart) : Review.OriginalRecord :=
  ⟨⟨⟨201, lesson.id, [place.customer]⟩, 301, lesson.coordinator, refund.amount.recordedAt⟩,
    some originalPart⟩

private def revisedRefund (originalPart : PaymentPart) (corrected : Amount := 90) :
    PaymentCorrectionCase :=
  let old := originalRefundDecision originalPart
  let finding : ReviewFinding := ⟨old.outcome.matter, 5, m 173004, "Reviewed fee restoration", 302, true⟩
  ⟨originalPart, finding, ⟨lesson.id, old.outcome.outcome, finding.outcome, lesson.coordinator,
    m 173006, [place.customer]⟩, ⟨{ originalPart with amount := corrected }, finding.decidedAt, [paid]⟩⟩

private def addReview (s : State) (originalPart : PaymentPart) (corrected : Amount := 90) : State :=
  let original := originalRefundDecision originalPart
  let revision := revisedRefund originalPart corrected
  { s with review :=
    { s.review with originals := s.review.originals ++ [original]
                    reviewFindings := s.review.reviewFindings ++ [revision.finding]
                    corrections := s.review.corrections ++ [.monetary original revision] } }

private def appendAccount (s : State) (account : FiledLessonAccount) : State :=
  { s with settlement := { s.settlement with filed := s.settlement.filed ++ [account] } }

private theorem fileAtRoot {s : State} {account : FiledLessonAccount}
    (filed : account.matches form (s.course lesson.id).ledger)
    (retained : form ∈ (s.course lesson.id).effectiveForms)
    (source : LessonAccounts.uses s.settlement s.redress s.review s.materials (s.course lesson.id)
      (.fileAccount form account) s.verifiedMaterialsGross) :
    Step s (.settlement (.fileAccount form account)) (appendAccount s account) :=
  Step.settlement trivial trivial trivial trivial source trivial (.fileAccount filed (.inl retained))

private theorem restoredFileChecks (account : FiledLessonAccount)
    (identity : account.lesson = lesson.id ∧ account.place = place.id ∧ account.account = place.account ∧
      account.filedBy = lesson.coordinator ∧ form.confirmedAt.by account.filedAt)
    (debitRestored : account.debited = SourceV14.Settlement.debitTotal place [debit, receipt] account.filedAt ∧
      account.restored = SourceV14.Settlement.creditsRestoredFor place [debit, receipt] account.filedAt) :
    account.matches form (restored.course lesson.id).ledger := by
  obtain ⟨hLesson, hPlace, hAccount, hCoordinator, hTime⟩ := identity
  exact ⟨formMatches, hTime, hCoordinator, hLesson, hPlace, hAccount, debitRestored⟩

private theorem noMaterialsPendingForCancellationForm (point : Moment) (review : Review.History)
    (gross : MaterialsGrossEvidence) :
    (false = true ↔ LessonAccounts.materialsUnresolved form {} point ∨
      LessonAccounts.reviewedMaterialsPending form {} review point gross) := by
  have noneRecognised : ({} : Materials.History).recognisedChargesAt form.lesson.id point
      ⟨review.paymentCorrections, gross⟩ = [] := rfl
  simp [LessonAccounts.materialsUnresolved, LessonAccounts.reviewedMaterialsPending, noneRecognised,
    show form.materialsTermsRef = none from rfl]

theorem fileRestorationWithoutRewritingTheOriginalSettlement :
    Step restored (.settlement (.fileAccount form accountBeforeReview))
      (appendAccount restored accountBeforeReview) := by
  apply fileAtRoot
  · exact restoredFileChecks accountBeforeReview ⟨rfl, rfl, rfl, rfl, by decide⟩
      ⟨by decide +kernel, by decide +kernel⟩
  · exact List.mem_cons_self
  · refine ⟨some fee, rfl, ?_, by simp, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · intro entry member
      have equal : fee = entry := by simpa using member
      subst entry
      exact ⟨List.mem_cons_self, rfl, by decide, trivial⟩
    · decide +kernel
    · intro amount
      constructor
      · intro same
        have equal : amount = 20 :=
          (Option.some.inj (show some (20 : Amount) = some amount from same)).symm
        subst amount
        constructor
        · decide +kernel
        · refine ⟨?_, ?_⟩
          · intro other member _
            change other ∈ [fee] at member
            have equal : other = fee := List.mem_singleton.mp member
            subst other
            decide +kernel
          · intro row _
            change row.feeEvidenceAt _ _ Review.History.empty _
            trivial
      · intro ⟨expected, _⟩
        refine Eq.trans ?_ expected
        decide +kernel
    · decide +kernel
    · exact noMaterialsPendingForCancellationForm _ _ _

private def accountAfterReview : FiledLessonAccount :=
  { accountBeforeReview with
    filedAt := m 173007
    feePayable := none
    refunds := [(part.ref.obligation, some 90)]
    creditDueBack := some 90 }

/-- The account filing reads the previously retained review correction. -/
theorem fileReviewedRefundAndRetainEarlierAccount :
    let before := addReview (appendAccount restored accountBeforeReview) part
    Step before (.settlement (.fileAccount form accountAfterReview))
      (appendAccount before accountAfterReview) ∧
    (appendAccount before accountAfterReview).settlement.filed =
      [accountBeforeReview, accountAfterReview] := by
  refine ⟨?_, rfl⟩
  apply fileAtRoot
  · exact restoredFileChecks accountAfterReview ⟨rfl, rfl, rfl, rfl, by decide⟩
      ⟨by decide +kernel, by decide +kernel⟩
  · exact List.mem_cons_self
  · refine ⟨some fee, rfl, ?_, by simp, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · intro entry member
      have equal : fee = entry := by simpa using member
      subst entry
      exact ⟨List.mem_cons_self, rfl, by decide, trivial⟩
    · decide +kernel
    · intro amount
      constructor
      · intro impossible
        nomatch (show (none : Option Amount) = some amount from impossible)
      · intro ⟨expected, _⟩
        refine Eq.trans ?_ expected
        decide +kernel
    · decide +kernel
    · exact noMaterialsPendingForCancellationForm _ _ _

private theorem refundSnapshotAtRoot {s next : State} {account : FiledLessonAccount}
    (step : Step s (.settlement (.fileAccount form account)) next) :
    LessonAccounts.uses s.settlement s.redress s.review s.materials (s.course lesson.id)
      (.fileAccount form account) s.verifiedMaterialsGross := by
  cases step with
  | settlement _ _ _ _ uses _ _ => exact uses

theorem unrelatedRefundCannotChangeThisPlacesAccount (next : State) :
    let otherPlace : PaymentPart := { part with ref := { part.ref with purpose := .lessonRefund 99 } }
    let otherObligation : PaymentPart := { part with ref := { part.ref with obligation := 99 } }
    let before := addReview (addReview restored otherPlace) otherObligation
    ¬ Step before (.settlement (.fileAccount form accountAfterReview)) next := by
  dsimp only
  intro step
  obtain ⟨_, _, _, _, amounts, _⟩ := refundSnapshotAtRoot step
  apply (by decide +kernel : accountAfterReview.refunds ≠ [(part.ref.obligation, some 80)])
  exact amounts.trans (by decide +kernel)

theorem reviewDoesNotChangeAlreadyReceivedCredit (next : State) :
    let before := addReview restored part
    ¬ Step before (.settlement (.fileAccount form { accountAfterReview with restored := 90 })) next := by
  dsimp only
  intro step
  cases step with
  | settlement _ _ _ _ _ _ recorded =>
    cases recorded with
    | fileAccount filed _ =>
      have actual := filed.2.2.2.2.2.2.2
      change (90 : Amount) =
        SourceV14.Settlement.creditsRestoredFor place [debit, receipt] accountAfterReview.filedAt at actual
      exact (by decide +kernel : ¬(90 : Amount) =
        SourceV14.Settlement.creditsRestoredFor place [debit, receipt] accountAfterReview.filedAt) actual

private def reviewedFeePart : PaymentPart :=
  ⟨{ part.ref with purpose := .customerFee place.id }, .person lesson.provider none, 20⟩

private def oldFeeOutcome : Review.OriginalRecord :=
  let old := originalRefundDecision reviewedFeePart
  { old with outcome := { old.outcome with
      matter := fee.decision.assignment.matter
      outcome := fee.reference
      decidedAt := fee.decision.decidedAt } }

private def feeRevision : PaymentCorrectionCase :=
  let revision := revisedRefund reviewedFeePart 15
  { revision with
    finding := { revision.finding with matter := oldFeeOutcome.outcome.matter }
    correction := { revision.correction with originalOutcome := fee.reference }
    money := { revision.money with actualReceipts := [] } }

private def retainedFeeRevision : State :=
  { assessed with review := { Review.History.empty with
      originals := [oldFeeOutcome]
      reviewFindings := [feeRevision.finding]
      corrections := [.monetary oldFeeOutcome feeRevision] } }

private def filedFeeRevision : FiledLessonAccount :=
  { accountAfterReview with feePayable := some 15, refunds := [], creditDueBack := none, restored := 0 }

theorem explicitReviewedFeeChangesDueWithoutInventingARefund :
    Step retainedFeeRevision (.settlement (.fileAccount form filedFeeRevision))
      (appendAccount retainedFeeRevision filedFeeRevision) := by
  apply fileAtRoot
  · exact ⟨formMatches, by decide, rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel⟩
  · exact List.mem_cons_self
  · refine ⟨some fee, rfl, ?_, by simp, rfl, ?_, by decide +kernel, rfl, rfl, ?_⟩
    · intro entry member
      have equal : fee = entry := by simpa using member
      subst entry
      exact ⟨List.mem_cons_self, rfl, by decide, trivial⟩
    · intro amount
      constructor
      · intro same
        have equal : amount = 15 :=
          (Option.some.inj (show some (15 : Amount) = some amount from same)).symm
        subst amount
        constructor
        · decide +kernel
        · refine ⟨?_, ?_⟩
          · intro other member _
            change other ∈ [fee] at member
            have equal : other = fee := List.mem_singleton.mp member
            subst other
            decide +kernel
          · intro row member
            change row ∈ ([] : List Redress.AssessedRefund) at member
            cases member
      · intro ⟨expected, _⟩
        refine Eq.trans ?_ expected
        decide +kernel
    · exact noMaterialsPendingForCancellationForm _ _ _

theorem equalOriginalFeesOnDifferentObligationsDoNotIdentifyTheReviewedFee (next : State) :
    let otherPart := { reviewedFeePart with ref := { reviewedFeePart.ref with obligation := 70 } }
    let otherOriginal := { oldFeeOutcome with payment := some otherPart }
    let review := { retainedFeeRevision.review with originals := [oldFeeOutcome, otherOriginal] }
    let before := { retainedFeeRevision with review }
    ¬ Step before (.settlement (.fileAccount form filedFeeRevision)) next := by
  dsimp only
  intro step
  obtain ⟨original, reference, available, _, _, publishedFee, _⟩ := refundSnapshotAtRoot step
  have projected := (publishedFee 15).mp rfl
  cases original with
  | none => nomatch (show some fee.reference = (none : Option EvidenceRef) from reference)
  | some entry =>
    have retained : entry ∈ [fee] := (available entry (by simp)).1
    have equal : entry = fee := List.mem_singleton.mp retained
    subst entry
    have impossible := projected.1
    cbv at impossible
    cases impossible

private def revisedPartOfSplitRefund : PaymentPart := { part with amount := 40 }

private def splitRefund : Redress.RefundAssessment :=
  { refund.amount with parts := [revisedPartOfSplitRefund,
      { part with ref := { part.ref with portion := 2 }, amount := 40 }] }

theorem sameObligationCorrectionOnlyRevisesItsOwnPortion :
    let review := (addReview restored revisedPartOfSplitRefund 30).review
    LessonAccounts.refundPrincipalAt review splitRefund (m 173005) = some 80 ∧
    LessonAccounts.refundPrincipalAt review splitRefund (m 173006) = some 70 := by decide +kernel

theorem unresolvedParallelCorrectionsDoNotSelectAnAmount :
    let before := addReview restored part
    let other := revisedRefund part 85
    let later := { other with
      finding := { other.finding with outcome := 303 }
      correction := { other.correction with correction := 303 } }
    let review := { before.review with corrections :=
      before.review.corrections ++ [.monetary (originalRefundDecision part) later] }
    LessonAccounts.refundPrincipalAt review refund.amount (m 173007) = none := by cbv

theorem currentRefundFollowsTheLinkedReviewedOutcome :
    let before := addReview restored part
    let corrected := revisedRefund part
    let current := corrected.money.corrected
    let original := { originalRefundDecision current with outcome :=
      { (originalRefundDecision current).outcome with
        outcome := corrected.finding.outcome, decidedAt := corrected.correction.recordedAt } }
    let later := revisedRefund current 85
    let linked := { later with
      finding := { later.finding with outcome := 303, decidedAt := m 173009 }
      correction := { later.correction with
        originalOutcome := original.outcome.outcome, correction := 303, recordedAt := m 173010 }
      money := { later.money with reviewedAt := m 173009 } }
    let review := { before.review with corrections :=
      before.review.corrections ++ [.monetary original linked] }
    LessonAccounts.refundPrincipalAt review refund.amount (m 173008) = some 90 ∧
    LessonAccounts.refundPrincipalAt review refund.amount (m 173010) = some 85 := by cbv

theorem refundCorrectionCanReplaceThePortionReference :
    let revision := revisedRefund part
    let reassigned := { revision.money.corrected with
      ref := { revision.money.corrected.ref with portion := 2 } }
    let tracked := { revision with money := { revision.money with corrected := reassigned } }
    let review := { (addReview restored part).review with
      corrections := [.monetary (originalRefundDecision part) tracked] }
    LessonAccounts.refundPrincipalAt review refund.amount (m 173005) = some 80 ∧
    LessonAccounts.refundPrincipalAt review refund.amount (m 173006) = some 90 := by decide +kernel

theorem wrongRecipientCorrectionLeavesTheRefundAmountPending :
    let revision := revisedRefund part
    let misplaced := { revision.money.corrected with recipient := .lessonRefund 99 }
    let tracked := { revision with money := { revision.money with corrected := misplaced } }
    let review := { (addReview restored part).review with
      corrections := [.monetary (originalRefundDecision part) tracked] }
    LessonAccounts.refundPrincipalAt review refund.amount (m 173005) = some 80 ∧
    LessonAccounts.refundPrincipalAt review refund.amount (m 173006) = none := by decide +kernel

theorem unlinkedPortionOfSameObligationLeavesTheAmountPending :
    let unrelatedPart := { part with ref := { part.ref with portion := 99 } }
    let review := (addReview restored unrelatedPart).review
    LessonAccounts.refundPrincipalAt review refund.amount (m 173005) = some 80 ∧
    LessonAccounts.refundPrincipalAt review refund.amount (m 173006) = none := by decide +kernel

#print axioms fileRestorationWithoutRewritingTheOriginalSettlement
#print axioms fileReviewedRefundAndRetainEarlierAccount
#print axioms unrelatedRefundCannotChangeThisPlacesAccount
#print axioms reviewDoesNotChangeAlreadyReceivedCredit
#print axioms explicitReviewedFeeChangesDueWithoutInventingARefund
#print axioms equalOriginalFeesOnDifferentObligationsDoNotIdentifyTheReviewedFee
#print axioms sameObligationCorrectionOnlyRevisesItsOwnPortion
#print axioms unresolvedParallelCorrectionsDoNotSelectAnAmount
#print axioms currentRefundFollowsTheLinkedReviewedOutcome
#print axioms refundCorrectionCanReplaceThePortionReference
#print axioms wrongRecipientCorrectionLeavesTheRefundAmountPending
#print axioms unlinkedPortionOfSameObligationLeavesTheAmountPending

end FidelityCancellationChecks
