import SourceV14.Workflow

/-! A verified recovery and takeover use the actual receipts and the original dates. -/
namespace SourceV14.FidelityReviewFollowthroughChecks

open Confirmation Course Operations Workflow.Review

private def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩
private def payTerms : PaymentTerms := ⟨.fixed (tick 150), .fixed (tick 180)⟩

private def form : PartOne where
  lesson := ⟨42, .oneToOne, 10, 20, 30, 60⟩
  place := ⟨1, 42, 101, 201, 301, 401, 100, 100⟩
  contacts := ⟨"Spark", "provider", "student", none, "coordinator", 50, "lead",
    none, none, 60, "reviewer", 70, "alternative", true, 80, "escalation"⟩
  rulesVersion := "1.5"
  confirmedAt := tick 10
  customerRepresentatives := []
  schedule := ⟨42, tick 60, tick 70, "UTC", tick 10, tick 10⟩
  serviceTerms := "service"
  serviceItems := [1]
  discountBasis := none
  privateRoster := none
  rosterLock := none
  groupRescheduleCutoff := none
  oneToOneAdvanceCutoff := some (.fixed (tick 30))
  cancelChangeTerms := "cancellation"
  noFaultTerms := "no-fault cancellation"
  applicableStartTerms := "start"
  tutorAgreementRef := "tutor terms"
  absentGroupPlacePay := none
  materialsOrBundle := none
  materialsTermsRef := none
  materialsPayer := none
  deadlines := ⟨.fixed (tick 60), tick 40, none, payTerms, payTerms, payTerms,
    payTerms, .fixed (tick 120), tick 150, tick 130, tick 140, .fixed (tick 200)⟩

private def terms : ReviewTerms := ⟨30, 70, 50, .exact (tick 120), tick 150, tick 130,
  tick 140, 80⟩
private def matter : ReviewMatter := ⟨2, 42, [201]⟩
private def part : PaymentPart := ⟨⟨42, 12, 1, .other⟩, .person 201 none, 100⟩
private def oldPart : PaymentPart := { part with amount := 80 }
private def original : OriginalRecord := ⟨⟨matter, 72, 50, tick 30⟩, some oldPart⟩
private def finding : ReviewFinding := ⟨matter, 60, tick 100, "Revised amount", 73, true⟩
private def wrong : PostedPayment := ⟨1, ⟨part.ref, .person 202, 30, 40, tick 50⟩, some 10⟩
private def correct : PostedPayment := ⟨2, ⟨part.ref, .person 201, 30, 100, tick 170⟩, some 11⟩
private def correction : PaymentCorrectionCase :=
  ⟨oldPart, finding, ⟨42, 72, 73, 30, tick 110, [201]⟩, ⟨part, tick 100, [wrong]⟩⟩
private def returned : ReturnedPayment := ⟨3, wrong.id, 10, tick 195, 90⟩
private def recovery : RecoveryRecord := ⟨73, ⟨matter, wrong.id, 10, 10, tick 120⟩, returned⟩

private def authority : ReviewAuthorities where
  corePartner := fun _ _ ↦ False
  initialFinding := fun _ _ _ ↦ False
  reviewer := fun caseMatter actor _ ↦ caseMatter = matter ∧ (actor = 60 ∨ actor = 61)
  approvesPayment := fun _ _ _ ↦ False
  interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
  originalDecisionMaker := fun _ ↦ some 50
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

private def facts : HoldFacts where
  terms := fun _ ↦ terms
  termsApply := (· = matter)
  acceptedPaymentConcern := fun _ _ _ _ ↦ False
  reviewerCannotActInTime := fun _ _ ↦ False
  temporaryAuthority := fun _ _ _ _ ↦ False
  allegedFactsWouldChangePayment := fun _ _ _ ↦ False
  separatelyIdentifiable := fun _ _ ↦ False
  establishedParts := fun lesson purpose ↦
    if lesson = part.ref.lesson ∧ purpose = part.ref.purpose then [part] else []
  paymentAffected := fun caseMatter ref ↦ caseMatter = matter ∧ ref = part.ref
  decisionPending := fun _ _ _ ↦ False
  partFallsUnderDecision := fun _ _ _ ↦ False
  decisionConcernsWholeGroup := fun _ _ ↦ False
  isGroupLesson := fun _ ↦ False
  affectsWholeSettlement := fun _ ↦ False
  groupSettlementParts := fun _ ↦ []

private def evidence (paymentLaw : Option Moment := none) : Evidence where
  authority := authority
  holds := facts
  concernFacts :=
    { effectivePlace := fun _ _ ↦ False
      tutorAffected := fun _ _ ↦ False
      relevantShareClaimantAffected := fun _ _ ↦ False
      believesUseOmitted := fun _ _ ↦ False
      relevantContributor := fun _ _ ↦ False
      coordinatorUnreachable := fun _ _ ↦ False
      coordinatorPersonallyInterested := fun _ _ ↦ False
      complaintAboutCoordinator := fun _ ↦ False }
  publishedTerms := fun _ _ _ ↦ False
  replyTrigger := fun _ _ ↦ none
  verifiedReplyTrigger := fun _ _ ↦ False
  replyLegalDeadline := fun _ ↦ none
  verifiedFactCheck := fun _ ↦ False
  originalOutcome := (· = original.outcome)
  recordedAmount := fun _ _ _ ↦ False
  recoveryUnderOriginalTerms := fun payment decision ↦ payment = oldPart ∧
    decision.payment = wrong.id ∧ decision.amount = 10
  mayApproveRecovery := fun caseMatter actor point ↦
    caseMatter = matter ∧ actor = 10 ∧ point = tick 120
  governingReviewForm := fun caseMatter confirmed ↦ caseMatter = matter ∧ confirmed = form
  establishedPaymentTerms := fun caseMatter ref confirmed agreed ↦
    caseMatter = matter ∧ ref = part.ref ∧ confirmed = form ∧ agreed = payTerms
  paymentLegalDeadline := fun _ ↦ paymentLaw

private def history : History :=
  { History.empty with originals := [original], corrections := [.monetary original correction] }

private def holds : HoldHistory where
  payments := ⟨[wrong], [], []⟩
  temporary := []
  formal := []
  lifts := []

private def held : FormalHold := ⟨6, matter, .payment, [part], 60, tick 130, tick 140,
  "Verify this unpaid portion", tick 145⟩
private def withHold : HoldHistory := { holds with formal := [held] }
private def withReturn : HoldHistory := { holds with
  payments := { holds.payments with returned := [returned] } }
private def fullyPaid : HoldHistory := { holds with
  payments := { holds.payments with posted := [wrong, correct] } }

private def notice (kind : EscalationMatter) (point : Moment) : EscalationNotice :=
  ⟨kind, 80, point, 61, "Waiting on the verified outcome", tick 210, [201]⟩

private def assignment (record : EscalationNotice) : EscalationAssignment :=
  ⟨record.caseRef, record.takenOverBy, record.responsiblePerson, record.takenOverAt⟩

private def paymentNotice (law : Option Moment) (point : Moment) : PaymentEscalation :=
  let record := notice (.payment part.ref) point
  ⟨form, matter, part, payTerms, none, none, ⟨tick 150, tick 180, law, .date (tick 200)⟩,
    record, assignment record, none⟩

private def atRoot (base : Workflow.State) (saved : HoldHistory) (review : History) :
    Workflow.State :=
  let course := base.course form.lesson.id
  let state := base.withCourse form.lesson.id { course with effectiveForms := [form] }
  { state.withHolds saved with review }

@[simp] private theorem rootHolds (base : Workflow.State) (saved : HoldHistory)
    (review : History) : (atRoot base saved review).holds = saved := rfl

@[simp] private theorem rootReview (base : Workflow.State) (saved : HoldHistory)
    (review : History) : (atRoot base saved review).review = review := rfl

private theorem assignmentMatches (kind : EscalationMatter) (point : Moment)
    (inTime : point.by (tick 210)) : (assignment (notice kind point)).matches (notice kind point) :=
  ⟨rfl, rfl, rfl, Or.inr rfl, inTime⟩

private theorem formMatches : form.matches := by
  simp [PartOne.matches, form, payTerms, Place.matches, Place.validFees, Booking.Schedule.valid,
    Contacts.complete, PayAndReviewTerms.valid, PaymentTerms.valid, PaymentDeadline.valid,
    AdvanceWindow.validAt, tick, Moment.by, Moment.before]
  all_goals decide +kernel

private theorem termsMatch : Operations.ReviewTerms.matchesForm terms form := by
  simp [Operations.ReviewTerms.matchesForm, terms, form]

private theorem effectiveForm (base : Workflow.State) (saved : HoldHistory) (review : History) :
    form ∈ ((atRoot base saved review).course form.lesson.id).effectiveForms := by
  simp [atRoot, Workflow.State.course, Workflow.State.withCourse, Workflow.State.withHolds,
    Workflow.LessonFile.evidence, Workflow.LessonFile.fromEvidence]

theorem actualReturnCanBeRecordedBeforeAuthorityCheck (base : Workflow.State) :
    let state := atRoot base holds history
    let before := { state with credit := { state.credit with creditRecords :=
      { state.credit.creditRecords with verifiedRefunds := [] } } }
    Workflow.Step before (.payment (.returnPayment returned))
      { before.withHolds withReturn with paymentRecords := before.paymentRecords ++
          [.returnPayment returned] } := by
  dsimp only
  apply Workflow.Step.payment
  · simp [Workflow.Payment.Event.independentCreditChange]
  · have recorded : Workflow.Payment.Step holds (.returnPayment returned) withReturn := by
      apply Workflow.Payment.Step.returnPayment (paid := wrong)
      all_goals decide +kernel
    exact recorded

private theorem recoveryUsesCurrentReceipts (receipts : List PostedPayment) :
    recoveryConforms withReturn.payments
      { correction with money := { correction.money with actualReceipts := receipts } }
      (evidence none).recoveryUnderOriginalTerms (evidence none).mayApproveRecovery recovery := by
  refine ⟨rfl, rfl, wrong, ?_, rfl, ⟨by simp [withReturn, holds], rfl⟩,
    by decide +kernel, (show finding.decidedAt.by (tick 120) by decide), by decide +kernel,
    ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl, by simp [withReturn, recovery], ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl, (show (tick 50).by (tick 100) by decide)⟩
  · simp [PaymentHistory.distinctReceipts, withReturn, holds]
  · simp [PaymentHistory.validReturns, withReturn, holds]
    all_goals decide +kernel

theorem authorisedRecoveryFiledAtRoot (base : Workflow.State) :
    let state := atRoot base withReturn history
    Workflow.Step state (.review (evidence none) (.fileRecovery form.lesson correction recovery))
      { state with review := { history with recoveries := [(correction, recovery)] } } := by
  dsimp only
  apply Workflow.Step.review
  · trivial
  · trivial
  · intro row impossible
    cases impossible
  apply Step.fileRecovery
  · simp [History.paymentCorrections, history]
  · rfl
  · exact recoveryUsesCurrentReceipts correction.money.actualReceipts
  · simp [history, History.empty]

/-- The earlier actual receipt can be discovered after the correction was filed.
Its recovery still requires the original terms and an actual authorised return. -/
theorem earlierReceiptDiscoveredAfterReviewCanBeRecovered (base : Workflow.State) :
    let archived := { correction with money := { correction.money with actualReceipts := [] } }
    let reviewed := { history with corrections := [.monetary original archived] }
    let state := atRoot base withReturn reviewed
    Workflow.Step state (.review (evidence none) (.fileRecovery form.lesson archived recovery))
      { state with review := { reviewed with recoveries := [(archived, recovery)] } } := by
  dsimp only
  apply Workflow.Step.review
  · trivial
  · trivial
  · intro row impossible
    cases impossible
  apply Step.fileRecovery
  · simp [History.paymentCorrections]
  · rfl
  · exact recoveryUsesCurrentReceipts []
  · simp [history, History.empty]

theorem returnByItselfDoesNotFileARecovery (start : StartEvidence) :
    let denied := { evidence none with mayApproveRecovery := fun _ _ _ ↦ False }
    ¬ ∃ next, Step denied start withReturn history (.fileRecovery form.lesson correction recovery)
      next := by
  dsimp only
  rintro ⟨_, step⟩
  cases step with
  | fileRecovery =>
    have recovered : recoveryConforms withReturn.payments correction
        (evidence none).recoveryUnderOriginalTerms (fun _ _ _ ↦ False) recovery := by assumption
    obtain ⟨_, _, _, _, _, _, _, _, _, _, allowed, _⟩ := recovered
    exact allowed

theorem misdirectedRecoveryDoesNotOffsetTheCorrectPayee :
    withReturn.payments.remainingObligationBefore part.ref.lesson part.ref.obligation
      part.recipient part.amount (tick 196) (some part.ref.purpose) = 100 ∧
    holds.payments.remainingObligationBefore part.ref.lesson part.ref.obligation
      part.recipient part.amount (tick 196) (some part.ref.purpose) = 100 := by
  decide +kernel

private theorem canonical : facts.isCanonicalPart part := by
  simp [HoldFacts.isCanonicalPart, facts, part]
  all_goals decide +kernel

private theorem validHold :
    withHold.validFormalHold (history.authorities authority) facts held := by
  simp [HoldHistory.validFormalHold, FormalHold.mayImpose, ReviewAuthorities.mayImposeOrLift,
    ReviewAuthorities.disinterested, DirectInterest.affected, facts, authority, history,
    History.authorities, withHold, holds, held, HoldFacts.isCanonicalPart,
    HoldHistory.originallyApprovedBy,
    HoldHistory.notTemporarySetter, HoldHistory.originalSettlementActor]
  all_goals decide +kernel

private def cutoff (_ : Moment) := ClockCutoff.exact (tick 200)

private theorem escalationWithDeadline (base : Workflow.State) (law : Option Moment)
    (saved : HoldHistory) (point : Moment)
    (kept : form.confirmedAt.by point)
    (overdue : paymentEscalationConforms (history.authorities authority) facts
      (saved.withPartRevisionsKnownAt point) matter part (paymentNotice law point).schedule
      (fun releasedAt ↦ (PostLiftCutoffMatches form.deadlines.postLiftPay
        (saved.withPartRevisionsKnownAt point) releasedAt (cutoff releasedAt), cutoff releasedAt)) (paymentNotice law point).notice
        (paymentNotice law point).assignment) :
    let state := atRoot base saved history
    let row := paymentNotice law point
    Workflow.Step state (.review (evidence law) (.escalatePayment row))
      { state with review := { history with paymentEscalations := [row] } } := by
  dsimp only
  apply Workflow.Step.review
  · trivial
  · simp [Workflow.Review.Event.readsMaterialsTerms, paymentNotice]
  · intro row impossible
    cases impossible
  apply Step.escalatePayment
  · refine ⟨⟨rfl, formMatches, kept, Or.inl (effectiveForm base saved history)⟩, rfl, trivial,
      trivial, formMatches, rfl, termsMatch, ⟨rfl, rfl, rfl, rfl⟩, rfl, ?_, rfl, overdue⟩
    simp [paymentNotice, part, payTerms, PaymentDeadline.appliesForLesson, PaymentDeadline.applies]
  · simp [history, History.empty]

theorem overduePaymentFiledAtRoot (base : Workflow.State) :
    let state := atRoot base holds history
    let row := paymentNotice none (tick 190)
    Workflow.Step state (.review (evidence none) (.escalatePayment row))
      { state with review := { history with paymentEscalations := [row] } } := by
  apply escalationWithDeadline base none holds (tick 190) (by decide +kernel)
  refine ⟨rfl, rfl, canonical, assignmentMatches _ _ (by decide +kernel), by decide +kernel,
    .exact (tick 180), Or.inr (Or.inl ⟨rfl, ?_, ?_⟩),
    by unfold ClockCutoff.hasPassed; decide +kernel, ?_,
    by unfold ClockCutoff.forEveryOrder; decide +kernel⟩
  · simp [HoldHistory.formalInForce, HoldHistory.validFormalHold, HoldHistory.withPartRevisionsKnownAt,
      holds]
  · simp [HoldHistory.withPartRevisionsKnownAt, holds]
  · simp [escalationDetailsConform, facts, terms, matter, paymentNotice, notice]
    decide +kernel

theorem earlierLawStillTriggersTakeoverUnderHold (base : Workflow.State) :
    let state := atRoot base withHold history
    let law := some (tick 160)
    let row := paymentNotice law (tick 165)
    Workflow.Step state (.review (evidence law) (.escalatePayment row))
      { state with review := { history with paymentEscalations := [row] } } := by
  apply escalationWithDeadline base (some (tick 160)) withHold (tick 165) (by decide +kernel)
  refine ⟨rfl, rfl, canonical, assignmentMatches _ _ (by decide +kernel), by decide +kernel,
    .exact (tick 160), Or.inl ⟨tick 160, by simp [paymentNotice], rfl⟩,
    by unfold ClockCutoff.hasPassed; decide +kernel, ?_,
    by unfold ClockCutoff.forEveryOrder; decide +kernel⟩
  simp [escalationDetailsConform, facts, terms, matter, paymentNotice, notice]
  decide +kernel

/-- A release before the execution deadline cannot supply a second window when
a formal hold covers the unpaid portion at that deadline. -/
theorem takeoverWaitsForFirstApplicableRelease (authority : ReviewAuthorities) (facts : HoldFacts)
    (holds : HoldHistory) (matter : ReviewMatter) (part : PaymentPart) (schedule : PaymentSchedule)
    (cutoff : Moment → Prop × ClockCutoff) (notice : EscalationNotice)
    (assignment : EscalationAssignment)
    (ordinaryLaw : schedule.legalDeadline = none)
    (held : ∃ hold, holds.formalInForce authority facts hold part.ref
      schedule.originalExecutionDeadline notice.takenOverAt)
    (noElapsedWindow : ∀ release,
      postLiftWindowOpened authority facts holds part schedule release notice.takenOverAt →
      ¬ (cutoff release).2.hasPassed notice.takenOverAt) :
    ¬ paymentEscalationConforms authority facts holds matter part schedule cutoff notice assignment := by
  rintro ⟨_, _, _, _, _, deadline, source, elapsed, _, _⟩
  rcases source with ⟨law, applies, _⟩ | ⟨_, noHold, _⟩ | ⟨release, _, _, same, prompt | opened⟩
  · simp [ordinaryLaw] at applies
  · exact noHold held
  · exact prompt.1 held
  · exact noElapsedWindow release opened (same ▸ elapsed)

#print axioms takeoverWaitsForFirstApplicableRelease

private theorem paysByNotice (paid : HoldHistory)
    (row : PaymentEscalation) (start : StartEvidence)
    (checked : row.conforms history (evidence row.schedule.legalDeadline) start paid) :
    0 < (paid.withPartRevisionsKnownAt row.notice.takenOverAt).remainingPortionBefore row.part
      row.notice.takenOverAt := by
  obtain ⟨_, _, _, _, _, _, _, rule⟩ := checked.2.2.2.2
  exact rule.2.2.2.2.1

theorem alreadyPaidDoesNotQualifyForTakeover (start : StartEvidence) :
    ¬ ∃ next, Step (evidence none) start fullyPaid history
      (.escalatePayment (paymentNotice none (tick 190))) next := by
  rintro ⟨_, step⟩
  cases step with
  | escalatePayment _ checked _ =>
    exact (by decide +kernel : ¬ 0 < fullyPaid.remainingPortionBefore part (tick 190))
      (paysByNotice fullyPaid (paymentNotice none (tick 190)) start checked)

theorem uncheckedRelativeTriggerCannotSupplyDeadline (start : StartEvidence)
    (event : PaymentTrigger) :
    let row := { paymentNotice none (tick 190) with
      terms := { payTerms with latestExecution := .after 80 "verified event" }
      executionTrigger := some event }
    ¬ ∃ next, Step (evidence none) start holds history (.escalatePayment row) next := by
  dsimp only
  rintro ⟨_, step⟩
  cases step with
  | escalatePayment _ checked _ =>
    exact (checked.2.2.2.1 event (by simp)).1

theorem originalDeadlineBranchKeepsExistingHoldInterpretation (start : StartEvidence) :
    ¬ ∃ next, Step (evidence none) start withHold history
      (.escalatePayment (paymentNotice none (tick 190))) next := by
  rintro ⟨_, step⟩
  cases step with
  | escalatePayment _ checked _ =>
    obtain ⟨_, _, _, _, _, _, _, rule⟩ := checked.2.2.2.2
    obtain ⟨_, _, _, _, _, _, basis, _⟩ := rule
    rcases basis with law | ⟨_, excluded⟩ | ⟨releasedAt, _, _, _, released⟩
    · simp [paymentNotice] at law
    · refine excluded.1 ⟨held, validHold, by decide +kernel, part, by simp [held],
        by decide +kernel, ?_⟩
      simp [HoldHistory.withPartRevisionsKnownAt, withHold, holds]
    · have effect := released.elim (fun prompt ↦ prompt.2.2.2.1.1) (fun window ↦ window.2.1)
      obtain ⟨_, lift, release, _⟩ := effect
      simpa [HoldHistory.withPartRevisionsKnownAt, withHold, holds] using release.2.1

theorem overdueHeldReviewFiledAtRoot (base : Workflow.State) :
    let state := atRoot base withHold history
    let record := notice (.review held.id) (tick 155)
    Workflow.Step state (.review (evidence none)
      (.escalateHeldReview form held record (assignment record)))
      { state with review := { history with reviewEscalations :=
          [(matter, record, assignment record)] } } := by
  dsimp only
  apply Workflow.Step.review
  · trivial
  · trivial
  · intro row impossible
    cases impossible
  apply Step.escalateHeldReview
  all_goals try simp only [Workflow.State.reviewEvidence]
  · exact ⟨rfl, formMatches, by decide +kernel, Or.inl (effectiveForm base withHold history)⟩
  · simp [history, History.empty]
  · refine ⟨formMatches, rfl, ⟨rfl, rfl⟩, termsMatch, validHold, by decide +kernel, rfl,
      ⟨⟨by decide +kernel, by simp⟩, ?_⟩, assignmentMatches _ _ (by decide +kernel),
      ?_, ?_, ?_, ?_, ?_⟩
    · simp [escalationDetailsConform, evidence, facts, terms, matter, notice, held]
      decide +kernel
    · simp +contextual [independentReviewer, history, History.authorities, evidence, authority,
        held, matter, original, ReviewMatter.sameCase, ReviewAuthorities.disinterested,
        DirectInterest.affected, assignment, notice]
      all_goals decide +kernel
    · simp [didNotMakeOriginalFinding, history, History.empty]
    · simp [HoldHistory.notTemporarySetter, withHold, holds]
    · simp [withHold, holds]
    · simp [reviewFindingRecordedConforms, history, History.empty]
  · simp [history, History.empty]

private def publication : PublishedContacts :=
  ⟨42, ⟨.materialsTerms, 10, 30, "coordinator", 70, "alternative"⟩, tick 10⟩
private def entry : Intake :=
  ⟨form.lesson, terms, none, publication, ⟨matter, 201, .share, 30, tick 90⟩⟩
private def request : ConcernAppointmentTrigger := ⟨matter, .partyRequestedReview 201, tick 100, 72⟩
private def requestHistory : History :=
  { history with intakes := [entry], appointmentTriggers := [request] }

theorem overdueRequestedReviewWithoutHoldOrForm (base : Workflow.State) :
    let state := atRoot base holds requestHistory
    let record := notice (.reviewRequest matter.id) (tick 155)
    Workflow.Step state (.review (evidence none)
      (.escalateRequestedReview entry request.atTime record (assignment record)))
      { state with review := { requestHistory with reviewEscalations :=
          [(matter, record, assignment record)] } } := by
  dsimp only
  apply Workflow.Step.review
  · trivial
  · trivial
  · intro row impossible
    cases impossible
  apply Step.escalateRequestedReview
  all_goals try simp only [Workflow.State.reviewEvidence]
  · simp [requestHistory]
  · refine ⟨request, by simp [requestHistory], rfl, ?_, 201, rfl⟩
    simp [ConcernAppointmentTrigger.applies, request, entry, matter, ReviewMatter.sameCase, notice]
    all_goals decide +kernel
  · refine ⟨⟨by decide +kernel, by simp⟩, ?_⟩
    simp [escalationDetailsConform, entry, terms, matter, notice]
    decide +kernel
  · simp [requestHistory, history, History.empty]
  · exact assignmentMatches _ _ (by decide +kernel)
  · simp +contextual [independentReviewer, didNotMakeOriginalFinding, HoldHistory.notTemporarySetter,
      requestHistory, history, History.empty, History.authorities, evidence, authority, entry, matter,
      original, ReviewMatter.sameCase, ReviewAuthorities.disinterested, DirectInterest.affected,
      assignment, notice, holds]
    all_goals decide +kernel
  · simp [requestHistory, history, History.empty]

#print axioms actualReturnCanBeRecordedBeforeAuthorityCheck
#print axioms authorisedRecoveryFiledAtRoot
#print axioms earlierReceiptDiscoveredAfterReviewCanBeRecovered
#print axioms returnByItselfDoesNotFileARecovery
#print axioms misdirectedRecoveryDoesNotOffsetTheCorrectPayee
#print axioms overduePaymentFiledAtRoot
#print axioms earlierLawStillTriggersTakeoverUnderHold
#print axioms alreadyPaidDoesNotQualifyForTakeover
#print axioms uncheckedRelativeTriggerCannotSupplyDeadline
#print axioms originalDeadlineBranchKeepsExistingHoldInterpretation
#print axioms overdueHeldReviewFiledAtRoot
#print axioms overdueRequestedReviewWithoutHoldOrForm

private def tutorMatter : ReviewMatter := ⟨9, form.lesson.id, [form.lesson.tutor]⟩

private def tutorPart : PaymentPart :=
  ⟨⟨form.lesson.id, 91, 1, .tutorPay form.lesson.tutor⟩, .person form.lesson.tutor none, 100⟩

private def reviewedTutorPart : PaymentPart :=
  { tutorPart with ref := { tutorPart.ref with portion := 2 }, amount := 60 }

private def tutorOriginal : OriginalRecord :=
  ⟨⟨tutorMatter, 91, 50, tick 140⟩, some tutorPart⟩

private def tutorFinding : ReviewFinding :=
  ⟨tutorMatter, 60, tick 165, "Correct tutor pay to 60", 92, true⟩

private def tutorCorrection : PaymentCorrectionCase :=
  ⟨tutorPart, tutorFinding, ⟨42, 91, 92, 30, tick 170, [form.lesson.tutor]⟩,
    ⟨reviewedTutorPart, tick 165, []⟩⟩

private def tutorHolds : HoldHistory := { holds with payments := ⟨[], [], []⟩ }

private def revisedTutorHolds : HoldHistory :=
  tutorHolds.withPartRevision tutorOriginal.outcome tutorCorrection

private def tutorAppointment : ReviewAppointment :=
  ⟨tutorMatter, form.lesson.provider, 60, tick 150⟩

private def tutorHistory : History := { History.empty with
  originals := [tutorOriginal]
  reviewFindings := [tutorFinding]
  appointments := [tutorAppointment] }

private def revisedTutorHistory : History :=
  { tutorHistory with corrections := [.monetary tutorOriginal tutorCorrection] }

private def tutorFacts : HoldFacts := { facts with
  termsApply := (· = tutorMatter)
  establishedParts := fun lesson purpose ↦
    if lesson = tutorPart.ref.lesson ∧ purpose = tutorPart.ref.purpose then [tutorPart] else [] }

private def tutorEvidence : Evidence := { evidence none with
  holds := tutorFacts
  authority := { authority with
    corePartner := fun actor _ ↦ actor = form.lesson.provider
    reviewer := fun actMatter actor _ ↦ actMatter = tutorMatter ∧ actor = 60 }
  originalOutcome := (· = tutorOriginal.outcome)
  recordedAmount := fun actMatter ref value ↦
    actMatter = tutorMatter ∧ ref = tutorFinding.outcome ∧ value = reviewedTutorPart
  establishedPaymentTerms := fun actMatter ref confirmed agreed ↦
    actMatter = tutorMatter ∧ ref = tutorPart.ref ∧ confirmed = form ∧ agreed = payTerms }

private def tutorNotice (part : PaymentPart) (point : Moment) : PaymentEscalation :=
  let sent : EscalationNotice :=
    ⟨.payment part.ref, 80, point, 61, "Unpaid tutor pay", tick 210, [form.lesson.tutor]⟩
  ⟨form, tutorMatter, part, payTerms, none, none, ⟨tick 150, tick 180, none, .date (tick 200)⟩,
    sent, assignment sent, none⟩

private def tutorRoot (base : Workflow.State) (saved : HoldHistory) (review : History) :
    Workflow.State :=
  let course := base.course form.lesson.id
  let state := base.withCourse form.lesson.id
    { course with
      effectiveForms := [form]
      teachingBegan := some (tick 60)
      tutorReplacements := []
      tutorPayAmendments := {} }
  { state.withHolds saved with review }

private theorem tutorFormRetained (base : Workflow.State) (saved : HoldHistory) (review : History) :
    form ∈ ((tutorRoot base saved review).course form.lesson.id).effectiveForms := by
  simp [tutorRoot, Workflow.State.course, Workflow.State.withCourse, Workflow.State.withHolds,
    Workflow.LessonFile.evidence, Workflow.LessonFile.fromEvidence]

private theorem agreedTutorTerms (base : Workflow.State) :
    EffectiveTutorAgreementAt form
      ((tutorRoot base revisedTutorHolds revisedTutorHistory).course form.lesson.id)
      (tick 60) form.lesson.tutor form.tutorAgreementRef form.lesson.normalTutorFee payTerms
      (tick 190) (tick 190) := by
  refine ⟨formMatches, by decide +kernel, Or.inr rfl, Or.inl (tutorFormRetained _ _ _), none, ?_,
    ⟨rfl, by decide +kernel, rfl⟩⟩
  simp [tutorRoot, Workflow.State.course, Workflow.State.withCourse, Workflow.State.withHolds,
    Workflow.LessonFile.evidence, Workflow.LessonFile.fromEvidence,
    StartEvidence.effectiveReplacement, StartEvidence.latestReplacement]

private theorem retainedTutorCorrection (base : Workflow.State) :
    Workflow.Step (tutorRoot base tutorHolds tutorHistory)
      (.review tutorEvidence (.recordCorrection form.lesson (.monetary tutorOriginal tutorCorrection)))
      (tutorRoot base revisedTutorHolds revisedTutorHistory) := by
  apply Workflow.Step.review
  · trivial
  · trivial
  · intro row impossible
    cases impossible
  apply Step.recordMonetary
  · simp [tutorRoot, tutorHistory]
  · simp [tutorRoot, tutorHistory, tutorCorrection]
  · exact ⟨rfl, rfl, rfl⟩
  · refine ⟨[], ?_, ?_⟩
    · change ([] : List PaymentPart) ∈ some []
      simp
    · unfold PaymentCorrectionCase.recorded PaymentCorrectionCase.outcomeConforms
      refine ⟨⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel⟩, ?_⟩
      · refine ⟨?_, rfl, tutorOriginal.outcome, by simp, ?_⟩
        · change reviewFindingConforms (tutorHistory.authorities tutorEvidence.authority)
            tutorHistory.appointments tutorFinding
          simp [reviewFindingConforms, reviewFindingConformsWithContacts, independentReviewer,
            History.authorities, tutorHistory, tutorEvidence, tutorFinding, tutorAppointment,
            ReviewAppointment.applies, ReviewAuthorities.mayDecideDispute, ReviewMatter.sameCase,
            tutorOriginal, ReviewAuthorities.disinterested, DirectInterest.affected, authority]
          refine ⟨?_, by decide +kernel⟩
          intro _ oldActor _ _ actorEquals _ _ _ _
          rw [actorEquals]
          decide +kernel
        · refine ⟨rfl, rfl, ⟨rfl, rfl⟩, by decide +kernel, by decide +kernel,
            rfl, rfl, by decide +kernel, rfl, by decide +kernel, ?_⟩
          simp [tutorOriginal, tutorCorrection, tutorFinding, tutorMatter]
      · simp [correctionActualPaymentsRecorded, correctionActualPaymentsRetained,
          PaymentHistory.distinctReceipts, PaymentHistory.validReturns, tutorRoot, tutorHolds,
          tutorCorrection, Workflow.State.withHolds]
  · simp [History.paymentCorrections, tutorRoot, tutorHistory, History.empty]

private theorem tutorEscalationConforms (base : Workflow.State) :
    (tutorNotice reviewedTutorPart (tick 190)).conforms revisedTutorHistory
      ((tutorRoot base revisedTutorHolds revisedTutorHistory).reviewEvidence tutorEvidence)
      ((tutorRoot base revisedTutorHolds revisedTutorHistory).course form.lesson.id) revisedTutorHolds := by
  refine ⟨⟨rfl, formMatches, by decide +kernel, Or.inl (tutorFormRetained _ _ _)⟩,
    rfl, trivial, trivial, formMatches, rfl, termsMatch, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [Workflow.State.reviewEvidence, tutorEvidence]
    exact ⟨rfl, by decide +kernel, rfl, rfl⟩
  · refine ⟨tutorOriginal.outcome, ?_, ⟨rfl, by decide +kernel, reviewedTutorPart, ?_, rfl⟩,
      by decide +kernel, ?_, tick 60, form.tutorAgreementRef, form.lesson.normalTutorFee, Or.inl rfl,
      agreedTutorTerms base⟩
    · decide +kernel
    · decide +kernel
    · intro other saved _
      have only (rows : List RecordedSettlementOutcome) (member : other ∈ rows)
          (equal : rows = [tutorOriginal.outcome]) : other = tutorOriginal.outcome := by
        rw [equal] at member
        exact List.mem_singleton.mp member
      rw [only _ saved (by decide +kernel)]
      exact Or.inr rfl
  · simp [tutorNotice, reviewedTutorPart, tutorPart, form, payTerms,
      PaymentDeadline.appliesForLesson, PaymentDeadline.applies]
  · refine ⟨rfl, rfl, ?_, ⟨rfl, rfl, rfl, Or.inr rfl, by decide +kernel⟩, by decide +kernel,
      .exact (tick 180), Or.inr (Or.inl ⟨rfl, ?_, ?_⟩),
      by unfold ClockCutoff.hasPassed; decide +kernel, ?_, ?_⟩
    · change reviewedTutorPart ∈ [reviewedTutorPart] ∧ [reviewedTutorPart.ref].Nodup ∧
        ∀ p ∈ [reviewedTutorPart], p.ref.lesson = reviewedTutorPart.ref.lesson ∧
          p.ref.purpose = reviewedTutorPart.ref.purpose ∧ 0 < p.amount
      simp [reviewedTutorPart, tutorPart]
      decide +kernel
    · simp [HoldHistory.formalInForce, HoldHistory.validFormalHold, revisedTutorHolds,
        HoldHistory.withPartRevision, HoldHistory.withPartRevisionsKnownAt, tutorHolds, holds]
    · simp [HoldHistory.paymentHoldScopeUnresolved, HoldHistory.validFormalHold, revisedTutorHolds,
        HoldHistory.withPartRevision, HoldHistory.withPartRevisionsKnownAt, tutorHolds, holds]
    · change escalationDetailsConform terms tutorMatter (.payment reviewedTutorPart.ref)
        (tutorNotice reviewedTutorPart (tick 190)).notice
      simp [escalationDetailsConform, tutorNotice, terms, tutorMatter]
      decide +kernel
    · unfold ClockCutoff.forEveryOrder
      decide +kernel

theorem correctedTutorPayTakesOverAtRoot (base : Workflow.State) :
    let state := tutorRoot base revisedTutorHolds revisedTutorHistory
    let row := tutorNotice reviewedTutorPart (tick 190)
    Workflow.Step state (.review tutorEvidence (.escalatePayment row))
      { state with review := { revisedTutorHistory with paymentEscalations := [row] } } := by
  dsimp only
  apply Workflow.Step.review
  · trivial
  · simp [Workflow.Review.Event.readsMaterialsTerms, tutorNotice]
  · intro row impossible
    cases impossible
  apply Step.escalatePayment
  · exact tutorEscalationConforms base
  · simp [revisedTutorHistory, tutorHistory, History.empty, tutorRoot]

private theorem rootRejectsTutorNotice (state : Workflow.State) (row : PaymentEscalation)
    (invalid : ¬row.conforms state.review (state.reviewEvidence tutorEvidence)
      (state.course row.form.lesson.id) state.holds) :
    ¬∃ next, Workflow.Step state (.review tutorEvidence (.escalatePayment row)) next := by
  rintro ⟨_, step⟩
  cases step with
  | review _ _ _ rule =>
    cases rule with
    | escalatePayment _ checked _ => exact invalid checked

theorem staleTutorPayCannotTakeOverAtRoot (base : Workflow.State) :
    let state := tutorRoot base revisedTutorHolds revisedTutorHistory
    let row := tutorNotice tutorPart (tick 190)
    ¬∃ next, Workflow.Step state (.review tutorEvidence (.escalatePayment row)) next := by
  dsimp only
  apply rootRejectsTutorNotice
  intro checked
  rw [show (tutorRoot base revisedTutorHolds revisedTutorHistory).review = revisedTutorHistory
    from rfl] at checked
  obtain ⟨_, _, _, _, tutor, _⟩ := checked.2.2.2.2
  obtain ⟨settled, retained, _⟩ := tutor
  have noOriginal (rows : List RecordedSettlementOutcome) (member : settled ∈ rows)
      (empty : rows = []) : False := by
    rw [empty] at member
    cases member
  exact noOriginal _ retained (by decide +kernel)

theorem unadoptedTutorRevisionCannotTakeOverAtRoot (base : Workflow.State) :
    let state := tutorRoot base revisedTutorHolds tutorHistory
    let row := tutorNotice reviewedTutorPart (tick 190)
    ¬∃ next, Workflow.Step state (.review tutorEvidence (.escalatePayment row)) next := by
  dsimp only
  apply rootRejectsTutorNotice
  intro checked
  obtain ⟨_, _, _, anchored, _⟩ := checked.2.2.2.2
  change tutorEvidence.establishedPaymentTerms tutorMatter reviewedTutorPart.ref form payTerms at anchored
  exact (by decide +kernel : reviewedTutorPart.ref ≠ tutorPart.ref) anchored.2.1

theorem revisedTutorPayCannotResetOriginalDeadline (base : Workflow.State) :
    let state := tutorRoot base revisedTutorHolds revisedTutorHistory
    let row := tutorNotice reviewedTutorPart (tick 190)
    let reset := { row with schedule :=
      { row.schedule with originalExecutionDeadline := tick 175 } }
    ¬∃ next, Workflow.Step state (.review tutorEvidence (.escalatePayment reset)) next := by
  dsimp only
  apply rootRejectsTutorNotice
  intro checked
  obtain ⟨_, _, _, _, _, schedule, _⟩ := checked.2.2.2.2
  have execution := schedule.2
  simp [tutorNotice, reviewedTutorPart, tutorPart, payTerms, PaymentDeadline.appliesForLesson,
    PaymentDeadline.applies] at execution
  exact (by decide +kernel : tick 175 ≠ tick 180) execution

#print axioms retainedTutorCorrection
#print axioms correctedTutorPayTakesOverAtRoot
#print axioms staleTutorPayCannotTakeOverAtRoot
#print axioms unadoptedTutorRevisionCannotTakeOverAtRoot
#print axioms revisedTutorPayCannotResetOriginalDeadline

end SourceV14.FidelityReviewFollowthroughChecks
