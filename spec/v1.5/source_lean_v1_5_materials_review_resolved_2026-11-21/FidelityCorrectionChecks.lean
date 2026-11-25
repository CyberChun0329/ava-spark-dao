import SourceV14.Workflow

/-! A correction is filed with the receipts known then. Later receipts affect what is still owed. -/
namespace SourceV14.FidelityCorrectionChecks

open Booking Confirmation Course CreditEvidence Operations Workflow.Review

set_option maxRecDepth 4096

private def day (n : Nat) : Moment := ⟨n * 86400, 0⟩
private def terms : PaymentTerms := ⟨.fixed (day 15), .fixed (day 18)⟩

private def form : PartOne where
  lesson := ⟨42, .oneToOne, 10, 20, 30, 60⟩
  place := ⟨1, 42, 101, 201, 301, 401, 100, 100⟩
  contacts := ⟨"Spark", "provider", "student", none, "coordinator", 50, "lead",
    none, none, 60, "reviewer", 70, "alternative", true, 80, "escalation"⟩
  rulesVersion := "1.5"
  confirmedAt := day 1
  customerRepresentatives := []
  schedule := ⟨42, day 6, day 7, "UTC", day 1, day 1⟩
  serviceTerms := "service"
  serviceItems := [1]
  discountBasis := none
  privateRoster := none
  rosterLock := none
  groupRescheduleCutoff := none
  oneToOneAdvanceCutoff := some (.fixed (day 3))
  cancelChangeTerms := "cancellation"
  noFaultTerms := "no-fault cancellation"
  applicableStartTerms := "start"
  tutorAgreementRef := "tutor terms"
  absentGroupPlacePay := none
  materialsOrBundle := none
  materialsTermsRef := none
  materialsPayer := none
  deadlines := ⟨.fixed (day 6), day 4, none, terms, terms, terms,
    terms, .fixed (day 12), day 15, day 13, day 14, .fixed (day 20)⟩

private def part : PaymentPart := ⟨⟨42, 12, 1, .other⟩, .person 201 none, 10⟩
private def matter : ReviewMatter := ⟨2, 42, [201]⟩
private def oldPart : PaymentPart := { part with amount := 8 }
private def original : OriginalRecord := ⟨⟨matter, 72, 50, day 9⟩, some oldPart⟩
private def finding : ReviewFinding := ⟨matter, 60, day 13, "Revised amount", 73, true⟩

private def receipt (id person date : Nat) (amount : Amount) : PostedPayment :=
  ⟨id, ⟨part.ref, .person person, 30, amount, day date⟩, some id⟩

private def known := receipt 1 201 10 1
private def wrong := receipt 2 202 11 5
private def proper := receipt 3 201 12 2
private def payment (amount : Amount) : CorrectionPaymentRecord :=
  ⟨73, receipt 4 201 17 amount, none⟩

private def correction : PaymentCorrectionCase :=
  ⟨oldPart, finding, ⟨42, 72, 73, 30, day 14, [201]⟩, ⟨part, day 13, [known]⟩⟩

private def approval : PaymentApproval :=
  ⟨21, 10, 30, day 15, none, none, [⟨part.ref, .person 201, 10, none⟩]⟩

private def holds (receipts : List PostedPayment) : HoldHistory where
  payments := ⟨receipts, [], []⟩
  temporary := []
  formal := []
  lifts := []
  approvals := [approval]

private def before := { holds [known] with approvals := [] }
private def current (amount : Amount) := holds [known, wrong, proper, (payment amount).paid]

private def authority : ReviewAuthorities where
  corePartner := fun actor atTime ↦ actor = 10 ∧ atTime = day 12
  initialFinding := fun _ _ _ ↦ False
  reviewer := fun caseMatter actor atTime ↦
    caseMatter = matter ∧ actor = 60 ∧ atTime = finding.decidedAt
  approvesPayment := fun ref actor atTime ↦ ref = part.ref ∧ actor = 10 ∧ atTime = day 15
  interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
  originalDecisionMaker := fun _ ↦ some 50
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

private def evidence (base : Evidence) : Evidence :=
  { base with
    authority
    holds := { base.holds with
      establishedParts := fun lesson purpose ↦
        if lesson = part.ref.lesson ∧ purpose = part.ref.purpose then [part] else []
      paymentAffected := fun _ _ ↦ False
      temporaryAuthority := fun _ _ _ _ ↦ False
      partFallsUnderDecision := fun _ _ _ ↦ False }
    recordedAmount := fun caseMatter outcome amount ↦
      caseMatter = matter ∧ outcome = finding.outcome ∧ amount = part
    reviewedFaultRefund := fun _ ↦ none }

private def reviewBefore : History :=
  { History.empty with
    originals := [original]
    appointments := [⟨matter, 10, 60, day 12⟩]
    reviewFindings := [finding] }

private def reviewAfter : History :=
  { reviewBefore with corrections := [.monetary original correction] }

private def payoutScope : CorrectedMonetaryScope :=
  ⟨⟨part, [oldPart]⟩, [⟨part, [oldPart]⟩], 8, 10⟩

private def start (base : StartEvidence) : StartEvidence :=
  { base with effectiveForms := [form], groupRoster := none }

private def payout (base : Evidence) (decisions : DecisionRecords) : CorrectedPayout :=
  let a := reviewAfter.authorities authority
  let facts := (evidence base).holds
  let schedule : PaymentSchedule := ⟨day 15, day 18, none, .date (day 20)⟩
  { form, original, correction, payment := payment 7, recordedAt := day 18, part
    applicable := terms, settledAbsence := none, reviewedRefund := none
    reviewedGroupAbsence := none, reviewedFee := fun _ _ _ ↦ False
    reviewedUnavailable := fun _ _ ↦ False, earlierGroupRefunds := []
    reviewedTutorAmounts := none
    decisions, funds := ⟨42, 10, day 17, [⟨90, .providerFunds, .spendable, 7, 0, 7⟩]⟩
    approval := .ordinary approval, schedule, agreedConditions := fun _ ↦ True, afterLift := []
    dueTrigger := none, executionTrigger := none
    onTime := FiledPaymentOnTime form a facts (current 7) part schedule (payment 7).paid []
    completedOnTime := FiledPaymentCompletedOnTime form a facts (current 7) part schedule []
      (day 17) }

private theorem formMatches : form.matches := by
  simp [PartOne.matches, form, terms, Place.matches, Place.validFees, Schedule.valid,
    Contacts.complete, PayAndReviewTerms.valid, PaymentTerms.valid, PaymentDeadline.valid,
    AdvanceWindow.validAt,
    day, Moment.by, Moment.before]
  all_goals decide +kernel

theorem recordedAtAdoption (base : StartEvidence) (input : Evidence) :
    Step (evidence input) (start base) before reviewBefore
      (.recordCorrection form.lesson (.monetary original correction)) reviewAfter := by
  apply Step.recordMonetary
  · simp [reviewBefore]
  · simp [reviewBefore, correction]
  · simp [evidence, correction, finding]
  · refine ⟨[], rfl, ?_⟩
    simp +contextual [PaymentCorrectionCase.recorded, PaymentCorrectionCase.outcomeConforms,
      correctionAfterReviewConforms, correctionRecordConforms, reviewFindingConforms,
      reviewFindingConformsWithContacts, ReviewAppointment.applies, independentReviewer,
      ReviewAuthorities.disinterested, DirectInterest.affected, ReviewAuthorities.mayDecideDispute,
      ReviewMatter.sameCase, History.authorities, reviewBefore, evidence, authority,
      correction, finding, original, matter, form, PaymentPartRef.sameCorrectionClaim,
      PaymentPart.matchesMaterialsCreditor, PaymentCorrectionCase.priorMaterialsRefs,
      PaymentPurpose.isMaterialsShare, correctionActualPaymentsRecorded,
      correctionActualPaymentsRetained, MonetaryCorrection.matchesReceipt,
      PaymentHistory.distinctReceipts, PaymentHistory.validReturns, before, holds, known, receipt,
      part, oldPart, sumAmounts]
    all_goals (repeat' apply And.intro) <;> first | rfl | decide +kernel
  · simp [History.paymentCorrections, reviewBefore, History.empty]

theorem laterReceiptsWereAbsentFromAdoptionSnapshot :
    ¬ correctionActualPaymentsRecorded (current 7).payments correction.money := by
  intro complete
  have membership := complete.2 wrong (by simp [current, holds]) (by
    unfold MonetaryCorrection.matchesReceipt
    decide +kernel)
  exact (by decide +kernel : wrong ∉ correction.money.actualReceipts) membership

theorem laterProperReceiptReducesTheBalance :
    (current 7).payments.remainingObligationBefore
      part.ref.lesson part.ref.obligation part.recipient part.amount (day 17)
        (some part.ref.purpose) = 7 := by
  decide +kernel

theorem correctedPayoutAfterLateReceipts (base : StartEvidence) (input : Evidence)
    (decisions : DecisionRecords) :
    Step (evidence input) (start base) (current 7) reviewAfter
      (.fileCorrectedPayment (payout input decisions))
      { reviewAfter with correctedPayouts := [payout input decisions] } := by
  apply Step.fileCorrectedPayment
  · refine ⟨by simp [payout, reviewAfter, reviewBefore], by simp [payout, reviewAfter],
      by change (day 17).by (day 18); decide +kernel, payoutScope, ?_, ?_⟩
    · change payoutScope ∈ reviewAfter.correctedScopeAt correction (day 17)
      decide +kernel
    unfold CorrectedPaymentPosted
    dsimp only [payout]
    rw [show (current 7).withPartRevisionsKnownAt (day 18) = current 7 from rfl]
    refine ⟨?_, formMatches, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_,
      ⟨rfl, ⟨rfl, trivial⟩, ⟨rfl, trivial⟩⟩, rfl, Iff.rfl, Iff.rfl⟩
    · refine ⟨original.outcome, by simp, rfl, ⟨rfl, rfl⟩, none, [form], ?_, by simp⟩
      exact ⟨⟨⟨by simp [start], by
        intro row member
        obtain rfl := List.mem_singleton.mp member
        exact ⟨rfl, formMatches⟩⟩, rfl⟩, rfl⟩
    · simp +contextual [reviewFindingRecordedConforms, reviewFindingConformsWithContacts,
        independentReviewer, didNotMakeOriginalFinding, History.decisionRecords,
        History.authorities,
        reviewAfter, reviewBefore, History.empty, authority, evidence, original, finding,
        ReviewAuthorities.disinterested, DirectInterest.affected,
        ReviewAuthorities.mayDecideDispute, form, correction, ReviewMatter.sameCase, matter]
    · simp [HoldHistory.temporarySettersRecorded, History.decisionRecords, History.authorities,
        authority, evidence, current, holds]
    · simp +contextual [PaymentCorrectionCase.retained, PaymentCorrectionCase.outcomeConforms,
        correctionAfterReviewConforms, correctionRecordConforms, reviewFindingConforms,
        reviewFindingConformsWithContacts, ReviewAppointment.applies, independentReviewer,
        ReviewAuthorities.disinterested, DirectInterest.affected,
        ReviewAuthorities.mayDecideDispute, ReviewMatter.sameCase, History.authorities,
        History.decisionRecords, History.monetaryOutcome,
        reviewAfter, reviewBefore, evidence, authority, correction, finding, original, matter, form,
        PaymentPartRef.sameCorrectionClaim, PaymentPart.matchesMaterialsCreditor,
        PaymentCorrectionCase.priorMaterialsRefs, PaymentPurpose.isMaterialsShare,
        correctionActualPaymentsRetained, MonetaryCorrection.matchesReceipt,
        PaymentHistory.distinctReceipts, PaymentHistory.validReturns, current, holds, part, oldPart,
        known, wrong, proper, payment, receipt, sumAmounts]
      all_goals (repeat' apply And.intro) <;> first | rfl | decide +kernel
    · simp [correction, part]
    · simp [form]
    · refine Or.inl ⟨rfl, by decide +kernel, rfl, rfl, by decide +kernel, by decide +kernel, ?_,
        by decide +kernel, ⟨7, ?_, by decide +kernel⟩, ?_, rfl⟩
      · exact ⟨by simp [current, holds], rfl⟩
      · change (7 : Amount) = (current 7).payments.remainingObligationBefore
          part.ref.lesson part.ref.obligation part.recipient payoutScope.principal (day 17)
          (some part.ref.purpose)
        decide +kernel
      · change (7 : Amount) ≤ payoutScope.selected.outstandingBefore (current 7).payments
          [] none (day 17)
        decide +kernel
    · simp [HoldFacts.matchesForm, evidence]
  · simp [reviewAfter, reviewBefore, History.empty]

private def refundPart (portion : Nat) (amount : Amount) : PaymentPart :=
  ⟨⟨42, 12, portion, .lessonRefund 1⟩, .lessonRefund 401, amount⟩

private def beforeRevision := refundPart 1 50
private def unchanged := refundPart 2 50
private def afterRevision := refundPart 3 40
private def refundPortions : Moment × List PaymentPart := ⟨day 9, [beforeRevision, unchanged]⟩
private def refundOriginal := { original with payment := some beforeRevision }

private def refundReceipt (piece : PaymentPart) (id date : Nat) (amount : Amount) : PostedPayment :=
  ⟨id, ⟨piece.ref, .account 401, 30, amount, day date⟩, some id⟩

private def credit (receipt : PostedPayment) : CreditPosting :=
  ⟨receipt.id, 401, .lessonRefund 42 1 12, receipt.instruction.amount, receipt.instruction.atTime⟩

private def otherReceipt := refundReceipt unchanged 201 10 50
private def oldReceipt := refundReceipt beforeRevision 202 11 25
private def refundPayment (amount : Amount) : CorrectionPaymentRecord :=
  let receipt := refundReceipt afterRevision 203 17 amount
  ⟨73, receipt, some (credit receipt)⟩

private def refundCorrection : PaymentCorrectionCase :=
  { correction with
    originalPart := beforeRevision
    money := ⟨afterRevision, day 13, [otherReceipt]⟩ }

private def refundReview : History :=
  { reviewBefore with
    originals := [refundOriginal]
    corrections := [.monetary refundOriginal refundCorrection] }

private def refundScope : CorrectedMonetaryScope :=
  ⟨⟨afterRevision, [beforeRevision]⟩,
    [⟨afterRevision, [beforeRevision]⟩, ⟨unchanged, []⟩], 100, 90⟩

private def refundApproval : PaymentApproval :=
  ⟨31, 10, 30, day 15, none, none, [⟨afterRevision.ref, .account 401, 40, none⟩]⟩

private def otherApproval : PaymentApproval :=
  ⟨32, 10, 30, day 9, none, none, [⟨unchanged.ref, .account 401, 50, none⟩]⟩

private def refundHolds (receipts : List PostedPayment) : HoldHistory :=
  { holds receipts with approvals := [otherApproval, refundApproval] }

private def refundAuthority : ReviewAuthorities :=
  { authority with approvesPayment := fun ref actor time ↦
      (ref = afterRevision.ref ∧ actor = 10 ∧ time = day 15) ∨
      (ref = unchanged.ref ∧ actor = 10 ∧ time = day 9) }

private def refundEvidence (base : Evidence) : Evidence :=
  { evidence base with
    authority := refundAuthority
    holds := { (evidence base).holds with
      establishedParts := fun lesson purpose ↦
        if lesson = 42 ∧ purpose = .lessonRefund 1 then [afterRevision, unchanged] else [] }
    refundPortionsAt := fun confirmed obligation query ↦
      if form.lesson.id = confirmed.lesson.id ∧ form.place = confirmed.place ∧
          12 = obligation ∧ refundPortions.1.by query then some refundPortions else none
    refundOriginAt := fun confirmed ref query ↦
      if ref.lesson ≠ confirmed.lesson.id ∨ ref.purpose ≠ .lessonRefund confirmed.place.id then none
      else if form.lesson.id = confirmed.lesson.id ∧ form.place = confirmed.place ∧
          12 = ref.obligation ∧ refundPortions.1.by query then
        some (.agreedChange, day 8, day 18)
      else none }

private def debit : CreditPosting := ⟨200, 401, .lessonDebit 42 1, 100, day 2⟩

private def otherFiling : VerifiedLessonRefund :=
  { form
    originalDebit := debit
    obligation := 12
    settlement := ⟨42, 1, 401, "agreed change", .agreedChange, 0, day 8, day 18, 100, 50,
      [day 10], false, false⟩
    payment := otherReceipt
    approval := some otherApproval }

private def correctedFiling : VerifiedLessonRefund :=
  { otherFiling with
    settlement := ⟨42, 1, 401, "reviewed fee", .agreedChange, 10, day 8, day 18, 90, 90,
      [day 10, day 17], false, false⟩
    payment := (refundPayment 40).paid
    approval := some refundApproval }

private def refundStart (base : StartEvidence) : StartEvidence :=
  { start base with
    ledger := [debit, credit otherReceipt, credit (refundPayment 40).paid]
    creditRecords := { base.creditRecords with verifiedRefunds := [otherFiling, correctedFiling] } }

/-- A filed receipt with the wrong basis does not replace the retained assessment. -/
theorem retainedAssessmentControlsReceiptBasis (base : StartEvidence) (input : Evidence) :
    let evidence := { refundEvidence input with
      refundOriginAt := fun _ _ _ ↦ some (.agreedChange, day 8, day 18) }
    let wrong := { otherFiling with settlement := { otherFiling.settlement with
      basis := .noFaultCancellation, trigger := day 9 } }
    let start := refundStart base
    let history := { start with creditRecords := { start.creditRecords with
      verifiedRefunds := [wrong] } }
    evidence.retainedRefundAt form history (day 12) afterRevision.ref = none ∧
    evidence.retainedRefundAt form start (day 12) afterRevision.ref = some otherFiling.settlement :=
  ⟨rfl, rfl⟩

#print axioms retainedAssessmentControlsReceiptBasis

private def refundPayout (base : Evidence) (decisions : DecisionRecords) : CorrectedPayout :=
  let row := payout base decisions
  let facts := (refundEvidence base).holds
  let a := refundReview.authorities refundAuthority
  let h := refundHolds [otherReceipt, (refundPayment 40).paid]
  { row with
    original := refundOriginal
    correction := refundCorrection
    payment := refundPayment 40
    part := afterRevision
    decisions := { decisions with faultOutcomes := [] }
    funds := ⟨42, 10, day 17, [⟨90, .providerFunds, .spendable, 40, 0, 40⟩]⟩
    approval := .ordinary refundApproval
    onTime := FiledPaymentOnTime form a facts h afterRevision row.schedule (refundPayment 40).paid []
    completedOnTime := FiledPaymentCompletedOnTime form a facts h afterRevision row.schedule []
      (day 17) }

/-- Even with 50 already restored under the other portion, the reviewed portion can pay 40. -/
theorem splitRefundFilesAfterSiblingReceipt (base : StartEvidence) (input : Evidence)
    (decisions : DecisionRecords) :
    let row := refundPayout input decisions
    Step (refundEvidence input) (refundStart base)
      (refundHolds [otherReceipt, (refundPayment 40).paid]) refundReview
      (.fileCorrectedPayment row) { refundReview with correctedPayouts := [row] } := by
  apply Step.fileCorrectedPayment
  · refine ⟨by simp [refundPayout, refundReview], by simp [refundPayout, refundReview],
      by change (day 17).by (day 18); decide +kernel, refundScope, ?_, ?_⟩
    · change refundScope ∈ refundReview.correctedScopeAt refundCorrection (day 17)
        (some refundPortions)
      decide +kernel
    unfold CorrectedPaymentPosted
    dsimp only [refundPayout, payout]
    have holdsAtFiling :
        (refundHolds [otherReceipt, (refundPayment 40).paid]).withPartRevisionsKnownAt (day 18) =
          refundHolds [otherReceipt, (refundPayment 40).paid] := rfl
    rw [holdsAtFiling]
    refine ⟨?_, formMatches, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl,
      Iff.rfl, Iff.rfl⟩
    · refine ⟨refundOriginal.outcome, by simp, rfl, ⟨rfl, rfl⟩, none, [form], ?_, by simp⟩
      exact ⟨⟨⟨by simp [refundStart, start], by
        intro row member
        obtain rfl := List.mem_singleton.mp member
        exact ⟨rfl, formMatches⟩⟩, rfl⟩, rfl⟩
    · simp +contextual [reviewFindingRecordedConforms, reviewFindingConformsWithContacts,
        independentReviewer, didNotMakeOriginalFinding, History.decisionRecords,
        History.authorities, refundReview, reviewBefore, History.empty, refundAuthority,
        authority, refundEvidence, evidence, refundOriginal, original, finding,
        ReviewAuthorities.disinterested, DirectInterest.affected, ReviewAuthorities.mayDecideDispute,
        form, refundCorrection, correction, ReviewMatter.sameCase, matter]
    · simp [HoldHistory.temporarySettersRecorded, History.decisionRecords, History.authorities,
        refundAuthority, authority, refundEvidence, evidence, refundHolds, holds]
    · simp +contextual [PaymentCorrectionCase.retained, PaymentCorrectionCase.outcomeConforms,
        correctionAfterReviewConforms, correctionRecordConforms, reviewFindingConforms,
        reviewFindingConformsWithContacts, ReviewAppointment.applies, independentReviewer,
        ReviewAuthorities.disinterested, DirectInterest.affected, ReviewAuthorities.mayDecideDispute,
        ReviewMatter.sameCase, History.authorities, History.decisionRecords, History.monetaryOutcome,
        refundReview, reviewBefore, refundEvidence, evidence, refundAuthority, authority,
        refundCorrection, correction, finding, refundOriginal, original, matter, form,
        PaymentPartRef.sameCorrectionClaim, PaymentPart.matchesMaterialsCreditor,
        PaymentCorrectionCase.priorMaterialsRefs, PaymentPurpose.isMaterialsShare,
        correctionActualPaymentsRetained, MonetaryCorrection.matchesReceipt,
        PaymentHistory.distinctReceipts, PaymentHistory.validReturns, refundHolds, holds,
        beforeRevision, unchanged, afterRevision, refundPart, otherReceipt, refundReceipt,
        refundPayment, sumAmounts]
      all_goals (repeat' apply And.intro) <;> first | rfl | decide +kernel
    · simp [History.decisionRecords]
    · simp [form]
    · refine Or.inl ⟨rfl, by decide +kernel, rfl, rfl, by decide +kernel, by decide +kernel,
        ⟨by simp [refundHolds, holds], rfl⟩, by decide +kernel, ⟨40, ?_, by decide +kernel⟩,
        ?_, form.place, by simp, credit (refundPayment 40).paid, by simp [refundPayment],
        rfl, rfl, rfl, ?_⟩
      · exact ⟨form.place, by simp, rfl, rfl, rfl, by
          simp only [refundStart]
          decide +kernel⟩
      · change (40 : Amount) ≤ refundScope.selected.outstandingBefore
          (refundHolds [otherReceipt, (refundPayment 40).paid]).payments
          [debit, credit otherReceipt, credit (refundPayment 40).paid] (some form.place) (day 17)
        decide +kernel
      · unfold SourceV14.Settlement.ValidLessonRefund
        refine ⟨⟨by simp [refundStart], rfl, rfl, by decide +kernel⟩, ?_, ?_⟩
        all_goals simp only [refundStart] <;> decide +kernel
    · simp [HoldFacts.matchesForm, refundEvidence, evidence]
    · refine Or.inr ⟨?_, rfl, ⟨rfl, trivial⟩, ⟨rfl, trivial⟩⟩
      rintro ⟨_, _, (absent | ⟨old, retains, isNoFault, _⟩), _⟩
      · cases absent
      have found : some otherFiling.settlement = some old := retains
      have same := Option.some.inj found
      rw [← same] at isNoFault
      exact (by decide : otherFiling.settlement.basis ≠ .noFaultCancellation) isNoFault
  · simp [refundReview, reviewBefore, History.empty]

private def refundState (base : Workflow.State) (assessment : Workflow.Redress.AssessmentEvidence) :
    Workflow.State :=
  let h := refundHolds [otherReceipt, (refundPayment 40).paid]
  { base with
    review := refundReview
    redress := { assessments := [⟨⟨form, 12, .agreedChange, "agreed change", day 8,
      refundPortions.1, ⟨day 15, day 18, none, .date (day 20)⟩, 0, 100, refundPortions.2⟩,
      assessment, none, none⟩] }
    holds := h
    lessons := fun lesson ↦ { base.lessons lesson with effectiveForms := [form], groupRoster := none }
    credit := { base.credit with
      openingCredit := fun account ↦ if account = 401 then 100 else 0
      ledger := [debit, credit otherReceipt]
      creditRecords := { base.credit.creditRecords with
        topUps := [], grants := [], topUpReturns := [], closed := [],
        payments := h.payments, verifiedRefunds := [otherFiling],
        paymentAuthorities := refundAuthority } } }

private theorem refundEvidenceMatchesRoot (base : Workflow.State)
    (assessment : Workflow.Redress.AssessmentEvidence) (input : Evidence) :
    let state := refundState base assessment
    state.reviewEvidence (refundEvidence input) = { refundEvidence input with
      refundPriorPrincipals := fun form obligation query ↦
        state.redress.otherRefundPrincipals form obligation state.review query } := by
  simp only [Workflow.State.reviewEvidence, refundEvidence]
  congr
  · funext confirmed obligation query
    by_cases applies : form.lesson.id = confirmed.lesson.id ∧ form.place = confirmed.place ∧
        12 = obligation ∧ (day 9).by query <;> simp [refundState, refundPortions, applies]
  · funext confirmed ref query
    by_cases wrong : ref.lesson ≠ confirmed.lesson.id ∨ ref.purpose ≠ .lessonRefund confirmed.place.id
    · simp [wrong]
    · by_cases applies : form.lesson.id = confirmed.lesson.id ∧ form.place = confirmed.place ∧
          12 = ref.obligation ∧ (day 9).by query <;>
        simp [refundState, refundPortions, refundDeadline, wrong, applies]

private def splitLedger : List CreditPosting :=
  [debit, credit otherReceipt, credit (refundPayment 40).paid]

private def splitPayments : PaymentHistory :=
  (refundHolds [otherReceipt, (refundPayment 40).paid]).payments

private theorem otherRefundTime (time : Moment) :
    time = day 10 ↔ (day 10 = time ∧ time.by (day 10)) ∨
      (day 17 = time ∧ time.by (day 10)) := by
  constructor
  · rintro rfl
    exact Or.inl ⟨rfl, Or.inr rfl⟩
  · rintro (⟨rfl, _⟩ | ⟨rfl, late⟩)
    · rfl
    · exact False.elim ((by decide : ¬(day 17).by (day 10)) late)

private theorem correctedRefundTimes (time : Moment) :
    time = day 10 ∨ time = day 17 ↔ (day 10 = time ∧ time.by (day 17)) ∨
      (day 17 = time ∧ time.by (day 17)) := by
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr ⟨rfl, Or.inr rfl⟩
  · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl

private theorem splitRefundFileMatches (reviewed : Bool) :
    let file := if reviewed then correctedFiling else otherFiling
    file.matches splitLedger splitPayments refundAuthority (credit file.payment) := by
  cases reviewed <;>
    refine ⟨formMatches, by decide +kernel, rfl, rfl, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  all_goals first
    | (refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel, ?_,
          by decide +kernel⟩
       intro time
       simp [splitLedger, correctedFiling, otherFiling, debit, credit, refundPayment,
         otherReceipt, refundReceipt, form]
       first | exact otherRefundTime time | exact correctedRefundTimes time)
    | exact ⟨by decide +kernel, rfl, rfl, by decide +kernel⟩
    | exact ⟨by decide +kernel, rfl⟩
    | (simp [PaymentApproval.authorisedAtGrant, refundAuthority, correctedFiling, otherFiling,
        refundApproval, otherApproval] <;> decide +kernel)

private theorem splitRefundCanPostCredit (base : Workflow.State)
    (assessment : Workflow.Redress.AssessmentEvidence) (input : Evidence)
    (decisions : DecisionRecords) :
    let s := refundState base assessment
    s.credit.mayFileCorrectedRefund s.holds.payments
      (credit (refundPayment 40).paid) correctedFiling (refundPayout input decisions) refundScope := by
  refine ⟨rfl, rfl, rfl, rfl, by decide +kernel, ?_, ?_, rfl, ?_, ?_⟩
  · change (credit (refundPayment 40).paid).id ∉ ([debit, credit otherReceipt].map (·.id))
    decide +kernel
  · intro earlier prior
    have same : earlier = otherFiling := List.mem_singleton.mp prior
    rw [same]
    decide +kernel
  · exact splitRefundFileMatches true
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [CreditOriginsValid, Workflow.CreditBook.withCorrectedRefund, refundState,
        refundHolds, holds, debit, credit]
    · change (splitLedger.map (·.id)).Nodup
      decide +kernel
    · change (splitLedger.map (·.point)).Nodup
      decide +kernel
    · change splitPayments.distinctReceipts
      exact ⟨by decide +kernel, by decide +kernel⟩
    · intro entry listed
      change entry ∈ splitLedger at listed
      rcases List.mem_cons.mp listed with rfl | tail
      · refine ⟨by decide +kernel, ?_⟩
        change debit.amount ≤ balanceBefore (fun account ↦ if account = 401 then 100 else 0)
          splitLedger debit.account debit.point
        decide +kernel
      · rcases List.mem_cons.mp tail with rfl | single
        · exact ⟨by decide +kernel, otherFiling, List.mem_cons_self,
            splitRefundFileMatches false⟩
        · obtain rfl := List.mem_singleton.mp single
          exact ⟨by decide +kernel, correctedFiling, by
            change correctedFiling ∈ [otherFiling, correctedFiling]
            simp, splitRefundFileMatches true⟩
    · intro entry listed cutoff
      change entry ∈ splitLedger at listed
      change SourceV14.Settlement.returnedFrom splitLedger entry cutoff ≤ entry.amount
      rcases List.mem_cons.mp listed with rfl | tail
      · simp [SourceV14.Settlement.returnedFrom, splitLedger, debit, credit, sumAmountsWhere] <;>
          decide +kernel
      · rcases List.mem_cons.mp tail with rfl | single
        · simp [SourceV14.Settlement.returnedFrom, splitLedger, debit, credit, sumAmountsWhere] <;>
            decide +kernel
        · obtain rfl := List.mem_singleton.mp single
          simp [SourceV14.Settlement.returnedFrom, splitLedger, debit, credit, sumAmountsWhere] <;>
            decide +kernel
    · simp [Workflow.CreditBook.withCorrectedRefund, refundState]

/-- The root filing takes both the principal and the chosen portion from retained decisions. -/
theorem rootFilesSplitCorrectedRefund (base : Workflow.State)
    (assessment : Workflow.Redress.AssessmentEvidence) (input : Evidence)
    (decisions : DecisionRecords) :
    let s := refundState base assessment
    let row := refundPayout input decisions
    let posting := credit (refundPayment 40).paid
    Workflow.Step s (.correctedRefund (refundEvidence input) row posting correctedFiling)
      { s with
        review := { refundReview with correctedPayouts := [row] }
        credit := s.credit.withCorrectedRefund s.holds.payments posting correctedFiling } := by
  refine Workflow.Step.correctedRefund (scope := refundScope) ?_
    (splitRefundCanPostCredit base assessment input decisions) ?_
  · rw [refundEvidenceMatchesRoot]
    change refundReview.correctedScopeAt refundCorrection (day 17) (some refundPortions) =
      some refundScope
    decide +kernel
  · rw [refundEvidenceMatchesRoot]
    let state := refundState base assessment
    exact splitRefundFilesAfterSiblingReceipt (state.course form.lesson.id)
      { input with refundPriorPrincipals := fun form obligation query ↦
          state.redress.otherRefundPrincipals form obligation state.review query } decisions

/-- A receipt for the old reference follows the renumbered portion. Only its own return reopens it. -/
theorem renumberedRefundCountsPriorReceiptAndItsReturn :
    let receipts := (refundHolds [otherReceipt, oldReceipt]).payments
    let ledger := [debit, credit otherReceipt, credit oldReceipt]
    let returned : CreditPosting := ⟨204, 401, .creditReturned oldReceipt.id, 5, day 16⟩
    refundScope.principal = 90 ∧
    refundScope.selected.outstandingBefore receipts ledger (some form.place) (day 17) = 15 ∧
    refundScope.selected.outstandingBefore receipts (ledger ++ [returned])
      (some form.place) (day 17) = 20 := by
  decide +kernel

/-- An unpaid sibling cannot supply extra room to the part already paid under its old reference. -/
theorem renumberedPortionCannotSpendSiblingBalance :
    let row := { refundCorrection with
      money := { refundCorrection.money with actualReceipts := [oldReceipt] } }
    let payment := refundPayment 16
    let receipts := (refundHolds [oldReceipt, payment.paid]).payments
    let ledger := [debit, credit oldReceipt, credit payment.paid]
    SourceV14.Settlement.refundBalanceDue form.place ledger (day 16)
      refundScope.principal (some 12) = 65 ∧
    ¬row.additionalPaymentPosted form.lesson receipts ledger (some form.place) payment
      refundScope := by
  refine ⟨by decide +kernel, ?_⟩
  intro posted
  obtain ⟨_, _, _, _, _, _, _, _, _, withinPortion, _⟩ := posted
  exact (by decide +kernel : ¬(16 : Amount) ≤ refundScope.selected.outstandingBefore
    (refundHolds [oldReceipt, (refundPayment 16).paid]).payments
    [debit, credit oldReceipt, credit (refundPayment 16).paid] (some form.place) (day 17))
      withinPortion

/-- The verified account received 105 even though the corrected obligation totals 90. -/
theorem correctedOverrefundRecordedWithoutPayoutAuthority :
    let payment := refundPayment 55
    let receipts := (refundHolds [otherReceipt, payment.paid]).payments
    let ledger := [debit, credit otherReceipt, credit payment.paid]
    refundCorrection.observedRefundPosted form.place receipts ledger payment ∧
    SourceV14.Settlement.creditsRestoredFor form.place ledger (day 17) (some 12) = 105 ∧
    ¬refundCorrection.additionalPaymentPosted form.lesson receipts ledger (some form.place)
      payment refundScope := by
  refine ⟨?_, by decide +kernel, ?_⟩
  · refine ⟨rfl, by decide +kernel, rfl, rfl, rfl, rfl, rfl, ⟨by simp [refundHolds, holds], rfl⟩,
      ?_, ?_, credit (refundPayment 55).paid, rfl, ⟨by simp, rfl, rfl, by decide +kernel⟩,
      rfl, rfl, rfl⟩
    · unfold PaymentHistory.distinctReceipts
      decide +kernel
    · simp [PaymentHistory.validReturns, refundHolds, holds, otherReceipt, refundPayment,
        refundReceipt, sumAmounts]
      all_goals decide +kernel
  · intro authorised
    obtain ⟨_, _, _, _, _, _, _, _, _, withinPortion, _⟩ := authorised
    exact (by decide +kernel : ¬ (55 : Amount) ≤ refundScope.selected.outstandingBefore
      (refundHolds [otherReceipt, (refundPayment 55).paid]).payments
      [debit, credit otherReceipt, credit (refundPayment 55).paid] (some form.place) (day 17))
      withinPortion

/-- A renumbering cannot reuse a reference already assigned to another portion. -/
theorem conflictingRenumberingLeavesNoOperativeScope :
    let bad := { refundCorrection with
      money := { refundCorrection.money with corrected := {afterRevision with ref := unchanged.ref} } }
    let review := { refundReview with corrections := [.monetary refundOriginal bad] }
    review.correctedScopeAt bad (day 17) (some refundPortions) = none := by
  decide +kernel

private def materialTerms : MaterialsTerms where
  lesson := 42
  adoptedBy := 10
  agreedAt := day 1
  agreementReference := "material terms"
  accountingAndPaymentParty := 10
  materialsOrBundle := "lesson materials"
  contact := "provider"
  licensedUse := (· = 97)
  sharesAndAdjustmentsReference := "agreed shares"
  sharesInForce := fun _ _ ↦ none
  contributors := fun _ ↦ [201, 202]
  consents := [⟨97, 201, "material terms", day 1⟩, ⟨97, 202, "material terms", day 1⟩]
  ordinaryShareTime := fun _ _ firstUse _ ↦ firstUse
  paymentDue := day 15
  paymentDeadline := day 18
  pricing := .standardBundle [⟨97, 9 / 100⟩]

private def materialForm : PartOne :=
  { form with
    place := { form.place with normalFee := 200, feePayable := 200 }
    materialsOrBundle := some materialTerms.materialsOrBundle
    materialsTermsRef := some materialTerms.agreementReference
    materialsPayer := some materialTerms.accountingAndPaymentParty }

private theorem materialFormMatches : materialForm.matches := by
  simp [PartOne.matches, materialForm, materialTerms, form, terms, Place.matches, Place.validFees,
    Schedule.valid, Contacts.complete, PayAndReviewTerms.valid, PaymentTerms.valid,
    PaymentDeadline.valid, AdvanceWindow.validAt, day, Moment.by, Moment.before]
  all_goals decide +kernel

private def materialOld : PaymentPart :=
  ⟨⟨42, 12, 1, .materialsShare 97 201⟩, .person 201 none, 8⟩

private def materialNew : PaymentPart :=
  ⟨⟨42, 12, 3, .materialsShare 97 202⟩, .person 202 none, 10⟩

private def otherOldHolderPortion : PaymentPart :=
  { materialOld with ref := { materialOld.ref with portion := 2 }, amount := 4 }

private def otherNewHolderPortion : PaymentPart :=
  { materialNew with ref := { materialNew.ref with portion := 4 }, amount := 4 }

private def materialMatter : ReviewMatter := ⟨2, 42, [201, 202]⟩
private def materialOriginal : OriginalRecord :=
  ⟨⟨materialMatter, 72, 50, day 9⟩, some materialOld⟩

private def materialFinding : ReviewFinding :=
  { finding with matter := materialMatter, reasons := "Correcting the creditor" }

private def materialReceipt (piece : PaymentPart) (id person date : Nat) (amount : Amount) :
    PostedPayment :=
  ⟨id, ⟨piece.ref, .person person, 30, amount, day date⟩, some id⟩

private def paidToOld := materialReceipt materialOld 11 201 10 5
private def paidToNewOnOldRef := materialReceipt materialOld 12 202 11 2
private def unrelatedMaterialPayment := materialReceipt otherOldHolderPortion 13 202 11 4
private def paidOnOtherPortion := materialReceipt otherNewHolderPortion 14 202 12 1
private def materialPayment : CorrectionPaymentRecord :=
  ⟨73, materialReceipt materialNew 15 202 17 8, none⟩

private def materialCorrection : PaymentCorrectionCase :=
  ⟨materialOld, materialFinding, ⟨42, 72, 73, 30, { day 17 with order := 1 }, [201, 202]⟩,
    ⟨materialNew, day 13, [paidToOld, paidToNewOnOldRef, paidOnOtherPortion]⟩⟩

private def materialBefore : History :=
  { reviewBefore with
    originals := [materialOriginal,
      ⟨⟨materialMatter, 172, 50, day 9⟩, some otherOldHolderPortion⟩,
      ⟨⟨materialMatter, 173, 50, day 9⟩, some otherNewHolderPortion⟩]
    appointments := [⟨materialMatter, 10, 60, day 12⟩]
    reviewFindings := [materialFinding] }

private def materialAfter : History :=
  { materialBefore with corrections := [.monetary materialOriginal materialCorrection] }

private def materialScope : CorrectedMonetaryScope :=
  ⟨⟨materialNew, [materialOld]⟩,
    [⟨materialNew, [materialOld]⟩, ⟨otherOldHolderPortion, []⟩, ⟨otherNewHolderPortion, []⟩],
    12, 14⟩

private def materialApproval : PaymentApproval :=
  ⟨25, 10, 30, day 15, none, none, [⟨materialNew.ref, .person 202, 10, none⟩]⟩

private def materialLedger : HoldHistory :=
  { holds [paidToOld, paidToNewOnOldRef, unrelatedMaterialPayment, paidOnOtherPortion] with
    approvals := [] }

private def materialReceived : HoldHistory :=
  { materialLedger with
    payments := { materialLedger.payments with
      posted := materialLedger.payments.posted ++ [materialPayment.paid] }
    approvals := [materialApproval] }

private def materialPaid : HoldHistory :=
  materialReceived.withPartRevision materialOriginal.outcome materialCorrection

private theorem materialPaidKnownAtFiling :
    materialPaid.withPartRevisionsKnownAt (day 18) = materialPaid := by
  decide +kernel

private def materialAuthority : ReviewAuthorities :=
  { authority with
    reviewer := fun m actor time ↦ m = materialMatter ∧ actor = 60 ∧ time = day 13
    approvesPayment := fun ref actor time ↦ ref = materialNew.ref ∧ actor = 10 ∧ time = day 15 }

private def materialEvidence (base : Evidence) : Evidence :=
  { evidence base with
    authority := materialAuthority
    originalOutcome := (· = materialOriginal.outcome)
    refundPortionsAt := fun _ _ _ ↦ none
    refundOriginAt := fun _ _ _ ↦ none
    recordedAmount := fun m outcome p ↦ m = materialMatter ∧
      ((outcome = 72 ∧ p = materialOld) ∨ (outcome = 73 ∧ p = materialNew))
    holds := { (evidence base).holds with
      establishedParts := fun lesson purpose ↦
        if lesson = 42 ∧ purpose = materialNew.ref.purpose then [materialNew] else [] } }

private def materialStart (base : StartEvidence) : StartEvidence :=
  { start base with effectiveForms := [materialForm] }

private def materialPayout (input : Evidence) (decisions : DecisionRecords) : CorrectedPayout :=
  let row := payout input decisions
  let a := materialAfter.authorities materialAuthority
  let facts := (materialEvidence input).holds
  { row with
    form := materialForm, original := materialOriginal, correction := materialCorrection
    payment := materialPayment, part := materialNew, adoptedMaterials := some materialTerms
    approval := .ordinary materialApproval
    funds := ⟨42, 10, day 17, [⟨90, .providerFunds, .spendable, 8, 0, 8⟩]⟩
    onTime := FiledPaymentOnTime materialForm a facts materialPaid materialNew
      row.schedule materialPayment.paid []
    completedOnTime := FiledPaymentCompletedOnTime materialForm a facts materialPaid materialNew
      row.schedule [] (day 17) }

/-- The coordinator keeps the old creditor's actual payment and the exact reviewed new portion. -/
theorem recordMaterialsCreditorCorrection (base : StartEvidence) (input : Evidence) :
    Step (materialEvidence input) (materialStart base) materialReceived materialBefore
      (.recordCorrection materialForm.lesson (.monetary materialOriginal materialCorrection))
      materialAfter := by
  apply Step.recordMonetary
  · simp [materialBefore]
  · simp [materialBefore, materialCorrection]
  · exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  · refine ⟨[materialOld], by decide +kernel, ?_⟩
    simp +contextual [PaymentCorrectionCase.recorded, PaymentCorrectionCase.outcomeConforms,
      correctionAfterReviewConforms, correctionRecordConforms, reviewFindingConforms,
      reviewFindingConformsWithContacts, ReviewAppointment.applies, independentReviewer,
      ReviewAuthorities.disinterested, DirectInterest.affected, ReviewAuthorities.mayDecideDispute,
      ReviewMatter.sameCase, History.authorities, materialBefore, reviewBefore, materialEvidence,
      materialAuthority, authority, materialCorrection, materialFinding, finding, materialOriginal,
      materialMatter, materialForm, form, PaymentPartRef.sameCorrectionClaim,
      PaymentPart.matchesMaterialsCreditor, PaymentCorrectionCase.priorMaterialsRefs,
      PaymentPurpose.isMaterialsShare, correctionActualPaymentsRecorded,
      correctionActualPaymentsRetained, MonetaryCorrection.matchesReceipt,
      PaymentHistory.distinctReceipts, PaymentHistory.validReturns, materialReceived,
      materialLedger, materialPayment, holds,
      paidToOld, paidToNewOnOldRef, unrelatedMaterialPayment, paidOnOtherPortion,
      materialReceipt, materialNew, materialOld, otherOldHolderPortion, otherNewHolderPortion,
      sumAmounts]
    all_goals (repeat' apply And.intro) <;> first | rfl | decide +kernel
  · simp [History.paymentCorrections, materialBefore, reviewBefore, History.empty]

/-- Only B's actual receipt on the linked old reference credits the revised portion.
B's receipt for A's separate portion cannot discharge it. -/
theorem materialsReceiptsFollowExactCreditorAndPortion :
    materialAfter.correctedScopeAt materialCorrection (day 17) (knownAt := day 18) =
      some materialScope ∧
    materialScope.principal = 14 ∧
    materialScope.selected.outstandingBefore materialPaid.payments [] none (day 17) = 8 ∧
    materialScope.matchesMaterialsReceipt unrelatedMaterialPayment.instruction.part = false ∧
    materialCorrection.money.outstandingBefore materialPaid.payments [] none (day 17) 11
      materialScope := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  unfold MonetaryCorrection.outstandingBefore
  dsimp only [materialCorrection, materialNew]
  decide +kernel

theorem materialsFilingUsesDecisionTimeAndAvailableEvidence :
    let early := { materialCorrection with
      correction := { materialCorrection.correction with recordedAt := day 14 } }
    let earlyHistory := { materialBefore with corrections := [.monetary materialOriginal early] }
    materialFinding.decidedAt.before materialApproval.grantedAt ∧
    materialApproval.grantedAt.before materialPayment.paid.instruction.atTime ∧
    materialPayment.paid.instruction.atTime.before materialCorrection.correction.recordedAt ∧
    materialAfter.correctedScopeAt materialCorrection (day 17) = none ∧
    materialAfter.correctedScopeAt materialCorrection (day 12) (knownAt := day 18) = none ∧
    materialAfter.correctedScopeAt materialCorrection (day 17) (knownAt := day 18) =
      earlyHistory.correctedScopeAt early (day 17) := by
  decide +kernel

private theorem materialAdditionalReceipt (base : StartEvidence) :
    materialCorrection.additionalPaymentPosted materialForm.lesson materialPaid.payments
      (materialStart base).ledger (some materialForm.place) materialPayment materialScope := by
  refine ⟨rfl, by decide +kernel, rfl, rfl, by decide +kernel, by decide +kernel, ?_,
    by decide +kernel, ⟨11, ?_, by decide +kernel⟩, ?_, rfl⟩
  · exact ⟨by simp [materialPaid, HoldHistory.withPartRevision, materialReceived], rfl⟩
  · exact materialsReceiptsFollowExactCreditorAndPortion.2.2.2.2
  · change (8 : Amount) ≤ materialScope.selected.outstandingBefore materialPaid.payments
      [] none (day 17)
    rw [materialsReceiptsFollowExactCreditorAndPortion.2.2.1]
    decide +kernel

private theorem materialPayoutConforms (base : StartEvidence) (input : Evidence)
    (decisions : DecisionRecords) :
    (materialPayout input decisions).conforms materialAfter (materialEvidence input)
      (materialStart base) materialPaid := by
  refine ⟨by simp [materialPayout, materialAfter, materialBefore],
      by simp [materialPayout, materialAfter],
      by change (day 17).by (day 18); decide +kernel, materialScope,
      materialsReceiptsFollowExactCreditorAndPortion.1, ?_⟩
  unfold CorrectedPaymentPosted
  dsimp only [materialPayout, payout]
  rw [materialPaidKnownAtFiling]
  refine ⟨?_, materialFormMatches, ?_, ?_, ?_, ?_, ?_, Or.inl (materialAdditionalReceipt base),
    rfl, rfl, rfl, ?_, ?_, rfl, Iff.rfl, Iff.rfl⟩
  · refine ⟨materialOriginal.outcome, by simp, rfl, ⟨rfl, rfl⟩, none,
      [materialForm], ?_, by simp⟩
    exact ⟨⟨⟨by simp [materialStart], by
      intro row member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨rfl, materialFormMatches⟩⟩, rfl⟩, rfl⟩
  · simp +contextual [reviewFindingRecordedConforms, reviewFindingConformsWithContacts,
      independentReviewer, didNotMakeOriginalFinding, History.decisionRecords,
      History.authorities, materialAfter, materialBefore, reviewBefore, History.empty,
      materialAuthority, authority, materialEvidence, materialOriginal, materialFinding,
      finding, ReviewAuthorities.disinterested, DirectInterest.affected,
      ReviewAuthorities.mayDecideDispute, materialForm, form, materialCorrection,
      ReviewMatter.sameCase, materialMatter]
  · simp [HoldHistory.temporarySettersRecorded, materialEvidence, evidence, materialPaid,
      materialReceived, materialLedger, holds, HoldHistory.withPartRevision, History.decisionRecords,
      History.authorities, materialAuthority, authority]
  · simp +contextual [PaymentCorrectionCase.retained, PaymentCorrectionCase.outcomeConforms,
      correctionAfterReviewConforms, correctionRecordConforms, reviewFindingConforms,
      reviewFindingConformsWithContacts, ReviewAppointment.applies, independentReviewer,
      ReviewAuthorities.disinterested, DirectInterest.affected,
      ReviewAuthorities.mayDecideDispute, ReviewMatter.sameCase, History.authorities,
      History.decisionRecords, History.monetaryOutcome, materialAfter, materialBefore,
      reviewBefore, materialAuthority, authority, materialEvidence, materialCorrection,
      materialFinding, finding, materialOriginal, materialMatter, materialForm, form,
      PaymentPartRef.sameCorrectionClaim, PaymentPart.matchesMaterialsCreditor,
      PaymentCorrectionCase.priorMaterialsRefs, PaymentPurpose.isMaterialsShare,
      correctionActualPaymentsRetained, MonetaryCorrection.matchesReceipt,
      PaymentHistory.distinctReceipts, PaymentHistory.validReturns, materialPaid, materialReceived,
      HoldHistory.withPartRevision, materialLedger, holds, paidToOld, paidToNewOnOldRef,
      unrelatedMaterialPayment, paidOnOtherPortion,
      materialPayment, materialReceipt, materialScope, materialOld, materialNew,
      otherOldHolderPortion, otherNewHolderPortion, sumAmounts]
    all_goals (repeat' apply And.intro) <;> first | rfl | decide +kernel
  · simp [materialCorrection, materialNew]
  · simp [materialForm, form]
  · simp [HoldFacts.matchesForm, materialEvidence, evidence]
  · refine ⟨rfl, materialTerms, rfl, ?_, by decide +kernel, ?_, rfl, rfl, rfl, rfl, rfl,
      Or.inl ⟨rfl, trivial⟩, Or.inl ⟨rfl, trivial⟩⟩
    · simp [MaterialsTerms.adoptedFor, MaterialsTerms.agreedBy, MaterialsPricing.materials,
        materialTerms, materialForm, form]
      all_goals decide +kernel
    · simp [MaterialsPricing.covers, MaterialsPricing.materials, materialTerms]

private def materialState (base : Workflow.State) (review : History)
    (holds : HoldHistory) : Workflow.State :=
  { base.withHolds holds with
    review
    redress := {}
    lessons := fun lesson ↦
      { base.lessons lesson with effectiveForms := [materialForm], groupRoster := none }
    materials := { base.materials with terms := [materialTerms] } }

private theorem materialEvidenceMatchesRoot (base : Workflow.State) (review : History)
    (holds : HoldHistory) (input : Evidence) :
    let state := materialState base review holds
    state.reviewEvidence (materialEvidence input) = materialEvidence
      { input with refundPriorPrincipals := fun form obligation query ↦
          state.redress.otherRefundPrincipals form obligation state.review query } := by
  simp [Workflow.State.reviewEvidence, materialState, materialEvidence, evidence]

theorem rootRecordsMaterialsCreditorCorrection (base : Workflow.State) (input : Evidence) :
    let before := materialState base materialBefore materialReceived
    let event := Event.recordCorrection materialForm.lesson
      (.monetary materialOriginal materialCorrection)
    Workflow.Step before (.review (materialEvidence input) event)
      { before with review := materialAfter
                    holds := materialPaid } := by
  dsimp only
  apply Workflow.Step.review
  · trivial
  · trivial
  · intro _ impossible
    cases impossible
  · rw [materialEvidenceMatchesRoot]
    let state := materialState base materialBefore materialReceived
    exact recordMaterialsCreditorCorrection (state.course materialForm.lesson.id)
      { input with refundPriorPrincipals := fun form obligation query ↦
          state.redress.otherRefundPrincipals form obligation state.review query }

theorem rootFilesMaterialsCreditorCorrection (base : Workflow.State) (input : Evidence)
    (decisions : DecisionRecords) :
    let state := materialState base materialAfter materialPaid
    let row := materialPayout input decisions
    Workflow.Step state (.review (materialEvidence input) (.fileCorrectedPayment row))
      { state with review := { materialAfter with correctedPayouts := [row] } } := by
  dsimp only
  apply Workflow.Step.review
  · trivial
  · simp [Workflow.Review.Event.readsMaterialsTerms, materialPayout, materialState]
  · intro _ same
    cases same
    exact ⟨trivial, trivial⟩
  · rw [materialEvidenceMatchesRoot]
    let state := materialState base materialAfter materialPaid
    exact Step.fileCorrectedPayment _
      (materialPayoutConforms (state.course materialForm.lesson.id)
        { input with refundPriorPrincipals := fun form obligation query ↦
            state.redress.otherRefundPrincipals form obligation state.review query } decisions)
      (by simp [materialState, materialAfter, materialBefore, reviewBefore, History.empty])

theorem rootReplaysLateRecordedMaterialsCorrection (base : Workflow.State) (input : Evidence)
    (decisions : DecisionRecords) :
    let receiptEvent := Workflow.Payment.Event.post materialPayment.paid
    let before := materialState base materialBefore { materialLedger with
      approvals := [materialApproval] }
    let received := { base with paymentRecords := base.paymentRecords ++ [receiptEvent] }
    let afterReceipt := materialState received materialBefore materialReceived
    let afterCorrection := materialState received materialAfter materialPaid
    let afterFiling := { afterCorrection with review :=
      { materialAfter with correctedPayouts := [materialPayout input decisions] } }
    Workflow.Step before (.payment receiptEvent) afterReceipt ∧
    Workflow.Step afterReceipt (.review (materialEvidence input)
      (.recordCorrection materialForm.lesson (.monetary materialOriginal materialCorrection)))
      afterCorrection ∧
    Workflow.Step afterCorrection (.review (materialEvidence input)
      (.fileCorrectedPayment (materialPayout input decisions))) afterFiling ∧
    afterFiling.holds.payments = afterReceipt.holds.payments := by
  dsimp only
  exact ⟨Workflow.Step.payment trivial
      (Workflow.Payment.Step.post _ (by decide +kernel) (by
        change materialPayment.paid.id ∉ materialLedger.payments.posted.map PostedPayment.id
        decide +kernel)),
    rootRecordsMaterialsCreditorCorrection _ input,
    rootFilesMaterialsCreditorCorrection _ input decisions, rfl⟩

theorem rootCannotFileMaterialsBeforeCorrectionIsKnown (base : Workflow.State) (input : Evidence)
    (decisions : DecisionRecords) (next : Workflow.State) :
    let state := materialState base materialAfter materialPaid
    let row := { materialPayout input decisions with recordedAt := day 17 }
    ¬Workflow.Step state (.review (materialEvidence input) (.fileCorrectedPayment row)) next := by
  dsimp only
  intro step
  cases step with
  | review _ _ _ linked =>
    cases linked with
    | fileCorrectedPayment row checked _ =>
      obtain ⟨_, _, _, _, selected, _⟩ := checked
      change _ ∈ materialAfter.correctedScopeAt materialCorrection (day 17) at selected
      rw [materialsFilingUsesDecisionTimeAndAvailableEvidence.2.2.2.1] at selected
      contradiction

theorem rootCannotFilePaymentBeforeCorrectionTakesEffect
    {before after : Workflow.State} {evidence : Evidence} {row : CorrectedPayout}
    (future : ¬row.correction.finding.decidedAt.by row.payment.paid.instruction.atTime) :
    ¬Workflow.Step before (.review evidence (.fileCorrectedPayment row)) after := by
  intro step
  cases step with
  | review _ _ _ linked =>
    cases linked with
    | fileCorrectedPayment _ checked _ =>
      obtain ⟨_, _, _, _, _, posted⟩ := checked
      obtain ⟨_, _, _, _, _, _, _, actual, _⟩ := posted
      exact actual.elim (fun ordinary ↦ future ordinary.2.1) (fun refund ↦ future refund.2.1)

theorem authoriseMaterialsCreditorCorrection (base : StartEvidence) (input : Evidence)
    (decisions : DecisionRecords) :
    (materialPayout input decisions).authorised materialAfter (materialEvidence input)
      (materialStart base) materialPaid := by
  unfold CorrectedPayout.authorised
  dsimp only [materialPayout, payout]
  rw [materialPaidKnownAtFiling]
  refine ⟨materialPayoutConforms base input decisions, materialScope,
    materialsReceiptsFollowExactCreditorAndPortion.1, [], rfl, materialAdditionalReceipt base, ?_, rfl,
    ?_, ?_⟩
  · simp [CurrentLessonFunds.validFor, FundingEntry.valid, FundingEntry.available, materialForm, form]
    all_goals decide +kernel
  · change (⟨42, 10, day 17, [⟨90, .providerFunds, .spendable, 8, 0, 8⟩]⟩ :
      CurrentLessonFunds).covers 8
    unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
    decide +kernel
  · refine ⟨⟨by simp [materialPaid, HoldHistory.withPartRevision, materialReceived], rfl⟩,
      by decide +kernel, ?_, ?_⟩
    · simp only [PaymentApprovalRoute.allows]
      refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, trivial, by decide +kernel, ?_, ?_, ?_,
        by decide +kernel⟩
      · change materialNew ∈ [materialNew] ∧
          ([materialNew].map PaymentPart.ref).Nodup ∧
          ∀ p ∈ [materialNew], p.ref.lesson = materialNew.ref.lesson ∧
            p.ref.purpose = materialNew.ref.purpose ∧ 0 < p.amount
        simp [materialNew]
        decide +kernel
      · simp [HoldHistory.approvalRecorded, HoldHistory.withPartRevision, materialPaid,
          materialReceived]
      · simp [PaymentApproval.authorisedAtGrant, materialAfter, History.authorities,
          materialEvidence, materialAuthority, materialApproval]
      · simp [PaymentApproval.validAt, materialApproval]
        decide +kernel
      · refine ⟨⟨materialNew.ref, .person 202, 10, none⟩, by simp [materialApproval], rfl,
          rfl, by simp, ?_⟩
        decide +kernel
      · refine ⟨rfl, Or.inl rfl, by decide +kernel, by decide +kernel, ?_, ?_⟩
        · unfold PaymentHistory.distinctReceipts
          decide +kernel
        · simp [PaymentHistory.validReturns, HoldHistory.withPartRevision, materialPaid,
            materialReceived, materialLedger, holds, materialPayment, paidToOld, paidToNewOnOldRef,
            unrelatedMaterialPayment, paidOnOtherPortion, materialReceipt, sumAmounts]
          all_goals decide +kernel
      · simp [HoldHistory.distinctFormalDecisions, HoldHistory.withPartRevision,
          materialPaid, materialReceived, materialLedger, holds]
      · simp [HoldHistory.paymentOnHold, HoldHistory.formalInForce, HoldHistory.validFormalHold,
          HoldHistory.temporaryInForce, HoldHistory.withPartRevision, materialPaid,
          materialReceived, materialLedger, holds]
      · simp [HoldHistory.paymentHoldScopeUnresolved, HoldHistory.validFormalHold,
          HoldHistory.withPartRevision, materialPaid, materialReceived, materialLedger, holds]
    · simp [HoldHistory.paymentReleasedAt, HoldHistory.releasesPart, HoldHistory.validFormalHold,
        HoldHistory.withPartRevision, materialPaid, materialReceived, materialLedger, holds]

/-- Even an independently supplied reviewed amount cannot revise a different obligation. -/
theorem differentMaterialsClaimCannotBeRecorded (base : StartEvidence) (input : Evidence)
    (original : OriginalRecord) (revision : PaymentCorrectionCase)
    (different : revision.originalPart.ref.sameCorrectionClaim revision.money.corrected.ref = false) :
    ¬ ∃ next, Step input base materialLedger materialBefore
        (.recordCorrection materialForm.lesson (.monetary original revision)) next := by
  rintro ⟨_, step⟩
  cases step with
  | recordMonetary =>
    rename_i linked
    obtain ⟨_, _, recorded⟩ := linked
    obtain ⟨_, _, _, _, _, same, _⟩ := recorded.1
    rw [different] at same
    contradiction

theorem distinctMaterialsReferencesDoNotMatch :
    materialOld.ref.sameCorrectionClaim { materialNew.ref with obligation := 17 } = false ∧
    materialOld.ref.sameCorrectionClaim
      { materialNew.ref with purpose := .materialsShare 98 202 } = false ∧
    let prior := { materialOld.ref with purpose := .materialsShortfall 97 201 "claim-1" }
    let next := { materialNew.ref with purpose := .materialsShortfall 97 202 "claim-1" }
    prior.sameCorrectionClaim next = true ∧
    prior.sameCorrectionClaim { next with purpose := .materialsShortfall 97 202 "claim-2" } = false ∧
    prior.sameCorrectionClaim materialNew.ref = false := by
  decide +kernel

theorem materialsRevisionKeepsTheWholePortionTrail :
    let retained : OriginalRecord :=
      ⟨⟨materialMatter, materialFinding.outcome, 60, materialFinding.decidedAt⟩, some materialNew⟩
    let latestPart : PaymentPart :=
      ⟨⟨42, 12, 5, .materialsShare 97 203⟩, .person 203 none, 9⟩
    let latest : PaymentCorrectionCase :=
      ⟨materialNew, { materialFinding with reviewer := 61, decidedAt := day 16, outcome := 74 },
        ⟨42, 73, 74, 30, day 20, [201, 202, 203]⟩, ⟨latestPart, day 16, []⟩⟩
    let history : History :=
      { materialAfter with
        originals := materialAfter.originals ++ [retained]
        corrections := .monetary retained latest :: materialAfter.corrections }
    let scope : CorrectedMonetaryScope :=
      ⟨⟨latestPart, [materialNew, materialOld]⟩,
        [⟨latestPart, [materialNew, materialOld]⟩, ⟨otherOldHolderPortion, []⟩,
          ⟨otherNewHolderPortion, []⟩],
        14, 9⟩
    history.correctedScopeAt latest (day 21) = some scope := by
  decide_cbv

theorem independentHolderPortionCannotReplaceExactOriginal :
    let mistaken := { materialCorrection with originalPart := otherOldHolderPortion }
    let history : History := { materialBefore with
      corrections := [.monetary materialOriginal mistaken] }
    history.correctedScopeAt mistaken (day 17) (knownAt := day 18) = none := by
  decide +kernel

#print axioms materialsRevisionKeepsTheWholePortionTrail
#print axioms independentHolderPortionCannotReplaceExactOriginal
#print axioms recordMaterialsCreditorCorrection
#print axioms materialsReceiptsFollowExactCreditorAndPortion
#print axioms materialsFilingUsesDecisionTimeAndAvailableEvidence
#print axioms rootRecordsMaterialsCreditorCorrection
#print axioms rootFilesMaterialsCreditorCorrection
#print axioms rootReplaysLateRecordedMaterialsCorrection
#print axioms rootCannotFileMaterialsBeforeCorrectionIsKnown
#print axioms rootCannotFilePaymentBeforeCorrectionTakesEffect
#print axioms authoriseMaterialsCreditorCorrection
#print axioms differentMaterialsClaimCannotBeRecorded
#print axioms distinctMaterialsReferencesDoNotMatch

#print axioms recordedAtAdoption
#print axioms laterReceiptsWereAbsentFromAdoptionSnapshot
#print axioms laterProperReceiptReducesTheBalance
#print axioms correctedPayoutAfterLateReceipts
#print axioms splitRefundFilesAfterSiblingReceipt
#print axioms rootFilesSplitCorrectedRefund
#print axioms renumberedRefundCountsPriorReceiptAndItsReturn
#print axioms renumberedPortionCannotSpendSiblingBalance
#print axioms correctedOverrefundRecordedWithoutPayoutAuthority
#print axioms conflictingRenumberingLeavesNoOperativeScope

end SourceV14.FidelityCorrectionChecks
