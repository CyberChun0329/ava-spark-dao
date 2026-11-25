import SourceV14.Workflow

/-! Dated gross attribution and the actual Direct root interface. -/

namespace SourceV14.M2Checks

open Workflow.Materials

private def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩
private def lesson : Lesson := ⟨42, .group, 10, 20, 30, 60⟩
private def placeA : Place := ⟨1, lesson.id, 40, 50, 60, 70, 50, 50⟩
private def placeB : Place := { placeA with id := 2, student := 41, account := 51 }
private def mat : MaterialId := 7
private def atA (amount : Amount) : MaterialsCharge := ⟨placeA.id, mat, amount⟩
private def atB (amount : Amount) : MaterialsCharge := ⟨placeB.id, mat, amount⟩

private def original : MaterialsSettlementRecord :=
  ⟨lesson.id, mat, "agreed terms", "original", 10, tick 5, [placeA.id, placeB.id], [atA 4]⟩

private def supplement : MaterialsShortfall :=
  ⟨lesson.id, mat, "agreed terms", original.reference, "previous supplement", 11, tick 7,
    [atA 1, atB 0]⟩

private def newRow (atTime : Moment) : MaterialsShortfall :=
  { supplement with reference := "new supplement", obligation := 12, identifiedAt := atTime }

private def matter : ReviewMatter := ⟨31, lesson.id, [100, 101]⟩

private def paymentPart (obligation : ObligationId) (purpose : PaymentPurpose) (amount : Amount) :
    PaymentPart :=
  ⟨⟨lesson.id, obligation, 1, purpose⟩, .person 100 none, amount⟩

private def correction (old new : PaymentPart) : PaymentCorrectionCase :=
  ⟨old, ⟨matter, 60, tick 8, "Replace the reviewed principal", 92, true⟩,
    ⟨lesson.id, 90, 92, lesson.coordinator, tick 9, [100, 101]⟩, ⟨new, tick 8, []⟩⟩

private def oldPart : PaymentPart :=
  paymentPart original.obligation (.materialsShare mat 100) 4

private def increased : PaymentCorrectionCase :=
  correction oldPart { oldPart with amount := 5 }

private def decreased : PaymentCorrectionCase :=
  correction oldPart { oldPart with amount := 3 }

private def holderOnly : PaymentCorrectionCase :=
  correction oldPart { oldPart with
    ref := { oldPart.ref with purpose := .materialsShare mat 101 }
    recipient := .person 101 none }

private def supplementIncrease : PaymentCorrectionCase :=
  let part := paymentPart supplement.obligation (.materialsShortfall mat 100 supplement.reference) 1
  correction part { part with amount := 2 }

private def useA (checkedAt : Moment) (reference : String) : ConfirmedMaterialUse :=
  ⟨lesson.id, placeA.id, mat, 1, tick 2, lesson.coordinator, checkedAt, .lessonRecord reference⟩

private def factualRecheck : ConfirmedMaterialUse :=
  { useA (tick 11) "additional material changes the verified combination" with material := 8 }

private def grossEvidence
    (scope : MaterialsChargeScope) (review : PaymentCorrectionCase) (previousA revisedA : Amount)
    (revisedB : Option Amount := some 0) (availableAt : Moment := tick 9) :
    MaterialsGrossEvidence where
  atPlace := fun source adopted place ↦
    if source = scope ∧ adopted = review then
      if place = placeA.id then some ⟨availableAt, previousA, revisedA⟩
      else if place = placeB.id then revisedB.map (fun amount ↦ ⟨availableAt, 0, amount⟩)
      else none
    else none
  supportsLaterUse := fun source adopted finding ↦
    decide (source = scope ∧ adopted = review ∧ finding.checkedAt = factualRecheck.checkedAt ∧
      finding.material = factualRecheck.material ∧
      finding.evidence.reference = factualRecheck.evidence.reference)

private def reviewedOnly (review : PaymentCorrectionCase) : MaterialsPrincipalContext :=
  { corrections := [review] }

private def resolvedIncrease : MaterialsPrincipalContext :=
  ⟨[increased], grossEvidence original.chargeScope increased 4 5⟩

private def resolvedDecrease : MaterialsPrincipalContext :=
  ⟨[decreased], grossEvidence original.chargeScope decreased 4 3⟩

theorem adoptedIncreasedGrossPreventsANewChargeForTheSameFive :
    (newRow (tick 12)).newCharges original [] [atA 5] = [atA 1] ∧
    (newRow (tick 12)).newCharges original [] [atA 5] resolvedIncrease = [atA 0] ∧
    original.charges = [atA 4] := by
  constructor
  · decide +kernel
  · exact ⟨by decide +kernel, rfl⟩

private def pendingAtAEvidence : MaterialsGrossEvidence where
  atPlace := fun scope review place ↦
    if scope = original.chargeScope ∧ review = increased ∧ place = placeB.id then
      some ⟨tick 9, 0, 0⟩
    else none

private def pendingAtA : MaterialsPrincipalContext :=
  ⟨[increased], pendingAtAEvidence⟩

theorem pendingDoesNotSwallowAPlaceWithVerifiedUnchangedGross :
    (newRow (tick 12)).newCharges original [] [atA 5, atB 1] pendingAtA = [atA 0, atB 1] ∧
    pendingAtA.chargeAt original.chargeScope (atA 4) (tick 12) = (atA 4, true) := by
  constructor <;> decide +kernel

theorem anOriginalPlaceWithNoHistoricalChargeCanHaveReviewedGross :
    let attributed : MaterialsPrincipalContext :=
      ⟨[increased], grossEvidence original.chargeScope increased 4 4 (some 1)⟩
    (newRow (tick 12)).newCharges original [] [atA 4, atB 1] attributed = [atA 0, atB 0] ∧
    (newRow (tick 12)).newCharges original [] [atB 1] (reviewedOnly increased) = [atB 0] ∧
    (reviewedOnly increased).chargeAt original.chargeScope (atB 0) (tick 12) = (atB 0, true) := by
  dsimp only
  constructor <;> first | decide +kernel | (constructor <;> decide +kernel)

theorem originalAmountPersistsUntilTheCorrectionAndTheAttributionAreAvailable :
    (newRow (tick 8)).newCharges original [] [atA 5] resolvedIncrease = [atA 1] ∧
    let attribution := grossEvidence original.chargeScope increased 4 5 (availableAt := tick 11)
    let effective := { resolvedIncrease with gross := attribution }
    effective.chargeAt original.chargeScope (atA 4) (tick 10) = (atA 4, true) ∧
    effective.chargeAt original.chargeScope (atA 4) (tick 11) = (atA 5, false) := by
  constructor
  · decide +kernel
  · dsimp only
    constructor <;> decide +kernel

theorem scopeAndAdoptionMatterAndHolderRedistributionDoesNotChangeGross :
    let wrongTerms := { original with termsReference := "different agreement" }
    resolvedIncrease.chargeAt wrongTerms.chargeScope (atA 4) (tick 12) = (atA 4, true) ∧
    let noAdoption := { resolvedIncrease with corrections := [] }
    noAdoption.chargeAt original.chargeScope (atA 4) (tick 12) = (atA 4, false) ∧
    (reviewedOnly holderOnly).chargeAt original.chargeScope (atA 4) (tick 12) =
      (atA 4, false) := by
  dsimp only
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

theorem aReductionDoesNotResurrectStaleOrIncompatibleVerifiedUse :
    resolvedDecrease.chargeAt original.chargeScope (atA 4) (tick 12) = (atA 3, false) ∧
    (newRow (tick 12)).newCharges original [] [atA 5, atB 1] resolvedDecrease
      [{ factualRecheck with checkedAt := tick 6 }] = [atA 0, atB 1] ∧
    (newRow (tick 12)).newCharges original [] [atA 5] resolvedDecrease
      [useA (tick 11) "unrelated recheck"] = [atA 0] ∧
    (newRow (tick 12)).newCharges original [] [atA 5] resolvedDecrease [factualRecheck] =
      [atA 2] := by
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · constructor <;> decide +kernel

theorem aReviewCanAttributeAnEarlierSupplementIncludingAFormerZero :
    let revised : MaterialsPrincipalContext :=
      ⟨[supplementIncrease], grossEvidence supplement.chargeScope supplementIncrease 1 2⟩
    let atFormerZero : MaterialsPrincipalContext :=
      ⟨[supplementIncrease], grossEvidence supplement.chargeScope supplementIncrease 1 1 (some 1)⟩
    (newRow (tick 12)).newCharges original [supplement] [atA 7, atB 1] revised =
      [atA 1, atB 1] ∧
    (newRow (tick 12)).newCharges original [supplement] [atA 5, atB 1] atFormerZero =
      [atA 0, atB 0] ∧
    let wrongClaim := { supplement with reference := "another supplement" }
    revised.chargeAt wrongClaim.chargeScope (atA 1) (tick 12) = (atA 1, false) := by
  dsimp only
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

/-- The old supplement omitted B, but the adopted amount correction can still affect it. -/
theorem omittedSupplementPlaceAwaitsAttribution :
    let omitted := { supplement with charges := [atA 1] }
    let future := newRow (tick 12)
    let checked := [atB 1]
    let prior := [omitted]
    future.newCharges original prior checked = [atB 1] ∧
    future.newCharges original prior checked (reviewedOnly supplementIncrease) = [atB 0] ∧
    future.newCharges original prior checked
        ⟨[supplementIncrease], grossEvidence omitted.chargeScope supplementIncrease 1 2⟩ =
      [atB 1] ∧
    future.newCharges original prior checked
        ⟨[supplementIncrease], grossEvidence omitted.chargeScope supplementIncrease 1 1 (some 1)⟩ =
      [atB 0] := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private def authority : ReviewAuthorities where
  corePartner := fun actor _ ↦ actor = lesson.provider
  initialFinding := fun _ _ _ ↦ False
  reviewer := fun subject actor _ ↦ subject = matter ∧ actor = 60
  approvesPayment := fun _ _ _ ↦ False
  interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
  originalDecisionMaker := fun _ ↦ none
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

private def useB : ConfirmedMaterialUse :=
  { useA (tick 4) "second place verified" with place := placeB.id }

private def use : VerifiedMaterialsUse where
  lesson := lesson
  startedAt := tick 2
  endedAt := tick 3
  tutorReport := none
  authority := ⟨authority, fun _ ↦ matter, fun _ ↦ none⟩
  places := [placeA, placeB]
  deliveryReports := []
  findings := [useA (tick 4) "original place verified", useB]
  verifiesEvidence := fun _ ↦ True
  verifiedReportOmission := fun _ ↦ False
  uniquePlaces := by decide
  placeInLesson := by simp [Place.matches, placeB, placeA]
  findingInLesson := by simp [useA, useB]
  findingAtPlace := by simp [useA, useB]

private def terms : MaterialsTerms where
  lesson := lesson.id
  adoptedBy := lesson.provider
  agreedAt := tick 0
  agreementReference := original.termsReference
  accountingAndPaymentParty := lesson.provider
  materialsOrBundle := "lesson materials"
  contact := "coordinator"
  licensedUse := (· = mat)
  sharesAndAdjustmentsReference := "shares"
  sharesInForce := fun _ _ ↦ some ⟨"shares", [100], fun _ _ base ↦ base⟩
  contributors := fun _ ↦ [100]
  consents := [⟨mat, 100, original.termsReference, tick 0⟩]
  ordinaryShareTime := fun _ _ firstUse _ ↦ firstUse
  paymentDue := tick 20
  paymentDeadline := tick 20
  pricing := .standardBundle [⟨mat, 1 / 10⟩]

private def check : UseCheck := ⟨use, terms, none, tick 4⟩
private def settlement : Settlement := ⟨original, check⟩
private def materials : History := { originals := [settlement], useChecks := [check] }

private def bounded : MaterialsPrincipalContext :=
  { reviewedOnly increased with gross := {
      upperBound := fun scope revisions ↦
        if scope = original.chargeScope ∧ revisions = [increased] then some (tick 9, 5)
        else none } }

theorem capUsesVerifiedWholeScopeEvenWhilePlaceAttributionIsPending :
    ¬ materials.combinedCapAllows lesson.id [atB 1] (tick 12) (reviewedOnly increased) ∧
    materials.combinedCapAllows lesson.id [atB 5] (tick 12) bounded ∧
    ¬ materials.combinedCapAllows lesson.id [atB 6] (tick 12) bounded ∧
    materials.combinedCapAllows lesson.id [atB 5] (tick 12) resolvedIncrease ∧
    ¬ materials.combinedCapAllows lesson.id [atB 6] (tick 12) resolvedIncrease := by
  unfold History.combinedCapAllows
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · constructor
      · decide +kernel
      · constructor <;> decide +kernel

private def old : Workflow.Review.OriginalRecord :=
  ⟨⟨matter, 90, 50, tick 5⟩, some oldPart⟩

private def reviewBefore : Workflow.Review.History :=
  { Workflow.Review.History.empty with
    originals := [old]
    appointments := [⟨matter, lesson.provider, 60, tick 6⟩]
    reviewFindings := [increased.finding] }

private def reviewAfter : Workflow.Review.History :=
  { reviewBefore with corrections := [.monetary old increased] }

private def noHolds : HoldHistory :=
  { payments := ⟨[], [], []⟩, temporary := [], formal := [], lifts := [] }

private def evidence (input : Workflow.Review.Evidence) : Workflow.Review.Evidence :=
  { input with
    authority := authority
    originalOutcome := (· = old.outcome)
    recordedAmount := fun subject ref part ↦
      subject = matter ∧ ref = increased.finding.outcome ∧ part = increased.money.corrected
    reviewedFaultRefund := fun _ ↦ none }

private def rootBefore (base : Workflow.State) : Workflow.State :=
  { base with
    holds := noHolds
    review := reviewBefore
    materials := materials
    verifiedMaterialsGross := resolvedIncrease.gross }

private def recordReview : Workflow.Review.Event :=
  .recordCorrection lesson (.monetary old increased)

private def rootAfter (base : Workflow.State) : Workflow.State :=
  { rootBefore base with review := reviewAfter, holds := noHolds.withPartRevision old.outcome increased }

theorem aLegalRootReviewSuppliesTheEffectiveGrossAndPreservesTheOriginal
    (base : Workflow.State) (input : Workflow.Review.Evidence) :
    Workflow.Step (rootBefore base) (.review (evidence input) recordReview) (rootAfter base) ∧
    (rootAfter base).materials.originals = (rootBefore base).materials.originals ∧
    (newRow (tick 12)).newCharges original [] [atA 5] (rootAfter base).materialsPrincipalContext =
      [atA 0] := by
  refine ⟨?_, rfl, ?_⟩
  · apply Workflow.Step.review
    · trivial
    · trivial
    · intro row impossible
      cases impossible
    apply Workflow.Review.Step.recordMonetary
    · simp [rootBefore, reviewBefore]
    · simp [rootBefore, reviewBefore, increased]
    · exact ⟨rfl, rfl, rfl⟩
    · refine ⟨[oldPart], ?_, ?_⟩
      · dsimp only [rootBefore]
        decide +kernel
      simp +contextual [PaymentCorrectionCase.recorded, PaymentCorrectionCase.outcomeConforms,
        correctionAfterReviewConforms, correctionRecordConforms, reviewFindingConforms,
        reviewFindingConformsWithContacts, ReviewAppointment.applies, independentReviewer,
        ReviewAuthorities.disinterested, DirectInterest.affected, ReviewAuthorities.mayDecideDispute,
        ReviewMatter.sameCase, Workflow.Review.History.authorities, Workflow.State.reviewEvidence,
        rootBefore, reviewBefore, Workflow.Review.History.empty, evidence, authority,
        correction, increased, old, oldPart, paymentPart, matter, lesson, original,
        PaymentPartRef.sameCorrectionClaim, PaymentPart.matchesMaterialsCreditor,
        PaymentCorrectionCase.priorMaterialsRefs, PaymentPurpose.isMaterialsShare,
        correctionActualPaymentsRecorded, correctionActualPaymentsRetained,
        PaymentHistory.distinctReceipts, PaymentHistory.validReturns, noHolds]
      all_goals (repeat' apply And.intro) <;> first | rfl | decide +kernel
    · simp [Workflow.Review.History.paymentCorrections, rootBefore, reviewBefore,
        Workflow.Review.History.empty]
  · change (newRow (tick 12)).newCharges original [] [atA 5] resolvedIncrease = [atA 0]
    decide +kernel

theorem rootShortfallUsesTheEffectiveBasis {s next : Workflow.State}
    {lessonId : LessonId} {row : Shortfall}
    (step : Workflow.Step s (.materials lessonId (.identifyShortfall row)) next) :
    row.conforms (s.materials.shortfalls.map Shortfall.record) s.materialsPrincipalContext := by
  cases step with
  | materials _ _ localStep _ =>
    cases localStep with
    | identifyShortfall _ _ computed _ _ _ _ _ => exact computed

private def estimate : Operations.PendingMaterialsShare :=
  ⟨lesson.id, placeA.id, mat, original.termsReference, tick 1,
    ⟨false, false, false, false⟩, 6⟩

private def fundsAt (amount : Amount) (point : Moment) : CurrentLessonFunds :=
  ⟨lesson.id, lesson.provider, point, [⟨100, .providerFunds, .spendable, amount, 0, amount⟩]⟩

private def individualPayment (id : Nat) (principal : Amount) (point : Moment) :
    PostedPayment :=
  ⟨id, ⟨oldPart.ref, .person 100, lesson.coordinator, principal, point⟩, some id⟩

private def originalEntitlement : Entitlement :=
  ⟨settlement, none, 100, 4, tick 6, lesson.provider,
    { originalReference := 50
      agreedSharesAt := fun _ ↦ none
      verifiedOriginal := fun _ _ _ ↦ True }⟩

private def oldCash : PostedPayment := individualPayment 1 4 (tick 7)

private def oldCashHistory : History :=
  { materials with
    entitlements := [originalEntitlement]
    receipts := [⟨oldCash, fundsAt 4 (tick 7), tick 7, some (tick 7)⟩] }

private def ledger : PaymentHistory := ⟨[oldCash], [], []⟩

theorem aHistoricalFourCannotDischargeAReviewedFive :
    oldCashHistory.paidOriginalCharge ledger estimate (tick 12) = true ∧
    oldCashHistory.paidOriginalCharge ledger estimate (tick 12) resolvedIncrease = false := by
  constructor <;> decide +kernel

#print axioms adoptedIncreasedGrossPreventsANewChargeForTheSameFive
#print axioms pendingDoesNotSwallowAPlaceWithVerifiedUnchangedGross
#print axioms anOriginalPlaceWithNoHistoricalChargeCanHaveReviewedGross
#print axioms originalAmountPersistsUntilTheCorrectionAndTheAttributionAreAvailable
#print axioms scopeAndAdoptionMatterAndHolderRedistributionDoesNotChangeGross
#print axioms aReductionDoesNotResurrectStaleOrIncompatibleVerifiedUse
#print axioms aReviewCanAttributeAnEarlierSupplementIncludingAFormerZero
#print axioms omittedSupplementPlaceAwaitsAttribution
#print axioms capUsesVerifiedWholeScopeEvenWhilePlaceAttributionIsPending
#print axioms aLegalRootReviewSuppliesTheEffectiveGrossAndPreservesTheOriginal
#print axioms rootShortfallUsesTheEffectiveBasis
#print axioms aHistoricalFourCannotDischargeAReviewedFive

end SourceV14.M2Checks
