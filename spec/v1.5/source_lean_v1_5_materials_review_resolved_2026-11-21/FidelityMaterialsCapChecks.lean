import SourceV14.Workflow

/-! §5.3. Two materials for one place, independent partial checks and later shortfalls. -/

namespace SourceV14.FidelityMaterialsCapChecks

open SourceV14.Workflow.Materials

private def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩
private def lesson : Lesson := ⟨42, .oneToOne, 10, 20, 30, 60⟩
private def place : Place := ⟨1, lesson.id, 40, 50, 60, 70, 100, 100⟩
private def first : MaterialId := 7
private def second : MaterialId := 8
private def omitted : MaterialId := 9
private def another : MaterialId := 10

private def coordinator : MaterialsUseAuthority where
  authorities :=
    { corePartner := fun _ _ ↦ False
      initialFinding := fun _ _ _ ↦ False
      reviewer := fun _ _ _ ↦ False
      approvesPayment := fun _ _ _ ↦ False
      interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
      originalDecisionMaker := fun _ ↦ none
      originalSettlementProposers := fun _ ↦ []
      originalSettlementApprovers := fun _ ↦ [] }
  matterFor := fun _ ↦ ⟨1, lesson.id, [1]⟩
  recusalFor := fun _ ↦ none

private def useFinding (material : MaterialId) : ConfirmedMaterialUse :=
  let order := if material = first then 1 else if material = second then 3
    else if material = omitted then 5 else 7
  ⟨lesson.id, place.id, material, 1, ⟨2, order⟩, lesson.coordinator, tick 4,
    .lessonRecord "record of actual use"⟩

private def used (materials : List MaterialId) : VerifiedMaterialsUse where
  lesson := lesson
  startedAt := tick 2
  endedAt := tick 3
  tutorReport := none
  authority := coordinator
  places := [place]
  deliveryReports := []
  findings := materials.map useFinding
  verifiesEvidence := fun finding ↦ finding ∈ materials.map useFinding
  verifiedReportOmission := fun _ ↦ False
  uniquePlaces := by simp
  placeInLesson := by simp [Place.matches, place]
  findingInLesson := by
    intro finding seen
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp seen
    rfl
  findingAtPlace := by
    intro finding seen
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp seen
    exact List.Mem.head []

private def terms (pricing : MaterialsPricing) : MaterialsTerms where
  lesson := lesson.id
  adoptedBy := lesson.provider
  agreedAt := tick 0
  agreementReference := "materials terms"
  accountingAndPaymentParty := lesson.provider
  materialsOrBundle := "teaching materials"
  contact := "coordinator"
  licensedUse := fun m ↦ m ∈ pricing.materials
  sharesAndAdjustmentsReference := "original shares"
  sharesInForce := fun _ _ ↦ some ⟨"one contributor", [1], fun _ _ base ↦ base⟩
  contributors := fun _ ↦ [1]
  consents := [first, second, omitted, another].map (fun m ↦ ⟨m, 1, "materials terms", tick 0⟩)
  ordinaryShareTime := fun _ _ firstUse _ ↦ firstUse
  paymentDue := tick 20
  paymentDeadline := tick 20
  pricing := pricing

private def check (pricing : MaterialsPricing) (materials : List MaterialId)
    (checkedAt : Moment := tick 4) : UseCheck where
  use := used materials
  terms := terms pricing
  advanceCheck := match pricing with
    | .standardBundle _ => none
    | .otherCombination .. => some
        ⟨lesson.id, "materials terms", tick 1, [(used materials).combination], false, []⟩
  checkedAt := checkedAt

private theorem singleChargePlace (pricing : MaterialsPricing) (materials : List MaterialId)
    (m : MaterialId) :
    ∀ charge ∈ (used materials).chargesFor (terms pricing) m, charge.place ∈ [place.id] := by
  cases pricing <;> intro charge present <;>
    simp [VerifiedMaterialsUse.chargesFor, VerifiedMaterialsUse.charges, terms,
      MaterialsPricing.charges, VerifiedMaterialsUse.combination, used,
      MaterialsPricing.chargesAt] at present
  all_goals
    obtain ⟨_, _, rfl⟩ := present.1
    exact List.Mem.head []

private def original (pricing : MaterialsPricing) (materials : List MaterialId)
    (m : MaterialId) (ref : String) (id : ObligationId) : Settlement :=
  let basis := check pricing materials
  ⟨⟨lesson.id, m, (terms pricing).agreementReference, ref, id, tick 5, [place.id],
    basis.use.chargesFor basis.terms m⟩, basis⟩

private theorem originalConforms (pricing : MaterialsPricing) (materials : List MaterialId)
    (m : MaterialId) (ref : String) (id : ObligationId) (named : ref ≠ "") :
    (original pricing materials m ref id).conforms := by
  exact ⟨rfl, rfl, named, (by decide : (tick 3).before (tick 5)),
    (by decide : (tick 4).by (tick 5)), by simp [original], rfl,
    singleChargePlace pricing materials m⟩

private def ordinaryPricing : MaterialsPricing :=
  .standardBundle [⟨first, 3 / 50⟩, ⟨second, 1 / 25⟩]

private def ordinaryFirst := original ordinaryPricing [first, second] first "first settlement" 1
private def ordinarySecond := original ordinaryPricing [first, second] second "second settlement" 2
private def ordinaryBase : History :=
  { terms := [terms ordinaryPricing], useChecks := [check ordinaryPricing [first, second]] }
private def ordinaryAfterFirst : History := { ordinaryBase with originals := [ordinaryFirst] }

private theorem ordinaryPriced :
    (terms ordinaryPricing).calculatesVerifiedUse (used [first, second]) none (tick 5) := by
  simp [MaterialsTerms.calculatesVerifiedUse, MaterialsTerms.adoptedFor, MaterialsTerms.agreedBy,
    MaterialsTerms.covers, MaterialsPricing.covers, MaterialsPricing.materials,
    VerifiedMaterialsUse.verifiedBy, MaterialsUseAuthority.mayCheck,
    ReviewAuthorities.disinterested, DirectInterest.affected, coordinator,
    VerifiedMaterialsUse.combination, VerifiedMaterialsUse.materialsAt, used, useFinding,
    materialsCombinationWithinCap, materialsCapBase, MaterialsPricing.charges,
    MaterialsPricing.chargesAt, StandardMaterialsBundle, materialsCapRate, sumAmounts,
    ordinaryPricing, terms, lesson, place, first, second, omitted, another, tick, Moment.before,
    Moment.by]
  all_goals decide +kernel

theorem twoOrdinaryMaterialsCanSettleAtTheCombinedCap
    (ev : Course.StartEvidence) (holds : HoldHistory) :
    Step ev holds ordinaryBase (.settle ordinaryFirst) ordinaryAfterFirst ∧
    Step ev holds ordinaryAfterFirst (.settle ordinarySecond)
      { ordinaryAfterFirst with originals := [ordinarySecond, ordinaryFirst] } := by
  refine ⟨.settle ?_ ?_ ordinaryPriced ?_ ?_, .settle ?_ ?_ ordinaryPriced ?_ ?_⟩
  · exact List.Mem.head []
  · exact originalConforms _ _ _ _ _ (by decide)
  · unfold History.combinedCapAllows
    decide +kernel
  · simp [ordinaryBase]
  · exact List.Mem.head []
  · exact originalConforms _ _ _ _ _ (by decide)
  · unfold History.combinedCapAllows
    decide +kernel
  · intro prior saved _ sameMaterial
    obtain rfl := List.mem_singleton.mp saved
    exact (show first ≠ second from by decide) sameMaterial |>.elim

private def splitPricing : MaterialsPricing := .otherCombination [first, second] (fun _ _ _ _ ↦ 6)
private def splitFirst := original splitPricing [first] first "first partial settlement" 1
private def splitSecond := original splitPricing [second] second "second partial settlement" 2
private def prospective (pricing : MaterialsPricing) (materials : List MaterialId)
    (checkedAt : Moment) (reference : String) (adjustments : List MaterialsAdjustment := [])
    (consents : List MaterialsConsent := []) : CombinationCheck :=
  ⟨lesson, checkedAt, checkedAt, reference,
    [[⟨terms pricing, [⟨place, materials⟩], adjustments, consents⟩]],
    fun _ _ _ _ ↦ True⟩

private def firstPlan (pricing : MaterialsPricing) : CombinationCheck :=
  prospective pricing [first] (tick 1) "first plan"

private def splitChecks : History :=
  { terms := [terms splitPricing]
    useChecks := [splitFirst.check, splitSecond.check]
    combinationChecks := [firstPlan splitPricing,
      prospective splitPricing [second] ⟨2, 2⟩ "second plan"] }

private theorem splitChecksPass :
    splitFirst.check.terms.calculatesVerifiedUse splitFirst.check.use
      splitFirst.check.advanceCheck splitFirst.check.checkedAt ∧
    splitSecond.check.terms.calculatesVerifiedUse splitSecond.check.use
      splitSecond.check.advanceCheck splitSecond.check.checkedAt := by
  constructor <;>
    simp [splitFirst, splitSecond, original, check, used, useFinding, splitPricing, terms,
      MaterialsTerms.calculatesVerifiedUse, MaterialsTerms.adoptedFor, MaterialsTerms.agreedBy,
      MaterialsTerms.covers, MaterialsPricing.covers, MaterialsPricing.materials,
      MaterialsTerms.nonstandardUseAllowed, VerifiedMaterialsUse.verifiedBy,
      MaterialsUseAuthority.mayCheck, ReviewAuthorities.disinterested, DirectInterest.affected,
      coordinator, VerifiedMaterialsUse.combination, VerifiedMaterialsUse.materialsAt,
      materialsCombinationWithinCap, materialsCapBase, MaterialsPricing.charges,
      MaterialsPricing.chargesAt, materialsCapRate, sumAmounts, lesson, place,
      first, second, omitted, another, tick, Moment.before, Moment.by]
  all_goals decide +kernel

theorem individualChecksDoNotAuthorizeTheKnownCombination
    (ev : Course.StartEvidence) (holds : HoldHistory) (next : History) :
    splitFirst.check.terms.calculatesVerifiedUse splitFirst.check.use
      splitFirst.check.advanceCheck splitFirst.check.checkedAt ∧
    splitSecond.check.terms.calculatesVerifiedUse splitSecond.check.use
      splitSecond.check.advanceCheck splitSecond.check.checkedAt ∧
    ¬ Step ev holds splitChecks (.settle splitFirst) next := by
  refine ⟨splitChecksPass.1, splitChecksPass.2, ?_⟩
  intro accepted
  cases accepted with
  | settle _ _ pricing _ _ =>
    simp [History.pricingAvailable, History.checkedNonstandardPricing, History.usesKnownAt,
      UseCheck.matchesPricing, UseCheck.coveredThrough,
      CombinationPart.coversUse, splitChecks, firstPlan, prospective, splitFirst, splitSecond,
      splitPricing, original, check, used, useFinding, VerifiedMaterialsUse.combination,
      VerifiedMaterialsUse.materialsAt, terms, lesson, place, first, second, tick, Moment.before,
      Moment.by] at pricing

theorem repeatedChecksForOnePlaceUseItsNormalFeeOnce :
    splitChecks.combinedCapAllows lesson.id [⟨place.id, first, 10⟩] (tick 5) ∧
    ¬ splitChecks.combinedCapAllows lesson.id [⟨place.id, first, 11⟩] (tick 5) := by
  constructor <;> unfold History.combinedCapAllows <;> decide +kernel

private def revisionPricing : MaterialsPricing :=
  .otherCombination [first, second, omitted, another] (fun _ _ materials m ↦
    if m = first then
      if another ∈ materials then 4 else if omitted ∈ materials then 5 else 3
    else if m = second then
      if another ∈ materials then 6 else if omitted ∈ materials then 5
      else if first ∈ materials then 4 else 2
    else 0)

private def combinedCharge (material : MaterialId) (reference : String)
    (obligation : ObligationId) : Settlement :=
  let settlement := original revisionPricing [first, second] material reference obligation
  { settlement with check := { settlement.check with advanceCheck := none } }

private def establishedFirst := combinedCharge first "first charge" 1
private def establishedSecond := combinedCharge second "second charge" 2

private def expansionPoint : Moment := ⟨2, 2⟩

private def expansionPlan (point : Moment := expansionPoint)
    (agreed : Bool := true) : CombinationCheck :=
  prospective revisionPricing [first, second] point "expansion plan"
    [⟨second, 1, expansionPoint⟩]
    (if agreed then [⟨second, 1, "materials terms", expansionPoint⟩] else [])

private def knownExpansion (extra : CombinationCheck := expansionPlan) : History :=
  { terms := [terms revisionPricing]
    useChecks := [establishedFirst.check, check revisionPricing [first]]
    combinationChecks := [extra, firstPlan revisionPricing] }

theorem aConsentedExpansionCanBeRecordedBeforeUseVerification
    (ev : Course.StartEvidence) (holds : HoldHistory)
    (formsAt : ∃ roster forms, ev.arrangementFormsAt lesson expansionPoint roster forms ∧
      ∃ form ∈ forms, form.place = place ∧ form.confirmedAt.by expansionPoint ∧
        form.materialsOrBundle = some "teaching materials" ∧
        form.materialsTermsRef = some "materials terms" ∧ form.materialsPayer = some lesson.provider) :
    Step ev holds
      { terms := [terms revisionPricing], combinationChecks := [firstPlan revisionPricing] }
      (.checkCombination (expansionPlan))
      { terms := [terms revisionPricing]
        combinationChecks := [expansionPlan, firstPlan revisionPricing] } := by
  refine .checkCombination ⟨by decide, by decide, by simp [expansionPlan, prospective], trivial,
    ?_, ?_⟩ ?_
  · simpa [expansionPlan, prospective, terms] using formsAt
  · simp [expansionPlan, expansionPoint, prospective, terms, revisionPricing,
      CombinationPart.agreedAdjustments, MaterialsTerms.covers, MaterialsPricing.covers,
      MaterialsPricing.materials, materialsCapBase, materialsCapRate, MaterialsPricing.charges,
      MaterialsPricing.chargesAt, sumAmounts, first, second, omitted, another, lesson, place,
      tick, Moment.by, Moment.before]
    refine ⟨?_, ?_⟩
    · intro charge
      constructor <;> rintro rfl <;> decide +kernel
    · decide +kernel
  · simp [firstPlan, expansionPlan, prospective]

private theorem firstAndExpansionChecked :
    (knownExpansion).pricingAvailable establishedFirst.check (tick 5) := by
  simp [History.pricingAvailable, History.checkedNonstandardPricing, History.usesKnownAt,
    UseCheck.matchesPricing, UseCheck.coveredThrough,
    CombinationPart.coversUse, knownExpansion, expansionPlan, expansionPoint, firstPlan,
    prospective, establishedFirst, combinedCharge, revisionPricing, original, check, used, useFinding,
    VerifiedMaterialsUse.combination, VerifiedMaterialsUse.materialsAt, MaterialsTerms.covers,
    MaterialsPricing.covers, MaterialsPricing.materials, terms, lesson, place, first, second, tick,
    Moment.before, Moment.by, List.eraseDups_cons, -List.mem_eraseDups]

theorem aLaterConsentedCheckUsesCombinedPricing
    (ev : Course.StartEvidence) (holds : HoldHistory) :
    establishedSecond.check.advanceCheck = none ∧
    establishedSecond.record.charges = [⟨place.id, second, 4⟩] ∧
    (check revisionPricing [second]).use.chargesFor (terms revisionPricing) second =
      [⟨place.id, second, 2⟩] ∧
    Step ev holds (knownExpansion) (.settle establishedSecond)
      { (knownExpansion) with originals := [establishedSecond] } := by
  refine ⟨rfl, by decide +kernel, by decide +kernel, .settle ?_ ?_ firstAndExpansionChecked ?_ ?_⟩
  · exact List.Mem.head _
  · exact originalConforms _ _ _ _ _ (by decide)
  · unfold History.combinedCapAllows
    decide +kernel
  · simp [knownExpansion]

theorem checkAfterTheSecondUseCannotAuthorizeTheExpansion
    (ev : Course.StartEvidence) (holds : HoldHistory) (next : History) :
    ¬ Step ev holds (knownExpansion (expansionPlan ⟨2, 4⟩))
      (.settle establishedSecond) next := by
  intro accepted
  cases accepted with
  | settle _ _ pricing _ _ =>
    simp [History.pricingAvailable, History.checkedNonstandardPricing, History.usesKnownAt,
      UseCheck.matchesPricing, UseCheck.coveredThrough,
      CombinationPart.coversUse, knownExpansion, expansionPlan, expansionPoint, firstPlan,
      prospective, establishedSecond, establishedFirst, combinedCharge, revisionPricing,
      original, check, used,
      useFinding, VerifiedMaterialsUse.combination, VerifiedMaterialsUse.materialsAt, terms, lesson,
      place, first, second, tick, Moment.before, Moment.by] at pricing

private def isolatedSecond := original revisionPricing [second] second "isolated charge" 2

theorem aFullCheckDoesNotAuthorizeUnderpricingFromAnIndependentSlice
    (ev : Course.StartEvidence) (holds : HoldHistory) (next : History) :
    ¬ Step ev holds
      { (knownExpansion) with useChecks := isolatedSecond.check :: (knownExpansion).useChecks }
      (.settle isolatedSecond) next := by
  intro accepted
  cases accepted with
  | settle _ _ pricing _ _ =>
    simp [History.pricingAvailable, History.checkedNonstandardPricing, History.usesKnownAt,
      UseCheck.matchesPricing, UseCheck.coveredThrough, CombinationPart.coversUse, knownExpansion,
      expansionPlan, expansionPoint, firstPlan, prospective, establishedFirst, combinedCharge,
      isolatedSecond, revisionPricing,
      original, check, used, useFinding, VerifiedMaterialsUse.combination,
      VerifiedMaterialsUse.materialsAt, terms, lesson, place, first, second, tick, Moment.before,
      Moment.by, List.eraseDups_cons] at pricing

theorem theAdjustmentNeedsConsentBeforeTheExpandedUse (ev : Course.StartEvidence) :
    ¬ (expansionPlan expansionPoint false).conforms ev [terms revisionPricing] := by
  intro accepted
  have adjusted := (accepted.2.2.2.2.2 _ (List.Mem.head [])).2.2.1 _ (List.Mem.head [])
  simp [CombinationPart.agreedAdjustments, expansionPlan, expansionPoint, prospective, terms,
    MaterialsPricing.covers, MaterialsPricing.materials, revisionPricing, second, first, omitted,
    another, tick, Moment.by, Moment.before] at adjusted

theorem theOverCapCombinationCannotBeChecked
    (ev : Course.StartEvidence) (holds : HoldHistory) (next : History) :
    ¬ Step ev holds splitChecks
      (.checkCombination (prospective splitPricing [first, second] (tick 1) "over cap")) next := by
  intro accepted
  cases accepted with
  | checkCombination conforms _ =>
    have capped := (conforms.2.2.2.2.2 _ (List.Mem.head [])).2.2.2.2
    revert capped
    decide +kernel

private def observedOverCap := { check splitPricing [first, second] with advanceCheck := none }

theorem overCapUseCanStillBeRecordedAsFact
    (ev : Course.StartEvidence) (holds : HoldHistory) (course : observedOverCap.matchesCourse ev) :
    Step ev holds { terms := [terms splitPricing] } (.verify observedOverCap)
      { terms := [terms splitPricing], useChecks := [observedOverCap] } := by
  refine .verify (List.Mem.head []) (by simp [observedOverCap, check, used]) course ?_
  simp [MaterialsTerms.adoptedFor, MaterialsTerms.agreedBy, MaterialsPricing.materials,
    VerifiedMaterialsUse.verifiedBy, MaterialsUseAuthority.mayCheck, ReviewAuthorities.disinterested,
    DirectInterest.affected, observedOverCap, check, splitPricing, coordinator, used, useFinding,
    terms, lesson, place, first, second, omitted, another, tick, Moment.before, Moment.by]
  all_goals decide +kernel

private def verifiedLater :=
  { check revisionPricing [first, second, omitted] (tick 6) with advanceCheck := none }

private def settledExpansion : History :=
  { (knownExpansion) with originals := [establishedFirst, establishedSecond] }

theorem perPlaceAccountResolvesContainedUseAndRetainsAnOmission (form : Confirmation.PartOne)
    (lessonMatches : form.lesson = lesson) (placeMatches : form.place = place) :
    ¬ Workflow.LessonAccounts.materialsUnresolved form settledExpansion (tick 5) ∧
    Workflow.LessonAccounts.materialsUnresolved form
      { settledExpansion with useChecks := verifiedLater :: settledExpansion.useChecks } (tick 6) := by
  constructor <;>
    simp [Workflow.LessonAccounts.materialsUnresolved, settledExpansion, knownExpansion,
      establishedFirst, establishedSecond, combinedCharge, verifiedLater, original, check, used,
      useFinding,
      VerifiedMaterialsUse.combination, VerifiedMaterialsUse.materialsAt,
      VerifiedMaterialsUse.chargesFor, VerifiedMaterialsUse.charges, MaterialsPricing.charges,
      MaterialsPricing.chargesAt, revisionPricing, terms, lessonMatches, placeMatches, lesson, place,
      first, second, omitted, tick, Moment.before, Moment.by, List.eraseDups_cons, -List.mem_eraseDups]

private def shortfall (base : Settlement) (reference : String) (id : ObligationId) : Shortfall :=
  ⟨base, ⟨base.record.lesson, base.record.material, base.record.termsReference,
    base.record.reference, reference, id, tick 8,
      [⟨place.id, base.record.material, if base.record.material = first then 2 else 1⟩]⟩,
    verifiedLater⟩

private def retainedShortfall := shortfall establishedFirst "first shortfall" 3
private def nextShortfall := shortfall establishedSecond "second shortfall" 4

private def laterKnown : History :=
  { (knownExpansion) with
    useChecks := verifiedLater :: (knownExpansion).useChecks
    combinationChecks := prospective revisionPricing [first, second, omitted] ⟨2, 4⟩
      "second expansion" :: (knownExpansion).combinationChecks
    originals := [establishedFirst, establishedSecond]
    shortfalls := [retainedShortfall] }

private theorem shortfallPricingAvailable :
    laterKnown.pricingAvailable nextShortfall.check (tick 8) := by
  simp [History.pricingAvailable, History.checkedNonstandardPricing, History.usesKnownAt,
    UseCheck.matchesPricing, UseCheck.coveredThrough,
    CombinationPart.coversUse, laterKnown, knownExpansion, expansionPlan, expansionPoint, firstPlan,
    prospective, nextShortfall, shortfall, establishedFirst, combinedCharge, revisionPricing,
    original, check, used,
    useFinding, VerifiedMaterialsUse.combination, VerifiedMaterialsUse.materialsAt, verifiedLater,
    MaterialsTerms.covers, MaterialsPricing.covers, MaterialsPricing.materials, terms, lesson,
    place, first, second, omitted, tick, Moment.before, Moment.by, List.eraseDups_cons,
    -List.mem_eraseDups]

theorem retainedAndNewShortfallsCountTheirAdditionalCharges
    (ev : Course.StartEvidence) (holds : HoldHistory) :
    retainedShortfall.additionalCharges = [⟨place.id, first, 2⟩] ∧
    nextShortfall.additionalCharges = [⟨place.id, second, 1⟩] ∧
    Step ev holds laterKnown (.identifyShortfall nextShortfall)
      { laterKnown with shortfalls := [nextShortfall, retainedShortfall] } := by
  refine ⟨by decide +kernel, by decide +kernel,
    .identifyShortfall ?_ ?_ ?_ ?_ ?_ shortfallPricingAvailable ?_ ?_⟩
  · exact List.Mem.tail _ (List.Mem.head [])
  · exact List.Mem.head _
  · refine ⟨rfl, rfl, rfl, rfl, (by decide : ("second shortfall" : String) ≠ ""), rfl, rfl,
      (by decide : (tick 5).before (tick 8)), (by decide : (tick 6).by (tick 8)),
      by decide +kernel, singleChargePlace _ _ _⟩
  · exact ⟨⟨place.id, second, 1⟩, by decide +kernel, by decide⟩
  · intro prior saved same
    obtain rfl := List.mem_singleton.mp saved
    contradiction
  · unfold History.combinedCapAllows
    decide +kernel
  · intro prior saved _ sameMaterial
    obtain rfl := List.mem_singleton.mp saved
    exact (show first ≠ second from by decide) sameMaterial |>.elim

private def afterSecondShortfall : History :=
  { laterKnown with shortfalls := [nextShortfall] }

private def duplicateShortfall : Shortfall :=
  { nextShortfall with
    record := { nextShortfall.record with
      reference := "copied shortfall", obligation := 5, identifiedAt := ⟨8, 1⟩ } }

private def duplicateWithCorrectBasis : Shortfall :=
  { duplicateShortfall with record := { duplicateShortfall.record with
      charges := [⟨place.id, second, 0⟩] } }

theorem repeatedMaterialShortfallCannotRegister (s next : Workflow.State)
    (history : s.materials = afterSecondShortfall)
    (principal : s.materialsPrincipalContext = {}) :
    ¬ Workflow.Step s (.materials lesson.id (.identifyShortfall duplicateShortfall)) next := by
  intro step
  cases step with
  | materials _ _ localStep _ =>
    rw [history, principal] at localStep
    cases localStep with
    | identifyShortfall _ _ computed _ _ _ _ _ =>
      rcases computed with ⟨_, _, _, _, _, _, _, _, _, chargesMatch, _⟩
      exact (by decide +kernel : ¬ duplicateShortfall.record.charges =
        duplicateShortfall.record.newCharges duplicateShortfall.original.record
          (afterSecondShortfall.shortfalls.map Shortfall.record)
          (duplicateShortfall.check.use.chargesFor duplicateShortfall.check.terms second))
        chargesMatch

theorem noFurtherShortfallAfterAllChargesEstablished (s next : Workflow.State) :
    ¬ Workflow.Step s (.materials lesson.id (.identifyShortfall duplicateWithCorrectBasis)) next := by
  intro step
  cases step with
  | materials _ _ localStep _ =>
    cases localStep with
    | identifyShortfall _ _ _ additional _ _ _ _ =>
      obtain ⟨charge, included, positive⟩ := additional
      have single : duplicateWithCorrectBasis.additionalCharges = [⟨place.id, second, 0⟩] := by
        decide +kernel
      rw [single] at included
      obtain rfl := List.mem_singleton.mp included
      exact (by decide : ¬ (0 : Amount) < 0) positive

private def newUseCheck : UseCheck :=
  { check revisionPricing [first, second, omitted, another] (tick 9) with advanceCheck := none }

private def laterSupplementHistory : History :=
  { afterSecondShortfall with
    useChecks := newUseCheck :: afterSecondShortfall.useChecks
    combinationChecks := prospective revisionPricing [first, second, omitted, another] ⟨2, 6⟩
      "third expansion" :: afterSecondShortfall.combinationChecks }

private def laterSupplement : Shortfall :=
  { duplicateWithCorrectBasis with
    check := newUseCheck
    record := { duplicateWithCorrectBasis.record with
      reference := "additional verified use", identifiedAt := tick 10,
      charges := [⟨place.id, second, 1⟩] } }

theorem laterVerifiedIncreaseRegistersOnlyNewDifference (s : Workflow.State)
    (history : s.materials = laterSupplementHistory)
    (principal : s.materialsPrincipalContext = {}) :
    laterSupplement.additionalCharges = [⟨place.id, second, 1⟩] ∧
    Workflow.Step s (.materials lesson.id (.identifyShortfall laterSupplement))
      { s.withHolds s.holds with materials := { s.materials with
        shortfalls := laterSupplement :: s.materials.shortfalls } } := by
  refine ⟨by decide +kernel,
    .materials (s := s) (lesson := lesson.id) (event := .identifyShortfall laterSupplement)
      ?_ trivial ?_ rfl⟩
  · intro id included
    cases included
    rfl
  · rw [history, principal]
    refine .identifyShortfall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact List.Mem.tail _ (List.Mem.head [])
    · exact List.Mem.head _
    · refine ⟨rfl, rfl, rfl, rfl, (by decide : ("additional verified use" : String) ≠ ""),
        rfl, rfl, (by decide : (tick 5).before (tick 10)), (by decide : (tick 9).by (tick 10)),
        by decide +kernel, singleChargePlace _ _ _⟩
    · exact ⟨⟨place.id, second, 1⟩, by decide +kernel, by decide⟩
    · intro prior saved _ _
      obtain rfl := List.mem_singleton.mp saved
      decide
    · simp [History.pricingAvailable, History.checkedNonstandardPricing, History.usesKnownAt,
        UseCheck.matchesPricing, UseCheck.coveredThrough, CombinationPart.coversUse, laterSupplement,
        laterSupplementHistory, afterSecondShortfall, laterKnown, knownExpansion, expansionPlan,
        expansionPoint, firstPlan, prospective, newUseCheck, duplicateWithCorrectBasis,
        duplicateShortfall, nextShortfall, shortfall, verifiedLater, establishedFirst, combinedCharge,
        revisionPricing, original, check, used, useFinding, VerifiedMaterialsUse.combination,
        VerifiedMaterialsUse.materialsAt, MaterialsTerms.covers, MaterialsPricing.covers,
        MaterialsPricing.materials, terms, lesson, place, first, second, omitted, another, tick,
        Moment.before, Moment.by, List.eraseDups_cons, -List.mem_eraseDups]
    · unfold History.combinedCapAllows
      decide +kernel
    · intro prior saved _ _
      obtain rfl := List.mem_singleton.mp saved
      decide

#print axioms laterVerifiedIncreaseRegistersOnlyNewDifference
#print axioms repeatedMaterialShortfallCannotRegister
#print axioms noFurtherShortfallAfterAllChargesEstablished

#print axioms twoOrdinaryMaterialsCanSettleAtTheCombinedCap
#print axioms individualChecksDoNotAuthorizeTheKnownCombination
#print axioms repeatedChecksForOnePlaceUseItsNormalFeeOnce
#print axioms aConsentedExpansionCanBeRecordedBeforeUseVerification
#print axioms aLaterConsentedCheckUsesCombinedPricing
#print axioms checkAfterTheSecondUseCannotAuthorizeTheExpansion
#print axioms aFullCheckDoesNotAuthorizeUnderpricingFromAnIndependentSlice
#print axioms theAdjustmentNeedsConsentBeforeTheExpandedUse
#print axioms theOverCapCombinationCannotBeChecked
#print axioms overCapUseCanStillBeRecordedAsFact
#print axioms perPlaceAccountResolvesContainedUseAndRetainsAnOmission
#print axioms retainedAndNewShortfallsCountTheirAdditionalCharges

end SourceV14.FidelityMaterialsCapChecks
