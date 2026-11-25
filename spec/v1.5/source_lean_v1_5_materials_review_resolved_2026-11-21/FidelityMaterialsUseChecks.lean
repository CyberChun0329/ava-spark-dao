import SourceV14.Workflow.LessonAccounts

/-! §5.2 and Form Part 2. Check one material used for one place, with and without
the tutor's report, against an independently verifiable record of actual use. -/

namespace SourceV14.FidelityMaterialsUseChecks

open SourceV14.Workflow.Materials

private def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩
private def lesson : Lesson := ⟨42, .oneToOne, 10, 20, 30, 60⟩
private def place : Place := ⟨1, lesson.id, 40, 50, 60, 70, 100, 100⟩
private def material : MaterialId := 7

private def useAuthority : MaterialsUseAuthority where
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

private def finding : ConfirmedMaterialUse :=
  ⟨lesson.id, place.id, material, 1, tick 2, lesson.coordinator, tick 4,
    .lessonRecord "record of the service delivered"⟩

private def report : TutorMaterialsReport :=
  ⟨lesson.id, lesson.tutor, lesson.coordinator, tick 1, [material], tick 4, [material]⟩

private def used (verifies : ConfirmedMaterialUse → Prop)
    (tutorReport : Option TutorMaterialsReport := none) : VerifiedMaterialsUse where
  lesson := lesson
  startedAt := tick 2
  endedAt := tick 3
  tutorReport := tutorReport
  authority := useAuthority
  places := [place]
  deliveryReports := []
  findings := [finding]
  verifiesEvidence := verifies
  verifiedReportOmission := fun _ ↦ False
  uniquePlaces := by simp
  placeInLesson := by simp [Place.matches, place]
  findingInLesson := by simp [finding]
  findingAtPlace := by simp [finding]

private def terms : MaterialsTerms where
  lesson := lesson.id
  adoptedBy := lesson.provider
  agreedAt := tick 0
  agreementReference := "materials terms"
  accountingAndPaymentParty := lesson.provider
  materialsOrBundle := "one text"
  contact := "coordinator"
  licensedUse := (· = material)
  sharesAndAdjustmentsReference := "original share"
  sharesInForce := fun _ _ ↦ some ⟨"one contributor", [1], fun _ _ base ↦ base⟩
  contributors := fun _ ↦ [1]
  consents := [⟨material, 1, "materials terms", tick 0⟩]
  ordinaryShareTime := fun _ _ firstUse _ ↦ firstUse
  paymentDue := tick 20
  paymentDeadline := tick 20
  pricing := .standardBundle [⟨material, 1 / 10⟩]

private def check (tutorReport : Option TutorMaterialsReport := none) : UseCheck :=
  ⟨used (· = finding) tutorReport, terms, none, tick 4⟩

private theorem pricedWithoutReport :
    terms.calculatesVerifiedUse (check).use none (tick 4) := by
  simp [MaterialsTerms.calculatesVerifiedUse, MaterialsTerms.adoptedFor,
    MaterialsTerms.agreedBy, MaterialsTerms.covers, MaterialsPricing.covers,
    VerifiedMaterialsUse.verifiedBy, MaterialsUseAuthority.mayCheck, ReviewAuthorities.disinterested,
    DirectInterest.affected, useAuthority, check, used, finding, StandardMaterialsBundle,
    VerifiedMaterialsUse.combination, VerifiedMaterialsUse.materialsAt,
    materialsCombinationWithinCap, materialsCapBase, MaterialsPricing.charges,
    MaterialsPricing.chargesAt, MaterialsPricing.materials, sumAmounts, materialsCapRate,
    terms, lesson, place, material, tick, Moment.before, Moment.by]
  all_goals decide +kernel

theorem independentlyVerifiedUseHasTheAgreedCharge :
    terms.calculatesVerifiedUse (check).use none (tick 4) ∧
    (check).use.chargesFor terms material = [⟨place.id, material, 10⟩] :=
  ⟨pricedWithoutReport, by decide +kernel⟩

/-- The course predicate supplies the retained teaching and form records independently. -/
theorem verificationCanBeRecordedEvenWhenTheTutorReportIsMissing
    (ev : Course.StartEvidence) (holds : HoldHistory) (course : (check).matchesCourse ev) :
    Step ev holds { terms := [terms] } (.verify (check)) { terms := [terms], useChecks := [check] } :=
  .verify (by simp [check]) (by simp [check, used]) course
    ⟨pricedWithoutReport.1, pricedWithoutReport.2.1⟩

theorem theMissingReportDoesNotEstablishUnverifiedUse :
    ¬ (used (fun _ ↦ False)).verifiedBy (tick 4) := by
  intro verified
  rcases verified.2.2 finding (List.Mem.head []) with
    ⟨_, _, _, _, _, _, _, _, _, confirmation⟩
  exact confirmation

theorem aCitedReportMustBeRetained
    (ev : Course.StartEvidence) (holds : HoldHistory) (next : History) :
    ¬ Step ev holds { terms := [terms] } (.verify (check (some report))) next := by
  intro verified
  cases verified with
  | verify _ recorded _ _ =>
    exact List.not_mem_nil (recorded report (by simp [check, used]))

#print axioms independentlyVerifiedUseHasTheAgreedCharge
#print axioms verificationCanBeRecordedEvenWhenTheTutorReportIsMissing
#print axioms theMissingReportDoesNotEstablishUnverifiedUse
#print axioms aCitedReportMustBeRetained

private def attributedCharge : Settlement where
  record := ⟨lesson.id, material, terms.agreementReference, "established material charge", 100,
    tick 5, [place.id], (check).use.chargesFor terms material⟩
  check := check

private def materialHistory : History :=
  { useChecks := [check], originals := [attributedCharge] }

/-- This reader reports a verified subtotal while an identified material charge is pending. -/
theorem perPlaceAccountReadsEstablishedMaterialCharge (form : Confirmation.PartOne)
    (lessonMatches : form.lesson = lesson) (placeMatches : form.place = place) :
    Workflow.LessonAccounts.materialsChargeAt form materialHistory (tick 4) = 0 ∧
    Workflow.LessonAccounts.materialsUnresolved form materialHistory (tick 4) ∧
    Workflow.LessonAccounts.materialsChargeAt form materialHistory (tick 5) = 10 ∧
    ¬ Workflow.LessonAccounts.materialsUnresolved form materialHistory (tick 5) := by
  have atFour : ¬(tick 5).by (tick 4) := by decide
  have atFive : (tick 5).by (tick 5) := by decide
  have useRetained : (tick 4).by (tick 5) := by decide
  have checkAtFour : (tick 4).by (tick 4) := by decide
  have materialAtPlace : (check).use.materialsAt place.id = [material] := by decide
  have priced := independentlyVerifiedUseHasTheAgreedCharge.2
  have useLesson : (check).use.lesson.id = lesson.id := rfl
  have usePlaces : (check).use.places = [place] := rfl
  have checked : (check).checkedAt = tick 4 := rfl
  simp [Workflow.LessonAccounts.materialsChargeAt, Workflow.LessonAccounts.materialsUnresolved,
    materialHistory, attributedCharge, lessonMatches, placeMatches, atFour, atFive, useRetained,
    checkAtFour, materialAtPlace, useLesson, usePlaces, checked, priced, sumAmountsWhere]
  all_goals decide +kernel

/-- The same authenticated materials charge cannot be copied to another place. -/
theorem accountExcludesMaterialsAttributedToAnotherPlace (form : Confirmation.PartOne)
    (otherPlace : form.place.id ≠ place.id) :
    Workflow.LessonAccounts.materialsChargeAt form materialHistory (tick 5) = 0 := by
  have recognised : materialHistory.recognisedChargesAt form.lesson.id (tick 5) =
      if lesson.id = form.lesson.id then [(⟨place.id, material, 10⟩, false)] else [] := by
    unfold History.recognisedChargesAt
    change ((([attributedCharge].filter
      (fun row : Settlement ↦ row.record.lesson == form.lesson.id)).map
      (fun row : Settlement ↦ (row.record.chargeScope, row.record.grossChargeInputs))) ++ []).flatMap _ = _
    by_cases sameLesson : lesson.id = form.lesson.id
    · rw [← sameLesson]
      decide +kernel
    · have omitted : [attributedCharge].filter
          (fun row : Settlement ↦ row.record.lesson == form.lesson.id) = [] := by
        simp [attributedCharge, sameLesson]
      simp [omitted, sameLesson]
  by_cases sameLesson : lesson.id = form.lesson.id
  · simp [Workflow.LessonAccounts.materialsChargeAt, recognised, sameLesson, sumAmountsWhere,
      Ne.symm otherPlace]
  · simp [Workflow.LessonAccounts.materialsChargeAt, recognised, sameLesson, sumAmountsWhere]

#print axioms perPlaceAccountReadsEstablishedMaterialCharge
#print axioms accountExcludesMaterialsAttributedToAnotherPlace

end SourceV14.FidelityMaterialsUseChecks
