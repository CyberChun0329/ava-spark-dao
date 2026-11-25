import ProvisionWitnessFixture
import RecognisedV15.Workflow

/-! A fixed same-second payment and transfer in the revised v1.5 research fixture. -/
namespace SparkGap.G3SameSecond

open SourceV14 SourceV14.Operations SourceV14.Workflow.Materials
open SourceV14.FidelityMaterialsProvisionChecks.TransferFixture

private def afterPaymentInSameSecond : Moment := ⟨45, 1⟩

private def signedTransfer : Transfer where
  material := 7
  sparkDao := courseLesson.provider
  recordedAt := afterPaymentInSameSecond
  record :=
    let split : MaterialsAllocation 7 :=
      ⟨"uncollected split", [99, 3],
        fun holder _ amount ↦ if holder = 99 then amount / 3 else 2 * amount / 3⟩
    let transfer : MaterialsTransfer 7 :=
      ⟨2, 99, .voluntaryTransfer, afterPaymentInSameSecond, .sharesAtFirstUse, split, split⟩
    { transfer
      reference := "signed original, place 1"
      verifiedTerms := fun reference terms ↦ reference = "signed original, place 1" ∧ terms = transfer
      transferorShareTime := time 35
      applicableOwnershipTime := (· = time 35)
      voluntary := True
      publishedTermsSatisfied := True
      governs := fun lesson ref place ↦
        lesson = courseLesson.id ∧ ref = firstOriginal.record.reference ∧ place = seat.id
      originalCollections := fun lesson ref place ↦
        if lesson = courseLesson.id ∧ ref = firstOriginal.record.reference ∧ place = seat.id then
          [⟨2, 2, time 40⟩, ⟨3, 4, time 45⟩] else []
      shortfallCollections := fun _ _ _ _ ↦ [] }

private def transferred : Workflow.State :=
  { rootPaid.withHolds rootPaid.holds with
    materials := { rootPaid.materials with transfers := signedTransfer :: rootPaid.materials.transfers } }

private def transferEvent : Workflow.Event := .materials courseLesson.id (.transfer signedTransfer)

private theorem transferStep : Workflow.Step rootPaid transferEvent transferred := by
  refine Workflow.Step.materials (sameLesson := ?_) (funds := trivial) (rule := ?_) (payment := rfl)
  · intro id present
    cases present
  · exact .transfer ⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩⟩ (by intro prior member; cases member)

/-- A verified payment before the effective transfer still discharges the original charge
    when the two events share a timestamp. The remaining live material budgets total six. -/
theorem sameSecondTransferKeepsSettlement :
    payFour.paid.instruction.atTime.seconds = afterPaymentInSameSecond.seconds ∧
    payFour.paid.instruction.atTime.before afterPaymentInSameSecond ∧
    rootPaid.materials.hasVerifiedReceiptAt payFour.paid afterPaymentInSameSecond = true ∧
    RecognisedV15.Workflow.Step (RecognisedV15.Workflow.State.fromDirect rootPaid) transferEvent
      (RecognisedV15.Workflow.State.fromDirect transferred) ∧
    transferred.materials.paidOriginalCharge transferred.holds.payments oldProvision.pending
      (time 48) = true ∧
    sumAmounts (transferred.materials.liveMaterialBudgetsAt transferred.holds.payments courseLesson.id
      (time 48) transferred.materialsPrincipalContext) Prod.snd = 6 := by
  exact ⟨rfl, by decide +kernel, by decide +kernel,
    (RecognisedV15.Workflow.step_iff _ _ _).mp transferStep, by decide_cbv, by decide_cbv⟩

#print axioms sameSecondTransferKeepsSettlement

end SparkGap.G3SameSecond
