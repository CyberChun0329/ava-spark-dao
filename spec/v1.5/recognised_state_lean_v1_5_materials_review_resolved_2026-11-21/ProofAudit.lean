import RecognisedV15

open Lean Elab Command Meta

run_cmd do
  let env ← getEnv
  let compared := (env.constants.toList.map Prod.fst).filter
    (fun name ↦ (`RecognisedV15.Checked.SourceV14).isPrefixOf name &&
      (name == name.getPrefix.str "direct_eq"))
  let required := [
    `RecognisedV15.Checked.SourceV14.Course.CanStart,
    `RecognisedV15.Checked.SourceV14.Course.CanRescheduleGroup,
    `RecognisedV15.Checked.SourceV14.Course.GroupSettlementAvailable,
    `RecognisedV15.Checked.SourceV14.Course.StartEvidence.retainsOneToOneAbsence,
    `RecognisedV15.Checked.SourceV14.Confirmation.PaymentDeadline.appliesForLesson,
    `RecognisedV15.Checked.SourceV14.HoldHistory.paymentHoldScopeUnresolved,
    `RecognisedV15.Checked.SourceV14.Operations.OrdinaryGroupCharge,
    `RecognisedV15.Checked.SourceV14.Operations.FaultReserveTransferRecorded,
    `RecognisedV15.Checked.SourceV14.Operations.FiledPaymentOnTime,
    `RecognisedV15.Checked.SourceV14.Operations.TutorPaymentPosted,
    `RecognisedV15.Checked.SourceV14.Operations.MaterialsPaymentPosted,
    `RecognisedV15.Checked.SourceV14.Operations.CorrectedPaymentPosted
  ]
  for name in required do
    unless compared.contains (name.str "direct_eq") do
      throwError "Missing selected production entry: {name}"
  let handWritten := [
    `RecognisedV15.LessonEvidence.toDirect_fromDirect,
    `RecognisedV15.LessonEvidence.fromDirect_toDirect,
    `RecognisedV15.PaymentEvidence.toDirect_fromDirect,
    `RecognisedV15.PaymentEvidence.fromDirect_toDirect,
    `RecognisedV15.State.toDirect_fromDirect,
    `RecognisedV15.State.fromDirect_toDirect,
    `RecognisedV15.state_correspondence,
    `RecognisedV15.observation_equal,
    `RecognisedV15.judgment_iff,
    `RecognisedV15.history_comparison_equal,
    `RecognisedV15.observations_through_equal,
    `RecognisedV15.PaymentEvidence.misdirected_execution,
    `RecognisedV15.recognisedMaterialUse_iff,
    `RecognisedV15.recognisedRemedyDelivery_iff,
    `RecognisedV15.Correction.bisimulation,
    `RecognisedV15.Correction.matching_direct_trace,
    `RecognisedV15.Correction.matching_recognised_trace
  ]
  let mut usedAxioms : NameSet := {}
  for name in compared ++ handWritten do
    let axioms ← liftTermElabM <| collectAxioms name
    for axiomName in axioms do
      unless [`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Unexpected axiom in {name}: {axiomName}"
      usedAxioms := usedAxioms.insert axiomName
  logInfo m!"Checked {compared.length} adapter equalities and {handWritten.length} named proofs. Axioms: {usedAxioms.toList}"

namespace ReceiptExample

open SourceV14 RecognisedV15

private def part : PaymentPart := ⟨⟨17, 33, 1, .tutorPay 1⟩, .person 1 none, 40⟩

private def paid : PostedPayment :=
  ⟨7, ⟨part.ref, .person 2, 3, 40, ⟨10, 1⟩⟩, some 81⟩

private def evidence (designationOrder : Nat) : PaymentEvidence :=
  PaymentEvidence.fromDirect {
    payments := ⟨[paid], [], [⟨paid, 1, 2, ⟨10, designationOrder⟩, none, 82⟩]⟩
    temporary := []
    formal := []
    lifts := []
  }

/- Only the actual ordering of the recipient designation changes. -/
example :
    (∃ row : ExecutedPayment (evidence 2) part, row.receipt = paid) ∧
      ¬(∃ row : QualifiedReceipt (evidence 2) part, row.receipt = paid) := by
  apply PaymentEvidence.misdirected_execution
  · simp [evidence, PaymentEvidence.fromDirect, PaymentHistory.actualPaymentWithEvidence, paid]
  · rfl
  · decide

example : ∃ row : QualifiedReceipt (evidence 0) part, row.receipt = paid := by
  apply (PaymentEvidence.qualifiedReceipt_iff (evidence 0) part paid).mpr
  refine ⟨?_, rfl, ?_⟩
  · simp [evidence, PaymentEvidence.fromDirect, PaymentHistory.actualPaymentWithEvidence, paid]
  · decide

example : (evidence 2).payments.remainingBefore part ⟨10, 3⟩ = 40 := by decide +kernel
example : (evidence 0).payments.remainingBefore part ⟨10, 3⟩ = 0 := by decide +kernel

end ReceiptExample
