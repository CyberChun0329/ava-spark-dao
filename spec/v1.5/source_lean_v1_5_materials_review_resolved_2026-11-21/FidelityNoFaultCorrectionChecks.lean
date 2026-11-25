import SourceV14.Workflow.Review

namespace SourceV14.FidelityNoFaultCorrectionChecks

open Confirmation Course Operations Workflow.Review

/-- A retained no-fault assessment supplies the clock even before any refund receipt. -/
theorem assessmentClockControlsCorrection (row : CorrectedPayout) (history : History)
    (evidence : Evidence) (start : StartEvidence) (holds : HoldHistory)
    (trigger due : Moment)
    (retained : evidence.noFaultRefundAt row.form row.correction.originalPart.ref
      row.correction.finding.decidedAt = some (trigger, due))
    (refund : row.part.ref.purpose = .lessonRefund row.form.place.id)
    (noFault : ¬∃ fault : FaultBasis, ∃ outcome ∈
      (history.decisionRecords evidence.authority row.decisions).faultOutcomes,
        outcome.place = row.form.place.id ∧ outcome.decision = .review row.correction.finding ∧
        outcome.disposition = .fault fault)
    (conforms : row.conforms history evidence start holds) :
    row.applicable = row.form.deadlines.noFaultRefundTerms := by
  rcases conforms with ⟨_, _, _, scope, _, posted⟩
  unfold CorrectedPaymentPosted at posted
  rcases posted with ⟨_, _, _, _, _, _, _, _, _, _, _, _, branch, _⟩
  rw [refund] at branch
  rcases branch with ⟨_, _, _, terms, _⟩ | ⟨absent, _⟩
  · exact terms
  · exact False.elim (absent ⟨trigger, due, Or.inl retained, noFault⟩)

end SourceV14.FidelityNoFaultCorrectionChecks
