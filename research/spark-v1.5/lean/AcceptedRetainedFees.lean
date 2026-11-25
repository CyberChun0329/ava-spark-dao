import EvidencePayment

/-! Sensitivity of the accepted-compensation payment to separately held lesson fees.
The retained amount is a supplied check-point condition, with no assertion about
the validity of a reserve release or the combined engineering history. -/

namespace SparkGap.AcceptedRetainedFees

open SourceV14 SourceV14.Workflow SourceV14.FidelityMaterialsProvisionChecks
open SparkJoint GovernanceEvidenceTrial

/-- Retain the accepted history for material eligibility, with given T backing at the cut. -/
def withRetained (retained : Amount) : State :=
  { at45 .accepted with activeReserves := [mInitial, tAt retained] }

/-- The checkpoint view differs only by the selected verification event. -/
def atCheck (retained : Amount) (early : Bool) : State :=
  if early then JointM.afterVerification (withRetained retained) 44 else withRetained retained

private theorem ready (retained : Amount) : MReady (withRetained retained) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- On this accepted-compensation view, holding the extra fees changes the funding guard. -/
theorem retainedFunding (bank : BankCorrection) (retained : Amount) (early : Bool)
    (nonnegative : 0 ≤ retained) :
    (∃ next, RStep (RecognisedV15.Workflow.State.fromDirect (atCheck retained early))
      (JointM.paymentEvent (grossAtCheck bank) retained) next) ↔
      requiredFunds early ≤ grossAtCheck bank - retained := by
  have exactMenu :
      (∃ next, Step (atCheck retained early)
        (JointM.paymentEvent (grossAtCheck bank) retained) next) ↔
        requiredFunds early ≤ grossAtCheck bank - retained := by
    cases early
    · exact paymentMenu _ bank retained .unverified (ready retained) rfl nonnegative
    · exact paymentMenu _ bank retained .verified44
        (JointM.retainsVerification (withRetained retained) 44 44 (ready retained))
        rfl nonnegative
  constructor
  · rintro ⟨next, step⟩
    exact exactMenu.mp ⟨next.toDirect, by simpa using RecognisedV15.Workflow.step_to_direct step⟩
  · intro enough
    obtain ⟨next, step⟩ := exactMenu.mpr enough
    exact ⟨RecognisedV15.Workflow.State.fromDirect next,
      RecognisedV15.Workflow.step_from_direct step⟩

/-- Six held units admit early posting at balance 16. Eight held units block it at 16. -/
theorem extraFeesChangePaymentAtSixteen :
    (∃ next, RStep (RecognisedV15.Workflow.State.fromDirect (atCheck 6 true))
      (JointM.paymentEvent 16 6) next) ∧
    ¬ ∃ next, RStep (RecognisedV15.Workflow.State.fromDirect (atCheck 8 true))
      (JointM.paymentEvent 16 8) next := by
  refine ⟨?_, ?_⟩
  · simpa only [cashAtCheck.1] using
      (retainedFunding lowerBankCut 6 true (by decide)).mpr (by decide +kernel)
  intro step
  exact (by decide +kernel : ¬ requiredFunds true ≤ grossAtCheck lowerBankCut - 8)
    ((retainedFunding lowerBankCut 8 true (by decide)).mp (by
      simpa only [cashAtCheck.1] using step))

/-- At balance 18 and reserve 8, early verification recovers the funding path. -/
theorem earlyRestoredAtEighteen :
    ∃ next, RStep (RecognisedV15.Workflow.State.fromDirect (atCheck 8 true))
      (JointM.paymentEvent 18 8) next := by
  simpa only [cashAtCheck.2.1] using
    (retainedFunding upperBankCut 8 true (by decide)).mpr (by decide +kernel)

#print axioms retainedFunding
#print axioms extraFeesChangePaymentAtSixteen
#print axioms earlyRestoredAtEighteen

end SparkGap.AcceptedRetainedFees
