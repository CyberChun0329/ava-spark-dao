import AcceptedRetainedFees

/-! Checkpoint calculations for the fixed M payment. Cash and T's protection at
the comparison point are parameters. The theorem does not construct their
history, give authority to release a reserve, or certify an Anvil trace. -/

namespace SparkGap.JoinedPaymentCut

open SourceV14 SourceV14.Workflow SourceV14.FidelityMaterialsProvisionChecks
open SparkJoint GovernanceEvidenceTrial SparkGap.AcceptedRetainedFees

def afterRelease : Amount := 2 + 4 + 2

def beforeRelease : Amount := afterRelease + 6

def status (early : Bool) : JointM.ReceiptStatus :=
  if early then .verified44 else .unverified

private theorem evidenceAtCheck (retained : Amount) (early : Bool) :
    JointM.HasMaterialEvidence (atCheck retained early) 44 (status early).point
      eligibleSlot := by
  have ready : MReady (withRetained retained) := ⟨rfl, rfl, rfl, rfl⟩
  cases early
  · exact ready
  · exact JointM.retainsVerification (withRetained retained) 44 44 ready

private theorem occupiedAtCheck (retained cash : Amount) (early : Bool) :
    Reserves.occupiedElsewhere (atCheck retained early).activeReserves
      (JointM.attempt cash retained).funds 1 ≤ retained := by
  have reserves : (atCheck retained early).activeReserves =
      [mInitial, tAt retained] := by cases early <;> rfl
  rw [reserves]
  change (0 : Amount) + retained ≤ retained
  rw [Rat.zero_add]
  exact Rat.le_refl

def permits (cash retained : Amount) (early : Bool) : Prop :=
  ∃ next, RStep (RecognisedV15.Workflow.State.fromDirect (atCheck retained early))
    (JointM.paymentEvent cash retained) next

/-- The right-hand side is the gross cash floor, including the entire separate
T protection. The only changed evidence across the two branches is availability
of the old material receipt at the comparison point. -/
theorem menuAtObservedCash (cash retained : Amount) (early : Bool)
    (nonnegative : 0 ≤ retained) :
    permits cash retained early ↔ (status early).requiredFunds + retained ≤ cash := by
  have numeric :
      (status early).requiredFunds ≤ cash - retained ↔
        (status early).requiredFunds + retained ≤ cash := by
    have h := Rat.add_le_add_right (a := (status early).requiredFunds)
      (b := cash - retained) (c := retained)
    rw [Rat.sub_add_cancel] at h
    exact h.symm
  constructor
  · rintro ⟨next, witness⟩
    apply numeric.mp
    apply Classical.byContradiction
    intro h
    exact JointM.insufficientFundsBlockMaterialsPayment _ next.toDirect 44 _
      cash retained (evidenceAtCheck retained early) h
      (by simpa using RecognisedV15.Workflow.step_to_direct witness)
  · intro canPay
    have step := JointM.enoughFundsForMaterialsPayment _ 44 _ cash retained
      (evidenceAtCheck retained early) (occupiedAtCheck retained cash early) nonnegative
      (numeric.mpr canPay)
    exact ⟨_, RecognisedV15.Workflow.step_from_direct step⟩

theorem cashFloors :
    (status true).requiredFunds + beforeRelease = 24 ∧
    (status false).requiredFunds + beforeRelease = 26 ∧
    (status true).requiredFunds + afterRelease = 18 ∧
    (status false).requiredFunds + afterRelease = 20 := by decide +kernel

theorem comparisonAtTwentyFour :
    permits 24 beforeRelease true ∧ ¬ permits 24 beforeRelease false ∧
    permits 24 afterRelease true ∧ permits 24 afterRelease false := by
  have beforeNonnegative : 0 ≤ beforeRelease := by decide +kernel
  have afterNonnegative : 0 ≤ afterRelease := by decide +kernel
  refine ⟨(menuAtObservedCash 24 beforeRelease true beforeNonnegative).mpr (by decide +kernel),
    fun late ↦ ?_,
    (menuAtObservedCash 24 afterRelease true afterNonnegative).mpr (by decide +kernel),
    (menuAtObservedCash 24 afterRelease false afterNonnegative).mpr (by decide +kernel)⟩
  exact (by decide +kernel : ¬ (status false).requiredFunds + beforeRelease ≤ 24)
    ((menuAtObservedCash 24 beforeRelease false beforeNonnegative).mp late)

#print axioms menuAtObservedCash
#print axioms cashFloors
#print axioms comparisonAtTwentyFour

end SparkGap.JoinedPaymentCut
