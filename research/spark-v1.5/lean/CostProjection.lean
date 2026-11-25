import Menu

/-! Research-only projections of the locked recognised-state payment histories.
The proof target is an institutional operation, with time and resource prices left open. -/

namespace GovernanceCostTrial

open SourceV14 SourceV14.Workflow
open SourceV14.FidelityMaterialsProvisionChecks
open SparkJoint

private def cohort : List Outcome :=
  [.normal, .accepted, .pendingChecked, .pendingTeachingOnly, .pendingUnreleased]

/-- Least nonnegative additional liquidity to meet the numerical requirement
at this cut, conditional on retaining the other permission conditions. -/
def liquidityGap (bank : BankCorrection) (kind : Outcome) (early : Bool) : Amount :=
  max 0 (requiredFunds early - observedNet bank kind)

-- Each row contains (T reserve, M net funds, extra without early evidence, extra with it).
def liquidityRows (bank : BankCorrection) : List (Amount × Amount × Amount × Amount) :=
  cohort.map fun kind ↦
    (retained kind, observedNet bank kind, liquidityGap bank kind false,
      liquidityGap bank kind true)

theorem fixedLiquidityRows :
    liquidityRows lowerBankCut = [(2, 14, 0, 0), (6, 10, 2, 0), (6, 10, 2, 0),
      (8, 8, 4, 2), (10, 6, 6, 4)] ∧
    liquidityRows upperBankCut = [(2, 16, 0, 0), (6, 12, 0, 0), (6, 12, 0, 0),
      (8, 10, 2, 0), (10, 8, 4, 2)] := by
  decide +kernel

private def matchingPost : Event := JointM.paymentEvent 18 6

def comparedEvents (early : Bool) : List Event :=
  datesBefore45 .accepted early ++ [matchingPost]

def comparedEnd (early : Bool) : State :=
  JointM.afterPaymentAt45 (whenChecked .accepted early) 18 6

/-- Both paths really reach the same material payment event. In one path
the verification is performed before posting, in the other it is still absent. -/
theorem comparedPaymentPaths (early : Bool) :
    RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step
      (RecognisedV15.Workflow.State.fromDirect commonStart) (comparedEvents early)
      (RecognisedV15.Workflow.State.fromDirect (comparedEnd early)) := by
  apply RecognisedV15.Workflow.path_from_direct
  apply append (followsCommonOpening .accepted early)
  refine .next ?_ (.nil _)
  cases early
  · exact JointM.enoughFundsForMaterialsPayment _ 44 .unverified 18 6
      (readyAt45 .accepted) (by decide +kernel) (by decide) (by decide +kernel)
  · exact JointM.enoughFundsForMaterialsPayment _ 44 .verified44 18 6
      (JointM.retainsVerification _ 44 44 (readyAt45 .accepted))
      (by decide +kernel) (by decide) (by decide +kernel)

/-- The monetary projection records identical transfers and reservations.
The early route has exactly one more root event through the same checkpoint. -/
theorem equalTransfersDifferentEvents :
    (comparedEnd false).holds.payments.posted = (comparedEnd true).holds.payments.posted ∧
    (comparedEnd false).activeReserves = (comparedEnd true).activeReserves ∧
    (JointM.attempt 18 6).paid.instruction.amount = 4 ∧
    (comparedEvents true).length = (comparedEvents false).length + 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

#eval liquidityRows lowerBankCut
#eval liquidityRows upperBankCut
#eval (comparedEvents false).length
#eval (comparedEvents true).length

#print axioms fixedLiquidityRows
#print axioms comparedPaymentPaths
#print axioms equalTransfersDifferentEvents

end GovernanceCostTrial
