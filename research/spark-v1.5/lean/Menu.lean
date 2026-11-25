import OtherBranches

/-! Payment at 45 on the actual branch endpoints. The two bank cuts and the
early/deferred timing use the same two-course start and prefix. -/

namespace SparkJoint
open SourceV14 SourceV14.Workflow
open SourceV14.FidelityMaterialsProvisionChecks

private abbrev DirectPath := RecognisedV15.Workflow.Path Step

inductive Outcome where
  | normal | accepted | pendingChecked | pendingTeachingOnly | pendingUnreleased
  deriving Repr

def retained : Outcome → Amount
  | .normal => 2
  | .accepted | .pendingChecked => 6
  | .pendingTeachingOnly => 8
  | .pendingUnreleased => 10

def at45 : Outcome → State
  | .normal => normalReleased
  | .accepted => faultReleased
  | .pendingChecked => checkedAndReleased
  | .pendingTeachingOnly => onlyTeachingReleased
  | .pendingUnreleased => afterPendingReceipt

def history : Outcome → List Event
  | .normal => normalEvents
  | .accepted => faultEvents
  | .pendingChecked => pendingEvents
  | .pendingTeachingOnly =>
      prefixEvents ++ JointT.teachingEvents ++ [publishEvent, intakeEvent, JointM.earlierPaymentEvent,
        .reserveReleased teachingOnlyRelease (verifiesTeachingOnlyRelease afterPendingReceipt)]
  | .pendingUnreleased =>
      prefixEvents ++ JointT.teachingEvents ++ [publishEvent, intakeEvent, JointM.earlierPaymentEvent]

theorem route (kind : Outcome) : DirectPath commonStart (history kind) (at45 kind) := by
  cases kind
  · exact normalReservedPath
  · exact faultReservedPath
  · exact pendingPath
  · exact onlyTeachingPath
  · exact pendingReceiptPath

theorem readyAt45 (kind : Outcome) : MReady (at45 kind) := by
  cases kind <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem actualReserve (kind : Outcome) :
    (at45 kind).activeReserves = [mInitial, tAt (retained kind)] := by
  cases kind <;> rfl

def whenChecked (kind : Outcome) (early : Bool) : State :=
  if early then JointM.afterVerification (at45 kind) 44 else at45 kind

def datesBefore45 (kind : Outcome) (early : Bool) : List Event :=
  history kind ++ if early then [JointM.verificationEvent 44] else []

theorem followsCommonOpening (kind : Outcome) (early : Bool) :
    DirectPath commonStart (datesBefore45 kind early) (whenChecked kind early) := by
  cases early
  · simpa [datesBefore45, whenChecked] using route kind
  · exact append (route kind) (.next (verify44 (readyAt45 kind)) (.nil _))

theorem verifiedAccountingAt45 (kind : Outcome) (early : Bool) :
    (whenChecked kind early).activeReserves = [mInitial, tAt (retained kind)] := by
  cases early <;> exact actualReserve kind

def requiredFunds (early : Bool) : Amount := if early then 10 else 12

def observedNet (bank : BankCorrection) (kind : Outcome) : Amount :=
  grossAtCheck bank - retained kind

theorem menu (bank : BankCorrection) (kind : Outcome) (early : Bool) :
    (∃ next, Step (whenChecked kind early)
      (JointM.paymentEvent (grossAtCheck bank) (retained kind)) next) ↔
      requiredFunds early ≤ observedNet bank kind := by
  have nonnegative : 0 ≤ retained kind := by cases kind <;> decide +kernel
  cases early
  · exact paymentMenu _ bank _ .unverified (readyAt45 kind) (actualReserve kind) nonnegative
  · exact paymentMenu _ bank _ .verified44 (JointM.retainsVerification _ 44 44 (readyAt45 kind))
      (actualReserve kind) nonnegative

theorem recognisedMenu (bank : BankCorrection) (kind : Outcome) (early : Bool) :
    (∃ next, RecognisedV15.Workflow.Step
      (RecognisedV15.Workflow.State.fromDirect (whenChecked kind early))
      (JointM.paymentEvent (grossAtCheck bank) (retained kind)) next) ↔
      requiredFunds early ≤ observedNet bank kind := by
  rw [← menu]
  constructor
  · rintro ⟨next, step⟩
    exact ⟨next.toDirect, by simpa using RecognisedV15.Workflow.step_to_direct step⟩
  · rintro ⟨next, step⟩
    exact ⟨RecognisedV15.Workflow.State.fromDirect next,
      RecognisedV15.Workflow.step_from_direct step⟩

/-- A dated positive root witness with a verified T prefix, funds and exact M payment event. -/
theorem fullPaymentHistory (bank : BankCorrection) (kind : Outcome) (early : Bool)
    (enough : requiredFunds early ≤ observedNet bank kind) :
    ∃ next, RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step
      (RecognisedV15.Workflow.State.fromDirect commonStart)
      (datesBefore45 kind early ++ [JointM.paymentEvent (grossAtCheck bank) (retained kind)])
      (RecognisedV15.Workflow.State.fromDirect next) := by
  obtain ⟨next, step⟩ := (menu bank kind early).mpr enough
  exact ⟨next, RecognisedV15.Workflow.path_from_direct
    (append (followsCommonOpening kind early) (.next step (.nil next)))⟩

theorem pendingAt46CannotSupply45 (next : State) :
    ¬ Step (JointM.afterVerification checkedAndReleased 46) (JointM.paymentEvent 16 6) next :=
  JointM.insufficientFundsBlockMaterialsPayment _ _ 44 .verified46 _ _
    (JointM.retainsVerification _ 44 46 pendingMReady) (by decide +kernel)

/-- The account calculation uses the prior outgoing actually retained in each
branch, and the M payment consumes that same provider entry with the real T occupation. -/
theorem cashInputsAreUsed (bank : BankCorrection) (kind : Outcome) (early : Bool) :
    JointM.earlierPayment ∈ (whenChecked kind early).holds.payments.posted ∧
    (JointM.attempt (grossAtCheck bank) (retained kind)).funds =
      mFunds (grossAtCheck bank) (retained kind) (tick 45) := by
  have ready := readyAt45 kind
  cases early
  · refine ⟨?_, rfl⟩
    change JointM.earlierPayment ∈ (at45 kind).holds.payments.posted
    rw [ready.holds]
    exact List.mem_cons_self
  · refine ⟨?_, rfl⟩
    have observed := JointM.retainsVerification _ 44 44 ready
    change JointM.earlierPayment ∈ (JointM.afterVerification (at45 kind) 44).holds.payments.posted
    rw [observed.holds]
    exact List.mem_cons_self

theorem fullEarlyPaymentKeepsTheOtherMaterialSix :
    let final := JointM.afterPaymentAt45 (JointM.afterVerification checkedAndReleased 44) 16 6
    final.materials.liveMaterialBudgetsAt final.holds.payments 42 (tick 46) =
      [(⟨42, 1, 8, "agreed materials terms"⟩, 6)] := by
  decide +kernel

private def comparedKinds : List Outcome :=
  [.normal, .accepted, .pendingChecked, .pendingTeachingOnly, .pendingUnreleased]

/-- Calculate the machine-checked thresholds to compare with the numerical model. -/
def rows (bank : BankCorrection) : List (Amount × Bool × Bool) :=
  comparedKinds.map fun branch ↦
    (retained branch, decide (requiredFunds false ≤ observedNet bank branch),
      decide (requiredFunds true ≤ observedNet bank branch))

theorem menuValues :
    rows lowerBankCut = [(2, true, true), (6, false, true), (6, false, true),
      (8, false, false), (10, false, false)] ∧
    rows upperBankCut = [(2, true, true), (6, true, true), (6, true, true),
      (8, false, true), (10, false, false)] := by
  decide +kernel

-- Each item is (T occupation, sufficiency without early evidence, with early evidence).
#eval rows lowerBankCut
#eval rows upperBankCut

#print axioms route
#print axioms recognisedMenu
#print axioms fullPaymentHistory
#print axioms pendingAt46CannotSupply45
#print axioms menuValues
#print axioms cashInputsAreUsed
#print axioms fullEarlyPaymentKeepsTheOtherMaterialSix

end SparkJoint
