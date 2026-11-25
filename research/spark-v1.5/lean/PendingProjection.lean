import PendingReserve
import TPrefix

/-! Continuing cases of the same funding inventory used by the T booking. -/

namespace SparkJoint
open SourceV14 SourceV14.Workflow
open JointT (fundingTerms place tutorExpense standardUntaught standardTaught
  providerCompensationTaught fullRefund noFaultUntaught ordinary partialNoFault
  someTeaching noTeaching tutorAtFault providerAtFault)

def pendingCut := tick 41

private theorem dueTutor :
    tutorExpense.owedAt fundingTerms.payments pendingCut = 2 := by decide +kernel

private theorem oneExpense (sc : FundingCase) :
    sc.expenses fundingTerms =
      if tutorExpense.conditions.all (fun c ↦ c.holds sc.facts) then [tutorExpense] else [] := by
  rw [FundingCase.expenses, JointT.onlyExpense]
  change List.filter (fun _ ↦ tutorExpense.conditions.all (fun c ↦ c.holds sc.facts))
      [tutorExpense] = _
  cases (tutorExpense.conditions.all (fun c ↦ c.holds sc.facts)) <;> rfl

private theorem costCases {sc : FundingCase} {row : PlaceFundingOutcome}
    (sel : sc.selections = [(place, row)]) :
    sc.remainingCost fundingTerms pendingCut =
      row.customerCost place +
        if tutorExpense.conditions.all (fun c ↦ c.holds sc.facts) then 2 else 0 := by
  unfold FundingCase.remainingCost
  rw [sel, oneExpense]
  split <;> simp [sumAmounts, dueTutor, Rat.zero_add]

/-- Verifying actual teaching and ruling out a provider-side fault in this
matter leaves the tutor's performance open. The worst live case costs six. -/
theorem pendingCap {sc : FundingCase}
    (possible : sc.possible fundingTerms JointT.lesson [place])
    (teaching : sc.facts .teachingBegan = true)
    (provider : sc.facts providerAtFault = false) :
    sc.remainingCost fundingTerms pendingCut ≤ 6 := by
  obtain ⟨row, member, selected, _, factMatch⟩ := onlyPlace (by rfl) possible
  rw [JointT.outcomes, List.mem_cons] at member
  rcases member with rfl | member
  · have obs := requiredFact factMatch (subject := .teachingBegan) (value := false)
        (by simp [standardUntaught, noTeaching])
    simp [teaching] at obs
  rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_cons, List.mem_cons,
    List.mem_singleton] at member
  rw [costCases selected]
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · have obs := requiredFact factMatch (subject := tutorAtFault) (value := true)
        (by simp [standardTaught])
    rw [JointT.customerCosts.2.1]
    simp [tutorExpense, FundingCondition.holds, obs]
    decide +kernel
  · have obs := requiredFact factMatch (subject := providerAtFault) (value := true)
        (by simp [providerCompensationTaught])
    simp [provider] at obs
  · rw [JointT.customerCosts.2.2.2.1]
    split <;> decide +kernel
  · have obs := requiredFact factMatch (subject := .teachingBegan) (value := false)
        (by simp [noFaultUntaught, noTeaching])
    simp [teaching] at obs
  · rw [JointT.customerCosts.2.2.2.2.2.1]
    split <;> decide +kernel
  · rw [JointT.customerCosts.2.2.2.2.2.2]
    split <;> decide +kernel

/-- A narrower fact check that verifies only teaching keeps provider fault open. -/
theorem teachingCapEight {sc : FundingCase}
    (possible : sc.possible fundingTerms JointT.lesson [place])
    (teaching : sc.facts .teachingBegan = true) :
    sc.remainingCost fundingTerms pendingCut ≤ 8 := by
  obtain ⟨row, member, selected, _, factMatch⟩ := onlyPlace (by rfl) possible
  rw [JointT.outcomes, List.mem_cons] at member
  rcases member with rfl | member
  · have obs := requiredFact factMatch (subject := .teachingBegan) (value := false)
        (by simp [standardUntaught, noTeaching])
    simp [teaching] at obs
  rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_cons, List.mem_cons,
    List.mem_singleton] at member
  rw [costCases selected]
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [JointT.customerCosts.2.1]
    split <;> decide +kernel
  · rw [JointT.customerCosts.2.2.1]
    split <;> decide +kernel
  · rw [JointT.customerCosts.2.2.2.1]
    split <;> decide +kernel
  · have obs := requiredFact factMatch (subject := .teachingBegan) (value := false)
        (by simp [noFaultUntaught, noTeaching])
    simp [teaching] at obs
  · rw [JointT.customerCosts.2.2.2.2.2.1]
    split <;> decide +kernel
  · rw [JointT.customerCosts.2.2.2.2.2.2]
    split <;> decide +kernel

def untaughtScenario : FundingCase :=
  ⟨[(place, standardUntaught)], (· == .partyAtFaultForDisruption)⟩

theorem untaughtStillCostsTen :
    untaughtScenario.possible fundingTerms JointT.lesson [place] ∧
    untaughtScenario.remainingCost fundingTerms pendingCut = 10 := by
  have selection : untaughtScenario.selections = [(place, standardUntaught)] := rfl
  refine ⟨?_, ?_⟩
  · simp [FundingCase.possible, untaughtScenario, JointT.outcomes, standardUntaught,
      PlaceFundingOutcome.matchesFacts, noTeaching, FundingCondition.holds]
    all_goals decide +kernel
  · rw [costCases selection, JointT.customerCosts.1]
    decide +kernel

def providerFaultScenario : FundingCase :=
  ⟨[(place, providerCompensationTaught)], fun f ↦ f == .teachingBegan || f == providerAtFault⟩

theorem teachingAloneStillAllowsEight :
    providerFaultScenario.facts .teachingBegan = true ∧
    providerFaultScenario.possible fundingTerms JointT.lesson [place] ∧
    providerFaultScenario.remainingCost fundingTerms pendingCut = 8 := by
  have selection : providerFaultScenario.selections = [(place, providerCompensationTaught)] := rfl
  refine ⟨rfl, ?_, ?_⟩
  · simp [FundingCase.possible, providerFaultScenario, JointT.outcomes,
      providerCompensationTaught, PlaceFundingOutcome.matchesFacts, someTeaching,
      FundingCondition.holds]
    all_goals decide +kernel
  · rw [costCases selection, JointT.customerCosts.2.2.1]
    decide +kernel

end SparkJoint
