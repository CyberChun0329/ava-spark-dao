import RecognisedV15.Workflow
import Init.Data.Rat.Lemmas

/-! Research witness for the retained no-teaching exposure and a separately verified
partial-teaching funding cut. Uses the locked workflow without extending its transitions. -/

namespace SparkJoint
open SourceV14 SourceV14.Workflow

def tick (n : Nat) : Moment := ⟨n, 0⟩

def tInitial : Reserves.Reservation := ⟨10, 100, 1, 10⟩

def mInitial : Reserves.Reservation := ⟨10, 42, 1, 12⟩

def tAt (amount : Amount) : Reserves.Reservation := { tInitial with amount }

def release (amount : Amount) (point : Moment) (evidence : EvidenceRef) : Reserves.Release :=
  ⟨10, 100, 1, amount, point, evidence⟩

def mFunds (gross occupied : Amount) (point : Moment) : CurrentLessonFunds :=
  ⟨42, 10, point, [⟨1, .providerFunds, .spendable, gross, occupied, 0⟩]⟩

theorem releaseUpdates {s : State} {first last : List Reserves.Reservation}
    {amount : Amount} {row : Reserves.Release} {verified : Reserves.Release → Prop}
    (past : s.activeReserves = first ++ tInitial :: last)
    (decrease : row.amount = amount)
    (same : row.matches tInitial) (accounts : verified row) :
    Step s (.reserveReleased row verified)
      {s with activeReserves := first ++ tAt (10 - amount) :: last} := by
  subst amount
  exact .reserveReleased past same accounts

theorem noReleaseWithoutAccounting {s t : State} {row : Reserves.Release}
    {verified : Reserves.Release → Prop}
    (step : Step s (.reserveReleased row verified) t) :
    verified row := by
  cases step with
  | reserveReleased _ _ evidence => exact evidence

theorem tenCannotBeReportedAsSix :
    ¬ Reserves.FundingContextMatches [mInitial, tInitial] (mFunds 16 6 (tick 45)) := by
  intro check
  have h := check ⟨1, .providerFunds, .spendable, 16, 6, 0⟩ (by simp [mFunds])
  revert h
  decide +kernel

theorem sixProvidesTen :
    Reserves.occupiedElsewhere [mInitial, tAt 6] (mFunds 16 6 (tick 45)) 1 = 6 ∧
    (⟨1, .providerFunds, .spendable, 16, 6, 0⟩ : FundingEntry).available = 10 := by
  decide +kernel

theorem tenLeavesSix :
    Reserves.occupiedElsewhere [mInitial, tInitial] (mFunds 16 10 (tick 45)) 1 = 10 ∧
    (⟨1, .providerFunds, .spendable, 16, 10, 0⟩ : FundingEntry).available = 6 := by
  decide +kernel

theorem onlyPlace {scenario : FundingCase} {terms : FundingTerms} {lesson : Lesson}
    {place : Place} (single : lesson.kind = .oneToOne)
    (p : scenario.possible terms lesson [place]) :
    ∃ row ∈ terms.outcomes, scenario.selections = [(place, row)] ∧
      row.place = place.id ∧ row.matchesFacts scenario.facts := by
  have len := p.2.1.resolve_right (by rw [single]; decide)
  obtain ⟨⟨found, row⟩, hs⟩ := List.length_eq_one_iff.mp len
  have retained := p.2.2.2 found row (by rw [hs]; simp)
  have foundEq : found = place := List.mem_singleton.mp retained.1
  subst found
  exact ⟨row, retained.2.1, hs, retained.2.2⟩

theorem requiredFact {row : PlaceFundingOutcome} {facts : FundingFact → Bool}
    {subject : FundingFact} {value : Bool} (p : row.matchesFacts facts)
    (member : ⟨subject, value⟩ ∈ row.conditions) : facts subject = value := by
  simpa [FundingCondition.holds] using p.1 _ member

/-- The two cash cuts use one provider's initial entry and actual movements,
not the customer's separate spend-only credit account. The post-commitment
debit is an exogenous bank loss, not an elective release of encumbered money. -/
structure BankCorrection where
  unrecoverableDebit : Amount
  debitAt : Moment
  evidence : EvidenceRef

def lowerBankCut : BankCorrection := ⟨4, tick 43, 91⟩
def upperBankCut : BankCorrection := ⟨2, tick 43, 92⟩

def accountGross (oldMaterialActuallyPaid : Amount) (bank : BankCorrection) : Amount :=
  22 - oldMaterialActuallyPaid - bank.unrecoverableDebit

theorem accountCuts :
    accountGross 2 lowerBankCut = 16 ∧ accountGross 2 upperBankCut = 18 ∧
    (tick 29).before (tick 40) ∧ (tick 40).before lowerBankCut.debitAt ∧
    lowerBankCut.debitAt.before (tick 45) := by
  decide +kernel

end SparkJoint
