import RecognisedV15.Workflow

namespace SparkGap.CompetingPrefunding

open SourceV14 SourceV14.Workflow

-- Entry 1 is the provider's spendable balance of 360. Customer recharge is separate.
private def providerEntry (committed secured : Amount) : FundingEntry :=
  ⟨1, .providerFunds, .spendable, 360, committed, secured⟩

private def secondCourse (point : Moment) (committed secured : Amount) : CurrentLessonFunds :=
  ⟨2, 1, point, [providerEntry committed secured]⟩

private def secondBefore := secondCourse ⟨0, 0⟩ 0 320
private def secondAfter := secondCourse ⟨0, 2⟩ 58 0
private def firstReservation : List Reserves.Reservation := [⟨1, 1, 1, 58⟩]

/-- At the earlier cut the same provider funding can cover course 2's request of 320. -/
theorem secondFundingBeforeFirstReservation :
    Reserves.FundingContextMatches [] secondBefore ∧
    (providerEntry 0 320).valid ∧ secondBefore.covers 320 ∧ secondBefore.secures 320 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro entry member
    simp only [secondBefore, secondCourse, List.mem_singleton] at member
    subst entry
    decide +kernel
  · unfold FundingEntry.valid
    decide +kernel
  · unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
    decide +kernel
  · unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
    decide +kernel

/-- The cross-layer input at the later cut includes the App's independently effective 58. -/
theorem secondFundingAfterFirstReservation :
    ¬ Reserves.FundingContextMatches firstReservation secondBefore ∧
    Reserves.FundingContextMatches firstReservation secondAfter ∧
    (providerEntry 58 0).available = 302 ∧ ¬ secondAfter.covers 320 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro contextMatches
    have stale := contextMatches (providerEntry 0 320) (by simp [secondBefore, secondCourse])
    have impossible : ¬ Reserves.occupiedElsewhere firstReservation secondBefore 1 ≤ 0 := by
      decide +kernel
    exact impossible stale
  · intro entry member
    simp only [secondAfter, secondCourse, List.mem_singleton] at member
    subst entry
    decide +kernel
  · decide +kernel
  · unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
    decide +kernel

#print axioms secondFundingBeforeFirstReservation
#print axioms secondFundingAfterFirstReservation

end SparkGap.CompetingPrefunding
