import SourceV14.Workflow.Redress

namespace FidelityRefundClockChecks

open SourceV14 SourceV14.Confirmation SourceV14.Course SourceV14.Workflow.Redress

variable (f : PartOne) (ev : StartEvidence) (request : CancellationRequest)
variable (actual : PaymentTrigger) (observed : Moment) (seconds : Nat) (reference : String)

private def cancellationEvidence : RefundTriggerEvidence where
  cancellationTerm := fun _ _ ↦ True

private def otherEvidence (actual : PaymentTrigger) : RefundTriggerEvidence where
  otherOccurrence := fun _ _ event ↦ event = actual

theorem cancellationUsesActualRequest
    (h : cancellationEvidence.applies f ev (.after seconds reference false) (some actual)
      (some request) observed) : actual.point = request.point := by
  have h' : actual.boundaries = ev.clockBoundaries ∧ actual.point.by observed ∧
      actual.point = request.point := by
    simpa [RefundTriggerEvidence.applies, cancellationEvidence] using h
  exact h'.2.2

theorem cancellationAllowsActualRequest
    (boundaries : actual.boundaries = ev.clockBoundaries) (before : actual.point.by observed)
    (point : actual.point = request.point) :
    cancellationEvidence.applies f ev (.after seconds reference false) (some actual)
      (some request) observed := by
  exact ⟨actual, rfl, boundaries, before, Or.inl ⟨trivial, request, rfl, point⟩⟩

theorem verifiedOtherOccurrenceAllowsDifferentClock
    (boundaries : actual.boundaries = ev.clockBoundaries) (before : actual.point.by observed) :
    (otherEvidence actual).applies f ev (.after seconds reference false) (some actual)
      (some request) observed := by
  exact ⟨actual, rfl, boundaries, before, Or.inr ⟨id, rfl⟩⟩

theorem unverifiedOccurrenceRejected :
    ¬ ({} : RefundTriggerEvidence).applies f ev (.after seconds reference false) (some actual)
      (some request) observed := by
  simp [RefundTriggerEvidence.applies]

theorem inventedBoundariesRejected (different : actual.boundaries ≠ ev.clockBoundaries) :
    ¬ cancellationEvidence.applies f ev (.after seconds reference false) (some actual)
      (some request) observed := by
  simp [RefundTriggerEvidence.applies, different]

theorem fixedUnaffected :
    ({} : RefundTriggerEvidence).applies f ev (.fixed observed) none none observed := by trivial

theorem lessonStartUnaffected :
    ({} : RefundTriggerEvidence).applies f ev (.after seconds reference true) none none observed := by
  trivial

private def day (n : Nat) : Moment := ⟨n * 86400, 0⟩
private def clock : List ClockBoundary :=
  [⟨day 2, .after, 86400, day 3⟩, ⟨day 3, .after, 86400, day 4⟩]
private def atDay (n : Nat) : PaymentTrigger := ⟨"cancellation", day n, clock⟩

/-- The retained day-2 receipt determines the day-3 boundary. -/
theorem actualCancellationUsesDayThree :
    PaymentDeadline.applies (.after 86400 "cancellation" false) (some (atDay 2)) (day 3) ∧
    cancellationEvidence.applies f { ev with clockBoundaries := clock }
      (.after 86400 "cancellation" false) (some (atDay 2))
      (some { request with point := day 2 }) (day 4) := by
  simp [PaymentDeadline.applies, RefundTriggerEvidence.applies, cancellationEvidence,
    atDay, clock, ClockBoundary.find, ClockBoundary.uniqueMatching, day, Moment.by, Moment.before]

/-- A day-3 event and its day-4 boundary cannot replace the retained day-2 cancellation. -/
theorem delayedCancellationCannotRestart :
    ¬ cancellationEvidence.applies f { ev with clockBoundaries := clock }
      (.after 86400 "cancellation" false) (some (atDay 3))
      (some { request with point := day 2 }) (day 4) := by
  simp [RefundTriggerEvidence.applies, cancellationEvidence, atDay, day]

#print axioms actualCancellationUsesDayThree
#print axioms delayedCancellationCannotRestart
#print axioms cancellationUsesActualRequest
#print axioms verifiedOtherOccurrenceAllowsDifferentClock
#print axioms inventedBoundariesRejected

end FidelityRefundClockChecks
