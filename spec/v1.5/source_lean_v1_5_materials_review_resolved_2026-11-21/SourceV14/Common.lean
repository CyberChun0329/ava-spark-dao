import Std

namespace SourceV14

abbrev ActorId := Nat
abbrev AccountId := Nat
abbrev LessonId := Nat
abbrev PlaceId := Nat
abbrev Amount := Rat

/-- Verified occurrence, with the actual order distinguished within a clock tick. -/
structure Moment where
  seconds : Nat
  order : Nat
  deriving DecidableEq, Repr

def Moment.before (a b : Moment) : Prop :=
  a.seconds < b.seconds ∨ (a.seconds = b.seconds ∧ a.order < b.order)

def Moment.by (a b : Moment) : Prop := a.before b ∨ a = b

instance (a b : Moment) : Decidable (Moment.before a b) := by
  unfold Moment.before
  infer_instance

instance (a b : Moment) : Decidable (Moment.by a b) := by
  unfold Moment.by
  infer_instance

/-- A verified deadline may determine only the second, without ordering events in it. -/
inductive ClockCutoff where
  | exact (point : Moment)
  | second (seconds : Nat)
  deriving DecidableEq, Repr

instance : Coe Moment ClockCutoff := ⟨ClockCutoff.exact⟩

def ClockCutoff.metBy (cutoff : ClockCutoff) (point : Moment) : Prop :=
  match cutoff with
  | .exact deadline => point.by deadline
  | .second seconds => point.seconds < seconds

def ClockCutoff.hasPassed (cutoff : ClockCutoff) (point : Moment) : Prop :=
  match cutoff with
  | .exact deadline => deadline.before point
  | .second seconds => seconds < point.seconds

def ClockCutoff.mayHavePassed (cutoff : ClockCutoff) (point : Moment) : Prop :=
  match cutoff with
  | .exact deadline => deadline.before point
  | .second seconds => (⟨seconds, 0⟩ : Moment).before point

/-- Test a history at the exact cutoff, or at every possible order in its known second. -/
def ClockCutoff.forEveryOrder (cutoff : ClockCutoff) (check : Moment → Prop) : Prop :=
  match cutoff with
  | .exact deadline => check deadline
  | .second seconds => ∀ order, check ⟨seconds, order⟩

inductive BoundaryDirection where
  | before | after
  deriving DecidableEq, Repr

/-- The verified location of a duration boundary in the event order. -/
structure ClockBoundary where
  anchor : Moment
  direction : BoundaryDirection
  duration : Nat
  cutoff : Moment
  deriving DecidableEq, Repr

@[simp, specialize] def ClockBoundary.uniqueMatching {α : Type} (matchesKey : α → Bool) : List α → Option α
  | [] => none
  | row :: rows =>
    if matchesKey row then
      if rows.any matchesKey then none else some row
    else uniqueMatching matchesKey rows

def ClockBoundary.find (boundaries : List ClockBoundary) (anchor : Moment)
    (direction : BoundaryDirection) (duration : Nat) : Option Moment :=
  if duration = 0 then some anchor
  else
    let matchesKey := fun row : ClockBoundary ↦
      row.anchor == anchor && row.direction == direction && row.duration == duration
    match ClockBoundary.uniqueMatching matchesKey boundaries with
    | some row =>
      if (match direction with
        | .before => row.cutoff.seconds + duration == anchor.seconds
        | .after => anchor.seconds + duration == row.cutoff.seconds) then some row.cutoff else none
    | _ => none

def ClockBoundary.after (boundaries : List ClockBoundary) (anchor : Moment)
    (duration : Nat) : ClockCutoff :=
  match ClockBoundary.find boundaries anchor .after duration with
  | some deadline => .exact deadline
  | none => .second (anchor.seconds + duration)

/-- The actual order matters only at the computed cutoff second. -/
def ClockBoundary.reachedAfter (boundaries : List ClockBoundary) (anchor : Moment)
    (duration : Nat) (point : Moment) : Prop :=
  match ClockBoundary.find boundaries anchor .after duration with
  | some cutoff => cutoff.by point
  | none => anchor.seconds + duration < point.seconds

def ClockBoundary.byBefore (boundaries : List ClockBoundary) (anchor : Moment)
    (duration : Nat) (point : Moment) : Prop :=
  duration ≤ anchor.seconds ∧
  match ClockBoundary.find boundaries anchor .before duration with
  | some cutoff => point.by cutoff
  | none => point.seconds + duration < anchor.seconds

def thirtyDays : Nat := 30 * 24 * 60 * 60

inductive LessonKind where
  | oneToOne
  | group
  deriving DecidableEq, Repr

/-- The parties and normal tutor fee agreed for a lesson. -/
structure Lesson where
  id : LessonId
  kind : LessonKind
  provider : ActorId
  tutor : ActorId
  coordinator : ActorId
  normalTutorFee : Amount
  deriving DecidableEq, Repr

/-- The confirmation terms for a place. The payable fee reflects applicable discounts. -/
structure Place where
  id : PlaceId
  lesson : LessonId
  student : ActorId
  customer : ActorId
  payer : ActorId
  account : AccountId
  normalFee : Amount
  feePayable : Amount
  deriving DecidableEq, Repr

def Place.matches (p : Place) (l : Lesson) : Prop := p.lesson = l.id

def Place.validFees (p : Place) : Prop :=
  0 < p.normalFee ∧ 0 ≤ p.feePayable ∧ p.feePayable ≤ p.normalFee

def sumAmounts {α : Type} (rows : List α) (amount : α → Amount) : Amount :=
  rows.foldl (fun acc row ↦ acc + amount row) 0

@[inline] def sumAmountsWhere {α : Type} (rows : List α) (includeRow : α → Bool)
    (amount : α → Amount) : Amount :=
  rows.foldl (fun total row ↦ if includeRow row then total + amount row else total) 0

@[simp] theorem sumAmountsWhere_eq_filter {α : Type} (rows : List α) (includeRow : α → Bool)
    (amount : α → Amount) :
    sumAmountsWhere rows includeRow amount = sumAmounts (rows.filter includeRow) amount := by
  simp only [sumAmountsWhere, sumAmounts, List.foldl_filter]

/-- Section 1.2 excludes the handler for this decision if any listed interest is affected. -/
structure DirectInterest where
  amountOwedToHandler : Bool
  amountOwedByHandler : Bool
  liability : Bool
  timeOfReceipt : Bool
  deriving DecidableEq, Repr

def DirectInterest.affected (i : DirectInterest) : Prop :=
  i.amountOwedToHandler = true ∨ i.amountOwedByHandler = true ∨
    i.liability = true ∨ i.timeOfReceipt = true

end SourceV14
