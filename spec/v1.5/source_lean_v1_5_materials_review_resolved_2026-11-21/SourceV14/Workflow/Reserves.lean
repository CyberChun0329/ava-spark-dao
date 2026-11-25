import SourceV14.Funding

namespace SourceV14.Workflow.Reserves

/-- Active commitments to the same verified funding entry are shared across
lesson accounts. A funding entry is identified within its provider's books. -/
structure Reservation where
  provider : ActorId
  lesson : LessonId
  entry : Nat
  amount : Amount

def occupiedElsewhere (active : List Reservation) (funds : CurrentLessonFunds)
    (entry : Nat) : Amount :=
  sumAmounts (active.filter fun row ↦
    row.provider == funds.provider && row.lesson != funds.lesson && row.entry == entry)
    Reservation.amount

def FundingContextMatches (active : List Reservation) (funds : CurrentLessonFunds) : Prop :=
  ∀ entry ∈ funds.entries, occupiedElsewhere active funds entry.id ≤ entry.committedElsewhere

/-- Confirmation may retain or enlarge this course's reservation. Closing
the underlying commitment remains a separate recorded matter. -/
def reserve (active : List Reservation) (funds : CurrentLessonFunds) : List Reservation :=
  funds.entries.foldl (fun reservations entry ↦
    let same := fun row : Reservation ↦
      row.provider == funds.provider && row.lesson == funds.lesson && row.entry == entry.id
    let prior := sumAmounts (reservations.filter same) Reservation.amount
    (reservations.filter fun row ↦ !same row) ++
      [⟨funds.provider, funds.lesson, entry.id, max prior entry.securedForLesson⟩]) active

/-- §4.4. Accounting evidence identifies the amount that has actually ceased
to be committed. This records that fact and cannot cancel a customer right. -/
structure Release where
  provider : ActorId
  lesson : LessonId
  entry : Nat
  amount : Amount
  occurred : Moment
  evidence : EvidenceRef

def Release.matches (row : Release) (reservation : Reservation) : Prop :=
  row.provider = reservation.provider ∧ row.lesson = reservation.lesson ∧
    row.entry = reservation.entry ∧ 0 < row.amount ∧ row.amount ≤ reservation.amount

end SourceV14.Workflow.Reserves
