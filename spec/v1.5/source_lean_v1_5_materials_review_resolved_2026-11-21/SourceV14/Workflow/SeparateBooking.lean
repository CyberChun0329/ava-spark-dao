import SourceV14.Course

namespace SourceV14.Workflow.SeparateBooking

open SourceV14.Booking SourceV14.Confirmation SourceV14.Course SourceV14.Settlement

/-- The Part 2 reference and the two previously retained booking rows. The roster
    supplied for each booking is the roster used when that place was confirmed. -/
structure Link where
  original : PartOne
  next : PartOne
  originalBooking : BookingEvidence
  nextBooking : BookingEvidence
  originalRoster : Option Roster
  nextRoster : Option Roster
  change : ChangeRecord

private def retainsRoster (ev : StartEvidence) (form : PartOne)
    (claimed : Option Roster) : Prop :=
  match form.lesson.kind, claimed with
  | .group, some roster =>
    (form, roster) ∈ ev.bookedRosters ∧
    ∀ other, (form, other) ∈ ev.bookedRosters → other = roster
  | .oneToOne, none => True
  | _, _ => False

/-- Record a separate booking without changing either lesson's evidence. The legacy
    check needs the original lesson's academic team and the new booking's roster,
    while its credit and teaching evidence belong to the new lesson. -/
def Step (original next : StartEvidence) (before : List Link) (link : Link)
    (after : List Link) : Prop :=
  (link.original, link.originalBooking) ∈ original.bookings ∧
  (link.next, link.nextBooking) ∈ next.bookings ∧
  retainsRoster original link.original link.originalRoster ∧
  retainsRoster next link.next link.nextRoster ∧
  CanConfirmPlace link.original link.originalBooking link.originalRoster original.openingCredit
    original.ledger original.creditRecords original.discounts original.teachingBegan ∧
  link.original.confirmedAt.by link.change.nextSchedule.agreedAt ∧
  CanConfirmSeparateBooking link.original link.next link.change link.nextBooking
    { next with groupRoster := link.nextRoster, academicTeamAt := original.academicTeamAt } ∧
  after = before ++ [link]

end SourceV14.Workflow.SeparateBooking
