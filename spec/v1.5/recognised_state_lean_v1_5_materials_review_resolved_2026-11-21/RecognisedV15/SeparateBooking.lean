import RecognisedV15.Institutional
import SourceV14.Workflow.SeparateBooking

namespace RecognisedV15.SeparateBooking

open SourceV14.Booking SourceV14.Confirmation SourceV14.Course SourceV14.Settlement
open SourceV14.Workflow.SeparateBooking (Link)

/-- A group booking refers to the unique roster retained for its form at confirmation.
A one-to-one form has no roster reference. -/
private def retainsRoster (evidence : BookingScheduleEvidence) (form : PartOne)
    (claimed : Option Roster) : Prop :=
  match form.lesson.kind, claimed with
  | .group, some roster =>
    (form, roster) ∈ evidence.bookedRosters ∧
    ∀ other, (form, other) ∈ evidence.bookedRosters → other = roster
  | .oneToOne, none => True
  | _, _ => False

/-- Record the Part 2 link between two retained bookings. Each booking uses its own
Part 1 confirmation, roster, credit and teaching evidence. The original place supplies
the coordinator, payer and student, and its academic team sends the notice.
The link is appended to the separate-booking history. -/
def Step (original next : LessonEvidence) (before : List Link) (link : Link)
    (after : List Link) : Prop :=
  let form := link.original
  let nextForm := link.next
  let change := link.change
  let date := change.nextSchedule
  let target := date.confirmationTarget
  (form, link.originalBooking) ∈ original.bookingSchedule.bookings ∧
  (nextForm, link.nextBooking) ∈ next.bookingSchedule.bookings ∧
  retainsRoster original.bookingSchedule form link.originalRoster ∧
  retainsRoster next.bookingSchedule nextForm link.nextRoster ∧
  original.confirmedPlace form link.originalBooking link.originalRoster ∧
  form.confirmedAt.by date.agreedAt ∧
  form.matches ∧ form.lesson.id ≠ nextForm.lesson.id ∧
  change.separateBooking = some nextForm.lesson.id ∧ change.replacementTutor = none ∧
  date = nextForm.schedule ∧
  change.originalLesson = form.lesson.id ∧ date.valid ∧ form.place.id ∈ change.scope ∧
  change.contactedCoordinator = form.lesson.coordinator ∧ change.contactedAt.by date.agreedAt ∧
  (∃ consent ∈ change.consents,
    consent.place = form.place.id ∧ consent.actor = form.place.payer ∧
    consent.target = target ∧ consent.point.by date.agreedAt) ∧
  (∃ notice ∈ change.notices,
    notice.target = target ∧ notice.recipient = form.place.student ∧
    notice.channel = form.contacts.studentNotice ∧
    original.bookingSchedule.academicTeamAt form.lesson.id notice.sender notice.point ∧
    date.agreedAt.by notice.point) ∧
  date.lesson = nextForm.lesson.id ∧
  next.confirmedPlace nextForm link.nextBooking link.nextRoster ∧
  after = before ++ [link]

/-- The local rule matches the source rule on the two selected lesson records. -/
theorem step_iff (original next : LessonEvidence) (before : List Link) (link : Link)
    (after : List Link) :
    Step original next before link after ↔
      SourceV14.Workflow.SeparateBooking.Step original.toDirect next.toDirect before link after := by
  by_cases replacement : link.change.replacementTutor = none
  · by_cases reference : link.change.separateBooking = some link.next.lesson.id
    · simp [Step, SourceV14.Workflow.SeparateBooking.Step, CanConfirmSeparateBooking,
        ChangeRecord.matches, ChangeRecord.matchesFrom, replacement, reference,
        DesignatedConfirmation, NoticePerformed, LessonEvidence.confirmedPlace,
        LessonEvidence.toDirect, and_assoc]
      intro _ _
      rfl
    · simp [Step, SourceV14.Workflow.SeparateBooking.Step, CanConfirmSeparateBooking, reference]
  · simp [Step, SourceV14.Workflow.SeparateBooking.Step, CanConfirmSeparateBooking, replacement]

end RecognisedV15.SeparateBooking
