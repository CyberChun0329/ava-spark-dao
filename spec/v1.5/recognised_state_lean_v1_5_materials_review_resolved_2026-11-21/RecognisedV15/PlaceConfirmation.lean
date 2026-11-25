import RecognisedV15.Institutional
import SourceV14.Workflow

namespace RecognisedV15.PlaceConfirmation

open SourceV14 SourceV14.Booking SourceV14.Confirmation SourceV14.Course SourceV14.Settlement
open SourceV14.Workflow

private def knownForm (schedule : BookingScheduleEvidence) (form : PartOne) : Prop :=
  form ∈ schedule.effectiveForms ∨ ∃ booking, (form, booking) ∈ schedule.bookings

private def sameLesson (schedule : BookingScheduleEvidence) (lesson : Lesson) : Prop :=
  (∀ form, knownForm schedule form → form.lesson = lesson) ∧
  (∀ roster ∈ schedule.groupRoster, roster.lesson = lesson.id) ∧
  ∀ date ∈ schedule.scheduleHistory, date.lesson = lesson.id

/-- Confirm a place with its agreed form, booking and roster evidence, using a fresh debit
or a recorded full discount. Record the agreed schedule and reserve the verified funding
against shared commitments. -/
def Step (before : LessonEvidence) (reserves : List Reserves.Reservation)
    (form : PartOne) (booking : BookingEvidence) (roster : Option Roster)
    (payment : Booking.ConfirmationPayment) (after : LessonEvidence)
    (followingReserves : List Reserves.Reservation) : Prop :=
  let schedule := before.bookingSchedule
  let credit := before.creditFee
  let confirmed : LessonEvidence := { before with
    bookingSchedule := { schedule with
      bookings := schedule.bookings ++ [(form, booking)]
      bookedRosters := schedule.bookedRosters ++ roster.toList.map (fun plan ↦ (form, plan))
      effectiveForms := match form.lesson.kind with
        | .oneToOne => [form]
        | .group => schedule.effectiveForms
      scheduleHistory := if form.schedule ∈ schedule.scheduleHistory then schedule.scheduleHistory
        else schedule.scheduleHistory ++ [form.schedule] }
    creditFee := match payment with
      | .debit posting => { credit with ledger := credit.ledger ++ [posting] }
      | .fullDiscount record => { credit with discounts := credit.discounts ++ [record] } }
  Reserves.FundingContextMatches reserves booking.funding.funds ∧
  (sameLesson schedule form.lesson ∧
    (∀ earlier ∈ schedule.bookings, earlier.1.place.id ≠ form.place.id) ∧
    ((schedule.scheduleHistory = [] ∧
        ∀ existing, knownForm schedule existing → existing.schedule = form.schedule) ∨
      EffectiveSchedule form.lesson before.toDirect form.schedule form.confirmedAt) ∧
    form.schedule.agreedAt.by form.confirmedAt ∧
    (match form.lesson.kind, roster, schedule.groupRoster with
    | .oneToOne, none, none => schedule.effectiveForms = [] ∨ schedule.effectiveForms = [form]
    | .group, some plan, none =>
        form.confirmedAt.by plan.lockedAt ∧
        ∀ existing, knownForm schedule existing → FormUsesRoster existing plan
    | .group, some plan, some locked =>
        plan = locked ∧ RegisterMatchesForms locked before.toDirect form.lesson ∧
          form ∈ schedule.effectiveForms
    | _, _, _ => False) ∧
    (match payment with
    | .debit posting =>
        booking.debit = some posting ∧
        ∀ earlier ∈ credit.ledger, earlier.id ≠ posting.id ∧ earlier.point ≠ posting.point
    | .fullDiscount record =>
        booking.debit = none ∧ record.covers form.place form.confirmedAt ∧
        form.discountBasis = some record.basis ∧ record ∉ credit.discounts) ∧
    confirmed.confirmedPlace form booking roster ∧
    before.toDirect.readsTutorAtConfirmation form ∧ after = confirmed) ∧
  followingReserves = Reserves.reserve reserves booking.funding.funds

theorem step_iff (before : LessonEvidence) (reserves : List Reserves.Reservation)
    (form : PartOne) (booking : BookingEvidence) (roster : Option Roster)
    (payment : Booking.ConfirmationPayment) (after : LessonEvidence)
    (followingReserves : List Reserves.Reservation) :
    Step before reserves form booking roster payment after followingReserves ↔
      let event := Booking.Event.confirmPlace form booking roster payment
      event.fundingContext reserves ∧ Booking.Step before.toDirect event after.toDirect ∧
        followingReserves = event.reservations reserves := by
  have directOutcome (confirmed : LessonEvidence) :
      after = confirmed ↔ after.toDirect = confirmed.toDirect :=
    ⟨congrArg LessonEvidence.toDirect, fun h ↦ by
      simpa only [LessonEvidence.fromDirect_toDirect] using
        congrArg LessonEvidence.fromDirect h⟩
  cases payment <;> simp only [Step, directOutcome] <;> rfl

end RecognisedV15.PlaceConfirmation
