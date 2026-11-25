import SourceV14.Workflow.Booking
import SourceV14.Workflow.Redress
import SourceV14.Workflow.SeparateBooking

namespace SourceV14.Workflow.BookingEntitlements

open SourceV14.Booking SourceV14.Confirmation SourceV14.Course

private def hasIndependentPrice (verifiedContractualDiscount : PartOne → Moment → Prop)
    (form : PartOne) (atTime : Moment) : Prop :=
  form.place.feePayable = form.place.normalFee ∨ verifiedContractualDiscount form atTime

/-- §§2.3 and 3.5. Identify a reduced price by the verified independent terms or by the
    recorded remedy applied to the booking being confirmed. -/
def confirmationAllowed (course : LessonId → StartEvidence)
    (verifiedContractualDiscount : PartOne → Moment → Prop) (history : Redress.History)
    (event : Booking.Event) (discount : Option Redress.DiscountBooking)
    (after : StartEvidence) : Prop :=
  match event with
  | .confirmPlace form booking .. =>
    match discount with
    | none => hasIndependentPrice verifiedContractualDiscount form form.confirmedAt
    | some use =>
      let original := course use.remedy.facts.form.lesson.id
      let shared := { original with ledger := after.ledger, discounts := after.discounts }
      use.agreed = form ∧ use.booking = booking ∧
      hasIndependentPrice verifiedContractualDiscount use.selected form.confirmedAt ∧
      use.appliesAtBooking history shared after (history.usedDiscounts ++ history.pendingDiscountUses)
  | _ => discount = none

/-- The confirmed booking consumes the right when the debit or full discount is recorded. -/
def recordConfirmation (history : Redress.History)
    (discount : Option Redress.DiscountBooking) : Redress.History :=
  match discount with
  | none => history
  | some use => { history with pendingDiscountUses := history.pendingDiscountUses ++ [use.use] }

/-- §2.2. Check retained acceptance by the original form's deadline, including changes
    that become effective later and a separately linked booking with timely signed consent. -/
def noTimelyRearrangement (ev : StartEvidence) (links : List SeparateBooking.Link)
    (event : Cancellation.Event) : Prop :=
  match event with
  | .oneToOne .. => True
  | .noFault form cancellation =>
    let timely := fun (point : Moment) ↦ point.by form.deadlines.noFaultAcceptance
    let affects := fun (row : ChangeRecord) ↦
      row.originalLesson = form.lesson.id ∧ form.place.id ∈ row.scope
    (∀ change ∈ ev.changes, change.previous = cancellation.schedule → affects change.record →
      change.allowed form.lesson ev → ¬timely change.record.nextSchedule.agreedAt) ∧
    (∀ replacement ∈ ev.tutorReplacements, replacement.previous = cancellation.schedule →
      affects replacement.record → replacement.conforms form.lesson ev →
      cancellation.disruptionVerifiedAt.before replacement.effectiveAt →
      ¬timely replacement.agreedAt) ∧
    (∀ link ∈ links, link.original = form →
      let agreedAt := link.change.nextSchedule.agreedAt
      let signed := link.nextBooking.signatures
      cancellation.disruptionVerifiedAt.by agreedAt →
      EffectiveSchedule form.lesson ev cancellation.schedule agreedAt →
      ¬(timely agreedAt ∧ timely signed.providerAccepted ∧ timely signed.tutorAccepted))

end SourceV14.Workflow.BookingEntitlements
