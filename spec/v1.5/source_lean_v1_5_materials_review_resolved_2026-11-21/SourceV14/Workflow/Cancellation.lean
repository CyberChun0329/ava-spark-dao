import SourceV14.Course

namespace SourceV14.Workflow.Cancellation

open SourceV14.Booking SourceV14.Confirmation SourceV14.Course

/-- §2.2 and Form Parts 1–2. The customer's actual contact with the coordinator
    identifies the original lesson and place. A later booking has its own lesson ID. -/
inductive Event where
  | oneToOne (form : PartOne) (request : CancellationRequest)
  | noFault (form : PartOne) (record : NoFaultCancellationRecord)

abbrev History := List Event

def Event.form : Event → PartOne
  | .oneToOne form _ | .noFault form _ => form

def Event.request : Event → CancellationRequest
  | .oneToOne _ request => request
  | .noFault _ record => record.cancellation

def Event.atTime (event : Event) : Moment := event.request.point

/-- §2.2. Retain the original form and the actual cancellation under its terms. -/
def Step (before : History) (ev : StartEvidence) (event : Event) (after : History) : Prop :=
  event.form.confirmedAt.by event.atTime ∧
  (∀ old ∈ before, old.request.lesson ≠ event.request.lesson ∨
    old.request.place ≠ event.request.place) ∧
  (match event with
  | .oneToOne form request =>
      form ∈ ev.effectiveForms ∧ CanCancelOneToOne form request ev
  | .noFault form record => record.conforms form ev) ∧
  after = before ++ [event]

/-- Use the original place's cancellation when deciding its start or fee treatment. -/
def PlaceCancelledAt (history : History) (place : Place) (query : Moment) : Prop :=
  ∃ event ∈ history, event.request.lesson = place.lesson ∧
    event.request.place = place.id ∧ event.atTime.by query

/-- Every effective place has a recorded cancellation for this lesson. -/
def LessonCancelledAt (history : History) (ev : StartEvidence) (lesson : Lesson)
    (query : Moment) : Prop :=
  ∃ roster forms, ev.rosterFormsAt lesson query roster forms ∧ forms ≠ [] ∧
    ∀ form ∈ forms, PlaceCancelledAt history form.place query

/-- §2.2. A group still needs a student taking the lesson under an active booking. -/
def CompatibleWithStart (history : History) (ev : StartEvidence) (lesson : Lesson)
    (query : Moment) (studentsTakingLesson : List ActorId) : Prop :=
  ∃ roster forms, ev.rosterFormsAt lesson query roster forms ∧
    match lesson.kind with
    | .oneToOne => ∀ form ∈ forms, ¬ PlaceCancelledAt history form.place query
    | .group => ∃ form ∈ forms, form.place.student ∈ studentsTakingLesson ∧
        ¬ PlaceCancelledAt history form.place query

def HasOneToOneCancellation (history : History) (form : PartOne)
    (request : CancellationRequest) : Prop :=
  Event.oneToOne form request ∈ history

def HasNoFaultCancellation (history : History) (form : PartOne)
    (record : NoFaultCancellationRecord) : Prop :=
  Event.noFault form record ∈ history

/-- §§2.2 and 4.3. The actual credit receipt uses the retained cancellation's obligation. -/
def NoFaultReceiptRecorded (history : History) (ev : StartEvidence) (form : PartOne)
    (cancellation : NoFaultCancellationRecord) (posting : CreditPosting)
    (refund : RefundRecord) : Prop :=
  HasNoFaultCancellation history form cancellation ∧
  NoFaultRefundReceipt form ev cancellation posting cancellation.refundObligation refund

end SourceV14.Workflow.Cancellation
