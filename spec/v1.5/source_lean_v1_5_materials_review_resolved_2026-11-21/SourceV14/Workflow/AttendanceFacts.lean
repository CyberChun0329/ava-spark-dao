import SourceV14.Confirmation
import SourceV14.Fault
import SourceV14.Review

namespace SourceV14.Workflow.AttendanceFacts

open SourceV14.Booking SourceV14.Confirmation

/-- The same agreed occurrence and verified facts support the two §3.1 routes. -/
structure OneToOneAbsence where
  form : PartOne
  schedule : Schedule
  start : Moment
  checkedAt : Moment
  facts : AbsenceFacts

def OneToOneAbsence.matchesAt (row : OneToOneAbsence) (form : PartOne)
    (start query : Moment) : Prop :=
  row.form = form ∧ row.start = start ∧ row.checkedAt.by query

/-- The reason can be established after the failed occurrence has been verified. -/
def OneToOneAbsence.resolvesReason (row earlier : OneToOneAbsence) : Prop :=
  row.form = earlier.form ∧ row.schedule = earlier.schedule ∧ row.start = earlier.start ∧
  earlier.checkedAt.before row.checkedAt ∧ earlier.facts.verifiedGoodReason = none ∧
  row.facts.verifiedGoodReason.isSome ∧
  { row.facts with verifiedGoodReason := none } = earlier.facts

/-- A dated reason for the already verified one-to-one occurrence. The actual
decision and the time its disposition was recorded can differ. -/
structure OneToOneAbsenceReason where
  recordedAt : Moment
  outcome : RecordedSettlementOutcome
  goodReason : Bool

def OneToOneAbsenceReason.latestAt (reasons : List OneToOneAbsenceReason)
    (query : Moment) : Option OneToOneAbsenceReason :=
  reasons.reverse.find? (fun reason ↦
    decide (reason.recordedAt.by query ∧ reason.outcome.decidedAt.by query))

/-- At the query, use the last recorded and already decided reason for the
occurrence. Keep the other verified facts and the original record. -/
def OneToOneAbsence.factsAt (row : OneToOneAbsence) (reasons : List OneToOneAbsenceReason)
    (query : Moment) : AbsenceFacts :=
  match OneToOneAbsenceReason.latestAt reasons query with
  | none => row.facts
  | some reason => { row.facts with verifiedGoodReason := some reason.goodReason }

def AttendanceConcerns (lesson : Lesson) (place : Place) (report : AttendanceReport) : Prop :=
  report.lesson = lesson.id ∧ report.place = place.id ∧ report.student = place.student ∧
    report.coordinator = lesson.coordinator

def ServiceFeedbackConcerns (form : PartOne) (report : DeliveryReport) : Prop :=
  report.lesson = form.lesson.id ∧ report.place = form.place.id ∧
  report.student = form.place.student ∧ report.coordinator = form.lesson.coordinator ∧
  (∀ service ∈ report.servicesReceived, service ∈ form.serviceItems) ∧
  (∀ service ∈ report.servicesNotReceived, service ∈ form.serviceItems) ∧
  (∀ service ∈ report.servicesReceived, service ∉ report.servicesNotReceived)

end SourceV14.Workflow.AttendanceFacts
