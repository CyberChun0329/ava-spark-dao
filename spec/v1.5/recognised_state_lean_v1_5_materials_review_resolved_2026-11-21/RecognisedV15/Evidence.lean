import SourceV14.Course

namespace RecognisedV15

open SourceV14 SourceV14.Booking SourceV14.Settlement SourceV14.Confirmation
  SourceV14.CreditEvidence SourceV14.Course
open SourceV14.Workflow.AttendanceFacts

/-- Booking, schedule and roster inputs, including their original timing evidence. -/
structure BookingScheduleEvidence where
  effectiveForms : List PartOne
  groupRoster : Option Roster
  bookings : List (PartOne × BookingEvidence)
  scheduleHistory : List Schedule
  changes : List AgreedScheduleChange
  notices : List Notice
  academicTeamAt : LessonId → ActorId → Moment → Prop
  tutorReplacements : List TutorReplacement := []
  rosterReview : Option RosterReviewHistory := none
  clockBoundaries : List ClockBoundary := []
  groupRegisters : List GroupRegisterSnapshot := []
  verifiesGroupRegister : GroupRegisterSnapshot → Prop := fun _ ↦ False
  bookedRosters : List (PartOne × Roster) := []

/-- Credit and fee inputs; these records do not assert their validity. -/
structure CreditFeeEvidence where
  openingCredit : AccountId → Amount
  creditRecords : CreditRecords
  ledger : List CreditPosting
  discounts : List DiscountRecord
  tutorPayAmendments : TutorPayAmendments := {}

/-- Actual teaching, reporting and fault inputs, including absent observations. -/
structure TeachingEvidence where
  teachingBegan : Option Moment
  teachingEnded : Option Moment
  verifiedOneToOneAbsence : Option OneToOneAbsence := none
  studentsTakingLesson : List ActorId
  afterLesson : AfterLessonRecords
  studentFaults : StudentFaultHistory
  oneToOneAbsenceReasons : List OneToOneAbsenceReason := []

/-- A factorised evidence carrier, not a proof of recognition. -/
structure LessonEvidence where
  bookingSchedule : BookingScheduleEvidence
  creditFee : CreditFeeEvidence
  teaching : TeachingEvidence

def LessonEvidence.fromDirect (ev : StartEvidence) : LessonEvidence where
  bookingSchedule := {
    effectiveForms := ev.effectiveForms
    groupRoster := ev.groupRoster
    bookings := ev.bookings
    scheduleHistory := ev.scheduleHistory
    changes := ev.changes
    notices := ev.notices
    academicTeamAt := ev.academicTeamAt
    tutorReplacements := ev.tutorReplacements
    rosterReview := ev.rosterReview
    clockBoundaries := ev.clockBoundaries
    groupRegisters := ev.groupRegisters
    verifiesGroupRegister := ev.verifiesGroupRegister
    bookedRosters := ev.bookedRosters }
  creditFee := {
    openingCredit := ev.openingCredit
    creditRecords := ev.creditRecords
    ledger := ev.ledger
    discounts := ev.discounts
    tutorPayAmendments := ev.tutorPayAmendments }
  teaching := {
    teachingBegan := ev.teachingBegan
    teachingEnded := ev.teachingEnded
    verifiedOneToOneAbsence := ev.verifiedOneToOneAbsence
    studentsTakingLesson := ev.studentsTakingLesson
    afterLesson := ev.afterLesson
    studentFaults := ev.studentFaults
    oneToOneAbsenceReasons := ev.oneToOneAbsenceReasons }

def LessonEvidence.toDirect (ev : LessonEvidence) : StartEvidence where
  effectiveForms := ev.bookingSchedule.effectiveForms
  groupRoster := ev.bookingSchedule.groupRoster
  bookings := ev.bookingSchedule.bookings
  scheduleHistory := ev.bookingSchedule.scheduleHistory
  changes := ev.bookingSchedule.changes
  openingCredit := ev.creditFee.openingCredit
  creditRecords := ev.creditFee.creditRecords
  ledger := ev.creditFee.ledger
  discounts := ev.creditFee.discounts
  notices := ev.bookingSchedule.notices
  academicTeamAt := ev.bookingSchedule.academicTeamAt
  teachingBegan := ev.teaching.teachingBegan
  teachingEnded := ev.teaching.teachingEnded
  verifiedOneToOneAbsence := ev.teaching.verifiedOneToOneAbsence
  studentsTakingLesson := ev.teaching.studentsTakingLesson
  afterLesson := ev.teaching.afterLesson
  studentFaults := ev.teaching.studentFaults
  tutorReplacements := ev.bookingSchedule.tutorReplacements
  rosterReview := ev.bookingSchedule.rosterReview
  clockBoundaries := ev.bookingSchedule.clockBoundaries
  tutorPayAmendments := ev.creditFee.tutorPayAmendments
  groupRegisters := ev.bookingSchedule.groupRegisters
  verifiesGroupRegister := ev.bookingSchedule.verifiesGroupRegister
  bookedRosters := ev.bookingSchedule.bookedRosters
  oneToOneAbsenceReasons := ev.teaching.oneToOneAbsenceReasons

@[simp] theorem LessonEvidence.toDirect_fromDirect (ev : StartEvidence) :
    (fromDirect ev).toDirect = ev := by
  cases ev
  rfl

@[simp] theorem LessonEvidence.fromDirect_toDirect (ev : LessonEvidence) :
    fromDirect ev.toDirect = ev := by
  cases ev with
  | mk bookingSchedule creditFee teaching =>
    cases bookingSchedule
    cases creditFee
    cases teaching
    rfl

end RecognisedV15
