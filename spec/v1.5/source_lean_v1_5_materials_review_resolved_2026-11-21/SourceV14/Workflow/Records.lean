import SourceV14.Course

namespace SourceV14.Workflow

open Booking Settlement Confirmation Course CreditEvidence

/-- A single common balance and credit history across lessons (§§2.3, 3.5, 4.3).
Payment evidence is synchronized with the separately retained receipt history. -/
structure CreditBook where
  openingCredit : AccountId → Amount
  creditRecords : CreditRecords
  ledger : List CreditPosting
  discounts : List DiscountRecord

def CreditBook.fromEvidence (e : StartEvidence) : CreditBook :=
  ⟨e.openingCredit, e.creditRecords, e.ledger, e.discounts⟩

/-- Course-local facts. A later course can read shared credit without taking
ownership of the original course's bookings, dates or teaching records. -/
structure LessonFile where
  effectiveForms : List PartOne
  groupRoster : Option Roster
  bookings : List (PartOne × BookingEvidence)
  scheduleHistory : List Schedule
  changes : List AgreedScheduleChange
  notices : List Notice
  academicTeamAt : LessonId → ActorId → Moment → Prop
  teachingBegan : Option Moment
  teachingEnded : Option Moment
  verifiedOneToOneAbsence : Option AttendanceFacts.OneToOneAbsence
  studentsTakingLesson : List ActorId
  afterLesson : AfterLessonRecords
  studentFaults : StudentFaultHistory
  tutorReplacements : List TutorReplacement
  rosterReview : Option RosterReviewHistory
  clockBoundaries : List ClockBoundary
  tutorPayAmendments : TutorPayAmendments
  groupRegisters : List GroupRegisterSnapshot
  verifiesGroupRegister : GroupRegisterSnapshot → Prop
  bookedRosters : List (PartOne × Roster)
  oneToOneAbsenceReasons : List AttendanceFacts.OneToOneAbsenceReason := []

def LessonFile.fromEvidence (e : StartEvidence) : LessonFile :=
  ⟨e.effectiveForms, e.groupRoster, e.bookings, e.scheduleHistory, e.changes, e.notices,
    e.academicTeamAt, e.teachingBegan, e.teachingEnded, e.verifiedOneToOneAbsence,
    e.studentsTakingLesson, e.afterLesson, e.studentFaults, e.tutorReplacements,
    e.rosterReview, e.clockBoundaries, e.tutorPayAmendments, e.groupRegisters,
    e.verifiesGroupRegister, e.bookedRosters, e.oneToOneAbsenceReasons⟩

def LessonFile.evidence (f : LessonFile) (book : CreditBook) : StartEvidence where
  effectiveForms := f.effectiveForms
  groupRoster := f.groupRoster
  bookings := f.bookings
  scheduleHistory := f.scheduleHistory
  changes := f.changes
  openingCredit := book.openingCredit
  creditRecords := book.creditRecords
  ledger := book.ledger
  discounts := book.discounts
  notices := f.notices
  academicTeamAt := f.academicTeamAt
  teachingBegan := f.teachingBegan
  teachingEnded := f.teachingEnded
  verifiedOneToOneAbsence := f.verifiedOneToOneAbsence
  studentsTakingLesson := f.studentsTakingLesson
  afterLesson := f.afterLesson
  studentFaults := f.studentFaults
  tutorReplacements := f.tutorReplacements
  rosterReview := f.rosterReview
  clockBoundaries := f.clockBoundaries
  tutorPayAmendments := f.tutorPayAmendments
  groupRegisters := f.groupRegisters
  verifiesGroupRegister := f.verifiesGroupRegister
  bookedRosters := f.bookedRosters
  oneToOneAbsenceReasons := f.oneToOneAbsenceReasons

@[simp] theorem LessonFile.from_evidence (f : LessonFile) (c : CreditBook) :
    fromEvidence (f.evidence c) = f := by cases f; rfl

@[simp] theorem CreditBook.from_evidence (f : LessonFile) (c : CreditBook) :
    fromEvidence (f.evidence c) = c := by cases c; rfl

@[simp] theorem evidence_from_parts (e : StartEvidence) :
    (LessonFile.fromEvidence e).evidence (CreditBook.fromEvidence e) = e := by cases e; rfl

namespace Credit

inductive Event where
  | topUp (receipt : TopUpReceipt) (posting : CreditPosting)
  | returnTopUp (receipt : TopUpReceipt) (authority : TopUpReturnAuthorisation)
      (posting : CreditPosting)

/-- §§2.3, 4.3. Top-ups and returns affect usable credit only with the
transaction record and applicable terms; a closed refund is a separate event. -/
def Step (before : CreditBook) (event : Event) (after : CreditBook) : Prop :=
  let validUpdate (ledger : List CreditPosting) (records : CreditRecords) : Prop :=
    ValidCreditHistory before.openingCredit ledger records ∧
      after = { before with creditRecords := records, ledger := ledger }
  match event with
  | .topUp receipt posting =>
    let records := { before.creditRecords with topUps := before.creditRecords.topUps ++ [receipt] }
    let ledger := before.ledger ++ [posting]
    topUpPostingMatches receipt posting ∧ validUpdate ledger records
  | .returnTopUp receipt authority posting =>
    ∃ authorised : List TopUpReturnAuthorisation,
      (authorised = before.creditRecords.topUpReturns ∨
        authorised = before.creditRecords.topUpReturns ++ [authority]) ∧
      receipt ∈ before.creditRecords.topUps ∧ authority ∈ authorised ∧
      let records := { before.creditRecords with topUpReturns := authorised }
      let ledger := before.ledger ++ [posting]
      topUpReturnMatches ledger receipt authority posting ∧ validUpdate ledger records

end Credit
end SourceV14.Workflow
