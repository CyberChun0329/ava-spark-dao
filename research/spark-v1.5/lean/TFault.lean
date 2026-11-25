import RecognisedV15.Workflow
import TPrefix

namespace JointTFault

open SourceV14
open SourceV14.Booking SourceV14.Confirmation SourceV14.Course SourceV14.CreditEvidence
open SourceV14.Operations SourceV14.Settlement SourceV14.Workflow

abbrev form := JointT.form
abbrev lesson := JointT.lesson
abbrev place := JointT.place
abbrev schedule := JointT.schedule
abbrev tick := JointT.tick

def issue : CourseCreditIssue := ⟨100, 1, 103, 4, tick 39, some (tick 39)⟩
def creditPosting : CreditPosting := ⟨1003, 103, .compensation 100 1, 4, tick 39⟩

def refundPart : PaymentPart := ⟨⟨100, 1004, 0, .lessonRefund 1⟩, .lessonRefund 103, 2⟩

/-- The shared booked state supplies the signed T file and the actual account.
    The principal expression reads that ledger and the absence of earlier obligations. -/
structure Ready (s : State) : Prop where
  forms : (s.course 100).effectiveForms = [form]
  bookings : (s.course 100).bookings = [(form, JointT.booking)]
  roster : (s.course 100).groupRoster = none
  schedules : (s.course 100).scheduleHistory = [schedule]
  unstarted : (s.course 100).teachingBegan = none
  unfinished : (s.course 100).teachingEnded = none
  noReplacement : (s.course 100).tutorReplacements = []
  tutorTerms : (s.course 100).tutorPayAmendments.amendments = []
  feeTerms : s.credit.creditRecords.lessonFees = {}
  owner : s.credit.creditRecords.ownsAccount 102 103
  noClosures : s.credit.creditRecords.closed = []
  noGrants : s.credit.creditRecords.grants = []
  noTemporaryHolds : s.holds.temporary = []
  noReview : s.review = .empty
  noRedress : s.redress = {}
  noTutorFaults : s.tutorFaults = .empty
  synchronised : s.synchronised
  ledger : s.credit.ledger = [JointT.topUpPosting, JointT.debit]

private theorem lessonFileRoundTrip (file : LessonFile) (book : CreditBook) :
    LessonFile.fromEvidence (file.evidence book) = file := by
  cases file
  rfl

private theorem courseRoundTrip (ev : StartEvidence) :
    (LessonFile.fromEvidence ev).evidence (CreditBook.fromEvidence ev) = ev := by
  cases ev
  rfl

private theorem courseAfterWrite (s : State) (ev : StartEvidence) :
    (s.withCourse 100 ev).course 100 = ev := by
  exact courseRoundTrip ev

private theorem withCourseSelf (s : State) : s.withCourse 100 (s.course 100) = s := by
  have sameFiles : (fun key ↦ if key = 100 then s.lessons 100 else s.lessons key) =
      s.lessons := by
    funext key
    by_cases h : key = 100
    · simp [h]
    · simp [h]
  simp only [State.withCourse, State.course, lessonFileRoundTrip, sameFiles]
  cases s
  rfl

private theorem withCourseOverwrite (s : State) (before after : StartEvidence) :
    (s.withCourse 100 before).withCourse 100 after = s.withCourse 100 after := by
  have sameFiles :
      (fun id ↦ if id = 100 then LessonFile.fromEvidence after
        else if id = 100 then LessonFile.fromEvidence before else s.lessons id) =
      (fun id ↦ if id = 100 then LessonFile.fromEvidence after else s.lessons id) := by
    funext id
    by_cases h : id = 100 <;> simp [h]
  simp only [State.withCourse, sameFiles]

private theorem withHoldsSelf (s : State) (same : s.synchronised) :
    s.withHolds s.holds = s := by
  have paymentEq : s.holds.payments = s.credit.creditRecords.payments := same.symm
  rw [State.withHolds, paymentEq]

def tutorReport : TutorDeliveryReport :=
  ⟨100, 20, 30, ⟨34, 0⟩, false, "I delivered item 1 and did not deliver item 2."⟩

def attendanceReport : AttendanceReport := ⟨100, 1, 101, 30, ⟨34, 1⟩, true⟩

def teachingReport : DeliveryReport := ⟨100, 1, 101, 30, ⟨34, 2⟩, [1], [2]⟩

private def begunData (s : State) : StartEvidence :=
  { s.course 100 with teachingBegan := some (tick 32), studentsTakingLesson := [101] }

private def begun (s : State) : State := s.withCourse 100 (begunData s)

private def endedData (s : State) : StartEvidence :=
  { begunData s with teachingEnded := some (tick 33) }

private def ended (s : State) : State := s.withCourse 100 (endedData s)

private def tutorReportedData (s : State) : StartEvidence :=
  let ev := endedData s
  { ev with afterLesson := { ev.afterLesson with tutorReports := ev.afterLesson.tutorReports ++ [tutorReport] } }

private def tutorReported (s : State) : State := s.withCourse 100 (tutorReportedData s)

private def attendedData (s : State) : StartEvidence :=
  let ev := tutorReportedData s
  { ev with afterLesson := { ev.afterLesson with attendance := ev.afterLesson.attendance ++ [attendanceReport] } }

private def attended (s : State) : State := s.withCourse 100 (attendedData s)

private def reportedData (s : State) : StartEvidence :=
  let ev := attendedData s
  { ev with afterLesson := { ev.afterLesson with serviceFeedback := ev.afterLesson.serviceFeedback ++ [teachingReport] } }

private def reported (s : State) : State := s.withCourse 100 (reportedData s)

macro "open_teaching" : tactic =>
  `(tactic| try simp only [reported, reportedData, attended, attendedData, tutorReported,
    tutorReportedData, ended, endedData, begun, begunData, courseAfterWrite] at *)

private theorem courseScope (ev : StartEvidence) (forms : ev.effectiveForms = [form])
    (bookings : ev.bookings = [(form, JointT.booking)]) (roster : ev.groupRoster = none)
    (schedules : ev.scheduleHistory = [schedule]) :
    (∀ entry, (entry ∈ ev.effectiveForms ∨ ∃ b, (entry, b) ∈ ev.bookings) →
      entry.lesson = lesson) ∧
    (∀ entry ∈ ev.groupRoster, entry.lesson = lesson.id) ∧
    (∀ entry ∈ ev.scheduleHistory, entry.lesson = lesson.id) := by
  rw [forms, bookings, roster, schedules]
  refine ⟨?_, by simp, ?_⟩
  · intro entry present
    rcases present with mem | ⟨b, mem⟩
    · cases List.mem_singleton.mp mem
      rfl
    · have same := congrArg Prod.fst (List.mem_singleton.mp mem)
      cases same
      rfl
  · intro entry mem
    cases List.mem_singleton.mp mem
    rfl

macro "t_scope " h:ident : tactic =>
  `(tactic| exact courseScope _
    (by open_teaching; exact Ready.forms $h)
    (by open_teaching; exact Ready.bookings $h)
    (by open_teaching; exact Ready.roster $h)
    (by open_teaching; exact Ready.schedules $h))

private theorem beganStep {s : State} (ready : Ready s) :
    Step s (.booking (.beginTeaching lesson (tick 32) [101])) (begun s) := by
  refine Step.booking (after := begunData s) trivial trivial trivial ?_ rfl trivial trivial trivial
  change SourceV14.Workflow.Booking.Step (s.course 100)
    (.beginTeaching lesson (tick 32) [101]) (begunData s)
  refine ⟨?_, ⟨form, Or.inl (by simp [ready.forms]), rfl⟩, ready.unstarted, ready.unfinished, rfl⟩
  t_scope ready

private theorem endedStep {s : State} (ready : Ready s) :
    Step (begun s) (.booking (.endTeaching lesson (tick 33))) (ended s) := by
  rw [show ended s = (begun s).withCourse 100 (endedData s) from
    (withCourseOverwrite s (begunData s) (endedData s)).symm]
  refine Step.booking (after := endedData s) trivial trivial trivial ?_ rfl trivial trivial trivial
  change SourceV14.Workflow.Booking.Step ((begun s).course 100)
    (.endTeaching lesson (tick 33)) (endedData s)
  rw [show (begun s).course 100 = begunData s from courseAfterWrite s (begunData s)]
  refine ⟨?_, ⟨form, Or.inl ?_, rfl⟩, ?_, ⟨tick 32, ?_, by decide⟩, rfl⟩
  · t_scope ready
  · open_teaching
    simp [ready.forms]
  · open_teaching
    exact ready.unfinished
  · open_teaching
    simp

private theorem tutorReportedStep {s : State} (ready : Ready s) :
    Step (ended s) (.booking (.tutorReport lesson tutorReport)) (tutorReported s) := by
  rw [show tutorReported s = (ended s).withCourse 100 (tutorReportedData s) from
    (withCourseOverwrite s (endedData s) (tutorReportedData s)).symm]
  refine Step.booking (after := tutorReportedData s) trivial trivial trivial ?_ rfl trivial trivial trivial
  change SourceV14.Workflow.Booking.Step ((ended s).course 100)
    (.tutorReport lesson tutorReport) (tutorReportedData s)
  rw [show (ended s).course 100 = endedData s from courseAfterWrite s (endedData s)]
  refine ⟨?_, ⟨form, Or.inl ?_, rfl⟩, ?_, rfl⟩
  · t_scope ready
  · open_teaching
    simp [ready.forms]
  · refine ⟨?_, rfl, ⟨tick 32, ?_, none, ?_, rfl⟩, rfl, by decide,
      tick 32, tick 33, ?_, ?_, by decide, by decide, by decide⟩
    · open_teaching
      simp
    · open_teaching
    · open_teaching
      simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement, ready.noReplacement]
    · open_teaching
    · open_teaching

private theorem attendanceStep {s : State} (ready : Ready s) :
    Step (tutorReported s) (.booking (.attendance form attendanceReport)) (attended s) := by
  rw [show attended s = (tutorReported s).withCourse 100 (attendedData s) from
    (withCourseOverwrite s (tutorReportedData s) (attendedData s)).symm]
  refine Step.booking (after := attendedData s) trivial trivial trivial ?_ rfl trivial trivial trivial
  change SourceV14.Workflow.Booking.Step ((tutorReported s).course 100)
    (.attendance form attendanceReport) (attendedData s)
  rw [show (tutorReported s).course 100 = tutorReportedData s from courseAfterWrite s (tutorReportedData s)]
  refine ⟨?_, Or.inl ?_, ⟨rfl, rfl, rfl, rfl⟩,
    Or.inl ⟨tick 32, tick 33, ?_, ?_, by decide, by decide, by decide⟩, rfl⟩
  · t_scope ready
  · open_teaching
    simp [ready.forms]
  · open_teaching
  · open_teaching

private theorem feedbackStep {s : State} (ready : Ready s) :
    Step (attended s) (.booking (.serviceFeedback form teachingReport)) (reported s) := by
  rw [show reported s = (attended s).withCourse 100 (reportedData s) from
    (withCourseOverwrite s (attendedData s) (reportedData s)).symm]
  refine Step.booking (after := reportedData s) trivial trivial trivial ?_ rfl trivial trivial trivial
  change SourceV14.Workflow.Booking.Step ((attended s).course 100)
    (.serviceFeedback form teachingReport) (reportedData s)
  rw [show (attended s).course 100 = attendedData s from courseAfterWrite s (attendedData s)]
  refine ⟨?_, Or.inl ?_, ?_, Or.inl ⟨tick 32, tick 33, ?_, ?_, by decide, by decide, by decide⟩, rfl⟩
  · t_scope ready
  · open_teaching
    simp [ready.forms]
  · simp [AttendanceFacts.ServiceFeedbackConcerns, teachingReport, JointT.form, JointT.lesson,
      JointT.place]
  · open_teaching
  · open_teaching

private def matter : ReviewMatter := ⟨1004, 100, [20, 101, 102]⟩
private def initial : InitialFinding :=
  ⟨matter, .fault, 31, tick 35, "Tutor and student agree that item 2 was missed.", []⟩

private def terms : ReviewTerms := ⟨30, 41, 31, .exact (tick 70), tick 72, tick 65, tick 66, 50⟩

private def authority : ReviewAuthorities where
  corePartner := fun _ _ ↦ False
  initialFinding := fun scope actor point ↦ scope = matter ∧ actor = 31 ∧ point = tick 35
  reviewer := fun scope actor _ ↦ scope = matter ∧ actor = 40
  approvesPayment := fun _ _ _ ↦ False
  interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
  originalDecisionMaker := fun scope ↦ if scope = matter then some 31 else none
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

private def holdFacts : HoldFacts where
  terms := fun _ ↦ terms
  termsApply := fun scope ↦ scope = matter
  acceptedPaymentConcern := fun _ _ _ _ ↦ False
  reviewerCannotActInTime := fun _ _ ↦ False
  temporaryAuthority := fun _ _ _ _ ↦ False
  allegedFactsWouldChangePayment := fun _ _ _ ↦ False
  separatelyIdentifiable := fun ref time ↦ ref = refundPart.ref ∧ (tick 37).by time
  establishedParts := fun id purpose ↦ if id = 100 ∧ purpose = .lessonRefund 1 then [refundPart] else []
  paymentAffected := fun scope ref ↦ scope = matter ∧ ref = refundPart.ref
  decisionPending := fun _ _ _ ↦ False
  partFallsUnderDecision := fun scope id ref ↦ scope = matter ∧ id = 1004 ∧ ref = refundPart.ref
  decisionConcernsWholeGroup := fun _ _ ↦ False
  isGroupLesson := fun _ ↦ False
  affectsWholeSettlement := fun _ ↦ False
  groupSettlementParts := fun _ ↦ []

private def outcome : RecordedSettlementOutcome := ⟨matter, 1004, 31, tick 35⟩
private def originalDecision : Review.OriginalRecord := ⟨outcome, none⟩

private def reviewEvidence : Review.Evidence where
  authority := authority
  holds := holdFacts
  concernFacts := ⟨fun candidate _ ↦ candidate = place,
    fun scope actor ↦ scope = matter ∧ actor = 20,
    fun _ _ ↦ False, fun _ _ ↦ False, fun _ _ ↦ False, fun _ _ ↦ False,
    fun _ _ ↦ False, fun _ ↦ False, []⟩
  publishedTerms := fun _ _ _ ↦ False
  replyTrigger := fun _ _ ↦ none
  verifiedReplyTrigger := fun _ _ ↦ False
  replyLegalDeadline := fun _ ↦ none
  verifiedFactCheck := fun _ ↦ False
  originalOutcome := fun row ↦ row = outcome
  recordedAmount := fun _ _ _ ↦ False

private def decided (s : State) : State :=
  let base := reported s
  { base with review := { base.review with initialFindings := base.review.initialFindings ++ [initial] } }

private def retained (s : State) : State :=
  let base := decided s
  { base with review := { base.review with originals := base.review.originals ++ [originalDecision] } }

private theorem decidedStep {s : State} (ready : Ready s) :
    Step (reported s) (.review reviewEvidence (.decideInitial form terms initial)) (decided s) := by
  refine Step.review trivial trivial (by intro row impossible; cases impossible) ?_
  refine Review.Step.decideInitial form terms initial ⟨⟨rfl, JointT.formMatches, by decide, Or.inl ?_⟩,
      rfl, ?_⟩ ?_ ?_ ?_
  · change form ∈ ((reported s).course 100).effectiveForms
    open_teaching
    simp [ready.forms]
  · simp [ReviewTerms.matchesForm, terms, JointT.form, JointT.lesson]
  · simp [HoldHistory.temporarySettersRecorded, State.reviewEvidence, Review.History.authorities,
      reviewEvidence, authority, reported,
      State.withCourse, ready.noTemporaryHolds]
  · simp [initialFindingRecordedConforms, initialFindingConformsWithContacts, initial, terms,
      State.reviewEvidence, Review.History.authorities, reviewEvidence, authority,
      ReviewAuthorities.mayDecideDispute, ReviewAuthorities.disinterested, DirectInterest.affected,
      reported, State.withCourse]
  · simp [reported, State.withCourse, ready.noReview,
      Review.History.empty]

private theorem retainedStep {s : State} (ready : Ready s) :
    Step (decided s) (.review reviewEvidence (.retainOriginal lesson originalDecision)) (retained s) := by
  refine Step.review trivial trivial (by intro row impossible; cases impossible) ?_
  refine Review.Step.retainOriginal lesson originalDecision rfl rfl (by simp [originalDecision]) ?_
  intro mem
  -- A pre-existing unrelated record may not substitute for this exact decision.
  exact (show False from by simp [decided, reported,
    State.withCourse, ready.noReview, Review.History.empty] at mem)

private def findings : Review.History :=
  { Review.History.empty with initialFindings := [initial], originals := [originalDecision] }

private theorem reviewRecorded {s : State} (ready : Ready s) : (retained s).review = findings := by
  simp [retained, decided, reported, State.withCourse,
    ready.noReview, findings, Review.History.empty]

private def finding (s : State) : TutorFaultFinding where
  lesson := 100
  tutor := 20
  coordinatorCheckedWithTutor := tutorReport ∈ ((reported s).course 100).afterLesson.tutorReports
  coordinatorCheckedWithAffectedStudents :=
    teachingReport ∈ ((reported s).course 100).afterLesson.serviceFeedback
  tutorGivenOpportunityToRespond := tutorReport ∈ ((reported s).course 100).afterLesson.tutorReports
  ground := .missedAgreedService "Teaching item 2"
    (2 ∈ form.serviceItems ∧ 2 ∈ teachingReport.servicesNotReceived)
  scope := .particularPlaces [1]

private def placeFacts (s : State) : TutorFaultPlaceFacts where
  feePaidInFull := (s.course 100).paidInFull form (tick 32)
  studentAttendedAsAgreed := attendanceReport ∈ ((reported s).course 100).afterLesson.attendance ∧
    attendanceReport.attended = true
  studentReadyToAttendAsAgreed := False

private def basis (s : State) : FaultBasis := .tutor (finding s) (placeFacts s)

private def fault (s : State) : TutorFaultCase := ⟨lesson, tick 33, finding s⟩

private def decision (s : State) : FaultDecisionRecord := ⟨.initial initial, 1, .fault (basis s)⟩

private def decisions (s : State) : DecisionRecords where
  authorities := authority
  terms := terms
  appointments := []
  initialFindings := [initial]
  faultOutcomes := [decision s]
  faultMatterCovers := fun scope id ↦ scope = matter ∧ id = 1
  wasResponsibleTutor := fun original checked ↦ original.id = checked.lesson ∧
    original.tutor = checked.tutor
  originalAttendanceTime := fun id seat point ↦ id = 100 ∧ seat = 1 ∧
    ((reported s).course 100).teachingBegan = some point ∧
    101 ∈ ((reported s).course 100).studentsTakingLesson

private theorem validFinding (s : State) : (finding s).establishedFor lesson := by
  simp only [finding, TutorFaultFinding.establishedFor, TutorFaultGround.established]
  open_teaching
  simp [JointT.lesson, JointT.form, teachingReport]

private theorem feeAt {s : State} (ready : Ready s) (query : Moment) :
    (s.course 100).feeAt form query 4 := by
  change s.credit.creditRecords.lessonFees.feeAt form query 4
  rw [ready.feeTerms]
  simp [LessonFeeAmendments.feeAt, JointT.form, JointT.place]

private theorem paid {s : State} (ready : Ready s) :
    (s.course 100).paidInFull form (tick 32) := by
  refine ⟨4, feeAt ready _, Or.inr ⟨by decide, ?_⟩⟩
  change 4 ≤ debitTotal place s.credit.ledger (tick 32) -
    creditsRestoredFor place s.credit.ledger (tick 32)
  rw [ready.ledger]
  decide +kernel

private theorem faultApplies {s : State} (ready : Ready s) :
    (basis s).applies ((basis s).lessonWithResponsibleTutor lesson) place := by
  refine ⟨by rfl, validFinding s,
    by simp [finding, TutorFaultScope.affects, JointT.place], paid ready,
    Or.inl ⟨?_, rfl⟩⟩
  open_teaching
  simp

private theorem scopeAt (s : State) (query : Moment) (later : (tick 35).by query) :
    (decision s).decision.effectiveForForm (decisions s) form query := by
  simp [decision, decisions, initial, terms, FaultDecision.effectiveForForm,
    DecisionRecords.faultStillApplies, initialFindingRecordedConforms, initialFindingConformsWithContacts,
    authority, ReviewAuthorities.mayDecideDispute, ReviewAuthorities.disinterested,
    DirectInterest.affected, JointT.form, JointT.lesson, JointT.place, matter, later]

private theorem recordsDecision (s : State) (query : Moment) (later : (tick 35).by query) :
    FaultDecisionWhenRequired (basis s) true (some (decision s)) (decisions s) form query := by
  intro _
  exact ⟨decision s, by simp [decisions], rfl, rfl, rfl, scopeAt s query later⟩

private theorem retainedPlace {s : State} (ready : Ready s) (query : Moment) :
    ((reported s).course 100).rosterFormsAt lesson query none [form] := by
  open_teaching
  simp [StartEvidence.rosterFormsAt, StartEvidence.rosterMatchesForms, StartEvidence.formsMatch,
    JointT.lesson, ready.roster, ready.forms, JointT.formMatches] <;> rfl

private theorem signedSchedule {s : State} (ready : Ready s) :
    EffectiveSchedule lesson ((reported s).course 100) schedule (tick 33) := by
  have history : ((reported s).course 100).scheduleHistory = [schedule] := by
    open_teaching
    exact ready.schedules
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [history]
    simp [Schedule.effectiveAtQuery, JointT.schedule, JointT.lesson, JointT.tick, Schedule.valid,
      Moment.by, Moment.before]
  · simp [history, JointT.schedule]
  · intro row mem _ _
    rw [history] at mem
    cases List.mem_singleton.mp mem
    refine ⟨rfl, by simp [Schedule.valid, JointT.schedule, JointT.tick, Moment.by, Moment.before],
      Or.inl ⟨rfl, (retainedPlace ready (tick 33)).1, ?_⟩⟩
    intro f present
    open_teaching
    rw [ready.forms] at present
    cases List.mem_singleton.mp present
    rfl

private theorem signedTutor {s : State} (ready : Ready s) :
    EffectiveTutorAgreementAt form ((reported s).course 100) (tick 32) 20
      form.tutorAgreementRef 2 form.deadlines.tutorPay (tick 35) := by
  refine ⟨JointT.formMatches, by decide, by decide, Or.inl ?_, none, ?_, ?_⟩
  · open_teaching
    simp [ready.forms]
  · open_teaching
    simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement, ready.noReplacement]
  · open_teaching
    simp [ready.tutorTerms, JointT.form, JointT.lesson, JointT.tick, Moment.by, Moment.before]

private def faultEvidence (s : State) : TutorFaultDecisionEvidence :=
  ⟨form, (retained s).course 100, schedule, decision s, decisions s⟩

def economicEntry (s : State) : TutorFaultHistory.Entry :=
  ⟨fault s, faultEvidence s, outcome, tick 36, 2, 0⟩

private theorem evidenceEstablishes {s : State} (ready : Ready s) :
    (faultEvidence s).establishes (fault s) (tick 36) := by
  refine ⟨⟨none, [form], retainedPlace ready (tick 35), by simp [faultEvidence]⟩,
    rfl, signedSchedule ready, rfl, ⟨form.tutorAgreementRef, form.deadlines.tutorPay, signedTutor ready⟩,
    validFinding s, by simp [faultEvidence, decisions], rfl, scopeAt s _ (by decide),
    ⟨placeFacts s, rfl⟩⟩

private def economic (s : State) : State :=
  let base := retained s
  { base with tutorFaults := { base.tutorFaults with entries := base.tutorFaults.entries ++ [economicEntry s] } }

private theorem economicStep {s : State} (ready : Ready s) :
    Step (retained s) (.tutorFault (.record (economicEntry s))) (economic s) := by
  refine Step.tutorFault (TutorFaultHistory.Step.record (economicEntry s)
    ⟨rfl, ?_, ?_, ?_, ?_, trivial, by change (tick 33).by (tick 36); decide,
      by change 1 ∈ ([1] : List Nat); simp,
      evidenceEstablishes ready, validFinding s, rfl, rfl⟩ ?_ ?_)
  · rw [reviewRecorded ready]
    rfl
  · rw [reviewRecorded ready]
    rfl
  · rw [reviewRecorded ready]
    rfl
  · change TutorFaultHistory.matchesInitialOutcome (retained s).review initial outcome
    rw [reviewRecorded ready]
    simp [TutorFaultHistory.matchesInitialOutcome, Review.History.originalOutcomes, findings,
      originalDecision, initial, outcome]
  · simp [retained, decided, reported, State.withCourse,
      ready.noTutorFaults, TutorFaultHistory.History.empty]
  · simp [TutorFaultHistory.History.operativeAt, retained, decided, reported, State.withCourse, ready.noTutorFaults, TutorFaultHistory.History.empty]

private theorem paidFaultEvidence {s : State} (ready : Ready s) (query : Moment)
    (later : (tick 32).by query) :
    FaultMatchesEvidence form (basis s) (decisions s) s.credit.ledger s.credit.discounts
      s.credit.creditRecords.lessonFees query := by
  refine ⟨faultApplies ready, ⟨rfl, rfl⟩, tick 32, ⟨rfl, rfl, ?_, ?_⟩, later, paid ready⟩
  · open_teaching
  · open_teaching
    simp

def facts (s : State) : Redress.FaultFacts :=
  ⟨form, basis s, some (decision s), true, decisions s, .some⟩

private theorem faultEstablished {s : State} (ready : Ready s) (query : Moment)
    (later : (tick 35).by query) (afterStart : (tick 32).by query) :
    (facts s).established ((reported s).course 100) query :=
  ⟨⟨none, [form], retainedPlace ready query, List.Mem.head []⟩,
    recordsDecision s query later, paidFaultEvidence ready query afterStart⟩

def settlement : LessonSettlement := ⟨100, 1, 2, 4, 2, 0, 0, 0⟩

def relief : OriginalCompensationSettlement :=
  ⟨settlement, tick 37, 2, 0, fun amount ↦ amount = 0⟩

def assessedRefund (s : State) : Redress.AssessedRefund where
  amount := ⟨form, 1004, .standardCompensation, "Half-price relief for partial tutor delivery",
    tick 37, tick 37, ⟨tick 80, tick 80, none, .date (tick 80)⟩, 2, 2, [refundPart]⟩
  evidence := .originalCompensation (facts s) relief
  dueEvent := none
  executionEvent := none

private def assessed (s : State) : State :=
  let base := economic s
  { base with redress := { base.redress with assessments := base.redress.assessments ++ [assessedRefund s] } }

private theorem refundConforms {s : State} (ready : Ready s) :
    (assessedRefund s).conforms (economic s).redress ((economic s).course 100) s.holds
      holdFacts s.verifiedAgreedRefundTrigger (economic s).review := by
  change (assessedRefund s).conforms s.redress ((reported s).course 100) s.holds
    holdFacts s.verifiedAgreedRefundTrigger (retained s).review
  rw [ready.noRedress, reviewRecorded ready]
  refine ⟨JointT.formMatches, by change "Half-price relief for partial tutor delivery" ≠ ""; decide,
    by exact Or.inr rfl, by change (0 : Amount) ≤ 2; decide +kernel,
    by change (0 : Amount) ≤ 2; decide +kernel, ?_,
    by simp [EarlierFeeRefundsFor], ?_, rfl, by simp, rfl,
    faultEstablished ready (tick 37) (by decide) (by decide), rfl, rfl, ?_, ⟨rfl, ?_⟩,
    ⟨4, feeAt ready _, ?_⟩, ?_⟩
  · change 2 ≤ debitTotal place s.credit.ledger (tick 37)
    rw [ready.ledger]
    decide +kernel
  · simp [Redress.RefundAssessment.partsMatch, assessedRefund, holdFacts, refundPart, JointT.form,
      JointT.lesson, JointT.place, sumAmounts] <;> decide +kernel
  · exact ⟨⟨rfl, trivial⟩, rfl, trivial⟩
  · change 2 = feeAdjustmentRefundPrincipal place s.credit.ledger (tick 37) 1004 2 [] []
    rw [ready.ledger]
    decide +kernel
  · refine ⟨Or.inr rfl, ?_, ?_, ?_, ?_⟩
    · change settlement.matchesPaymentHistory place s.credit.ledger (tick 37)
      rw [ready.ledger]
      exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩
    · change settlement.feePayable = feeAfterOriginalCompensation place .some 4
      decide +kernel
    · decide +kernel
    · change relief.appliedToOriginal = appliedHalfPriceBenefit place 4 ∧
          relief.unappliedFromOriginalUse = unappliedHalfPriceBenefit place 4
      decide +kernel
  · refine ⟨JointT.formMatches, recordsDecision s (tick 37) (by decide),
      paidFaultEvidence ready (tick 37) (by decide), ?_, Or.inr rfl, ⟨4, feeAt ready _, ?_⟩,
      by decide +kernel⟩
    · change settlement.matchesPaymentHistory place s.credit.ledger (tick 37)
      rw [ready.ledger]
      exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩
    · exact ⟨⟨faultApplies ready, trivial⟩, Or.inr trivial,
        by change settlement.feePayable = feeAfterOriginalCompensation place .some 4; decide +kernel⟩

private theorem reviewUsed {s : State} (ready : Ready s) :
    (decisions s).appointments = (retained s).review.appointments ∧
    (decisions s).initialFindings = (retained s).review.initialFindings ∧
    (decisions s).reviewFindings = (retained s).review.reviewFindings := by
  rw [reviewRecorded ready]
  exact ⟨rfl, rfl, rfl⟩

private theorem assessedStep {s : State} (ready : Ready s) :
    Step (economic s) (.redress (.assessRefund (assessedRefund s) holdFacts)) (assessed s) := by
  have root : Step (economic s) (.redress (.assessRefund (assessedRefund s) holdFacts))
      { ((economic s).withCourse 100 ((economic s).course 100)).withHolds (economic s).holds with
        redress := (assessed s).redress } := by
    refine Step.redress trivial trivial ?_ trivial ⟨refundConforms ready, rfl, rfl, rfl⟩
    intro actual mem
    have same : decisions s = actual :=
      Option.mem_some_iff.mp (show actual ∈ some (decisions s) from mem)
    subst actual
    exact reviewUsed ready
  rw [withCourseSelf, withHoldsSelf (economic s) ready.synchronised] at root
  exact root

def remedy (s : State) : Redress.AcceptedRemedy :=
  ⟨1005, facts s, ⟨100, 1, 102, .standardCompensation, ["Teaching item 2"], tick 38, tick 80⟩,
    some ⟨tick 80, none, none⟩⟩

private theorem agreementForPlace (s : State) : (remedy s).agreement.forPlace place := by
  simp [remedy, RemedyAgreement.forPlace, JointT.place, JointT.lesson]

private def accepted (s : State) : State :=
  let base := assessed s
  { base with redress := { base.redress with remedies := base.redress.remedies ++ [remedy s] } }

private theorem remedyConforms {s : State} (ready : Ready s) :
    (remedy s).conforms (assessed s).redress ((assessed s).course 100) := by
  refine ⟨faultEstablished ready (tick 38) (by decide) (by decide),
    ⟨agreementForPlace s, faultApplies ready, trivial⟩,
    by change (tick 38).by (tick 80); decide, ?_, ?_, ?_⟩
  · change ∀ other ∈ s.redress.remedies, _
    rw [ready.noRedress]
    simp
  · change ¬fullRefundClosedBy place s.credit.creditRecords.closed (tick 38)
    simp [ready.noClosures, fullRefundClosedBy]
  · intro _
    exact ⟨⟨tick 80, none, none⟩, rfl, agreementForPlace s,
      Or.inr rfl, ⟨rfl, trivial⟩, rfl, trivial⟩

private theorem acceptedStep {s : State} (ready : Ready s) :
    Step (assessed s) (.redress (.acceptRemedy (remedy s))) (accepted s) := by
  have root : Step (assessed s) (.redress (.acceptRemedy (remedy s)))
      { ((assessed s).withCourse 100 ((assessed s).course 100)).withHolds (assessed s).holds with
        redress := (accepted s).redress } := by
    refine Step.redress trivial trivial ?_ trivial ⟨remedyConforms ready, rfl, rfl, rfl⟩
    intro actual mem
    have same : decisions s = actual :=
      Option.mem_some_iff.mp (show actual ∈ some (decisions s) from mem)
    subst actual
    exact reviewUsed ready
  rw [withCourseSelf, withHoldsSelf (assessed s) ready.synchronised] at root
  exact root

def grant (s : State) : CompensationCreditOrigin :=
  (remedy s).creditOrigin issue ((accepted s).course 100)

private def issuedData (s : State) : StartEvidence :=
  Redress.issueCourseCredit ((accepted s).course 100) (grant s) creditPosting

def final (s : State) : State := (accepted s).withCourse 100 (issuedData s)

private theorem grantMatches {s : State} (ready : Ready s) :
    (grant s).matchesPosting s.credit.ledger s.credit.creditRecords.closed
      s.credit.creditRecords.ownsAccount creditPosting s.credit.creditRecords.lessonFees := by
  refine ⟨JointT.formMatches, rfl, rfl, ⟨faultApplies ready, trivial⟩,
    paidFaultEvidence ready (tick 39) (by decide), recordsDecision s (tick 39) (by decide), ?_,
    ready.owner, ?_, rfl, rfl, rfl, by decide, rfl⟩
  · simp [fullRefundClosedBy, ready.noClosures]
  · exact ⟨⟨agreementForPlace s, rfl⟩, rfl, rfl, rfl, rfl,
      by change (tick 38).by (tick 39); decide, tick 39, rfl, Or.inr rfl, Or.inr rfl⟩

private theorem issuedStep {s : State} (ready : Ready s) :
    Step (accepted s) (.redress (.issueCourseCredit (remedy s) issue creditPosting)) (final s) := by
  have root : Step (accepted s) (.redress (.issueCourseCredit (remedy s) issue creditPosting))
      ((final s).withHolds (final s).holds) := by
    refine Step.redress trivial trivial (by simp [Redress.Event.usesRecordedReviews, Redress.Event.assessmentDecisions]) trivial ?_
    refine ⟨?_, ?_, ?_, grantMatches ready, ?_, ?_, rfl, rfl, rfl⟩
    · change remedy s ∈ s.redress.remedies ++ [remedy s]
      simp
    · refine ⟨by change (tick 38).by (tick 39); decide, ?_, ?_⟩
      · change ∀ row ∈ s.redress.deliveries, _
        rw [ready.noRedress]
        simp
      · change ¬fullRefundClosedBy place s.credit.creditRecords.closed (tick 39)
        simp [ready.noClosures, fullRefundClosedBy]
    · change ∀ old ∈ s.credit.ledger, _
      rw [ready.ledger]
      simp [creditPosting, JointT.topUpPosting, JointT.topUpReceipt, JointT.debit,
        JointT.tick, Moment.before]
    · change ∀ old ∈ s.credit.creditRecords.grants, _
      rw [ready.noGrants]
      simp
    · change ∀ old ∈ s.credit.ledger, _
      rw [ready.ledger]
      simp [creditPosting, JointT.topUpPosting, JointT.debit]
  rw [withHoldsSelf (final s) ready.synchronised] at root
  exact root

def events (s : State) : List Event :=
  [.booking (.beginTeaching lesson (tick 32) [101]), .booking (.endTeaching lesson (tick 33)),
    .booking (.tutorReport lesson tutorReport), .booking (.attendance form attendanceReport),
    .booking (.serviceFeedback form teachingReport), .review reviewEvidence (.decideInitial form terms initial),
    .review reviewEvidence (.retainOriginal lesson originalDecision), .tutorFault (.record (economicEntry s)),
    .redress (.assessRefund (assessedRefund s) holdFacts), .redress (.acceptRemedy (remedy s)),
    .redress (.issueCourseCredit (remedy s) issue creditPosting)]

theorem path (s : State) (ready : Ready s) :
    RecognisedV15.Workflow.Path Step s (events s) (final s) :=
  .next (beganStep ready) <| .next (endedStep ready) <| .next (tutorReportedStep ready) <|
    .next (attendanceStep ready) <| .next (feedbackStep ready) <| .next (decidedStep ready) <|
    .next (retainedStep ready) <| .next (economicStep ready) <| .next (assessedStep ready) <|
    .next (acceptedStep ready) <| .next (issuedStep ready) (.nil _)

theorem ledger (s : State) (ready : Ready s) :
    (final s).credit.ledger = [JointT.topUpPosting, JointT.debit, creditPosting] := by
  change s.credit.ledger ++ [creditPosting] = _
  rw [ready.ledger]
  rfl

/-- The assessed refund has no receipt in this trace. The newly issued credit
    remains in the booking balance because the only lesson debit predates issue. -/
theorem accountAtForty (s : State) (ready : Ready s)
    (opening : s.credit.openingCredit 103 = 0) :
    debitTotal place (final s).credit.ledger (tick 40) = 4 ∧
    refundBalanceDue place (final s).credit.ledger (tick 40) 2 (some 1004) = 2 ∧
    balanceBefore (final s).credit.openingCredit (final s).credit.ledger 103 (tick 40) = 4 ∧
    returnedFrom (final s).credit.ledger creditPosting (tick 40) = 0 := by
  rw [ledger s ready]
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  change balanceBefore s.credit.openingCredit [JointT.topUpPosting, JointT.debit, creditPosting]
    103 (tick 40) = 4
  unfold balanceBefore
  rw [opening]
  decide +kernel

theorem reserves (s : State) : (final s).activeReserves = s.activeReserves := rfl

theorem unchangedLesson (s : State) (id : LessonId) (other : id ≠ 100) :
    (final s).lessons id = s.lessons id := by
  simp [final, accepted, assessed, economic, retained, decided, reported, State.withCourse, other]

theorem originalDelivery (s : State) :
    ((final s).course 100).teachingBegan = some (tick 32) ∧
    ((final s).course 100).teachingEnded = some (tick 33) ∧
    attendanceReport ∈ ((final s).course 100).afterLesson.attendance ∧
    teachingReport ∈ ((final s).course 100).afterLesson.serviceFeedback ∧
    (facts s).teaching = .some := by
  simp only [final, issuedData, Redress.issueCourseCredit, courseAfterWrite]
  change ((reported s).course 100).teachingBegan = _ ∧
    ((reported s).course 100).teachingEnded = _ ∧
    attendanceReport ∈ ((reported s).course 100).afterLesson.attendance ∧
    teachingReport ∈ ((reported s).course 100).afterLesson.serviceFeedback ∧
    (facts s).teaching = .some
  open_teaching
  simp [facts]

theorem retainedEffects (s : State) :
    economicEntry s ∈ (final s).tutorFaults.entries ∧ (economicEntry s).originalTutorPay = 0 ∧
    assessedRefund s ∈ (final s).redress.assessments ∧ (assessedRefund s).amount.finalFee = 2 ∧
    (assessedRefund s).amount.principal = 2 ∧ remedy s ∈ (final s).redress.remedies ∧
    grant s ∈ (final s).credit.creditRecords.grants ∧ issue.amount = 4 := by
  change economicEntry s ∈ s.tutorFaults.entries ++ [economicEntry s] ∧
    (economicEntry s).originalTutorPay = 0 ∧
    assessedRefund s ∈ s.redress.assessments ++ [assessedRefund s] ∧
    (assessedRefund s).amount.finalFee = 2 ∧ (assessedRefund s).amount.principal = 2 ∧
    remedy s ∈ s.redress.remedies ++ [remedy s] ∧
    grant s ∈ s.credit.creditRecords.grants ++ [grant s] ∧ issue.amount = 4
  simp [economicEntry, assessedRefund, issue]

end JointTFault

#print axioms JointTFault.path
#print axioms JointTFault.originalDelivery
#print axioms JointTFault.retainedEffects
#print axioms JointTFault.ledger
#print axioms JointTFault.accountAtForty
#print axioms JointTFault.unchangedLesson
