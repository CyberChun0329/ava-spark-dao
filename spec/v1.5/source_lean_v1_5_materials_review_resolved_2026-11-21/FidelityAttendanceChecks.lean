import SourceV14.Workflow

/-! Recorded attendance and feedback, verified absence, and the fee decision that uses it. -/

namespace FidelityAttendanceChecks

open SourceV14 SourceV14.Confirmation SourceV14.Course SourceV14.CreditEvidence
open SourceV14.Operations SourceV14.Workflow
open SourceV14.Workflow.AttendanceFacts
open SourceV14.Booking (Schedule AttendanceReport DeliveryReport TutorDeliveryReport)
open SourceV14.Settlement (Roster)

private def m (seconds : Nat) : Moment := ⟨seconds, 0⟩
private def lesson : Lesson := ⟨17, .oneToOne, 1, 2, 3, 80⟩
private def place : Place := ⟨8, 17, 11, 12, 13, 14, 100, 100⟩
private def schedule : Schedule := ⟨17, m 30, m 60, "UTC", m 8, m 9⟩
private def payment : PaymentTerms := ⟨.fixed (m 100), .fixed (m 100)⟩

private def form : PartOne where
  lesson := lesson
  place := place
  contacts := ⟨"Provider", "email", "student", none, "coordinator", 4, "lead", none, none,
    5, "review", 6, "alternative", false, 7, "escalation"⟩
  rulesVersion := "1.5"
  confirmedAt := m 10
  customerRepresentatives := []
  schedule := schedule
  serviceTerms := "Tutoring"
  serviceItems := [1]
  discountBasis := none
  privateRoster := none
  rosterLock := none
  groupRescheduleCutoff := none
  oneToOneAdvanceCutoff := some (.fixed (m 25))
  cancelChangeTerms := "Agreed changes"
  noFaultTerms := "No-fault terms"
  applicableStartTerms := "Start terms"
  tutorAgreementRef := "Tutor agreement"
  absentGroupPlacePay := none
  materialsOrBundle := none
  materialsTermsRef := none
  materialsPayer := none
  deadlines := ⟨.fixed (m 100), m 100, none, payment, payment, payment, payment,
    .fixed (m 100), m 105, m 105, m 105, .fixed (m 106)⟩

private def authorities : ReviewAuthorities where
  corePartner := fun _ _ ↦ False
  initialFinding := fun _ _ _ ↦ False
  reviewer := fun _ _ _ ↦ False
  approvesPayment := fun _ _ _ ↦ False
  interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
  originalDecisionMaker := fun _ ↦ none
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

private def holds : HoldHistory := { payments := ⟨[], [], []⟩, temporary := [], formal := [], lifts := [] }

private def course : StartEvidence where
  effectiveForms := [form]
  groupRoster := none
  bookings := []
  scheduleHistory := [schedule]
  changes := []
  openingCredit := fun _ ↦ 0
  creditRecords :=
    { topUps := [], grants := [], topUpReturns := [], closed := []
      ownsAccount := fun _ _ ↦ False, courseProviderAt := fun _ _ ↦ False
      verifiedRefunds := [], payments := holds.payments, paymentAuthorities := authorities }
  ledger := []
  discounts := []
  notices := []
  academicTeamAt := fun _ _ _ ↦ False
  teachingBegan := none
  teachingEnded := none
  studentsTakingLesson := []
  afterLesson := ⟨[], [], [], [], [], []⟩
  studentFaults :=
    { findings := []
      decisions :=
        { authorities, terms := ⟨3, 6, 4, .exact (m 100), m 105, m 105, m 105, 7⟩
          appointments := [], faultOutcomes := []
          faultMatterCovers := fun _ _ ↦ False, wasResponsibleTutor := fun _ _ ↦ False
          originalAttendanceTime := fun _ _ _ ↦ False }
      recordedStudentOutcome := fun _ ↦ False }

private def initial : State where
  lessons := fun _ ↦ LessonFile.fromEvidence course
  credit := CreditBook.fromEvidence course
  holds := holds
  cancelled := []
  settlement := {}
  redress := {}
  materials := {}
  review := Review.History.empty
  debts := {}
  activeReserves := []
  paymentRecords := []
  separateBookings := []

private def attended : AttendanceReport := ⟨17, 8, 11, 3, m 65, true⟩
private def service : DeliveryReport := ⟨17, 8, 11, 3, m 66, [], [1]⟩

private def withAttendance : StartEvidence :=
  { course with afterLesson := { course.afterLesson with attendance := [attended] } }

private def withFeedback : StartEvidence :=
  { withAttendance with afterLesson := { withAttendance.afterLesson with serviceFeedback := [service] } }

private def recordedAttendance : State := initial.withCourse lesson.id withAttendance
private def recordedFeedback : State := recordedAttendance.withCourse lesson.id withFeedback

private theorem formMatches : form.matches := by
  simp [PartOne.matches, form, lesson, place, schedule, m, Contacts.complete,
    Place.matches, Place.validFees, SourceV14.Booking.Schedule.valid, Moment.by, Moment.before,
    PayAndReviewTerms.valid, payment, PaymentTerms.valid, PaymentDeadline.valid,
    AdvanceWindow.validAt] <;> decide +kernel

private theorem agreedSlot : EffectiveSchedule lesson course schedule schedule.start := by
  have valid : schedule.valid := by
    unfold SourceV14.Booking.Schedule.valid
    decide +kernel
  have wasAgreed : ScheduleWasAgreed lesson course schedule := by
    refine ⟨rfl, valid, Or.inl ⟨rfl, ?_, ?_⟩⟩
    · simp [StartEvidence.rosterMatchesForms, StartEvidence.formsMatch,
        course, formMatches, show form.lesson = lesson from rfl, lesson]
    · simp [course, show form.schedule = schedule from rfl]
  refine ⟨rfl, ⟨by simp [course], valid, by decide, ?_⟩, ?_, ?_⟩
  · intro other present _ _ _
    have : other = schedule := by simpa [course] using present
    subst other
    exact Or.inr rfl
  · simp [course, lesson, schedule]
  · intro other present _ _
    have : other = schedule := by simpa [course] using present
    subst other
    exact wasAgreed

theorem tutorNoShowReportsAreRetained :
    Step initial (.booking (.attendance form attended)) recordedAttendance ∧
    Step recordedAttendance (.booking (.serviceFeedback form service)) recordedFeedback ∧
    attended ∈ (recordedFeedback.course lesson.id).afterLesson.attendance ∧
    service ∈ (recordedFeedback.course lesson.id).afterLesson.serviceFeedback ∧
    (recordedFeedback.course lesson.id).teachingBegan = none ∧
    ¬ ∃ row, TutorDeliveryRecorded (recordedFeedback.course lesson.id) lesson (m 66) row := by
  refine ⟨.booking trivial trivial trivial ?_ rfl trivial trivial trivial,
    .booking trivial trivial trivial ?_ rfl trivial trivial trivial, by simp [recordedFeedback, State.course,
      State.withCourse, withFeedback, withAttendance, course], by simp [recordedFeedback,
      State.course, State.withCourse, withFeedback, withAttendance, course], rfl, ?_⟩
  · refine ⟨?_, Or.inl (by simp [initial, State.course, course]), ⟨rfl, rfl, rfl, rfl⟩,
      Or.inr ⟨rfl, rfl, schedule, agreedSlot, by decide, by decide⟩, rfl⟩
    change (∀ f : PartOne, f ∈ [form] ∨ (∃ booking : SourceV14.Course.BookingEvidence,
      (f, booking) ∈ ([] : List (PartOne × SourceV14.Course.BookingEvidence))) → f.lesson = lesson) ∧
      (∀ roster ∈ (none : Option Roster), roster.lesson = lesson.id) ∧
      (∀ row ∈ [schedule], row.lesson = lesson.id)
    simp [show form.lesson = lesson from rfl, show schedule.lesson = lesson.id from rfl]
  · refine ⟨?_, Or.inl (by simp [recordedAttendance, State.course, State.withCourse,
      withAttendance, course, Booking.Event.lesson, show form.lesson = lesson from rfl]),
      ⟨rfl, rfl, rfl, rfl, by simp [service], by simp [service, form],
      by simp [service]⟩, Or.inr ⟨rfl, rfl, schedule, agreedSlot, by decide, by decide⟩, rfl⟩
    change (∀ f : PartOne, f ∈ [form] ∨ (∃ booking : SourceV14.Course.BookingEvidence,
      (f, booking) ∈ ([] : List (PartOne × SourceV14.Course.BookingEvidence))) → f.lesson = lesson) ∧
      (∀ roster ∈ (none : Option Roster), roster.lesson = lesson.id) ∧
      (∀ row ∈ [schedule], row.lesson = lesson.id)
    simp [show form.lesson = lesson from rfl, show schedule.lesson = lesson.id from rfl]
  · rintro ⟨row, recorded⟩
    exact List.not_mem_nil recorded.1

private theorem verifiedReasonCannotBeGood {before after : State} {f : PartOne}
    {s : Schedule} {start checkedAt query : Moment} {facts : AbsenceFacts}
    {reason : AbsenceReasonEvidence} {row : OneToOneAbsence}
    {handler : SourceV14.Booking.Handler} {assignment : SettlementAssignment}
    (step : Step before (.booking (.verifyOneToOneAbsence f s start checkedAt facts
      reason handler assignment)) after)
    (noGoodReason : facts.verifiedGoodReason = some false)
    (member : row ∈ (after.course f.lesson.id).verifiedOneToOneAbsence) :
    (row.factsAt (after.course f.lesson.id).oneToOneAbsenceReasons query).verifiedGoodReason ≠
      some true := by
  cases step with
  | booking _ _ _ checked _ _ =>
    rcases checked with ⟨_, _, _, _, _, _, _, resolves, _, _, _, _, _, accepted, installed⟩
    rw [noGoodReason] at accepted
    obtain ⟨outcome, _, rfl⟩ := accepted
    subst_vars
    simp only [Booking.Event.lesson, State.course, State.withCourse,
      LessonFile.evidence, LessonFile.fromEvidence] at member ⊢
    change row ∈ ((before.course f.lesson.id).verifiedOneToOneAbsence <|>
      some ⟨f, s, start, checkedAt, facts⟩) at member
    change (row.factsAt [⟨checkedAt, outcome, false⟩] query).verifiedGoodReason ≠ some true
    cases existing : (before.course f.lesson.id).verifiedOneToOneAbsence with
    | none =>
      simp [existing] at member
      subst row
      by_cases known : checkedAt.by query ∧ outcome.decidedAt.by query <;>
        simp [OneToOneAbsence.factsAt, OneToOneAbsenceReason.latestAt, known, noGoodReason]
    | some prior =>
      have unresolved := (resolves prior (by
        simpa only [Booking.Event.lesson, existing] using
          (show prior ∈ some prior by simp))).2.2.2.2.1
      simp [existing] at member
      subst row
      by_cases known : checkedAt.by query ∧ outcome.decidedAt.by query <;>
        simp [OneToOneAbsence.factsAt, OneToOneAbsenceReason.latestAt, known, unresolved]

/-- A fee assessment cannot substitute a good reason for the same checked failed occurrence. -/
theorem verifiedNoGoodReasonBlocksFreshGoodReason {before checked next : State} {f : PartOne}
    {s : Schedule} {start checkedAt : Moment} {verified fresh : AbsenceFacts}
    {checkedReason freshReason : AbsenceReasonEvidence} {handler : SourceV14.Booking.Handler}
    {assignment : SettlementAssignment} {entry : Settlement.AdoptedFee}
    {assessment : AgreedChangeAssessment}
    (verifiedStep : Step before (.booking (.verifyOneToOneAbsence f s start checkedAt verified
      checkedReason handler assignment)) checked)
    (noGoodReason : verified.verifiedGoodReason = some false)
    (freshGoodReason : fresh.verifiedGoodReason = some true)
    (sameForm : entry.decision.form = f)
    (feeBasis : entry.decision.basis = .agreedChange (.goodReasonAbsence fresh freshReason) assessment) :
    ¬ Step checked (.settlement (.assessFee entry)) next := by
  intro step
  cases step with
  | settlement _ _ _ _ _ _ assessed =>
    cases assessed with
    | assessFee allowed _ _ =>
      rw [Settlement.FeeDecision.allowed, feeBasis] at allowed
      rcases allowed.2.1 with ⟨row, membership, _, _, sameFacts⟩
      have atCheckedForm : row ∈ (checked.course f.lesson.id).verifiedOneToOneAbsence := by
        simpa only [Settlement.Event.lesson, sameForm] using membership
      apply verifiedReasonCannotBeGood (query := entry.decision.decidedAt)
        verifiedStep noGoodReason atCheckedForm
      simpa only [Settlement.Event.lesson, sameForm, freshGoodReason] using
        congrArg AbsenceFacts.verifiedGoodReason sameFacts

private def reasonFacts (good : Bool) : AbsenceFacts where
  startRequirementsMet := True
  studentNotifiedAsAgreed := True
  teachingAvailableAsAgreed := True
  studentDidNotAttend := True
  providerErrorCausedMissedService := False
  cancelledOrRescheduledUnderTerms := False
  lessonWentAhead := False
  couldNotProceedSolelyForNonattendance := True
  studentWasNotReady := True
  verifiedGoodReason := some good

private def reasonMatter : ReviewMatter := ⟨91, lesson.id, [place.student, place.customer]⟩
private def initialFinding : InitialFinding :=
  ⟨reasonMatter, .absenceReason, 4, m 31, "Initial reason finding", []⟩
private def originalReason : Review.OriginalRecord :=
  ⟨⟨reasonMatter, 72, 4, initialFinding.decidedAt⟩, none⟩
private def reviewerAppointment : ReviewAppointment := ⟨reasonMatter, lesson.provider, 5, m 37⟩
private def reviewedFinding : ReviewFinding :=
  ⟨reasonMatter, 5, m 40, "Independent review of the absence reason", 73, true⟩
private def reasonCorrection : SettlementCorrection :=
  ⟨lesson.id, originalReason.outcome.outcome, reviewedFinding.outcome, lesson.coordinator, m 45,
    [place.student, place.customer]⟩
private def reviewedChange (prior : Bool) : AbsenceReasonCorrection :=
  ⟨form, schedule, schedule.start, originalReason, reviewedFinding, reasonCorrection, !prior⟩

private def reasonAuthorities : ReviewAuthorities :=
  { authorities with
    corePartner := fun actor _ ↦ actor = lesson.provider
    initialFinding := fun matter actor _ ↦ matter = reasonMatter ∧ actor = 4
    reviewer := fun matter actor _ ↦ matter = reasonMatter ∧ actor = 5
    originalDecisionMaker := fun _ ↦ some 4 }

private def reasonTerms : ReviewTerms := course.studentFaults.decisions.terms

private def reasonHolds : HoldFacts where
  terms := fun _ ↦ reasonTerms
  termsApply := fun _ ↦ False
  acceptedPaymentConcern := fun _ _ _ _ ↦ False
  reviewerCannotActInTime := fun _ _ ↦ False
  temporaryAuthority := fun _ _ _ _ ↦ False
  allegedFactsWouldChangePayment := fun _ _ _ ↦ False
  separatelyIdentifiable := fun _ _ ↦ False
  establishedParts := fun _ _ ↦ []
  paymentAffected := fun _ _ ↦ False
  decisionPending := fun _ _ _ ↦ False
  partFallsUnderDecision := fun _ _ _ ↦ False
  decisionConcernsWholeGroup := fun _ _ ↦ False
  isGroupLesson := fun _ ↦ False
  affectsWholeSettlement := fun _ ↦ False
  groupSettlementParts := fun _ ↦ []

private def reviewEvidence : Review.Evidence where
  authority := reasonAuthorities
  holds := reasonHolds
  concernFacts :=
    { effectivePlace := fun _ _ ↦ False
      tutorAffected := fun _ _ ↦ False
      relevantShareClaimantAffected := fun _ _ ↦ False
      believesUseOmitted := fun _ _ ↦ False
      relevantContributor := fun _ _ ↦ False
      coordinatorUnreachable := fun _ _ ↦ False
      coordinatorPersonallyInterested := fun _ _ ↦ False
      complaintAboutCoordinator := fun _ ↦ False }
  publishedTerms := fun _ _ _ ↦ False
  replyTrigger := fun _ _ ↦ none
  verifiedReplyTrigger := fun _ _ ↦ False
  replyLegalDeadline := fun _ ↦ none
  verifiedFactCheck := fun _ ↦ False
  originalOutcome := (· = originalReason.outcome)
  recordedAmount := fun _ _ _ ↦ False

private def verifiedOccurrence (prior : Bool) : OneToOneAbsence :=
  ⟨form, schedule, schedule.start, m 42, reasonFacts prior⟩
private def verifiedReason (prior : Bool) : OneToOneAbsenceReason :=
  ⟨(verifiedOccurrence prior).checkedAt, originalReason.outcome, prior⟩

private def reviewReady (prior : Bool) : State :=
  { initial.withCourse lesson.id { course with
      ledger := [⟨1, place.account, .lessonDebit lesson.id place.id, 100, form.confirmedAt⟩]
      verifiedOneToOneAbsence := some (verifiedOccurrence prior)
      oneToOneAbsenceReasons := [verifiedReason prior] } with
    review := { Review.History.empty with
      appointments := [reviewerAppointment]
      initialFindings := [initialFinding]
      originals := [originalReason] }
    verifiedAbsenceOutcome := fun finding placeId ↦
      if finding = reviewedFinding ∧ placeId = place.id then some (!prior) else none }

private def reviewDecided (prior : Bool) : State :=
  { reviewReady prior with review := { (reviewReady prior).review with
      reviewFindings := [reviewedFinding] } }

private def reviewRecorded (prior : Bool) : State :=
  { reviewDecided prior with review := { (reviewDecided prior).review with
      corrections := [.nonmonetary originalReason reviewedFinding reasonCorrection] } }

private def reasonCorrected (prior : Bool) : State :=
  let saved := reviewRecorded prior
  let ev := saved.course lesson.id
  saved.withCourse lesson.id { ev with
    oneToOneAbsenceReasons := ev.oneToOneAbsenceReasons ++ [(reviewedChange prior).reason] }

private theorem reviewFindingValid (prior : Bool) :
    reviewFindingRecordedConforms ((reviewReady prior).review.authorities reasonAuthorities)
      none [reviewerAppointment] [initialFinding] [reviewedFinding] reviewedFinding := by
  simp [reviewFindingRecordedConforms, reviewFindingConformsWithContacts, independentReviewer,
    didNotMakeOriginalFinding, ReviewAuthorities.disinterested, ReviewAuthorities.mayDecideDispute,
    ReviewAppointment.applies, Review.History.authorities, Review.History.empty, reviewReady,
    reasonAuthorities, authorities, initialFinding, reviewedFinding, originalReason,
    reviewerAppointment, DirectInterest.affected]
  constructor
  · rintro _ _ _ _ rfl _ _ _
    decide
  · decide

private theorem decideAbsenceReview (prior : Bool) :
    Step (reviewReady prior) (.review reviewEvidence (.decideReview lesson none reviewedFinding))
      (reviewDecided prior) := by
  apply Step.review (by trivial) (by trivial) (by rintro _ h; cases h)
  apply Review.Step.decideReview
  · rfl
  · exact Or.inr (Or.inl ⟨initialFinding, by simp [reviewReady], ⟨rfl, rfl⟩, by decide⟩)
  · simp
  · simp [HoldHistory.temporarySettersRecorded, reviewReady, initial, State.withCourse, holds,
      Review.History.authorities, State.reviewEvidence, reviewEvidence, reasonAuthorities, authorities]
  · exact reviewFindingValid prior
  · simp [reviewReady, Review.History.empty]
  · simp [reviewReady, Review.History.empty]

private theorem recordAbsenceReview (prior : Bool) :
    Step (reviewDecided prior) (.review reviewEvidence
      (.recordCorrection lesson (.nonmonetary originalReason reviewedFinding reasonCorrection)))
      (reviewRecorded prior) := by
  apply Step.review (by trivial) (by trivial) (by rintro _ h; cases h)
  apply Review.Step.recordNonmonetary
  · simp [reviewDecided, reviewReady]
  · simp [reviewDecided]
  · simp [State.reviewEvidence, reviewEvidence]
  · refine ⟨(reviewFindingValid prior).2.1, rfl, originalReason.outcome, by simp, ?_⟩
    refine ⟨rfl, rfl, ⟨rfl, rfl⟩, by decide, by decide, rfl, rfl, by decide, rfl, by decide, ?_⟩
    simp [originalReason, reviewedFinding, reasonCorrection, reasonMatter]
  · simp [reviewDecided, reviewReady, Review.History.empty]

/-- Both reviewed polarities are recorded for the same occurrence and keep the original outcome. -/
theorem independentReviewChangesOperativeAbsenceReason (prior : Bool) :
    Step (reviewReady prior) (.review reviewEvidence (.decideReview lesson none reviewedFinding))
      (reviewDecided prior) ∧
    Step (reviewDecided prior) (.review reviewEvidence
      (.recordCorrection lesson (.nonmonetary originalReason reviewedFinding reasonCorrection)))
      (reviewRecorded prior) ∧
    Step (reviewRecorded prior) (.correctAbsenceReason (reviewedChange prior))
      (reasonCorrected prior) ∧
    (reasonCorrected prior).review.originals = [originalReason] ∧
    (reasonCorrected prior).settlement = (reviewRecorded prior).settlement ∧
    (reasonCorrected prior).holds = (reviewRecorded prior).holds ∧
    (reasonCorrected prior).credit = (reviewRecorded prior).credit := by
  refine ⟨decideAbsenceReview prior, recordAbsenceReview prior, .correctAbsenceReason ?_,
    rfl, rfl, rfl, rfl⟩
  refine ⟨by simp [reviewRecorded, reviewedChange], ?_,
    by change (m 40).by (m 45); decide, ?_, verifiedReason prior, rfl, rfl,
    by change (m 31).before (m 40); decide, by change (m 42).before (m 45); decide, ?_⟩
  · simp [reviewRecorded, reviewDecided, reviewReady, reviewedChange, form]
  · exact ⟨verifiedOccurrence prior, by simp [reviewRecorded, reviewDecided, reviewReady,
      State.course, State.withCourse, reviewedChange, verifiedOccurrence,
      show form.lesson = lesson from rfl],
      ⟨rfl, rfl, by change (m 42).by (m 45); decide⟩, rfl⟩
  · cases prior <;> decide

/-- A delayed filing preserves the prior reason at the intervening historical query. -/
theorem absenceReasonReadUsesRecordedCut (prior : Bool) :
    let ev := (reasonCorrected prior).course lesson.id
    ev.verifiedOneToOneAbsence = some (verifiedOccurrence prior) ∧
    ev.oneToOneAbsenceReasons = [verifiedReason prior, (reviewedChange prior).reason] ∧
    ev.retainsOneToOneAbsence form schedule schedule.start (m 44) (reasonFacts prior) ∧
    ev.retainsOneToOneAbsence form schedule schedule.start (m 45) (reasonFacts (!prior)) := by
  refine ⟨rfl, rfl, ⟨verifiedOccurrence prior, by simp [reasonCorrected, reviewRecorded,
    reviewDecided, reviewReady, State.course, State.withCourse],
    ⟨rfl, rfl, by change (m 42).by (m 44); decide⟩, rfl, ?_⟩,
    ⟨verifiedOccurrence prior, by simp [reasonCorrected, reviewRecorded, reviewDecided, reviewReady,
      State.course, State.withCourse], ⟨rfl, rfl, by change (m 42).by (m 45); decide⟩, rfl, ?_⟩⟩
  · rfl
  · rfl

/-- A retained finding alone supplies no recorded correction or verified change of reason. -/
theorem absenceReviewNeedsCorrectionAndVerifiedReason (prior : Bool) (next : State) :
    ¬ Step (reviewDecided prior) (.correctAbsenceReason (reviewedChange prior)) next ∧
    ¬ Step { reviewRecorded prior with verifiedAbsenceOutcome := fun _ _ ↦ none }
      (.correctAbsenceReason (reviewedChange prior)) next := by
  constructor
  · intro step
    cases step with
    | correctAbsenceReason linked =>
      simpa [reviewDecided, reviewReady, Review.History.empty] using linked.1
  · intro step
    cases step with
    | correctAbsenceReason verified =>
      simpa using verified.2.1

theorem absenceReviewCannotChangeAnotherStart (next : State) :
    ¬ Step (reviewRecorded false) (.correctAbsenceReason { reviewedChange false with
      start := m 31 }) next := by
  intro step
  cases step with
  | correctAbsenceReason verified =>
    obtain ⟨row, retained, checked, _⟩ := verified.2.2.2.1
    change row ∈ some (verifiedOccurrence false) at retained
    have exactRow : verifiedOccurrence false = row := by simpa using retained
    subst row
    exact (by decide : schedule.start ≠ m 31) checked.2.1

theorem absenceReviewCannotChangeAnotherOutcome (next : State) :
    let old : Review.OriginalRecord := { originalReason with
      outcome := { originalReason.outcome with outcome := 79 } }
    let record := { reasonCorrection with originalOutcome := 79 }
    let before := reviewRecorded false
    let state := { before with review := { before.review with
      originals := before.review.originals ++ [old]
      corrections := before.review.corrections ++ [.nonmonetary old reviewedFinding record] } }
    ¬ Step state (.correctAbsenceReason { reviewedChange false with
      original := old, correction := record }) next := by
  dsimp only
  intro step
  cases step with
  | correctAbsenceReason verified =>
    obtain ⟨prior, saved, linked, _⟩ := verified.2.2.2.2
    change some (verifiedReason false) = some prior at saved
    have exactPrior := Option.some.inj saved
    subst prior
    exact (by decide : (72 : Nat) ≠ 79) (congrArg RecordedSettlementOutcome.outcome linked)

private def goodReasonRecord : AbsenceReasonDecision :=
  ⟨initialFinding, some reviewedFinding, place.id, true⟩

private def goodReasonEvidence : AbsenceReasonEvidence :=
  ⟨True, (reviewRecorded false).review.decisionRecords reasonAuthorities
    course.studentFaults.decisions, [goodReasonRecord]⟩

private def reviewedFeeAt (query : Moment) : Settlement.AdoptedFee where
  reference := 74
  decision := {
    form, schedule, start := schedule.start, expiry := m 100, decidedAt := query
    handler := ⟨lesson.coordinator, false, ⟨false, false, false, false⟩⟩
    assignment := ⟨reasonMatter, 74, reasonAuthorities, none, none, (· = place.id)⟩
    holdFacts := reasonHolds
    basis := .agreedChange (.goodReasonAbsence (reasonFacts true) goodReasonEvidence)
      ⟨form.cancelChangeTerms, 15, 25, True⟩
    amounts := ⟨lesson.id, place.id, 15, 100, 85, 0, 25, 0⟩ }

private theorem goodReasonEvidenceApplies : goodReasonEvidence.applies form (reasonFacts true)
    (m 46) := by
  intro _
  refine ⟨?_, goodReasonRecord, by simp [goodReasonEvidence], ?_, rfl, ?_⟩
  · simp [goodReasonEvidence, Review.History.decisionRecords, Operations.ReviewTerms.matchesForm,
      course, form, lesson]
  · refine ⟨rfl, rfl, rfl, by decide, ?_, ⟨rfl, rfl⟩, by decide, by decide, ?_⟩
    · simp [goodReasonEvidence, goodReasonRecord, Review.History.decisionRecords, reviewRecorded,
        reviewDecided, reviewReady, course, initialFindingRecordedConforms,
        initialFindingConformsWithContacts, ReviewAuthorities.disinterested,
        ReviewAuthorities.mayDecideDispute, Review.History.authorities, reasonAuthorities,
        authorities, initialFinding, DirectInterest.affected]
    · obtain ⟨member, conformance, original⟩ := reviewFindingValid false
      obtain ⟨independent, reason, _, mayDecide⟩ := conformance
      exact ⟨member, ⟨independent, reason, Or.inl rfl, mayDecide⟩, original⟩
  · intro other member _
    have : other = goodReasonRecord := by simpa [goodReasonEvidence] using member
    subst other
    exact ⟨Or.inr rfl, fun _ ↦ rfl⟩

/-- The linked good reason opens the agreed change terms for an actual fee assessment. -/
theorem reviewedGoodReasonFeeAtRoot :
    let before := reasonCorrected false
    let fee := reviewedFeeAt (m 46)
    Step before (.settlement (.assessFee fee)) { before with settlement := { fees := [fee] } } := by
  apply Step.settlement
  · change ¬ Cancellation.PlaceCancelledAt [] form.place (m 46)
    simp [Cancellation.PlaceCancelledAt]
  case absence =>
    change (reasonCorrected false).absenceReasonCurrentAt form (m 46)
    intro prior current revision filed
    change prior ∈ some (reviewedChange false).reason at current
    change revision ∈ [Review.Correction.nonmonetary originalReason reviewedFinding
      reasonCorrection] at filed
    have exactPrior : (reviewedChange false).reason = prior := by simpa using current
    have exactRevision : revision = .nonmonetary originalReason reviewedFinding
        reasonCorrection := by simpa using filed
    subst prior
    subst revision
    intro sameOutcome
    exact ((by decide : originalReason.outcome ≠ (reviewedChange false).reason.outcome)
      sameOutcome).elim
  all_goals first | trivial | apply Settlement.Step.assessFee
  · have retained : ((reasonCorrected false).course lesson.id).retainsOneToOneAbsence
        form schedule schedule.start (m 46) (reasonFacts true) :=
      ⟨verifiedOccurrence false, by simp [reasonCorrected, reviewRecorded, reviewDecided,
        reviewReady, State.course, State.withCourse], ⟨rfl, rfl, by decide⟩, rfl, rfl⟩
    refine ⟨rfl, retained, by decide, ?_⟩
    refine ⟨⟨none, [form], ?_, List.mem_singleton_self _⟩, ?_, ?_, ?_, ?_,
      Or.inr (Or.inr ⟨(reasonFacts true, goodReasonEvidence), by simp, ?_,
        goodReasonEvidenceApplies, schedule, schedule.start, retained⟩),
      rfl, trivial, ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩, rfl, rfl, by decide +kernel⟩
    · change (course.formsMatch lesson ∧ [form].length = 1) ∧ [form] = [form]
      simp [StartEvidence.formsMatch, course, formMatches, show form.lesson = lesson from rfl]
    · simp [reviewedFeeAt, SettlementAssignment.authorised, reasonAuthorities, authorities,
        reasonMatter, form, SourceV14.Booking.Handler.maySettle,
        ReviewAuthorities.disinterested, DirectInterest.affected]
    · simp [reviewedFeeAt, FeeHoldTermsMatch, HoldFacts.matchesForm, reasonHolds]
    · change holds.mayCarryOutDecision reasonAuthorities reasonHolds reasonMatter 74 (m 46)
      simp [HoldHistory.mayCarryOutDecision, HoldHistory.distinctFormalDecisions,
        HoldHistory.decisionOnFormalHold, HoldHistory.validFormalHold, holds]
    · change ¬FeeOnHold holds reasonAuthorities reasonHolds form.place (m 46)
      simp [FeeOnHold, HoldHistory.paymentOnHold, HoldHistory.formalInForce,
        HoldHistory.temporaryInForce, HoldHistory.validFormalHold, holds]
    · change oneToOneAbsenceUsesChangeTerms lesson place (reasonFacts true)
      simp [oneToOneAbsenceUsesChangeTerms, verifiedStudentAbsence, lesson, place,
        Place.matches, reasonFacts]
  · change ∀ old ∈ ([] : List Settlement.AdoptedFee), old.reference ≠ 74
    simp
  · trivial

/-- An already filed reversal must be applied before assessing a fee from the old reason. -/
theorem filedAbsenceReviewBlocksStaleFee (next : State) :
    ¬ Step (reviewRecorded true) (.settlement (.assessFee (reviewedFeeAt (m 46)))) next := by
  intro step
  cases step with
  | settlement _ _ _ _ _ current _ =>
    change (reviewRecorded true).absenceReasonCurrentAt form (m 46) at current
    have rejected := current (verifiedReason true) (by change _ ∈ some _; simp)
      (.nonmonetary originalReason reviewedFinding reasonCorrection)
      (by change _ ∈ [_]; simp) rfl (by decide) false (by change false ∈ some false; simp)
    exact (by decide : false ≠ true) rejected

/-- A registered half fee takes priority for that place even if fresh inputs omit the absence. -/
theorem assessedGroupAbsenceBlocksOrdinaryCharge {before assessed next : State}
    {half ordinary : Settlement.AdoptedFee} {absenceFacts : AbsenceFacts}
    {absenceReason : AbsenceReasonEvidence} {roster : Roster}
    {completed verified wentAhead available : Bool} {attendance fault : List PlaceId}
    {ordinaryFacts : PlaceFeeFacts}
    (halfBasis : half.decision.basis = .absence absenceFacts absenceReason)
    (halfKind : half.decision.form.lesson.kind = .group)
    (assess : Step before (.settlement (.assessFee half)) assessed)
    (sameLesson : half.decision.form.lesson.id = ordinary.decision.form.lesson.id)
    (samePlace : half.decision.form.place.id = ordinary.decision.form.place.id)
    (prior : half.decision.decidedAt.by ordinary.decision.decidedAt)
    (ordinaryBasis : ordinary.decision.basis = .ordinaryGroup roster completed verified wentAhead
      available attendance fault { ordinaryFacts with absence := none }) :
    ¬ Step assessed (.settlement (.assessFee ordinary)) next := by
  intro step
  cases assess with
  | settlement _ _ _ _ _ _ original =>
    cases original with
    | assessFee allowed _ _ =>
      rw [Settlement.FeeDecision.allowed, halfBasis] at allowed
      have halfFee : groupAbsenceHalfFee half.decision.form.lesson half.decision.form.place
          absenceFacts := by
        rcases allowed with ⟨_, _, _, _, _, _, _, _, _, ⟨_, _, group | one⟩, _⟩
        · obtain ⟨_, _, _, amounts⟩ := group
          exact amounts.1
        · have wrongKind : half.decision.form.lesson.kind = .oneToOne := one.1.1
          simp [halfKind] at wrongKind
      cases step with
      | settlement _ _ _ _ _ _ following =>
        cases following with
        | assessFee _ _ precedence =>
          rw [Settlement.FeeDecision.respectsRecordedGroupAbsence, ordinaryBasis] at precedence
          refine precedence ⟨half, by simp, sameLesson, samePlace, prior, ?_⟩
          simpa only [halfBasis] using halfFee

#print axioms tutorNoShowReportsAreRetained
#print axioms verifiedNoGoodReasonBlocksFreshGoodReason
#print axioms assessedGroupAbsenceBlocksOrdinaryCharge
#print axioms independentReviewChangesOperativeAbsenceReason
#print axioms absenceReasonReadUsesRecordedCut
#print axioms absenceReviewNeedsCorrectionAndVerifiedReason
#print axioms absenceReviewCannotChangeAnotherStart
#print axioms absenceReviewCannotChangeAnotherOutcome
#print axioms reviewedGoodReasonFeeAtRoot
#print axioms filedAbsenceReviewBlocksStaleFee

end FidelityAttendanceChecks
