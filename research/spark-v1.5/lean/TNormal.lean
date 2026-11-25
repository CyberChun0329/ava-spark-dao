import TPrefix

namespace JointT

open SourceV14 SourceV14.Booking SourceV14.Confirmation SourceV14.Course
open SourceV14.CreditEvidence SourceV14.Settlement SourceV14.Operations SourceV14.Workflow

private abbrev DirectPath := RecognisedV15.Workflow.Path SourceV14.Workflow.Step

/-- The course-local projection of a booked T lesson with its original schedule and no
teaching reports. Other courses, obligations and reserves are outside this projection. -/
def teachingInput (credit : CreditBook) (decisions : DecisionRecords) : StartEvidence :=
  { (freshT decisions).evidence credit with
    effectiveForms := [form], bookings := [(form, booking)], scheduleHistory := [schedule] }

theorem bookedTeachingInput (s : State) {decisions : DecisionRecords}
    (fresh : s.lessons lesson.id = freshT decisions) :
    (booked s).course lesson.id = teachingInput (booked s).credit decisions := by
  simp [booked, bookedCourse, teachingInput, State.course, State.withCourse, fresh,
    LessonFile.evidence, LessonFile.fromEvidence, CreditBook.fromEvidence]

def startAt : Moment := tick 32
def endAt : Moment := tick 33

def studentNotice : Notice :=
  ⟨schedule.confirmationTarget, form.contacts.leadAcademicTutor, place.student,
    form.contacts.studentNotice, ⟨31, 1⟩⟩

def tutorNotice : Notice :=
  ⟨schedule.confirmationTarget, lesson.provider, lesson.tutor, "tutor", ⟨31, 2⟩⟩

private def addNotice (notice : Notice) (ev : StartEvidence) : StartEvidence :=
  { ev with notices := ev.notices ++ [notice] }

private def beginNormal (ev : StartEvidence) : StartEvidence :=
  { ev with teachingBegan := some startAt, studentsTakingLesson := [place.student] }

private def endNormal (ev : StartEvidence) : StartEvidence :=
  { ev with teachingEnded := some endAt }

def noticedCourse (ev : StartEvidence) : StartEvidence :=
  addNotice tutorNotice (addNotice studentNotice ev)

def deliveredCourse (ev : StartEvidence) : StartEvidence :=
  endNormal (beginNormal (noticedCourse ev))

private def onT (s : State) (update : StartEvidence → StartEvidence) : State :=
  s.withCourse lesson.id (update (s.course lesson.id))

@[simp] private theorem onT_course (s : State) (update : StartEvidence → StartEvidence) :
    (onT s update).course lesson.id = update (s.course lesson.id) := by
  simp [onT, State.withCourse, State.course]

private def afterStudentNotice (s : State) : State := onT s (addNotice studentNotice)
def afterNotices (s : State) : State := onT (afterStudentNotice s) (addNotice tutorNotice)
private def afterBegin (s : State) : State := onT (afterNotices s) beginNormal

def afterTeaching (s : State) : State := onT (afterBegin s) endNormal

@[simp] theorem afterTeaching_course (s : State) :
    (afterTeaching s).course lesson.id = deliveredCourse (s.course lesson.id) := by
  simp [afterTeaching, afterBegin, afterNotices, afterStudentNotice, deliveredCourse, noticedCourse]

@[simp] theorem afterNotices_course (s : State) :
    (afterNotices s).course lesson.id = noticedCourse (s.course lesson.id) := by
  simp [afterNotices, afterStudentNotice, noticedCourse]

def noticeEvents : List SourceV14.Workflow.Event :=
  [.booking (.notify lesson studentNotice), .booking (.notify lesson tutorNotice)]

def teachingEvents : List SourceV14.Workflow.Event :=
  noticeEvents ++
    [.booking (.beginTeaching lesson startAt [place.student]), .booking (.endTeaching lesson endAt)]

private theorem bookingScope (ev : StartEvidence)
    (forms : ev.effectiveForms = [form]) (bookings : ev.bookings = [(form, booking)])
    (roster : ev.groupRoster = none) (dates : ev.scheduleHistory = [schedule]) :
    (∀ f, (f ∈ ev.effectiveForms ∨ ∃ b, (f, b) ∈ ev.bookings) → f.lesson = lesson) ∧
    (∀ r ∈ ev.groupRoster, r.lesson = lesson.id) ∧
    ∀ d ∈ ev.scheduleHistory, d.lesson = lesson.id := by
  refine ⟨?_, ?_, ?_⟩
  · intro f kept
    rcases kept with kept | ⟨b, kept⟩
    · have eq : f = form := by simpa [forms] using kept
      subst f
      rfl
    · have eq := List.mem_singleton.mp (bookings ▸ kept)
      exact congrArg (fun p : PartOne × BookingEvidence ↦ p.1.lesson) eq
  · simp [roster]
  · intro d kept
    have eq : d = schedule := by simpa [dates] using kept
    subst d
    rfl

private theorem localOnT (s : State) (event : SourceV14.Workflow.Booking.Event)
    (update : StartEvidence → StartEvidence) (id : event.lesson.id = lesson.id)
    (funds : event.fundingContext s.activeReserves)
    (keepsReserves : event.reservations s.activeReserves = s.activeReserves)
    (active : event.respectsCancellation s.cancelled)
    (places : event.usesEffectivePlaces (s.course event.lesson.id) s.cancelled)
    (rule : Booking.Step (s.course lesson.id) event (update (s.course lesson.id)))
    (price : BookingEntitlements.confirmationAllowed s.course s.verifiedContractualDiscount
      s.redress event none (update (s.course lesson.id)))
    (findings : event.usesRecordedAbsenceFindings s.review)
    (materials : event.securesPendingMaterials s)
    (receipts : event.readsFundingReceipts s.holds.payments) :
    Step s (.booking event) (onT s update) := by
  have valid : Booking.Step (s.course event.lesson.id) event (update (s.course lesson.id)) := by
    rw [id]
    exact rule
  have step := Step.booking funds active places valid price findings materials receipts
  simpa only [id, keepsReserves, BookingEntitlements.recordConfirmation, onT,
    State.withCourse] using step

private theorem noticeStudentStep (s : State) {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions) :
    Step s (.booking (.notify lesson studentNotice)) (afterStudentNotice s) := by
  refine localOnT s _ _ rfl trivial rfl trivial trivial ?_ rfl trivial trivial trivial
  refine ⟨bookingScope _ ?_ ?_ ?_ ?_, ⟨form, Or.inl ?_, rfl⟩, rfl, rfl⟩
  all_goals simp [ready, teachingInput, LessonFile.evidence, freshT]

private theorem noticeTutorStep (s : State) {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions) :
    Step (afterStudentNotice s) (.booking (.notify lesson tutorNotice)) (afterNotices s) := by
  refine localOnT _ _ _ rfl trivial rfl trivial trivial ?_ rfl trivial trivial trivial
  refine ⟨bookingScope _ ?_ ?_ ?_ ?_, ⟨form, Or.inl ?_, rfl⟩, rfl, rfl⟩
  all_goals simp [afterStudentNotice, addNotice, ready, teachingInput, LessonFile.evidence, freshT]

private theorem beginStep (s : State) {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions) :
    Step (afterNotices s) (.booking (.beginTeaching lesson startAt [place.student]))
      (afterBegin s) := by
  refine localOnT _ _ _ rfl trivial rfl trivial trivial ?_ rfl trivial trivial trivial
  refine ⟨bookingScope _ ?_ ?_ ?_ ?_, ⟨form, Or.inl ?_, rfl⟩, ?_, ?_, rfl⟩
  all_goals
    simp [afterNotices, afterStudentNotice, addNotice, ready, teachingInput, LessonFile.evidence, freshT]

private theorem endStep (s : State) {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions) :
    Step (afterBegin s) (.booking (.endTeaching lesson endAt)) (afterTeaching s) := by
  refine localOnT _ _ _ rfl trivial rfl trivial trivial ?_ rfl trivial trivial trivial
  refine ⟨bookingScope _ ?_ ?_ ?_ ?_, ⟨form, Or.inl ?_, rfl⟩, ?_, ⟨startAt, ?_, by decide⟩, rfl⟩
  all_goals
    simp [afterBegin, beginNormal, afterNotices, afterStudentNotice, addNotice, ready,
      teachingInput, LessonFile.evidence, freshT]

theorem noticePath (s : State) {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions) :
    DirectPath s noticeEvents (afterNotices s) :=
  .next (noticeStudentStep s ready) (.next (noticeTutorStep s ready) (.nil _))

theorem teachingPath (s : State) {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions) :
    DirectPath s teachingEvents (afterTeaching s) :=
  .next (noticeStudentStep s ready) <|
    .next (noticeTutorStep s ready) <|
    .next (beginStep s ready) <|
    .next (endStep s ready) <|
    .nil _

def normalTutorReport : TutorDeliveryReport :=
  ⟨lesson.id, lesson.tutor, lesson.coordinator, tick 34, true, "All agreed teaching completed"⟩

def normalStudentReport : StudentCompletionReport :=
  ⟨lesson.id, place.id, place.student, lesson.coordinator, tick 35⟩

private def addTutorReport (ev : StartEvidence) : StartEvidence :=
  { ev with afterLesson :=
    { ev.afterLesson with tutorReports := ev.afterLesson.tutorReports ++ [normalTutorReport] } }

private def addStudentReport (ev : StartEvidence) : StartEvidence :=
  { ev with afterLesson :=
    { ev.afterLesson with
      studentCompletions := ev.afterLesson.studentCompletions ++ [normalStudentReport] } }

private def addCoordinatorReport (ev : StartEvidence) : StartEvidence :=
  { ev with afterLesson :=
    { ev.afterLesson with
      coordinatorConfirmations :=
        ev.afterLesson.coordinatorConfirmations ++ [(lesson.coordinator, tick 36)] } }

def confirmedCourse (ev : StartEvidence) : StartEvidence :=
  addCoordinatorReport (addStudentReport (addTutorReport (deliveredCourse ev)))

private def afterTutorReport (s : State) : State := onT (afterTeaching s) addTutorReport
private def afterStudentReport (s : State) : State := onT (afterTutorReport s) addStudentReport

def afterCompletionReports (s : State) : State := onT (afterStudentReport s) addCoordinatorReport

@[simp] theorem afterCompletionReports_course (s : State) :
    (afterCompletionReports s).course lesson.id = confirmedCourse (s.course lesson.id) := by
  simp [afterCompletionReports, afterStudentReport, afterTutorReport, confirmedCourse]

private theorem noReplacement (ev : StartEvidence) (empty : ev.tutorReplacements = [])
    (query : Moment) : ev.effectiveReplacement lesson query none := by
  simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement, empty]

private theorem reported (ev : StartEvidence) (began : ev.teachingBegan = some startAt)
    (ended : ev.teachingEnded = some endAt) {point query : Moment}
    (after : endAt.by point) (visible : point.by query) : ev.reportedAfterLesson point query :=
  ⟨startAt, endAt, began, ended, by decide, after, visible⟩

private theorem tutorReportConforms (ev : StartEvidence)
    (member : normalTutorReport ∈ ev.afterLesson.tutorReports)
    (began : ev.teachingBegan = some startAt) (ended : ev.teachingEnded = some endAt)
    (replacements : ev.tutorReplacements = []) (query : Moment)
    (visible : normalTutorReport.point.by query) :
    TutorDeliveryRecorded ev lesson query normalTutorReport :=
  ⟨member, rfl, ⟨startAt, began, none, noReplacement ev replacements startAt, rfl⟩, rfl,
    by decide, reported ev began ended (by decide) visible⟩

private theorem studentReportConforms (ev : StartEvidence)
    (member : normalStudentReport ∈ ev.afterLesson.studentCompletions)
    (began : ev.teachingBegan = some startAt) (ended : ev.teachingEnded = some endAt)
    (query : Moment) (visible : normalStudentReport.point.by query) :
    StudentCompletionRecorded ev form query normalStudentReport :=
  ⟨member, rfl, rfl, rfl, rfl, reported ev began ended (by decide) visible⟩

private theorem tutorReportStep (s : State) {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions) :
    Step (afterTeaching s) (.booking (.tutorReport lesson normalTutorReport))
      (afterTutorReport s) := by
  refine localOnT _ _ _ rfl trivial rfl trivial trivial ?_ rfl trivial trivial trivial
  refine ⟨bookingScope _ ?_ ?_ ?_ ?_, ⟨form, Or.inl ?_, rfl⟩,
    tutorReportConforms _ ?_ ?_ ?_ ?_ _ (by decide), rfl⟩
  all_goals
    simp [deliveredCourse, endNormal, beginNormal, noticedCourse, addNotice, ready,
      teachingInput, LessonFile.evidence, freshT]

private theorem studentReportStep (s : State) {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions) :
    Step (afterTutorReport s) (.booking (.studentCompletion form normalStudentReport))
      (afterStudentReport s) := by
  refine localOnT _ _ _ rfl trivial rfl trivial trivial ?_ rfl trivial trivial trivial
  refine ⟨bookingScope _ ?_ ?_ ?_ ?_, Or.inl ?_,
    studentReportConforms _ ?_ ?_ ?_ _ (by decide), rfl⟩
  all_goals
    simp [afterTutorReport, addTutorReport, deliveredCourse, endNormal,
      beginNormal, noticedCourse, addNotice, ready, teachingInput, LessonFile.evidence, freshT]

private theorem coordinatorReportStep (s : State) {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions) :
    Step (afterStudentReport s) (.booking (.coordinatorCompletion lesson lesson.coordinator
      (tick 36))) (afterCompletionReports s) := by
  refine localOnT _ _ _ rfl trivial rfl trivial trivial ?_ rfl trivial trivial trivial
  refine ⟨bookingScope _ ?_ ?_ ?_ ?_, ⟨form, Or.inl ?_, rfl⟩, rfl,
    reported _ ?_ ?_ (by decide : endAt.by (tick 36)) (by decide), rfl⟩
  all_goals
    simp [afterStudentReport, afterTutorReport, addTutorReport, addStudentReport, deliveredCourse,
      endNormal, beginNormal, noticedCourse, addNotice, ready, teachingInput, LessonFile.evidence,
      freshT]

def bookedCredit (payments : PaymentHistory) (authorities : ReviewAuthorities) : CreditBook :=
  { initialCredit payments authorities with ledger := [topUpPosting, debit] }

private theorem bookedRoster {ev : StartEvidence} {atTime : Moment}
    (forms : ev.effectiveForms = [form]) (roster : ev.groupRoster = none) :
    ev.rosterFormsAt lesson atTime none [form] := by
  refine ⟨?_, forms.symm⟩
  simp [StartEvidence.rosterMatchesForms, StartEvidence.formsMatch,
    show lesson.kind = .oneToOne by rfl, forms, roster, formMatches,
    show form.lesson = lesson by rfl]

private theorem bookedSchedule {ev : StartEvidence}
    (retained : ev.scheduleHistory = [schedule]) (forms : ev.effectiveForms = [form])
    (roster : ev.groupRoster = none) :
    EffectiveSchedule lesson ev schedule startAt := by
  refine ⟨rfl, ?_, by simp [retained, schedule, lesson], ?_⟩
  · simp only [Schedule.effectiveAtQuery, retained, List.mem_singleton, forall_eq]
    exact ⟨trivial, formMatches.2.2.2.2.2.1, by decide, fun _ _ _ ↦ by decide⟩
  · intro old member _ _
    cases List.mem_singleton.mp (retained ▸ member)
    refine ⟨rfl, formMatches.2.2.2.2.2.1, Or.inl ⟨rfl, (bookedRoster
      (atTime := startAt) forms roster).1, ?_⟩⟩
    intro f present
    cases List.mem_singleton.mp (forms ▸ present)
    rfl

private theorem normalPriceAt (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (query : Moment) :
    (initialCredit payments authorities).creditRecords.lessonFees.feeAt form query 4 := by
  left
  exact ⟨by simp [initialCredit], rfl⟩

private theorem preparedCanStart (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (decisions : DecisionRecords) (distinct : payments.distinctReceipts) (began ended : Option Moment)
    (afterBooking : ∀ time, began = some time → (tick 31).before time) :
    CanStart lesson
      { noticedCourse (teachingInput (bookedCredit payments authorities) decisions) with
        teachingBegan := began, teachingEnded := ended, studentsTakingLesson := [place.student] }
      schedule startAt := by
  have confirmation := canConfirm payments authorities distinct began afterBooking
  have roster := bookedRoster (atTime := startAt)
    (ev := { noticedCourse (teachingInput (bookedCredit payments authorities) decisions) with
      teachingBegan := began, teachingEnded := ended, studentsTakingLesson := [place.student] })
    rfl rfl
  refine ⟨bookedSchedule rfl rfl rfl, by decide, none, [form], none, roster, ?_, ?_,
    ?_, ?_, noReplacement _ rfl _, ?_⟩
  · simp
  · exact validCredit payments authorities distinct _
  · intro student member
    cases List.mem_singleton.mp member
    exact ⟨form, by simp, rfl⟩
  · intro impossible
    cases impossible
  · dsimp only
    intro f present
    cases List.mem_singleton.mp present
    refine ⟨by decide, ⟨booking, none, by simp [teachingInput, noticedCourse, addNotice],
      ?_, confirmation, ⟨none, noReplacement _ rfl _, rfl, rfl⟩⟩, ?_, ?_, ?_, ?_⟩
    · simp [StartEvidence.readsBookedRoster, teachingInput, noticedCourse, addNotice,
        LessonFile.evidence, freshT]
    · refine ⟨4, normalPriceAt _ _ _, Or.inr ?_⟩
      change (0 : Amount) < 4 ∧ 4 ≤ debitTotal form.place [topUpPosting, debit] startAt -
        creditsRestoredFor form.place [topUpPosting, debit] startAt
      decide +kernel
    · refine ⟨studentNotice, ?_, ⟨rfl, rfl, rfl⟩, ⟨rfl, Or.inr rfl⟩, by decide⟩
      change studentNotice ∈ [studentNotice, tutorNotice]
      simp
    · refine ⟨tutorNotice, ?_, rfl, rfl, by decide, ?_, by decide, Or.inl rfl⟩
      · change tutorNotice ∈ [studentNotice, tutorNotice]
        simp
      · intro channel same
        cases same
        rfl
    · simp

/-- The actual notices and booking support start permission before any delivery event. -/
theorem noticeStartPermitted (s : State) {decisions : DecisionRecords}
    {payments : PaymentHistory} {authorities : ReviewAuthorities}
    (ready : s.course lesson.id = teachingInput s.credit decisions)
    (credit : s.credit = bookedCredit payments authorities) (distinct : payments.distinctReceipts)
    (cancelled : s.cancelled = []) :
    (afterNotices s).startPermitted lesson schedule startAt [place.student] := by
  refine ⟨?_, ?_⟩
  · unfold SourceV14.Workflow.Booking.StartPermitted
    rw [afterNotices_course, ready, credit]
    exact preparedCanStart payments authorities decisions distinct none none (by simp)
  · change Cancellation.CompatibleWithStart s.cancelled
      ((afterNotices s).course lesson.id) lesson startAt [place.student]
    rw [cancelled, afterNotices_course, ready]
    refine ⟨none, [form], bookedRoster rfl rfl, ?_⟩
    simp [lesson, Cancellation.PlaceCancelledAt]

/-- Ordinary settlement can read the same permission with the actual teaching interval retained. -/
theorem taughtCanStart (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (decisions : DecisionRecords) (distinct : payments.distinctReceipts) :
    CanStart lesson (deliveredCourse (teachingInput (bookedCredit payments authorities) decisions))
      schedule startAt :=
  preparedCanStart payments authorities decisions distinct (some startAt) (some endAt) (by
    intro time eq
    cases Option.some.inj eq
    decide)

private def normalInterest : DirectInterest := ⟨false, false, false, false⟩

private def normalAuthority : ReviewAuthorities where
  corePartner := fun _ _ ↦ False
  initialFinding := fun _ _ _ ↦ False
  reviewer := fun _ _ _ ↦ False
  approvesPayment := fun _ _ _ ↦ False
  interest := fun _ _ _ ↦ normalInterest
  originalDecisionMaker := fun _ ↦ some lesson.coordinator
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

private def normalReviewTerms : ReviewTerms :=
  ⟨lesson.coordinator, form.contacts.alternativeContact, form.contacts.leadAcademicTutor,
    tick 70, form.deadlines.finalReview, form.deadlines.temporaryHoldExpiry,
    form.deadlines.reviewerHandoff, form.contacts.escalationContact⟩

private def normalHoldFacts : HoldFacts where
  terms := fun _ ↦ normalReviewTerms
  termsApply := fun _ ↦ True
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

private def normalHandler : Handler := ⟨lesson.coordinator, false, normalInterest⟩

private def normalAssignment : SettlementAssignment :=
  ⟨⟨1200, lesson.id, [lesson.provider, lesson.tutor, place.customer, place.student]⟩,
    1201, normalAuthority, none, none, fun seat ↦ seat = place.id⟩

private def normalFeeFacts (decisions : DecisionRecords) : PlaceFeeFacts :=
  ⟨[], [], fun _ _ _ ↦ False, none, decisions, []⟩

def normalAmounts : LessonSettlement :=
  ⟨lesson.id, place.id, 4, 4, 0, 0, 2, 0⟩

def normalFee (decisions : DecisionRecords) : Workflow.Settlement.AdoptedFee :=
  ⟨1202, ⟨form, schedule, startAt, tick (32 + thirtyDays), tick 37, normalHandler,
    normalAssignment, normalHoldFacts,
    .ordinaryOneToOne true true true true
      (normalTutorReport.completed = true ∧ normalTutorReport.details = "All agreed teaching completed")
      (normalFeeFacts decisions),
    normalAmounts⟩⟩

def normalTutorRow : TutorLessonRecord := ⟨lesson, some endAt, true, 2⟩

def normalCompletion : Workflow.Settlement.TutorCompletion :=
  ⟨form, normalTutorRow, startAt, tick 38, ⟨form.tutorAgreementRef, 2, paymentTerms⟩,
    fun f terms amount ↦ f = form ∧ amount = terms.normalFee⟩

private def normalTutorBasis : TutorSettlementBasis where
  paymentsByPlace := [normalAmounts]
  hadTutorPayUnderTerms := fun terms row ↦ row.tutorPay = terms.normalFee
  nowIndependentlyPayable := fun _ ↦ False
  tutorPartsForPlace := fun _ ↦ []
  absenceWithoutTeaching := none
  agreedNetPortion := fun _ ↦ none
  operativeSettlement := fun seat atTime ↦
    if seat = place.id ∧ (tick 37).by atTime then some (normalAmounts, tick 37) else none
  confirmedDebts := fun _ _ ↦ []
  separateDebtReferences := []

def normalDue : Workflow.Settlement.TutorDue where
  form := form
  roster := none
  forms := [form]
  schedule := schedule
  startedAt := startAt
  settledAt := tick 39
  next := normalTutorRow
  completionHistory := [normalTutorRow]
  faultDecisions := []
  faults := []
  deductions := []
  agreement := ⟨lesson.id, lesson.tutor, form.tutorAgreementRef, none, none, none, none⟩
  terms := paymentTerms
  basis := normalTutorBasis
  handler := normalHandler
  assignment := normalAssignment
  holdFacts := normalHoldFacts
  agreedFee := 2
  net := 2
  separatePart := none

private def afterNormalFee (s : State) (decisions : DecisionRecords) : State :=
  { afterCompletionReports s with
    settlement := { s.settlement with fees := s.settlement.fees ++ [normalFee decisions] } }

private def afterVerifiedTutor (s : State) (decisions : DecisionRecords) : State :=
  let prior := afterNormalFee s decisions
  { prior with settlement := { prior.settlement with
    tutorCompletions := prior.settlement.tutorCompletions ++ [normalCompletion] } }

def normalFinal (s : State) (decisions : DecisionRecords) : State :=
  let prior := afterVerifiedTutor s decisions
  { prior with settlement := { prior.settlement with
    tutors := prior.settlement.tutors ++ [normalDue] } }

def normalContinuationEvents (decisions : DecisionRecords) : List SourceV14.Workflow.Event :=
  [.booking (.tutorReport lesson normalTutorReport),
    .booking (.studentCompletion form normalStudentReport),
    .booking (.coordinatorCompletion lesson lesson.coordinator (tick 36)),
    .settlement (.assessFee (normalFee decisions)), .settlement (.verifyTutorCompletion normalCompletion),
    .settlement (.assessTutor normalDue)]

def normalEvents (decisions : DecisionRecords) : List SourceV14.Workflow.Event :=
  teachingEvents ++ normalContinuationEvents decisions

/-- The common trace begins this branch with no cancellation or settlement case, no tutor
fault or debt, and no hold on either determination. It can retain other lessons' reserves. -/
structure NormalSettlementInput (s : State) (payments : PaymentHistory)
    (authorities : ReviewAuthorities) : Prop where
  credit : s.credit = bookedCredit payments authorities
  distinct : payments.distinctReceipts
  cancelled : s.cancelled = []
  formal : s.holds.formal = []
  temporary : s.holds.temporary = []
  settlement : s.settlement = {}
  review : s.review = Review.History.empty
  redress : s.redress = {}
  debts : s.debts = {}
  tutorFaults : s.tutorFaults = TutorFaultHistory.History.empty

private theorem effectiveNormalAgreement {ev : StartEvidence} {credit : CreditBook}
    {decisions : DecisionRecords} (shape : ev = confirmedCourse (teachingInput credit decisions))
    (query : Moment) (started : startAt.by query) (confirmed : form.confirmedAt.by query) :
    EffectiveTutorAgreementAt form ev startAt lesson.tutor form.tutorAgreementRef 2 paymentTerms
      query query := by
  rw [shape]
  refine ⟨formMatches, started, Or.inr rfl, Or.inl (by simp [confirmedCourse,
    addCoordinatorReport, addStudentReport, addTutorReport, deliveredCourse, endNormal, beginNormal,
    noticedCourse, addNotice, teachingInput]), none, noReplacement _ rfl _, ?_⟩
  change lesson.tutor = form.lesson.tutor ∧
    (if form.agreedTutor ≠ lesson.tutor ∨ form.agreedTutorFee ≠ form.lesson.normalTutorFee
      then False else form.confirmedAt.by query ∧
        (⟨form.tutorAgreementRef, 2, paymentTerms⟩ : TutorPayTerms) =
          ⟨form.tutorAgreementRef, form.lesson.normalTutorFee, form.deadlines.tutorPay⟩)
  simp [PartOne.agreedTutor, PartOne.agreedTutorFee, form, lesson] at confirmed ⊢
  exact confirmed

private theorem normalAssignee (query : Moment) :
    normalAssignment.authorised form normalHandler query := by
  simp [SettlementAssignment.authorised, normalAssignment, normalHandler, normalAuthority,
    Handler.maySettle, ReviewAuthorities.disinterested, DirectInterest.affected, normalInterest,
    form]

private theorem noNormalHold (holds : HoldHistory) (formal : holds.formal = [])
    (point : Moment) :
    holds.mayCarryOutDecision normalAuthority normalHoldFacts normalAssignment.matter
      normalAssignment.decision point := by
  simp [HoldHistory.mayCarryOutDecision, HoldHistory.distinctFormalDecisions,
    HoldHistory.decisionOnFormalHold, HoldHistory.validFormalHold, formal]

private theorem normalLedgerMatch :
    normalAmounts.matchesPaymentHistory place [topUpPosting, debit] (tick 37) := by
  unfold LessonSettlement.matchesPaymentHistory
  decide +kernel

private theorem reportsForFee (credit : CreditBook) (decisions : DecisionRecords) :
    OneToOneReportsMatch (confirmedCourse (teachingInput credit decisions)) lesson
      (tick 37) true true true := by
  refine ⟨⟨fun _ ↦ ?_, fun _ ↦ rfl⟩, ⟨fun _ ↦ ?_, fun _ ↦ rfl⟩,
    ⟨fun _ ↦ ?_, fun _ ↦ rfl⟩⟩
  · refine ⟨form, List.mem_cons_self, rfl, normalStudentReport, ?_⟩
    exact studentReportConforms _ List.mem_cons_self rfl rfl _ (by decide)
  · refine ⟨normalTutorReport, ?_, rfl⟩
    exact tutorReportConforms _ List.mem_cons_self rfl rfl rfl _ (by decide)
  · exact ⟨(lesson.coordinator, tick 36), List.mem_cons_self, rfl,
      reported _ rfl rfl (by decide) (by decide)⟩

private theorem normalChargeAllowed (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (decisions : DecisionRecords) (holds : HoldHistory) (distinct : payments.distinctReceipts)
    (faults : decisions.faultOutcomes = []) (formal : holds.formal = [])
    (temporary : holds.temporary = []) :
    (normalFee decisions).decision.allowed
      (confirmedCourse (teachingInput (bookedCredit payments authorities) decisions)) holds := by
  have canStart :
      CanStart lesson (confirmedCourse (teachingInput (bookedCredit payments authorities) decisions))
        schedule startAt := taughtCanStart payments authorities decisions distinct
  have reports := reportsForFee (bookedCredit payments authorities) decisions
  have usual : OneToOneUsual lesson
      (CanStart lesson (confirmedCourse (teachingInput (bookedCredit payments authorities) decisions))
        schedule startAt) true true true := ⟨rfl, canStart, rfl, rfl, rfl⟩
  refine ⟨List.mem_cons_self, normalAssignee _, ?_, noNormalHold holds formal _,
    ⟨(normalAssignee (tick 37)).2.2.1, reports,
      Or.inl ⟨rfl, (show startAt.by (tick 37) by decide), reports, usual⟩⟩,
    canStart, ⟨rfl, rfl⟩, ?_, ?_,
    normalLedgerMatch, normalPriceAt payments authorities _⟩
  · change FeeHoldTermsMatch form normalHoldFacts
    simp [FeeHoldTermsMatch, HoldFacts.matchesForm, normalHoldFacts]
  · simp [normalFeeFacts, PlaceFeeFacts.exceptionApplies, faults, confirmedCourse,
      addCoordinatorReport, addStudentReport, addTutorReport, deliveredCourse, endNormal,
      beginNormal, noticedCourse, addNotice, teachingInput, LessonFile.evidence, freshT]
  · simp [FeeOnHold, HoldHistory.paymentOnHold, HoldHistory.formalInForce,
      HoldHistory.validFormalHold, HoldHistory.temporaryInForce, formal, temporary]

private theorem normalFeeStep (s : State) {payments : PaymentHistory}
    {authorities : ReviewAuthorities} {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions)
    (input : NormalSettlementInput s payments authorities) (faults : decisions.faultOutcomes = []) :
    Step (afterCompletionReports s) (.settlement (.assessFee (normalFee decisions)))
      (afterNormalFee s decisions) := by
  refine Step.settlement ?_ trivial trivial trivial trivial trivial
    (Workflow.Settlement.Step.assessFee ?_ ?_ trivial)
  · change ¬ Cancellation.PlaceCancelledAt s.cancelled place (tick 37)
    simp [input.cancelled, Cancellation.PlaceCancelledAt]
  · change (normalFee decisions).decision.allowed ((afterCompletionReports s).course lesson.id) s.holds
    rw [afterCompletionReports_course, ready, input.credit]
    exact normalChargeAllowed payments authorities decisions s.holds input.distinct faults
      input.formal input.temporary
  · change ∀ old ∈ s.settlement.fees, old.reference ≠ (normalFee decisions).reference
    simp [input.settlement]

private theorem normalCompletionConforms (credit : CreditBook) (decisions : DecisionRecords) :
    normalCompletion.conforms (confirmedCourse (teachingInput credit decisions)) := by
  refine ⟨rfl, ⟨none, [form], bookedRoster rfl rfl, List.mem_cons_self⟩,
    effectiveNormalAgreement rfl _ (by decide) (by decide), ⟨rfl, rfl⟩,
    rfl, rfl, rfl, normalTutorReport, ?_, rfl, rfl⟩
  exact tutorReportConforms _ List.mem_cons_self rfl rfl rfl _ (by decide)

private theorem verifyNormalStep (s : State) {payments : PaymentHistory}
    {authorities : ReviewAuthorities} {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions)
    (input : NormalSettlementInput s payments authorities) :
    Step (afterNormalFee s decisions) (.settlement (.verifyTutorCompletion normalCompletion))
      (afterVerifiedTutor s decisions) := by
  let prior := afterNormalFee s decisions
  let event := Workflow.Settlement.Event.verifyTutorCompletion normalCompletion
  have courseEq : prior.course event.lesson =
      confirmedCourse (teachingInput s.credit decisions) := calc
    _ = (afterCompletionReports s).course lesson.id := by
      rw [show event.lesson = lesson.id by rfl]
      simp only [prior, afterNormalFee, State.course]
    _ = confirmedCourse (s.course lesson.id) := afterCompletionReports_course s
    _ = _ := congrArg confirmedCourse ready
  have check : normalCompletion.conforms (prior.course event.lesson) :=
    Eq.mpr (congrArg normalCompletion.conforms courseEq)
      (normalCompletionConforms s.credit decisions)
  have fresh : ∀ old ∈ prior.settlement.tutorCompletions,
      old.occurrenceKey ≠ normalCompletion.occurrenceKey := by
    change ∀ old ∈ s.settlement.tutorCompletions, old.occurrenceKey ≠ normalCompletion.occurrenceKey
    simp [input.settlement]
  have faults : TutorFaultHistory.settlementUses prior.course prior.review prior.tutorFaults
      prior.settlement prior.verifiedTutorReview event := by
    change ∀ correction ∈ s.review.corrections, _
    simp [input.review, Review.History.empty]
  exact Step.settlement (s := prior) (event := event) trivial trivial faults trivial trivial trivial
    (Workflow.Settlement.Step.verifyTutorCompletion check fresh)

private def normalCompletionHistory (decisions : DecisionRecords) : Workflow.Settlement.History :=
  { fees := [normalFee decisions], tutorCompletions := [normalCompletion] }

private theorem afterVerifiedHistory (s : State) (decisions : DecisionRecords)
    (initial : s.settlement = {}) :
    (afterVerifiedTutor s decisions).settlement = normalCompletionHistory decisions := by
  simp [afterVerifiedTutor, afterNormalFee, initial, normalCompletionHistory]

private theorem normalDueEstablished (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (decisions : DecisionRecords) (holds : HoldHistory) (formal : holds.formal = []) :
    normalDue.established
      (confirmedCourse (teachingInput (bookedCredit payments authorities) decisions))
      holds (normalCompletionHistory decisions) := by
  refine ⟨List.mem_cons_self, bookedRoster rfl rfl, ?_, normalAssignee _,
    noNormalHold holds formal _, rfl, List.mem_cons_self, rfl,
    ⟨bookedSchedule rfl rfl rfl, (show startAt.by (tick 39) by decide), Or.inl rfl⟩,
    ?_, rfl, effectiveNormalAgreement rfl _ (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change normalHoldFacts.groupSettlementScopeMatches lesson [place]
    simp [HoldFacts.groupSettlementScopeMatches, normalHoldFacts, lesson]
  · intro impossible
    cases impossible
  · change normalTutorBasis.debtsReferenced lesson lesson.tutor (tick 39)
    simp [TutorSettlementBasis.debtsReferenced, ConfirmedTutorDebtsReferenced, normalTutorBasis]
  · simp [normalDue]
  · simp [normalDue]
  · intro row mem
    cases List.mem_singleton.mp mem
    exact ⟨tick 37, rfl, normalFee decisions, List.mem_cons_self, rfl, rfl, rfl, rfl,
      (show (tick 37).by (tick 39) by decide), trivial⟩
  · change normalTutorBasis.totals form
      (confirmedCourse (teachingInput (bookedCredit payments authorities) decisions))
      (tick 39) [form] ⟨form.tutorAgreementRef, 2, paymentTerms⟩ 2
    refine ⟨by simp [normalTutorBasis], by simp [normalTutorBasis], ?_, by decide +kernel⟩
    intro row mem
    cases List.mem_singleton.mp mem
    exact ⟨form, List.mem_cons_self, rfl, rfl, rfl,
      ⟨tick 37, rfl, by decide, normalLedgerMatch⟩, by decide⟩
  · refine ⟨by simp [normalDue, form, lesson], ?_, ?_⟩
    · intro f member
      cases List.mem_singleton.mp member
      exact ⟨normalAmounts, List.mem_cons_self, rfl⟩
    · change TutorAmountsForSettlement [normalTutorRow] normalTutorRow [] [] 2 2
      refine ⟨rfl, Or.inr ⟨by simp, ?_⟩⟩
      simp [nextTutorDeductionsSettled, normalTutorRow, sumAmounts] <;> decide +kernel

private theorem normalDueFaults (s : State) (decisions : DecisionRecords)
    (saved : s.settlement = normalCompletionHistory decisions) (review : s.review = Review.History.empty)
    (faults : s.tutorFaults = TutorFaultHistory.History.empty) :
    TutorFaultHistory.settlementUses s.course s.review s.tutorFaults s.settlement
      s.verifiedTutorReview (.assessTutor normalDue) := by
  rw [saved, review, faults]
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · change ∀ correction ∈ Review.History.empty.corrections, _
    simp [Review.History.empty]
  · simp [TutorFaultHistory.History.reviewFaultsRecordedAt, Review.History.empty]
  · simp [TutorFaultHistory.History.initialFaultsRecordedAt, Review.History.empty]
  · simp [TutorFaultHistory.History.operativeAt, TutorFaultHistory.History.empty]
  · simp [TutorFaultHistory.History.reads, TutorFaultHistory.Entry.applies,
      TutorFaultHistory.History.operativeAt, TutorFaultHistory.History.empty, normalDue]
  · simp [TutorFaultHistory.deductionsUsedOnce, normalDue]

private theorem assessNormalTutorStep (s : State) {payments : PaymentHistory}
    {authorities : ReviewAuthorities} {decisions : DecisionRecords}
    (ready : s.course lesson.id = teachingInput s.credit decisions)
    (input : NormalSettlementInput s payments authorities) :
    Step (afterVerifiedTutor s decisions) (.settlement (.assessTutor normalDue))
      (normalFinal s decisions) := by
  let prior := afterVerifiedTutor s decisions
  let event := Workflow.Settlement.Event.assessTutor normalDue
  have courseEq : prior.course event.lesson =
      confirmedCourse (teachingInput (bookedCredit payments authorities) decisions) := calc
    _ = (afterCompletionReports s).course lesson.id := by
      rw [show event.lesson = lesson.id by rfl]
      simp only [prior, afterVerifiedTutor, afterNormalFee, State.course]
    _ = confirmedCourse (s.course lesson.id) := afterCompletionReports_course s
    _ = confirmedCourse (teachingInput s.credit decisions) := congrArg confirmedCourse ready
    _ = _ := congrArg (fun credit ↦ confirmedCourse (teachingInput credit decisions)) input.credit
  have historyEq : prior.settlement = normalCompletionHistory decisions :=
    afterVerifiedHistory s decisions input.settlement
  have check : normalDue.established (prior.course event.lesson) prior.holds prior.settlement := by
    rw [courseEq, historyEq]
    exact normalDueEstablished payments authorities decisions s.holds input.formal
  have debts : event.readsConfirmedDebts prior.debts := by
    change event.readsConfirmedDebts s.debts
    simp [event, Workflow.Settlement.Event.readsConfirmedDebts, input.debts,
      normalDue, normalTutorBasis, Debt.History.confirmed]
  have retained : TutorFaultHistory.retainedRedressUses prior.course prior.tutorFaults
      prior.redress event := by
    change TutorFaultHistory.retainedRedressUses prior.course s.tutorFaults s.redress event
    simp [event, TutorFaultHistory.retainedRedressUses, TutorFaultHistory.redressRecordedAt,
      input.redress]
  have absence : event.usesCurrentAbsence prior := by
    simp [event, Workflow.Settlement.Event.usesCurrentAbsence, normalDue, normalTutorBasis]
  exact Step.settlement (s := prior) (event := event) trivial debts
    (normalDueFaults prior decisions historyEq input.review input.tutorFaults) retained
    trivial absence (Workflow.Settlement.Step.assessTutor check)

theorem normalContinuationPath (s : State) {decisions : DecisionRecords}
    {payments : PaymentHistory} {authorities : ReviewAuthorities}
    (ready : s.course lesson.id = teachingInput s.credit decisions)
    (input : NormalSettlementInput s payments authorities) (faults : decisions.faultOutcomes = []) :
    DirectPath (afterTeaching s) (normalContinuationEvents decisions) (normalFinal s decisions) :=
  .next (tutorReportStep s ready) <|
    .next (studentReportStep s ready) <|
    .next (coordinatorReportStep s ready) <|
    .next (normalFeeStep s ready input faults) <|
    .next (verifyNormalStep s ready input) <|
    .next (assessNormalTutorStep s ready input) <|
    .nil _

private theorem appendPath {s m t : State} {first next : List SourceV14.Workflow.Event}
    (pre : DirectPath s first m) (post : DirectPath m next t) :
    DirectPath s (first ++ next) t := by
  induction pre with
  | nil _ => exact post
  | next head _ ih => exact .next head (ih post)

theorem normalPath (s : State) {decisions : DecisionRecords}
    {payments : PaymentHistory} {authorities : ReviewAuthorities}
    (ready : s.course lesson.id = teachingInput s.credit decisions)
    (input : NormalSettlementInput s payments authorities) (faults : decisions.faultOutcomes = []) :
    DirectPath s (normalEvents decisions) (normalFinal s decisions) :=
  appendPath (teachingPath s ready) (normalContinuationPath s ready input faults)

theorem normalRecords (s : State) (decisions : DecisionRecords) (initial : s.settlement = {}) :
    (normalFinal s decisions).settlement.fees = [normalFee decisions] ∧
    (normalFinal s decisions).settlement.tutorCompletions = [normalCompletion] ∧
    (normalFinal s decisions).settlement.tutors = [normalDue] ∧
    (normalFinal s decisions).settlement.tutorPayments = [] := by
  simp [normalFinal, afterVerifiedHistory s decisions initial, normalCompletionHistory]

theorem normalAmountsAtCheckpoint :
    (∀ decisions, (normalFee decisions).decision.amounts.feePayable = 4 ∧
      (normalFee decisions).decision.amounts.debited = 4 ∧
      (normalFee decisions).decision.decidedAt.by (tick 45)) ∧
    normalCompletion.row.completedAt = some endAt ∧
    normalCompletion.verifiedAt.by (tick 45) ∧ normalDue.net = 2 ∧
    normalDue.settledAt.by (tick 45) := by
  exact ⟨fun _ ↦ ⟨rfl, rfl, (show (tick 37).by (tick 45) by decide)⟩, rfl,
    (show (tick 38).by (tick 45) by decide), rfl, (show (tick 39).by (tick 45) by decide)⟩

#print axioms noticePath
#print axioms noticeStartPermitted
#print axioms teachingPath
#print axioms taughtCanStart
#print axioms normalPath
#print axioms normalRecords
#print axioms normalAmountsAtCheckpoint

end JointT
