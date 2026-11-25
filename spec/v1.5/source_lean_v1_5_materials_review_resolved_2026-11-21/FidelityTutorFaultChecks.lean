import SourceV14.Workflow

namespace SourceV14.Workflow.TutorFaultChecks

open SourceV14.Booking SourceV14.Settlement Confirmation Course CreditEvidence Operations

private def tick (second : Nat) : Moment := ⟨second, 0⟩

private def lesson (id : LessonId) (tutor : ActorId) (fee : Amount) : Lesson :=
  ⟨id, .oneToOne, 1, tutor, 3, fee⟩

private def paymentTerms : PaymentTerms := ⟨.fixed (tick 100), .fixed (tick 101)⟩

private def signedForm (l : Lesson) (start : Nat) : PartOne where
  lesson := l
  place := ⟨8, l.id, 4, 5, 5, 6, 100, 100⟩
  contacts := ⟨"Spark", "provider", "student", none, "coordinator", 7, "lead",
    none, none, 9, "reviewer", 10, "alternative", true, 11, "escalation"⟩
  rulesVersion := "1.5"
  confirmedAt := tick 3
  customerRepresentatives := []
  schedule := ⟨l.id, tick start, tick (start + 1), "UTC", tick 1, tick 2⟩
  serviceTerms := "agreed teaching"
  serviceItems := [1]
  discountBasis := none
  privateRoster := none
  rosterLock := none
  groupRescheduleCutoff := none
  oneToOneAdvanceCutoff := some (.fixed (tick 4))
  cancelChangeTerms := "change terms"
  noFaultTerms := "no-fault terms"
  applicableStartTerms := "start terms"
  tutorAgreementRef := "signed agreement"
  absentGroupPlacePay := none
  materialsOrBundle := none
  materialsTermsRef := none
  materialsPayer := none
  deadlines := ⟨.fixed (tick 55), tick 60, none, paymentTerms, paymentTerms, paymentTerms,
    paymentTerms, .fixed (tick 70), tick 72, tick 65, tick 66, .fixed (tick 102)⟩

private def original := signedForm (lesson 17 2 80) 10
private def middle := signedForm (lesson 18 2 90) 20
private def later := signedForm (lesson 19 2 100) 29

private def authority : ReviewAuthorities where
  corePartner := fun _ _ ↦ False
  initialFinding := fun case actor _ ↦ case.lesson = 17 ∧ actor = 7
  reviewer := fun case actor _ ↦ case.lesson = 17 ∧ actor = 9
  approvesPayment := fun _ _ _ ↦ False
  interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
  originalDecisionMaker := fun _ ↦ some 7
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

private def reported : TutorFaultFinding :=
  ⟨17, 2, True, True, True, .missedAgreedService "Teaching" True, .entireClass⟩

private def fault : TutorFaultCase := ⟨original.lesson, tick 10, reported⟩

private def matter : ReviewMatter := ⟨41, 17, [2, 4, 5]⟩
private def initial : InitialFinding := ⟨matter, .fault, 7, tick 15, "Tutor did not attend", []⟩
private def outcome : RecordedSettlementOutcome := ⟨matter, 50, 7, tick 15⟩
private def originalRecord : Review.OriginalRecord := ⟨outcome, none⟩

private def decision : FaultDecisionRecord :=
  ⟨.initial initial, original.place.id, .fault (.tutor reported ⟨False, False, False⟩)⟩

private def decisions : DecisionRecords where
  authorities := authority
  terms := ⟨3, 10, 7, .exact (tick 70), tick 72, tick 65, tick 66, 11⟩
  appointments := []
  initialFindings := [initial]
  faultOutcomes := [decision]
  faultMatterCovers := fun case place ↦ case = matter ∧ place = original.place.id
  wasResponsibleTutor := fun l f ↦ l.id = f.lesson ∧ l.tutor = f.tutor
  originalAttendanceTime := fun _ _ _ ↦ False

private def reviews : Review.History :=
  { Review.History.empty with initialFindings := [initial], originals := [originalRecord] }

private def noTeaching (f : PartOne) : StartEvidence where
  effectiveForms := [f]
  groupRoster := none
  bookings := []
  scheduleHistory := [f.schedule]
  changes := []
  openingCredit := fun _ ↦ 0
  creditRecords := ⟨[], [], [], [], fun _ _ ↦ False, fun _ _ ↦ False, [],
    ⟨[], [], []⟩, authority, {}⟩
  ledger := []
  discounts := []
  notices := []
  academicTeamAt := fun _ _ _ ↦ False
  teachingBegan := none
  teachingEnded := none
  studentsTakingLesson := []
  afterLesson := ⟨[], [], [], [], [], []⟩
  studentFaults := ⟨[], decisions, fun _ ↦ False⟩

private def delivery (f : PartOne) (reportAt : Nat) : TutorDeliveryReport :=
  ⟨f.lesson.id, f.lesson.tutor, f.lesson.coordinator, tick reportAt, true, "Completed teaching"⟩

private def taught (f : PartOne) (endedAt reportAt : Nat) : StartEvidence :=
  { (noTeaching f) with
    teachingBegan := some f.schedule.start
    teachingEnded := some (tick endedAt)
    afterLesson := { (noTeaching f).afterLesson with tutorReports := [delivery f reportAt] } }

private def courses (id : LessonId) : StartEvidence :=
  if id = 17 then noTeaching original
  else if id = 18 then taught middle 21 22
  else taught later 30 31

private def evidence : TutorFaultDecisionEvidence :=
  ⟨original, noTeaching original, original.schedule, decision, decisions⟩

private def origin : TutorFaultHistory.Entry := ⟨fault, evidence, outcome, tick 16, 80, 0⟩
private def retained : TutorFaultHistory.History := ⟨[origin], []⟩
private def next : TutorLessonRecord := ⟨later.lesson, some (tick 30), true, 100⟩
private def prior : TutorLessonRecord := ⟨middle.lesson, some (tick 21), true, 90⟩
private def deduction : NextTutorDeductionRecord := ⟨(2, 17), 19, 100, 40, 40, 0, none⟩

private theorem formMatches : original.matches := by
  simp [original, signedForm, lesson, PartOne.matches, Place.matches, Place.validFees,
    Schedule.valid, Contacts.complete, PayAndReviewTerms.valid, PaymentTerms.valid, PaymentDeadline.valid,
    AdvanceWindow.validAt, paymentTerms, tick, Moment.by, Moment.before]
  all_goals decide +kernel

private theorem noTeachingRoster (query : Moment) :
    (noTeaching original).rosterFormsAt original.lesson query none [original] := by
  simpa [noTeaching, original, signedForm, lesson, StartEvidence.rosterFormsAt,
    StartEvidence.rosterMatchesForms, StartEvidence.formsMatch] using
    (show original.matches from formMatches)

private theorem faultEstablished : fault.finding.establishedFor fault.originalLesson := by
  simp [TutorFaultFinding.establishedFor, TutorFaultGround.established, fault, reported,
    original, signedForm, lesson]

private theorem originSchedule :
    EffectiveSchedule original.lesson (noTeaching original) original.schedule (tick 10) := by
  refine ⟨rfl, ?_, by simp [noTeaching, original, signedForm], ?_⟩
  · simp [Schedule.effectiveAtQuery, Schedule.valid, noTeaching, original, signedForm,
      tick, Moment.by, Moment.before]
  · intro row mem _ _
    have same : row = original.schedule := List.mem_singleton.mp mem
    subst row
    refine ⟨rfl, ?_, Or.inl ⟨rfl, (noTeachingRoster (tick 10)).1, ?_⟩⟩
    · simp [Schedule.valid, original, signedForm, tick, Moment.by, Moment.before]
    · intro f mem
      cases List.mem_singleton.mp mem
      rfl

private theorem evidenceEstablishes (query : Moment) (available : (tick 15).by query) :
    evidence.establishes fault query := by
  refine ⟨⟨none, [original], noTeachingRoster (tick 15), by simp [evidence]⟩, rfl,
    originSchedule, rfl, ?_, faultEstablished, by simp [evidence, decisions], rfl, ?_,
    ⟨⟨False, False, False⟩, rfl⟩⟩
  · refine ⟨original.tutorAgreementRef, paymentTerms, formMatches, by decide, by decide,
      Or.inl (by simp [evidence, noTeaching]), none, ?_, ?_⟩
    · simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement,
        evidence, noTeaching]
    · exact ⟨rfl, by decide, rfl⟩
  · simp [evidence, decisions, decision, initial, original, signedForm, lesson,
      FaultDecision.effectiveForForm, DecisionRecords.faultStillApplies,
      initialFindingRecordedConforms, initialFindingConformsWithContacts, authority,
      ReviewAuthorities.mayDecideDispute, ReviewAuthorities.disinterested, DirectInterest.affected,
      tick, Moment.by, Moment.before, matter] at available ⊢
    exact available

/-- The economic outcome records the full original deduction even with no teaching,
    absence verification, customer remedy, settled customer account or payment receipt. -/
theorem originalNoShowRecordsZero (interpretation : TutorFaultHistory.ReviewInterpretation) :
    TutorFaultHistory.Step courses reviews interpretation .empty (.record origin) retained := by
  refine TutorFaultHistory.Step.record origin ⟨rfl, rfl, rfl, rfl, ?_, trivial, by decide, trivial,
    evidenceEstablishes (tick 16) (by decide), ⟨faultEstablished, rfl, rfl⟩⟩ ?_ ?_
  · simp [TutorFaultHistory.Entry.matchesOutcome, TutorFaultHistory.matchesInitialOutcome,
      origin, evidence, decision, reviews, Review.History.originalOutcomes, originalRecord,
      outcome, initial]
  · simp [TutorFaultHistory.History.empty]
  · simp [TutorFaultHistory.History.operativeAt, TutorFaultHistory.History.empty]

private theorem nextQualifies : laterPayableTutorCompletion fault next (tick 30) := by
  simp [laterPayableTutorCompletion, fault, next, original, later, signedForm, lesson,
    tick, Moment.before]
  all_goals decide +kernel

private theorem nextIsFirstInSingleRecord : firstPayableLessonAfterFault fault [next] next :=
  ⟨faultEstablished, by simp, tick 30, nextQualifies, by simp⟩

private theorem originApplies (query : Moment) (h : (tick 16).by query) :
    origin.applies retained [next] next query :=
  ⟨⟨by simp [retained], h, by simp [retained]⟩, rfl, Or.inr nextIsFirstInSingleRecord⟩

/-- The retained applicable outcome cannot be replaced by the two empty submitted lists. -/
theorem cannotOmitOriginal :
    ¬ retained.reads [next] next (tick 35) [] [] := by
  intro check
  have included := (check.1 fault).2 ⟨origin, originApplies (tick 35) (by decide), rfl⟩
  simp at included

theorem agreedOriginal80MakesNextNet60 :
    TutorAmountsForSettlement [next] next [fault] [deduction] 100 60 := by
  refine ⟨rfl, Or.inr ⟨?_, ?_⟩⟩
  · simp [fault, next, original, later, signedForm, lesson]
  · have deductionMatches : deduction.matches fault next := by
      simp [NextTutorDeductionRecord.matches, deduction, TutorFaultCase.deductionKey, fault, next,
        original, later, signedForm, lesson, nextTutorDeduction, originalTutorDeduction]
      all_goals decide +kernel
    simp only [nextTutorDeductionsSettled, List.map_cons, List.map_nil,
      List.mem_singleton, forall_eq, exists_eq_left, List.not_mem_nil, not_false_eq_true,
      true_implies, true_and]
    exact ⟨by decide, by simp, fun _ ↦ deductionMatches,
      ⟨nextIsFirstInSingleRecord, deductionMatches⟩, by decide +kernel, by decide +kernel⟩

private theorem earlierReportRecorded :
    TutorDeliveryRecorded (courses 18) middle.lesson (tick 35) (delivery middle 22) := by
  refine ⟨by simp [courses, taught], rfl, ⟨tick 20, rfl, none, ?_, rfl⟩, rfl,
    by decide, tick 20, tick 21, rfl, rfl, by decide, by decide, by decide⟩
  simp [courses, taught, noTeaching, StartEvidence.effectiveReplacement,
    StartEvidence.latestReplacement]

/-- The earlier actual same-tutor completion is known even before its pay
    classification is entered. A fabricated history containing only lesson 19 fails. -/
theorem earlierRetainedCompletionCannotBeOmitted :
    ¬ TutorFaultHistory.priorCompletionsCovered courses [next] fault next (tick 35) := by
  intro covered
  obtain ⟨row, mem, sameId, _⟩ := covered (tick 30) nextQualifies 18 (by decide) (by decide)
    middle (by simp [courses, taught, noTeaching]) rfl (tick 21) rfl (by decide)
    (by decide) (delivery middle 22) earlierReportRecorded rfl rfl
  cases List.mem_singleton.mp mem
  contradiction

theorem earlierPaidCompletionChangesFirstLesson :
    ¬ firstPayableLessonAfterFault fault [prior, next] next := by
  intro first
  obtain ⟨completed, selected, earlier⟩ := first.2.2
  have sameTime : completed = tick 30 := by
    simpa [next] using selected.2.2.2.1.symm
  subst completed
  have priorQualifies : laterPayableTutorCompletion fault prior (tick 21) := by
    simp [laterPayableTutorCompletion, fault, prior, original, middle, signedForm, lesson,
      tick, Moment.before]
    all_goals decide +kernel
  rcases earlier prior (by simp) (tick 21) priorQualifies with same | wrongOrder
  · exact (by decide : prior ≠ next) same
  · exact (by decide : ¬ (tick 30).before (tick 21)) wrongOrder

private def independentReview : ReviewFinding :=
  ⟨matter, 9, tick 37, "Tutor was not at fault", 51, true⟩

private def correctionRecord : SettlementCorrection := ⟨17, 50, 51, 3, tick 40, [2, 4, 5]⟩

private def correction : Review.Correction :=
  .nonmonetary originalRecord independentReview correctionRecord

private def correctedReviews : Review.History :=
  { reviews with reviewFindings := [independentReview], corrections := [correction] }

private def faultReviewMeaning (finding : ReviewFinding) (outcome : FindingDisposition) :
    TutorFaultHistory.ReviewInterpretation where
  faultOutcome := fun row place ↦
    if row = finding ∧ place = original.place.id then some outcome else none

private def revision : TutorFaultHistory.Revision :=
  ⟨origin, correction, ⟨.review independentReview, original.place.id, .other⟩, none⟩

private def revised : TutorFaultHistory.History := ⟨[origin], [revision]⟩

theorem recordedCorrectionSupersedesOriginal :
    TutorFaultHistory.Step courses correctedReviews (faultReviewMeaning independentReview .other)
      retained (.revise revision) revised := by
  refine TutorFaultHistory.Step.revise revision
    ⟨⟨by simp [revision, retained], by decide, by simp [retained]⟩,
    by simp [retained], by simp [correctedReviews, revision], rfl, rfl, rfl, ?_⟩
  change (faultReviewMeaning independentReview .other).faultOutcome independentReview
    original.place.id = some .other
  simp [faultReviewMeaning]

theorem rootRecordsVerifiedReversal (s : State) (source : s.course = courses)
    (review : s.review = correctedReviews) (history : s.tutorFaults = retained)
    (meaning : s.verifiedTutorReview = faultReviewMeaning independentReview .other) :
    Step s (.tutorFault (.revise revision)) { s with tutorFaults := revised } := by
  apply Step.tutorFault
  simpa only [source, review, history, meaning] using recordedCorrectionSupersedesOriginal

private def affirmedReview : ReviewFinding :=
  { independentReview with reasons := "Tutor fault affirmed. Correct the recorded particulars." }

private def affirmedCorrection : Review.Correction :=
  .nonmonetary originalRecord affirmedReview correctionRecord

private def attemptedRetirement : TutorFaultHistory.Revision :=
  { revision with correction := affirmedCorrection
                  decision := { revision.decision with decision := .review affirmedReview } }

theorem rootRejectsRetirementWhenReviewAffirmsFault (s after : State)
    (meaning : s.verifiedTutorReview = faultReviewMeaning affirmedReview decision.disposition) :
    ¬ Step s (.tutorFault (.revise attemptedRetirement)) after := by
  intro step
  cases step with
  | tutorFault rule =>
    cases rule with
    | revise _ conformance =>
      have binding := conformance.2.2.2.2.2.2
      change s.verifiedTutorReview.faultOutcome affirmedReview original.place.id = some .other
        at binding
      simp [meaning, faultReviewMeaning, decision] at binding

private def originalTutorPart : PaymentPart := ⟨⟨17, 32, 0, .tutorPay 2⟩, .person 2 none, 0⟩

private def payOnlyFinding : ReviewFinding :=
  { independentReview with reasons := "Correct the recorded pay amount. The fault finding stands." }

private def payOnlyCorrection : Review.Correction :=
  .monetary { originalRecord with payment := some originalTutorPart }
    ⟨originalTutorPart, payOnlyFinding, correctionRecord,
      ⟨{ originalTutorPart with amount := 10 }, payOnlyFinding.decidedAt, []⟩⟩

private def payOnlyRetirement : TutorFaultHistory.Revision :=
  { revision with correction := payOnlyCorrection
                  decision := { revision.decision with decision := .review payOnlyFinding } }

theorem payOnlyCorrectionLeavesFaultOperative :
    ¬ origin.correctedBy {} payOnlyCorrection := by
  simp [TutorFaultHistory.Entry.correctedBy]

theorem rootRejectsRetirementFromPayOnlyCorrection (s after : State)
    (noFaultChange : s.verifiedTutorReview.faultOutcome payOnlyFinding original.place.id = none) :
    ¬ Step s (.tutorFault (.revise payOnlyRetirement)) after := by
  intro step
  cases step with
  | tutorFault rule =>
    cases rule with
    | revise _ conformance =>
      have binding := conformance.2.2.2.2.2.2
      change s.verifiedTutorReview.faultOutcome payOnlyFinding original.place.id = some .other
        at binding
      simp [noFaultChange] at binding

theorem correctionPreservesFaultBeforeRecordedAt :
    revised.operativeAt origin (tick 39) := by
  simp [TutorFaultHistory.History.operativeAt, revised, revision, correction,
    Review.Correction.record, origin, correctionRecord, tick, Moment.by, Moment.before]

theorem cannotPayUsingSupersededDeduction :
    ¬ revised.sameTreatmentAt [next] next (tick 45) [fault] := by
  intro same
  obtain ⟨entry, applies, _, _⟩ :=
    (same (2, 17) 80).1 ⟨fault, by simp, rfl, rfl⟩
  have present : entry ∈ revised.entries := applies.1.1
  cases List.mem_singleton.mp present
  exact applies.1.2.2 ⟨revision, by simp [revised], rfl, by decide⟩


theorem rootCanRecordOriginalNoShow (s : State) (source : s.course = courses)
    (review : s.review = reviews) (empty : s.tutorFaults = .empty) :
    Step s (.tutorFault (.record origin)) { s with tutorFaults := retained } := by
  apply Step.tutorFault
  simpa only [source, review, empty] using originalNoShowRecordsZero s.verifiedTutorReview

/-- The root assessment requires membership in its actual recorded history. -/
theorem rootAssessmentCannotOmitOperativeFault (s after : State) (due : Settlement.TutorDue)
    (active : origin.applies s.tutorFaults (s.settlement.tutorCompletionRowsAt due.settledAt)
      due.next due.settledAt)
    (step : Step s (.settlement (.assessTutor due)) after) :
    fault ∈ due.faults ∧ evidence ∈ due.faultDecisions := by
  cases step with
  | settlement _ _ faults _ _ =>
    exact ⟨(faults.2.2.1.1 fault).2 ⟨origin, active, rfl⟩,
      (faults.2.2.1.2 evidence).2 ⟨origin, active, rfl⟩⟩

private def eligible : TutorFaultPlaceFacts := ⟨True, False, True⟩

private def customerDecision : FaultDecisionRecord :=
  { decision with disposition := .fault (.tutor reported eligible) }

private def customerDecisions : DecisionRecords :=
  { decisions with
    faultOutcomes := [customerDecision]
    originalAttendanceTime := fun id place time ↦
      id = original.lesson.id ∧ place = original.place.id ∧ time = tick 10 }

private def customerElection : Redress.AcceptedRemedy where
  id := 1
  facts := ⟨original, .tutor reported eligible, some customerDecision, true,
    customerDecisions, .none⟩
  agreement := ⟨17, 8, original.place.customer, .standardCompensation,
    ["agreed teaching"], tick 16, tick 101⟩
  dates := some ⟨tick 100, none, none⟩

private def paidOriginal : StartEvidence :=
  { noTeaching original with ledger := [⟨1, 6, .lessonDebit 17 8, 100, tick 3⟩] }

private theorem acceptedStandardCompensation :
    customerElection.conforms {} paidOriginal := by
  let entry := customerElection
  have applies : entry.facts.fault.applies original.lesson original.place := by
    simp [entry, customerElection, eligible, reported, original, signedForm, lesson,
      FaultBasis.applies, tutorFaultCompensationEligible, TutorFaultFinding.establishedFor,
      TutorFaultGround.established, TutorFaultScope.affects, Place.matches]
  refine ⟨⟨⟨none, [original], noTeachingRoster (tick 16), by simp [customerElection]⟩,
    ?_, ?_⟩, ?_, by decide, by simp, by simp [paidOriginal, noTeaching, fullRefundClosedBy], ?_⟩
  · refine fun _ ↦ ⟨customerDecision, by simp [customerElection, customerDecisions],
      rfl, rfl, rfl, ?_⟩
    exact (evidenceEstablishes (tick 16) (by decide)).2.2.2.2.2.2.2.2.1
  · exact ⟨applies, ⟨rfl, rfl⟩, tick 10, ⟨rfl, rfl, rfl⟩, by decide,
      100, ⟨Or.inl ⟨by simp [paidOriginal, noTeaching], rfl⟩,
        Or.inr ⟨by decide, by decide +kernel⟩⟩⟩
  · exact ⟨⟨rfl, rfl, rfl, by decide, trivial⟩, applies, trivial⟩
  · exact fun _ ↦ ⟨⟨tick 100, none, none⟩, rfl,
      ⟨rfl, rfl, rfl, by decide, trivial⟩, by decide, ⟨rfl, trivial⟩, ⟨rfl, trivial⟩⟩

theorem customerCanAcceptBeforeEconomicRecord (holds : HoldHistory) :
    Redress.Step {} paidOriginal holds (.acceptRemedy customerElection)
      { remedies := [customerElection] } paidOriginal holds :=
  ⟨acceptedStandardCompensation, rfl, rfl, rfl⟩

/-- Customer acceptance is an independent path that already preserves knowledge
    of the finding. The same original economic outcome cannot be omitted there. -/
theorem rootRetainedRedressPreventsOmission (s after : State) (due : Settlement.TutorDue)
    (retainedRemedy : customerElection ∈ s.redress.remedies)
    (originalSource : s.course 17 = paidOriginal)
    (date : due.settledAt = tick 35) (sameNext : due.next = next)
    (absent : s.tutorFaults = .empty) :
    ¬ Step s (.settlement (.assessTutor due)) after := by
  intro step
  cases step with
  | settlement _ _ _ redress _ =>
    have checked := redress.1 customerElection retainedRemedy (by rw [date]; decide)
    rw [sameNext] at checked
    have notLater : ¬ ∃ schedule,
        let originalAt := (s.course 17).teachingEnded.getD schedule.start
        EffectiveSchedule original.lesson (s.course 17) schedule originalAt ∧
          ¬ originalAt.before (tick 30) := by
      rw [originalSource]
      intro existsSchedule
      obtain ⟨schedule, effective, late⟩ := existsSchedule
      have same : schedule = original.schedule := List.mem_singleton.mp effective.2.1.1
      subst schedule
      exact late (by decide)
    have registered := checked rfl (Or.inr ⟨rfl, by decide, tick 30, rfl, notLater⟩)
    rw [absent] at registered
    obtain ⟨entry, mem, _⟩ := registered
    exact List.not_mem_nil mem


private def straightCourse (id : LessonId) : StartEvidence :=
  if id = 19 then taught later 30 31 else noTeaching original

private def laterCompletion : Settlement.TutorCompletion :=
  ⟨later, next, tick 29, tick 31,
    ⟨later.tutorAgreementRef, 100, paymentTerms⟩, fun _ _ fee ↦ fee = 100⟩

private def noHolds : HoldHistory := ⟨⟨[], [], []⟩, [], [], [], [], [], [], [], []⟩

private def noHoldFacts : HoldFacts where
  terms := fun _ ↦ decisions.terms
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

private def handler : Handler := ⟨3, false, ⟨false, false, false, false⟩⟩
private def assignment : SettlementAssignment :=
  ⟨⟨43, 19, [2, 5]⟩, 60, authority, none, none, fun place ↦ place = 8⟩

private def feeRow : LessonSettlement := ⟨19, 8, 0, 0, 0, 0, 100, 0⟩
private def laterFee : Settlement.AdoptedFee :=
  ⟨59, ⟨later, later.schedule, tick 29, tick 34, tick 34, handler, assignment, noHoldFacts,
    .providerStartedEarly True (fun _ _ ↦ True) 0 100 (fun _ fee pay ↦ fee = 0 ∧ pay = 100),
    feeRow⟩⟩

private def laterHistory : Settlement.History :=
  { fees := [laterFee], tutorCompletions := [laterCompletion] }

private def basis : TutorSettlementBasis :=
  { paymentsByPlace := [feeRow]
    hadTutorPayUnderTerms := fun terms row ↦ row.tutorPay = terms.normalFee
    nowIndependentlyPayable := fun _ ↦ False
    tutorPartsForPlace := fun _ ↦ []
    absenceWithoutTeaching := none
    agreedNetPortion := fun _ ↦ none
    operativeSettlement := fun place _ ↦ if place = 8 then some (feeRow, tick 34) else none
    confirmedDebts := fun _ _ ↦ []
    separateDebtReferences := [] }

private def assessedDue : Settlement.TutorDue where
  form := later
  roster := none
  forms := [later]
  schedule := later.schedule
  startedAt := tick 29
  settledAt := tick 35
  next := next
  completionHistory := [next]
  faultDecisions := [evidence]
  faults := [fault]
  deductions := [deduction]
  agreement := ⟨19, 2, later.tutorAgreementRef, none, none, none, none⟩
  terms := paymentTerms
  basis := basis
  handler := handler
  assignment := assignment
  holdFacts := noHoldFacts
  agreedFee := 100
  net := 60
  separatePart := none

private def stateWith (settlement : Settlement.History) : State where
  lessons := fun id ↦ LessonFile.fromEvidence (straightCourse id)
  credit := CreditBook.fromEvidence (noTeaching original)
  holds := noHolds
  cancelled := {}
  settlement := settlement
  redress := {}
  materials := {}
  review := reviews
  debts := {}
  activeReserves := []
  paymentRecords := []
  separateBookings := []
  tutorFaults := retained

private theorem actualLaterForm : later.matches := by
  simp [later, signedForm, lesson, PartOne.matches, Place.matches, Place.validFees,
    Schedule.valid, Contacts.complete, PayAndReviewTerms.valid, PaymentTerms.valid, PaymentDeadline.valid,
    AdvanceWindow.validAt, paymentTerms, tick, Moment.by, Moment.before]
  all_goals decide +kernel

private theorem laterRoster (query : Moment) :
    (taught later 30 31).rosterFormsAt later.lesson query none [later] := by
  simpa [taught, noTeaching, later, signedForm, lesson, StartEvidence.rosterFormsAt,
    StartEvidence.rosterMatchesForms, StartEvidence.formsMatch] using
    (show later.matches from actualLaterForm)

private theorem laterSchedule :
    EffectiveSchedule later.lesson (taught later 30 31) later.schedule (tick 29) := by
  refine ⟨rfl, ?_, by simp [taught, noTeaching, later, signedForm], ?_⟩
  · simp [Schedule.effectiveAtQuery, Schedule.valid, taught, noTeaching, later, signedForm,
      tick, Moment.by, Moment.before]
  · intro row mem _ _
    cases List.mem_singleton.mp mem
    refine ⟨rfl, ?_, Or.inl ⟨rfl, (laterRoster (tick 29)).1, ?_⟩⟩
    · simp [Schedule.valid, later, signedForm, tick, Moment.by, Moment.before]
    · intro f has
      cases List.mem_singleton.mp has
      rfl

private theorem laterTerms (query : Moment) (started : (tick 29).by query) :
    EffectiveTutorAgreementAt later (taught later 30 31) (tick 29) 2 later.tutorAgreementRef
      100 paymentTerms query query := by
  refine ⟨actualLaterForm, started, Or.inr rfl, Or.inl (by simp [taught, noTeaching]), none, ?_,
    ⟨rfl, ?_, rfl⟩⟩
  · simp [taught, noTeaching, StartEvidence.effectiveReplacement, StartEvidence.latestReplacement]
  · cases query
    simp [later, signedForm, tick, Moment.by, Moment.before] at started ⊢
    omega

private theorem exactOriginal (candidate : TutorFaultCase)
    (established : evidence.establishes candidate (tick 35)) : fault = candidate := by
  rcases established with ⟨_, shape, _, incident, agreed, _, _, _, _, facts, disposition⟩
  obtain ⟨reference, terms, _, _, _, _, active, replacement, term⟩ := agreed
  cases active with
  | some selected =>
    simp [evidence, noTeaching, StartEvidence.effectiveReplacement,
      StartEvidence.latestReplacement] at replacement
  | none =>
    have person : candidate.originalLesson.tutor = original.lesson.tutor := term.1
    have fee : candidate.originalLesson.normalTutorFee = original.lesson.normalTutorFee := by
      have agreement := term.2
      rw [person] at agreement
      change _ ∧ ((⟨reference, candidate.originalLesson.normalTutorFee, terms⟩ : TutorPayTerms) =
        ⟨original.tutorAgreementRef, original.lesson.normalTutorFee, original.deadlines.tutorPay⟩)
        at agreement
      exact congrArg TutorPayTerms.normalFee agreement.2
    have originalLesson : candidate.originalLesson = original.lesson := by
      rw [shape, person, fee]
      rfl
    have originalMoment : candidate.originalLessonAt = tick 10 := incident
    have sameFinding : candidate.finding = reported := by
      have aligned := FaultBasis.tutor.inj (FindingDisposition.fault.inj disposition)
      exact aligned.1.symm
    cases candidate
    cases originalLesson
    cases originalMoment
    cases sameFinding
    rfl

private theorem laterLedgerMatches :
    feeRow.matchesPaymentHistory later.place [] (tick 34) := by
  unfold LessonSettlement.matchesPaymentHistory
  decide +kernel

private theorem laterCompletionVerified :
    laterCompletion.conforms (taught later 30 31) := by
  refine ⟨rfl, ⟨none, [later], laterRoster (tick 29), by simp [laterCompletion]⟩,
    laterTerms (tick 31) (by decide), rfl, rfl, rfl, rfl, delivery later 31, ?_, rfl, rfl⟩
  refine ⟨by simp [taught], rfl, ⟨tick 29, rfl, none, ?_, rfl⟩,
    rfl, by decide, tick 29, tick 30, rfl, rfl, by decide, by decide, by decide⟩
  simp [taught, noTeaching, StartEvidence.effectiveReplacement, StartEvidence.latestReplacement]

private theorem assessedDueEstablished :
    assessedDue.established (taught later 30 31) noHolds laterHistory := by
  refine ⟨by simp [assessedDue], laterRoster (tick 35), ?_, ?_, ?_, rfl, by simp [assessedDue],
    rfl, ⟨laterSchedule, by decide, Or.inl rfl⟩,
    by simp [Settlement.TutorDue.agreedAbsenceRecorded, taught], rfl,
    laterTerms (tick 35) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [assessedDue, HoldFacts.groupSettlementScopeMatches, noHoldFacts,
      later, signedForm, lesson]
  · simp [assessedDue, SettlementAssignment.authorised, assignment, handler, Handler.maySettle,
      authority, ReviewAuthorities.disinterested, DirectInterest.affected, later,
      signedForm, lesson]
  · simp [HoldHistory.mayCarryOutDecision, HoldHistory.distinctFormalDecisions, noHolds,
      HoldHistory.decisionOnFormalHold, HoldHistory.validFormalHold]
  · simp [assessedDue, basis, TutorSettlementBasis.debtsReferenced, ConfirmedTutorDebtsReferenced]
  · intro candidate
    simp only [assessedDue, List.mem_singleton, exists_eq_left]
    constructor
    · intro eq
      cases eq
      exact evidenceEstablishes (tick 35) (by decide)
    · exact fun h ↦ (exactOriginal candidate h).symm
  · intro item member short
    cases List.mem_singleton.mp member
    exact ((by decide : ¬ (0 : Amount) < 0) short).elim
  · intro placeAmounts member
    cases List.mem_singleton.mp member
    exact ⟨tick 34, rfl, laterFee, by simp [laterHistory], rfl, rfl, rfl, rfl, by decide, trivial⟩
  · refine ⟨by simp [assessedDue, basis], by simp [assessedDue, basis], ?_, by decide +kernel⟩
    intro placeAmounts member
    cases List.mem_singleton.mp member
    exact ⟨later, by simp [assessedDue], rfl, rfl, rfl,
      ⟨tick 34, rfl, by decide, laterLedgerMatches⟩, by decide⟩
  · refine ⟨by simp [assessedDue, later, signedForm, lesson], ?_,
      agreedOriginal80MakesNextNet60⟩
    intro f member
    cases List.mem_singleton.mp member
    exact ⟨feeRow, List.mem_singleton.mpr rfl, rfl⟩

/-- A positive root transition consumes the saved 80-fee finding, the actual
    lesson-19 completion and its 100 gross-fee assessment to record net pay 60. -/
theorem rootAssesses60ForFirstLaterLesson :
    Step (stateWith laterHistory) (.settlement (.assessTutor assessedDue))
      (stateWith { laterHistory with tutors := [assessedDue] }) := by
  have reads : retained.reads [next] next (tick 35) [fault] [evidence] := by
    constructor
    · intro candidate
      simp only [List.mem_singleton]
      constructor
      · intro eq
        cases eq
        exact ⟨origin, originApplies (tick 35) (by decide), rfl⟩
      · rintro ⟨entry, applies, rfl⟩
        cases List.mem_singleton.mp applies.1.1
        rfl
    · intro source
      simp only [List.mem_singleton]
      constructor
      · intro eq
        cases eq
        exact ⟨origin, originApplies (tick 35) (by decide), rfl⟩
      · rintro ⟨entry, applies, rfl⟩
        cases List.mem_singleton.mp applies.1.1
        rfl
  refine Step.settlement ?_ ?_ ⟨rfl, ?_, reads, ?_⟩ ?_ trivial ?_
    (Settlement.Step.assessTutor assessedDueEstablished)
  · simp [Settlement.Event.respectsCancellation]
  · simp [Settlement.Event.readsConfirmedDebts, stateWith, assessedDue, basis,
      Debt.History.confirmed]
  · have noCorrections : (stateWith laterHistory).review.corrections = [] := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro correction member
      simp only [noCorrections, List.not_mem_nil] at member
    · intro finding member
      simp [stateWith, reviews, Review.History.empty] at member
    · intro finding member _ originalCourse saved records form schedule _ selected _ verified _ _
      have sameFinding : finding = initial := List.mem_singleton.mp member
      subst finding
      obtain ⟨_, lessonIdentity, effectiveSchedule, scheduledTime, agreement, _⟩ := verified
      obtain ⟨reference, payment, _, _, _, retainedForm, active, replacement, agreedTerms⟩ :=
        agreement
      have sameForm : form = original := by
        rcases retainedForm with retained | ⟨_, _, _, _, ⟨_, _, booked, _⟩⟩
        · exact List.mem_singleton.mp retained
        · exact False.elim (List.not_mem_nil booked)
      subst form
      have sameSchedule : schedule = original.schedule :=
        List.mem_singleton.mp effectiveSchedule.2.1.1
      subst schedule
      have noReplacement : active = none := by
        cases active with
        | none => rfl
        | some _ => exact False.elim (List.not_mem_nil replacement.2.2.1)
      subst active
      have sameTutor : selected.originalLesson.tutor = original.lesson.tutor := agreedTerms.1
      have sameFee : selected.originalLesson.normalTutorFee = original.lesson.normalTutorFee := by
        have terms := agreedTerms.2
        rw [sameTutor] at terms
        change (tick 3).by (tick 10) ∧
          (⟨reference, selected.originalLesson.normalTutorFee, payment⟩ : TutorPayTerms) =
            ⟨original.tutorAgreementRef, original.lesson.normalTutorFee,
              original.deadlines.tutorPay⟩ at terms
        exact congrArg TutorPayTerms.normalFee terms.2
      refine Or.inl ⟨origin, (originApplies (tick 35) (by decide)).1, rfl, ?_, ?_,
        scheduledTime.symm⟩
      · simp [TutorFaultHistory.Entry.matchesOutcome, TutorFaultHistory.matchesInitialOutcome,
          origin, evidence, decision, stateWith, reviews, Review.History.originalOutcomes,
          originalRecord, outcome, initial]
      · rw [sameTutor, sameFee] at lessonIdentity
        exact lessonIdentity.symm
    · intro entry operative _
      cases List.mem_singleton.mp operative.1
      refine ⟨by simp [noCorrections], ?_, ?_⟩
      · intro _ _ id _ notNext
        have notLater : id ≠ 19 := notNext
        have notTaught : ((stateWith laterHistory).course id).teachingEnded = none := by
          simp [State.course, stateWith, straightCourse, notLater, noTeaching, LessonFile.evidence,
            LessonFile.fromEvidence]
        simp [notTaught]
      · intro _ _ _ _ _ _ _ _ _ _ correction member
        simp only [noCorrections, List.not_mem_nil] at member
  · simp [TutorFaultHistory.deductionsUsedOnce, stateWith, laterHistory, reviews,
      Review.History.empty]
  · simp [TutorFaultHistory.retainedRedressUses, TutorFaultHistory.redressRecordedAt, stateWith]
  · simp [Settlement.Event.usesCurrentAbsence, assessedDue, basis]

private def initialOnlyState : State :=
  { stateWith laterHistory with tutorFaults := .empty }

private def noDeductionDue : Settlement.TutorDue :=
  { assessedDue with faultDecisions := [], faults := [], deductions := [], net := 100 }

private theorem noDeductionEstablished :
    noDeductionDue.established (taught later 30 31) noHolds laterHistory := by
  rcases assessedDueEstablished with
    ⟨authorised, wholeGroup, unheld, matchingForm, roster, scope, nextInHistory, lessonMatches,
      completion, shortfalls, agrees, debts, totals, _, _, noSeparatePart, covered, amounts⟩
  refine ⟨authorised, wholeGroup, unheld, matchingForm, roster, scope, nextInHistory, lessonMatches,
    completion, shortfalls, agrees, debts, totals, ?_, ?_, noSeparatePart, covered, ?_⟩
  · simp [noDeductionDue]
  · simp [noDeductionDue]
  · refine ⟨amounts.1, amounts.2.1, ?_⟩
    simp [noDeductionDue, assessedDue, TutorAmountsForSettlement, nextTutorDeductionsSettled,
      next, sumAmounts]
    decide +kernel

private theorem retainedInitialEstablishes :
    { evidence with records := reviews.decisionRecords authority decisions }.establishes
      fault (tick 15) := by
  rcases evidenceEstablishes (tick 15) (by decide) with
    ⟨roster, lessonMatches, schedule, lessonTime, agreement, established, present, place, _, typed⟩
  refine ⟨roster, lessonMatches, schedule, lessonTime, agreement, established, present, place, ?_,
    typed⟩
  simp [evidence, decisions, decision, initial, original, signedForm, lesson,
    FaultDecision.effectiveForForm, DecisionRecords.faultStillApplies, reviews,
    Review.History.decisionRecords, Review.History.authorities, Review.History.empty,
    initialFindingRecordedConforms, initialFindingConformsWithContacts, authority,
    ReviewAuthorities.mayDecideDispute, ReviewAuthorities.disinterested, DirectInterest.affected,
    tick, Moment.by, Moment.before, matter]

/-- The retained typed decision already blocks gross 100 before the economic entry is filed. -/
theorem rootRejectsMissingVerifiedInitialEconomicEntry (after : State) :
    ¬ Step initialOnlyState (.settlement (.assessTutor noDeductionDue)) after := by
  intro step
  cases step with
  | settlement _ _ faults _ _ =>
    have recorded := faults.2.1.2.2.1 initial (List.mem_singleton.mpr rfl) (by decide)
      original original.schedule decision fault rfl retainedInitialEstablishes trivial
      ⟨rfl, Or.inr ⟨tick 30, nextQualifies⟩⟩
    rcases recorded with ⟨_, present, _⟩ | ⟨_, present, _⟩
    · exact List.not_mem_nil present.1
    · exact List.not_mem_nil present

/-- The existing recording transition from that prestate enables the 100−40 assessment. -/
theorem rootRegistersInitialAndAssesses60 :
    Step initialOnlyState (.tutorFault (.record origin)) (stateWith laterHistory) ∧
    Step (stateWith laterHistory) (.settlement (.assessTutor assessedDue))
      (stateWith { laterHistory with tutors := [assessedDue] }) := by
  refine ⟨Step.tutorFault ?_, rootAssesses60ForFirstLaterLesson⟩
  cases originalNoShowRecordsZero initialOnlyState.verifiedTutorReview with
  | record _ verified fresh newCase => exact .record origin verified fresh newCase

private def unregisteredState (dispositions : List FaultDecisionRecord)
    (review : Review.History) (meaning : ReviewFinding → PlaceId → Option FindingDisposition) :
    State :=
  { initialOnlyState with
    lessons := fun id ↦ if id = 17 then
      LessonFile.fromEvidence { (noTeaching original) with
        studentFaults := { (noTeaching original).studentFaults with
          decisions := { decisions with faultOutcomes := dispositions } } }
      else initialOnlyState.lessons id
    review := review
    verifiedTutorReview := { faultOutcome := meaning } }

private theorem unregisteredStateAssesses100 (dispositions : List FaultDecisionRecord)
    (review : Review.History) (meaning : ReviewFinding → PlaceId → Option FindingDisposition)
    (reviewed : TutorFaultHistory.History.empty.reviewFaultsRecordedAt
      (unregisteredState dispositions review meaning).course review ⟨meaning, fun _ _ ↦ none⟩ next
      (tick 35))
    (initials : TutorFaultHistory.History.empty.initialFaultsRecordedAt
      (unregisteredState dispositions review meaning).course review ⟨meaning, fun _ _ ↦ none⟩ next
      (tick 35)) :
    let s := unregisteredState dispositions review meaning
    Step s (.settlement (.assessTutor noDeductionDue))
      { s with settlement := { laterHistory with tutors := [noDeductionDue] } } := by
  refine Step.settlement ?_ ?_ ⟨rfl, ?_, ?_, ?_⟩ ?_ trivial ?_
    (Settlement.Step.assessTutor noDeductionEstablished)
  · simp [Settlement.Event.respectsCancellation]
  · simp [Settlement.Event.readsConfirmedDebts, unregisteredState, initialOnlyState, stateWith,
      noDeductionDue, assessedDue, basis, Debt.History.confirmed]
  · refine ⟨?_, reviewed, initials, ?_⟩
    · intro key correction member decided fee present
      exact False.elim (Option.not_mem_none fee present)
    · intro entry operative _
      exact False.elim (List.not_mem_nil operative.1)
  · simp [TutorFaultHistory.History.reads, TutorFaultHistory.Entry.applies,
      TutorFaultHistory.History.operativeAt, TutorFaultHistory.History.empty, unregisteredState,
      initialOnlyState, noDeductionDue]
  · simp [TutorFaultHistory.deductionsUsedOnce, noDeductionDue]
  · simp [TutorFaultHistory.retainedRedressUses, TutorFaultHistory.redressRecordedAt,
      unregisteredState, initialOnlyState, stateWith]
  · simp [Settlement.Event.usesCurrentAbsence, noDeductionDue, assessedDue, basis]

/-- The same text and original outcome alone do not establish tutor fault. -/
theorem rootAssesses100WithOnlyUntypedInitial :
    let s := unregisteredState [] reviews (fun _ _ ↦ none)
    Step s (.settlement (.assessTutor noDeductionDue))
      { s with settlement := { laterHistory with tutors := [noDeductionDue] } } := by
  refine unregisteredStateAssesses100 [] reviews (fun _ _ ↦ none) ?_ ?_
  · intro finding present
    exact False.elim (List.not_mem_nil present)
  · intro finding present _ originalCourse saved records form schedule row selected _ verified _ _
    have sameFinding : finding = initial := List.mem_singleton.mp present
    subst finding
    exact False.elim (List.not_mem_nil verified.2.2.2.2.2.2.1)

private def dismissalFinding : ReviewFinding := { independentReview with decidedAt := tick 20 }

private def dismissal : Review.Correction :=
  .nonmonetary originalRecord dismissalFinding { correctionRecord with recordedAt := tick 22 }

private def dismissedReviews : Review.History :=
  { reviews with reviewFindings := [dismissalFinding], corrections := [dismissal] }

/-- A retained dismissal of the exact initial outcome permits the same gross assessment. -/
theorem rootAssesses100AfterExactInitialDismissal :
    let s := unregisteredState [decision] dismissedReviews
      (faultReviewMeaning dismissalFinding .other).faultOutcome
    Step s (.settlement (.assessTutor noDeductionDue))
      { s with settlement := { laterHistory with tutors := [noDeductionDue] } } := by
  refine unregisteredStateAssesses100 [decision] dismissedReviews
    (faultReviewMeaning dismissalFinding .other).faultOutcome ?_ ?_
  · intro finding present _ place _ _ interpreted
    have sameFinding : finding = dismissalFinding := List.mem_singleton.mp present
    subst finding
    simp [faultReviewMeaning] at interpreted
  · intro finding present _ originalCourse saved records form schedule row selected _ verified _ _
    have sameFinding : finding = initial := List.mem_singleton.mp present
    subst finding
    have sameDecision : row = decision := List.mem_singleton.mp verified.2.2.2.2.2.2.1
    subst row
    have samePlace : decision.place = form.place.id := verified.2.2.2.2.2.2.2.1
    refine Or.inr ⟨dismissal, List.mem_singleton.mpr rfl, by decide, ?_,
      List.mem_singleton.mpr rfl, ?_⟩
    · change TutorFaultHistory.matchesInitialOutcome dismissedReviews initial outcome
      simp [TutorFaultHistory.matchesInitialOutcome, dismissedReviews, reviews,
        Review.History.originalOutcomes, originalRecord, outcome, initial]
    · rw [← samePlace]
      simp [faultReviewMeaning, decision, dismissal, TutorFaultHistory.correctionFinding]


private def unpayablePrior : TutorLessonRecord := { prior with feeOtherwisePayable := 0 }

private def middleCompletion : Settlement.TutorCompletion :=
  ⟨middle, unpayablePrior, tick 20, tick 22,
    ⟨middle.tutorAgreementRef, 90, paymentTerms⟩, fun _ _ fee ↦ fee = 0⟩

private def completionMatter : ReviewMatter := ⟨44, 18, [2, 3]⟩

private def completionFinding : ReviewFinding :=
  ⟨completionMatter, 9, tick 37, "The completed lesson carries gross tutor pay of 90", 64, true⟩

private def middleTutorPart : PaymentPart := ⟨⟨18, 33, 0, .tutorPay 2⟩, .person 2 none, 0⟩

private def savedCompletionOutcome : Review.OriginalRecord :=
  ⟨⟨completionMatter, 63, 3, tick 23⟩, some middleTutorPart⟩

private def completionAdjustment : Review.Correction :=
  .monetary savedCompletionOutcome
    ⟨middleTutorPart, completionFinding, ⟨18, 63, 64, 3, tick 40, [2, 3]⟩,
      ⟨{ middleTutorPart with amount := 50 }, completionFinding.decidedAt, []⟩⟩

private def completionMeaning : TutorFaultHistory.ReviewInterpretation where
  completionFee := fun finding key ↦
    if finding = completionFinding ∧ key = Settlement.tutorOccurrenceKey unpayablePrior then
      some 90
    else none

private def completionChange : Settlement.TutorCompletionRevision :=
  ⟨unpayablePrior, completionAdjustment, 90⟩

private def completionState : State :=
  { stateWith { laterHistory with tutorCompletions := [middleCompletion, laterCompletion] } with
    lessons := fun id ↦ LessonFile.fromEvidence
      (if id = 18 then taught middle 21 22 else straightCourse id)
    review := { reviews with
      originals := [originalRecord, savedCompletionOutcome]
      reviewFindings := [completionFinding]
      corrections := [completionAdjustment] }
    verifiedTutorReview := completionMeaning }

private def revisedCompletionState : State :=
  { completionState with settlement :=
    { completionState.settlement with tutorCompletionRevisions := [completionChange] } }

theorem rootRecordsReviewedCompletionFee :
    Step completionState (.settlement (.reviseTutorCompletion completionChange))
      revisedCompletionState := by
  refine Step.settlement trivial trivial ?_ trivial trivial trivial
    (Settlement.Step.reviseTutorCompletion ?_)
  · exact ⟨by simp [completionState, completionChange], by simp [completionState, completionChange,
      TutorFaultHistory.correctionFinding, completionAdjustment, completionMeaning]⟩
  · refine ⟨rfl, by decide +kernel, ⟨middleCompletion, by simp [completionState, stateWith],
      rfl, by decide⟩, by decide, by decide, ?_⟩
    simp [completionState, stateWith, laterHistory]

theorem rootRejectsNetPaymentAsReviewedGross (after : State) :
    ¬ Step completionState
      (.settlement (.reviseTutorCompletion { completionChange with correctedFee := 50 })) after := by
  intro step
  cases step with
  | settlement _ _ faults _ _ =>
    have binding := faults.2
    simp [completionState, completionChange, TutorFaultHistory.correctionFinding,
      completionAdjustment, completionMeaning] at binding

theorem reviewKeepsOriginalCompletionAndDatedFee :
    revisedCompletionState.settlement.tutorCompletions = completionState.settlement.tutorCompletions ∧
    revisedCompletionState.settlement.tutorCompletionRowsAt (tick 39) = [unpayablePrior, next] ∧
    revisedCompletionState.settlement.tutorCompletionRowsAt (tick 40) = [prior, next] :=
  ⟨rfl, by decide +kernel, by decide +kernel⟩

theorem reviewedPayableFeeSelectsEarlierCompletion :
    firstPayableLessonAfterFault fault
      (revisedCompletionState.settlement.tutorCompletionRowsAt (tick 40)) prior ∧
    ¬firstPayableLessonAfterFault fault
      (revisedCompletionState.settlement.tutorCompletionRowsAt (tick 40)) next := by
  rw [reviewKeepsOriginalCompletionAndDatedFee.2.2]
  refine ⟨⟨faultEstablished, by simp, tick 21, ?_, ?_⟩, earlierPaidCompletionChangesFirstLesson⟩
  · simp [laterPayableTutorCompletion, fault, prior, original, middle, signedForm, lesson,
      tick, Moment.before]
    all_goals decide +kernel
  · intro row mem atTime eligible
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact Or.inl rfl
    · have ended : atTime = tick 30 := Option.some.inj eligible.2.2.2.1.symm
      subst atTime
      exact Or.inr (by decide)

theorem rootRejectsStaleCompletionBeforeAssessingDeduction (after : State) :
    ¬ Step completionState
      (.settlement (.assessTutor { assessedDue with
        settledAt := tick 41, completionHistory := [unpayablePrior, next] })) after := by
  intro step
  cases step with
  | settlement _ _ faults _ _ =>
    have covered := faults.2.1.2.2.2 origin
      ⟨by simp [completionState, stateWith, retained], by decide, by simp [completionState,
        stateWith, retained]⟩
      ⟨rfl, Or.inr ⟨tick 30, nextQualifies⟩⟩
    have current := covered.2.2 (tick 30) nextQualifies unpayablePrior (by decide +kernel)
      (by decide) rfl (tick 21) rfl (by decide) (by decide)
    have update := current completionAdjustment (by simp [completionState]) rfl (by decide)
      90 (by simp [completionState, completionMeaning, TutorFaultHistory.correctionFinding,
        completionAdjustment]) (by
          simp [completionState, completionAdjustment, Review.Correction.record, tick,
            Moment.before])
    exact (by decide : (90 : Amount) ≠ 0) update


private def latestCompletionFinding : ReviewFinding :=
  { completionFinding with
    reviewer := 10, decidedAt := tick 42, reasons := "The completed lesson was fee-waived", outcome := 65 }

private def paidMiddlePart : PaymentPart := { middleTutorPart with amount := 50 }

private def priorCompletionOutcome : Review.OriginalRecord :=
  ⟨⟨completionMatter, 64, 9, tick 37⟩, some paidMiddlePart⟩

private def latestCompletionAdjustment : Review.Correction :=
  .monetary priorCompletionOutcome
    ⟨paidMiddlePart, latestCompletionFinding, ⟨18, 64, 65, 3, tick 44, [2, 3]⟩,
      ⟨middleTutorPart, latestCompletionFinding.decidedAt, []⟩⟩

private def lateCompletion : Settlement.TutorCompletion :=
  { middleCompletion with verifiedAt := tick 45 }

private def lateState : State :=
  { completionState with
    settlement := laterHistory
    review := { completionState.review with
      originals := [originalRecord, savedCompletionOutcome, priorCompletionOutcome]
      reviewFindings := [completionFinding, latestCompletionFinding]
      corrections := [completionAdjustment, latestCompletionAdjustment] }
    verifiedTutorReview :=
      { completionFee := fun finding key ↦
          if finding = latestCompletionFinding ∧
              key = Settlement.tutorOccurrenceKey unpayablePrior then
            some 0
          else completionMeaning.completionFee finding key } }

private theorem lateCompletionVerified :
    lateCompletion.conforms (lateState.course 18) := by
  change lateCompletion.conforms (taught middle 21 22)
  have matched : middle.matches := by
    simp [middle, signedForm, lesson, PartOne.matches, Place.matches, Place.validFees,
      Schedule.valid, Contacts.complete, PayAndReviewTerms.valid, PaymentTerms.valid,
      PaymentDeadline.valid, AdvanceWindow.validAt, paymentTerms, tick, Moment.by, Moment.before]
    all_goals decide +kernel
  refine ⟨rfl, ⟨none, [middle], ?_, by simp [lateCompletion, middleCompletion]⟩,
    ?_, rfl, rfl, rfl, rfl, delivery middle 22, ?_, rfl, rfl⟩
  · change (taught middle 21 22).rosterFormsAt middle.lesson (tick 20) none [middle]
    simpa [taught, noTeaching, middle, signedForm, lesson, StartEvidence.rosterFormsAt,
      StartEvidence.rosterMatchesForms, StartEvidence.formsMatch] using matched
  · change EffectiveTutorAgreementAt middle (taught middle 21 22) (tick 20) 2
      middle.tutorAgreementRef 90 paymentTerms (tick 45) (tick 45)
    refine ⟨matched, by decide, Or.inr rfl, Or.inl (by simp [taught, noTeaching]),
      none, ?_, rfl, by decide, rfl⟩
    simp [taught, noTeaching, StartEvidence.effectiveReplacement, StartEvidence.latestReplacement]
  · refine ⟨by simp [taught], rfl, ⟨tick 20, rfl, none, ?_, rfl⟩,
      rfl, by decide, tick 20, tick 21, rfl, rfl, by decide, by decide, by decide⟩
    simp [taught, noTeaching, StartEvidence.effectiveReplacement, StartEvidence.latestReplacement]

theorem rootAcceptsLateFirstVerificationAtCurrentFee :
    Step lateState (.settlement (.verifyTutorCompletion lateCompletion))
      { lateState with settlement :=
        { laterHistory with tutorCompletions := [laterCompletion, lateCompletion] } } := by
  refine Step.settlement trivial trivial ?_ trivial trivial trivial
    (Settlement.Step.verifyTutorCompletion lateCompletionVerified ?_)
  · intro correction member _ _ fee meaningful latest
    change correction ∈ [completionAdjustment, latestCompletionAdjustment] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (latest ⟨latestCompletionAdjustment, by simp [lateState], rfl, rfl, by decide,
        by decide, by simp [lateState, latestCompletionAdjustment, TutorFaultHistory.correctionFinding,
          lateCompletion, middleCompletion]⟩).elim
    · apply Eq.symm
      simpa [lateState, lateCompletion, middleCompletion, unpayablePrior,
        latestCompletionAdjustment, TutorFaultHistory.correctionFinding] using meaningful
  · intro other member
    have same : other = laterCompletion := List.mem_singleton.mp member
    subst other
    decide +kernel


private def newlyFoundTutorFault : ReviewFinding :=
  { independentReview with reasons := "The tutor did not provide the agreed teaching." }

private def unadoptedFaultState : State :=
  { stateWith laterHistory with
    tutorFaults := .empty
    review := { Review.History.empty with
      originals := [originalRecord]
      reviewFindings := [newlyFoundTutorFault] }
    verifiedTutorReview := faultReviewMeaning newlyFoundTutorFault decision.disposition }

theorem rootRejectsSettlementBeforeAdoptingReviewedFault (after : State) :
    ¬ Step unadoptedFaultState (.settlement (.assessTutor { assessedDue with
      settledAt := tick 38, faultDecisions := [], faults := [], deductions := [], net := 100 })) after := by
  intro step
  cases step with
  | settlement _ _ faultUses _ _ =>
    have recorded := faultUses.2.1.2.1 newlyFoundTutorFault (by simp [unadoptedFaultState])
      (by decide) original.place.id reported ⟨False, False, False⟩
      (by simp [unadoptedFaultState, faultReviewMeaning, decision]) rfl rfl
      (Or.inr ⟨rfl, by decide, tick 30, rfl, ?_⟩)
    · rcases recorded with ⟨_, present, _⟩ | ⟨saved, member, _⟩
      · exact List.not_mem_nil present.1
      · exact List.not_mem_nil member
    · rintro ⟨form, member, _, schedule, effective, notEarlier⟩
      have sameForm : form = original := by
        simpa [State.course, unadoptedFaultState, stateWith, straightCourse, noTeaching, reported,
          LessonFile.evidence, LessonFile.fromEvidence] using member
      subst form
      have sameSchedule : schedule = original.schedule := List.mem_singleton.mp effective.2.1.1
      subst schedule
      exact notEarlier (by decide)


private def earlierDeduction : NextTutorDeductionRecord :=
  { deduction with nextLesson := 18, payableBeforeDeductions := 90 }

private def filedDeductionHistory (filed : Review.CorrectedPayout)
    (original : Review.OriginalRecord) (correction : PaymentCorrectionCase) : Review.History :=
  { Review.History.empty with
    correctedPayouts := [filed]
    corrections := [.monetary original correction] }

theorem operativeCorrectedAssignmentPreventsAnotherUse (filed : Review.CorrectedPayout)
    (amounts : TutorCorrectionAmounts) (old : Review.OriginalRecord)
    (correction : PaymentCorrectionCase) (query : Moment)
    (filedBy : filed.recordedAt.by query)
    (futureCorrection : ¬correction.correction.recordedAt.by query)
    (sameTutor : filed.part.ref.purpose = .tutorPay 2)
    (sameAmounts : amounts ∈ filed.reviewedTutorAmounts)
    (applied : deduction ∈ amounts.deductions) :
    ¬TutorFaultHistory.deductionsUsedOnce (filedDeductionHistory filed old correction) {}
      [earlierDeduction] query := by
  intro use
  have once := (use earlierDeduction (by simp)).2 filed (by simp [filedDeductionHistory]) filedBy
  have distinct := once (by
      rintro ⟨other, member, _, cutoff, _, _, _⟩
      change other ∈ [correction] at member
      cases List.mem_singleton.mp member
      exact futureCorrection cutoff)
    sameTutor amounts sameAmounts deduction applied rfl
  contradiction

theorem recordedExactCorrectionReleasesEarlierAssignment (filed : Review.CorrectedPayout)
    (old : Review.OriginalRecord) (correction : PaymentCorrectionCase) (query : Moment)
    (laterCorrection :
      filed.correction.correction.recordedAt.before correction.correction.recordedAt)
    (cutoff : correction.correction.recordedAt.by query)
    (sameCase : correction.finding.matter.sameCase filed.correction.finding.matter)
    (sameOutcome : correction.correction.originalOutcome = filed.correction.finding.outcome)
    (samePart : correction.originalPart = filed.correction.money.corrected) :
    TutorFaultHistory.deductionsUsedOnce (filedDeductionHistory filed old correction) {}
      [earlierDeduction] query := by
  intro _ _
  refine ⟨by simp, ?_⟩
  intro prior member _ unchanged
  cases List.mem_singleton.mp member
  exact (unchanged ⟨correction, List.mem_singleton.mpr rfl, laterCorrection, cutoff,
    sameCase, sameOutcome, samePart⟩).elim

private def originalAccountPart : PaymentPart :=
  ⟨⟨19, 52, 1, .tutorPay 2⟩, .person 2 none, 60⟩

private def revisedAccountPart : PaymentPart :=
  { originalAccountPart with ref := { originalAccountPart.ref with portion := 2 }, amount := 55 }

private def finalAccountPart : PaymentPart :=
  { originalAccountPart with ref := { originalAccountPart.ref with portion := 3 }, amount := 45 }

private def accountMatter : ReviewMatter := assignment.matter

private def reviseAccountPay (prior corrected : PaymentPart)
    (oldOutcome newOutcome : EvidenceRef) (decidedAt recordedAt : Moment) :
    PaymentCorrectionCase :=
  ⟨prior, ⟨accountMatter, 9, decidedAt, "Correct the amount based on the verified fee", newOutcome, true⟩,
    ⟨19, oldOutcome, newOutcome, 3, recordedAt, [2, 3]⟩, ⟨corrected, decidedAt, []⟩⟩

private def firstAccountPayRevision : PaymentCorrectionCase :=
  reviseAccountPay originalAccountPart revisedAccountPart 71 72 (tick 40) (tick 41)

private def secondAccountPayRevision : PaymentCorrectionCase :=
  reviseAccountPay revisedAccountPart finalAccountPart 72 73 (tick 50) (tick 51)

private def accountPayOriginal : Review.OriginalRecord :=
  ⟨⟨accountMatter, 71, handler.actor, assessedDue.settledAt⟩, some originalAccountPart⟩

private def accountPayState (reverseOrder : Bool := false) : State :=
  let first := Review.Correction.monetary accountPayOriginal firstAccountPayRevision
  let prior : Review.OriginalRecord := ⟨⟨accountMatter, 72, 9, tick 40⟩, some revisedAccountPart⟩
  let second := Review.Correction.monetary prior secondAccountPayRevision
  { stateWith { laterHistory with tutors := [assessedDue] } with
    review := { Review.History.empty with
      originals := [accountPayOriginal]
      corrections := if reverseOrder then [second, first] else [first, second] } }

private theorem accountPayReadsRevisions (reverseOrder : Bool)
    {file : FiledLessonAccount} {after : State}
    (filedAt : file.filedAt = tick 60)
    (step : Step (accountPayState reverseOrder) (.settlement (.fileAccount later file)) after) :
    file.tutorPay = some 45 := by
  cases step with
  | settlement _ _ _ _ account _ _ =>
    obtain ⟨_, _, _, _, _, _, _, pay, _, _⟩ := account
    rw [filedAt] at pay
    refine pay.trans ?_
    cases reverseOrder <;> cbv

/-- The actual account entry follows the original recorded outcome and both
    adopted portion revisions before any successful payment. -/
theorem filedAccountReadsLatestTutorCorrection {file : FiledLessonAccount} {after : State}
    (filedAt : file.filedAt = tick 60)
    (step : Step accountPayState (.settlement (.fileAccount later file)) after) :
    file.tutorPay = some 45 :=
  accountPayReadsRevisions false filedAt step

theorem filedAccountReadsLatestTutorCorrectionInReverse
    {file : FiledLessonAccount} {after : State}
    (filedAt : file.filedAt = tick 60)
    (step : Step (accountPayState true) (.settlement (.fileAccount later file)) after) :
    file.tutorPay = some 45 :=
  accountPayReadsRevisions true filedAt step

#print axioms filedAccountReadsLatestTutorCorrection
#print axioms filedAccountReadsLatestTutorCorrectionInReverse

#print axioms originalNoShowRecordsZero
#print axioms cannotOmitOriginal
#print axioms agreedOriginal80MakesNextNet60
#print axioms earlierRetainedCompletionCannotBeOmitted
#print axioms earlierPaidCompletionChangesFirstLesson
#print axioms recordedCorrectionSupersedesOriginal
#print axioms rootRecordsVerifiedReversal
#print axioms rootRejectsRetirementWhenReviewAffirmsFault
#print axioms payOnlyCorrectionLeavesFaultOperative
#print axioms rootRejectsRetirementFromPayOnlyCorrection
#print axioms correctionPreservesFaultBeforeRecordedAt
#print axioms cannotPayUsingSupersededDeduction
#print axioms rootCanRecordOriginalNoShow
#print axioms rootAssessmentCannotOmitOperativeFault
#print axioms customerCanAcceptBeforeEconomicRecord
#print axioms rootRetainedRedressPreventsOmission
#print axioms rootAssesses60ForFirstLaterLesson
#print axioms rootRejectsMissingVerifiedInitialEconomicEntry
#print axioms rootRegistersInitialAndAssesses60
#print axioms rootAssesses100WithOnlyUntypedInitial
#print axioms rootAssesses100AfterExactInitialDismissal
#print axioms rootRecordsReviewedCompletionFee
#print axioms rootRejectsNetPaymentAsReviewedGross
#print axioms reviewKeepsOriginalCompletionAndDatedFee
#print axioms reviewedPayableFeeSelectsEarlierCompletion
#print axioms rootRejectsStaleCompletionBeforeAssessingDeduction
#print axioms rootAcceptsLateFirstVerificationAtCurrentFee
#print axioms rootRejectsSettlementBeforeAdoptingReviewedFault
#print axioms operativeCorrectedAssignmentPreventsAnotherUse
#print axioms recordedExactCorrectionReleasesEarlierAssignment

end SourceV14.Workflow.TutorFaultChecks
