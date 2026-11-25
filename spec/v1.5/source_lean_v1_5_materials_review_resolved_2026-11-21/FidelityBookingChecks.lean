import SourceV14.Workflow

/-! Booking witnesses for §§1.4, 2.2–2.5 and both parts of the confirmation form. -/

namespace SourceV14.FidelityBookingChecks

open Booking Confirmation Course Settlement

private def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩
private def groupLesson : Lesson := ⟨42, .group, 10, 20, 30, 60⟩
private def original : Schedule := ⟨42, tick 30, tick 32, "UTC", tick 1, tick 2⟩
private def revised : Schedule := ⟨42, tick 40, tick 42, "UTC", tick 10, tick 11⟩
private def tutor : ActorId := 40
private def paymentTerms : PaymentTerms := ⟨.fixed (tick 50), .fixed (tick 60)⟩
private def replacementPaymentTerms : PaymentTerms := ⟨.fixed (tick 52), .fixed (tick 62)⟩

private theorem originalValid : original.valid := ⟨by decide, by decide, by decide, by decide⟩
private theorem revisedValid : revised.valid := ⟨by decide, by decide, by decide, by decide⟩

private def groupForm : PartOne :=
  { lesson := groupLesson
    place := ⟨1, groupLesson.id, 101, 201, 301, 401, 100, 100⟩
    contacts := ⟨"Spark", "provider", "student-channel", none, "coordinator", 50, "lead",
      none, none, 60, "reviewer", 70, "alternative", true, 80, "escalation"⟩
    rulesVersion := "1.5"
    confirmedAt := tick 4
    customerRepresentatives := []
    schedule := original
    serviceTerms := "agreed service"
    serviceItems := [1]
    discountBasis := none
    privateRoster := some 9
    rosterLock := some (tick 20)
    groupRescheduleCutoff := some (.fixed (tick 18))
    oneToOneAdvanceCutoff := none
    cancelChangeTerms := "change terms"
    noFaultTerms := "no-fault terms"
    applicableStartTerms := "start terms"
    tutorAgreementRef := "teaching agreement"
    absentGroupPlacePay := some 10
    materialsOrBundle := none
    materialsTermsRef := none
    materialsPayer := none
    deadlines := ⟨.fixed (tick 55), tick 60, none, paymentTerms, paymentTerms, paymentTerms,
      paymentTerms, .fixed (tick 70), tick 72, tick 65, tick 66, .fixed (tick 80)⟩ }

private theorem groupFormMatches : groupForm.matches := by
  simp [PartOne.matches, groupForm, groupLesson, original, paymentTerms, Place.matches,
    Place.validFees, Schedule.valid, Contacts.complete, PayAndReviewTerms.valid,
    PaymentTerms.valid, PaymentDeadline.valid, AdvanceWindow.validAt, Moment.by, Moment.before,
    tick]
  all_goals decide +kernel

private def register : GroupRegisterSnapshot := ⟨groupLesson.id, tick 10, [groupForm]⟩

private theorem registerConforms : register.conforms groupLesson := by
  refine ⟨rfl, rfl, by simp [register], by simp [register], by simp [register], ?_⟩
  simpa only [register, List.mem_singleton, forall_eq] using
    (show groupForm.lesson = groupLesson ∧ groupForm.matches ∧
      groupForm.confirmedAt.by (tick 10) from ⟨rfl, groupFormMatches, by decide⟩)

private def teachingTerms (f : PartOne) (actor : ActorId) (ref : String) : TutorAgreement :=
  { lesson := f.lesson.id
    provider := f.lesson.provider
    tutor := actor
    reference := ref
    termsAgreedAt := tick 2
    service := f.serviceTerms
    serviceItems := f.serviceItems
    fee := f.lesson.normalTutorFee
    payment := f.deadlines.tutorPay
    tutorResponsibilities := "provide teaching"
    providerResponsibilities := "arrange teaching"
    signatures := [⟨f.lesson.provider, ref, "provider signature"⟩, ⟨actor, ref, "tutor signature"⟩] }

private theorem teachingTermsSigned (f : PartOne) (actor : ActorId) (ref : String) :
    (teachingTerms f actor ref).signed := by
  intro signer h
  change signer ∈ [f.lesson.provider, actor] at h
  rcases List.mem_cons.mp h with same | rest
  · subst signer
    exact ⟨⟨f.lesson.provider, ref, "provider signature"⟩, by simp [teachingTerms],
      rfl, rfl, show "provider signature" ≠ "" by decide⟩
  · have eq : signer = actor := List.mem_singleton.mp rest
    subst signer
    exact ⟨⟨actor, ref, "tutor signature"⟩, by simp [teachingTerms], rfl, rfl,
      show "tutor signature" ≠ "" by decide⟩

private def consent (target : ConfirmationTarget) : Confirmation :=
  ⟨target, groupForm.place.id, groupForm.place.payer, tick 9⟩

private def notice (target : ConfirmationTarget) : Notice :=
  ⟨target, 50, groupForm.place.student, groupForm.contacts.studentNotice, tick 10⟩

private def tutorTarget : ConfirmationTarget := .replacementTutor groupLesson.id tutor
private def scheduleFor (changesDate : Bool) : Schedule := if changesDate then revised else original

private def replacement (changesDate : Bool) : TutorReplacement :=
  let next := scheduleFor changesDate
  { previous := original
    record :=
      ⟨groupLesson.id, next, groupLesson.coordinator, tick 8, [groupForm.place.id],
        [consent tutorTarget] ++ (if changesDate then [consent next.confirmationTarget] else []),
        [notice tutorTarget] ++ (if changesDate then [notice next.confirmationTarget] else []),
        some groupLesson.tutor, some tutor, none⟩
    agreedAt := tick 10
    effectiveAt := tick 11
    agreement := { teachingTerms groupForm tutor "replacement agreement" with
      fee := 80, payment := replacementPaymentTerms }
    accepted := ⟨next.confirmationTarget, tutor, tick 9⟩
    providerConsent := ⟨tutorTarget, groupLesson.provider, tick 9⟩
    noticeChannel := none }

private def change : AgreedScheduleChange :=
  { previous := original
    record := (replacement true).record
    approvals := [⟨revised.confirmationTarget, tutor, tick 9⟩,
      ⟨revised.confirmationTarget, groupLesson.provider, tick 9⟩]
    compliesWithOneToOneTerms := fun _ ↦ False }

private def beforeReplacement (base : StartEvidence) (booking : BookingEvidence) : StartEvidence :=
  { base with
    effectiveForms := []
    groupRoster := none
    bookings := [(groupForm, booking)]
    scheduleHistory := [original]
    groupRegisters := []
    verifiesGroupRegister := fun row ↦ row = register
    changes := []
    teachingBegan := none
    tutorReplacements := []
    academicTeamAt := fun id actor _ ↦ id = groupLesson.id ∧ actor = 50 }

private def observed (base : StartEvidence) (booking : BookingEvidence) : StartEvidence :=
  { beforeReplacement base booking with groupRegisters := [register] }

private def replaced (base : StartEvidence) (booking : BookingEvidence)
    (changesDate : Bool) : StartEvidence :=
  { observed base booking with
    tutorReplacements := [replacement changesDate]
    scheduleHistory := if changesDate then [original, revised] else [original]
    changes := if changesDate then [change] else [] }

private theorem originalAgreed (ev : StartEvidence)
    (earliest : ∀ row ∈ ev.scheduleHistory, row.lesson = groupLesson.id →
      original.effectiveAt.by row.effectiveAt)
    (stored : register ∈ ev.groupRegisters) (verified : ev.verifiesGroupRegister register) :
    ScheduleWasAgreed groupLesson ev original :=
  ⟨rfl, originalValid, Or.inr (Or.inl ⟨rfl, earliest, Or.inr
    ⟨register, stored, registerConforms, verified, groupForm, by simp [register], rfl⟩⟩)⟩

private theorem originalAtAgreement (base : StartEvidence) (booking : BookingEvidence) :
    EffectiveSchedule groupLesson (observed base booking) original (tick 10) := by
  have agreed := originalAgreed (observed base booking)
    (by simp [observed, beforeReplacement]; decide) (by simp [observed]) rfl
  refine ⟨rfl, ⟨by simp [observed, beforeReplacement], originalValid, by decide, ?_⟩,
    by change [original.effectiveAt].Nodup; simp, ?_⟩
  · intro row member _ _ _
    have eq : row = original := by simpa [observed, beforeReplacement] using member
    subst row
    decide
  · intro row member _ _
    have eq : row = original := by simpa [observed, beforeReplacement] using member
    exact eq ▸ agreed

private theorem matchesChange (base : StartEvidence) (booking : BookingEvidence)
    (changesDate : Bool) :
    (replacement changesDate).record.matchesFrom groupForm original groupLesson.tutor
      ((replaced base booking changesDate).academicTeamAt groupLesson.id) (tick 10) := by
  have notified (target : ConfirmationTarget) : NoticePerformed (notice target) target
      groupForm.place.student groupForm.contacts.studentNotice := ⟨rfl, rfl, rfl⟩
  have confirmed (target : ConfirmationTarget) :
      DesignatedConfirmation groupForm.place (consent target) := ⟨rfl, rfl⟩
  refine ⟨rfl, ?_, by simp [replacement], rfl, show (tick 8).by (tick 10) by decide,
    ?_, ?_, ?_, ?_, ?_⟩
  · cases changesDate
    · exact originalValid
    · exact revisedValid
  · intro changed
    cases changesDate
    · simp [replacement, scheduleFor] at changed
    · exact ⟨⟨consent revised.confirmationTarget, by simp [replacement, scheduleFor],
        confirmed _, rfl, by decide⟩, notice revised.confirmationTarget,
        by simp [replacement, scheduleFor], notified _, ⟨rfl, rfl⟩, by decide⟩
  · intro newTutor same
    injection same with eq
    subst newTutor
    exact ⟨⟨consent tutorTarget, by simp [replacement], confirmed _, rfl, by decide⟩,
      notice tutorTarget, by simp [replacement], notified _, ⟨rfl, rfl⟩, by decide⟩
  · intro _
    rfl
  · intro _
    cases changesDate <;> rfl
  · simp [replacement]

private theorem replacementConforms (base : StartEvidence) (booking : BookingEvidence)
    (changesDate : Bool) :
    (replacement changesDate).conforms groupLesson (replaced base booking changesDate) := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, originalValid, ?_, show (tick 10).by (tick 11) by decide,
    by simp [replaced, observed, beforeReplacement], rfl, rfl, rfl, rfl,
    show "replacement agreement" ≠ "" by decide, show 0 ≤ (80 : Amount) by decide,
    ⟨trivial, trivial⟩, show "provide teaching" ≠ "" by decide,
    show "arrange teaching" ≠ "" by decide, teachingTermsSigned _ _ _,
    show (tick 2).before (tick 9) by decide, ⟨rfl, rfl, show (tick 9).by (tick 10) by decide⟩,
    ⟨rfl, rfl, show (tick 9).by (tick 10) by decide⟩, by simp [replacement], ?_⟩
  · cases changesDate <;> rfl
  · cases changesDate
    · refine ⟨by simp [replacement, scheduleFor, replaced], originalValid, by decide, ?_⟩
      intro row member _ _ _
      have eq : row = original := by simpa [replaced] using member
      subst row
      decide
    · refine ⟨by simp [replacement, scheduleFor, replaced], revisedValid, by decide, ?_⟩
      intro row member _ _ _
      have which : row = original ∨ row = revised := by simpa [replaced] using member
      rcases which with rfl | rfl <;> decide
  · cases changesDate <;> simp [replaced, replacement]
  · cases changesDate
    · simp [replacement, scheduleFor]
    · have different : revised.confirmationTarget ≠ original.confirmationTarget := by decide
      simpa only [replacement, scheduleFor, ite_true, different, ite_false] using
        (show original.effectiveAt.before revised.effectiveAt ∧
          revised.effectiveAt = tick 11 ∧ revised.agreedAt = tick 10 ∧
          ∃ row ∈ (replaced base booking true).changes, row.previous = original ∧
            row.record = (replacement true).record from
          ⟨by decide, rfl, rfl, change, by simp [replaced], rfl, rfl⟩)
  · refine ⟨none, [groupForm], none, ?_, ?_, ?_, show tutor ≠ groupLesson.tutor by decide, ?_⟩
    · exact ⟨by simp [replaced, observed, beforeReplacement], register,
        by simp [replaced, observed], rfl, registerConforms, rfl, rfl⟩
    · intro seat member
      have eq : seat = groupForm.place.id := by simpa [replacement] using member
      exact ⟨groupForm, by simp, eq⟩
    · intro row member
      obtain rfl := List.mem_singleton.mp (show row ∈ [replacement changesDate] from member)
      exact fun h ↦ (by decide : ¬ (tick 11).before (tick 11)) h.2
    · intro f member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨show groupForm.confirmedAt.before (tick 10) by decide, rfl, rfl,
        matchesChange base booking changesDate⟩

private theorem replacementActive (base : StartEvidence) (booking : BookingEvidence)
    (changesDate : Bool) :
    (replaced base booking changesDate).effectiveReplacement groupLesson (tick 11)
      (some (replacement changesDate)) := by
  simp only [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement, replaced,
    replacement, groupLesson, List.filter_cons, List.filter_nil, beq_self_eq_true, ite_true,
    List.map_cons, List.map_nil, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true, true_and, List.mem_singleton, forall_eq]
  exact ⟨fun _ ↦ replacementConforms base booking changesDate, by decide,
    fun _ ↦ by decide⟩

private theorem bookingScoped (base : StartEvidence) (booking : BookingEvidence) :
    (∀ f, (f ∈ (beforeReplacement base booking).effectiveForms ∨
      ∃ b, (f, b) ∈ (beforeReplacement base booking).bookings) → f.lesson = groupLesson) ∧
    (∀ roster ∈ (beforeReplacement base booking).groupRoster, roster.lesson = groupLesson.id) ∧
    ∀ schedule ∈ (beforeReplacement base booking).scheduleHistory,
      schedule.lesson = groupLesson.id := by
  refine ⟨?_, by simp [beforeReplacement], by simp [beforeReplacement, original, groupLesson]⟩
  intro f member
  rcases member with fromForms | ⟨b, fromBookings⟩
  · simp [beforeReplacement] at fromForms
  · have eq : (f, b) = (groupForm, booking) := by simpa [beforeReplacement] using fromBookings
    exact congrArg (fun pair : PartOne × BookingEvidence ↦ pair.1.lesson) eq

/-- The provider gains a retained effective tutor while the agreed time and later lock stay intact. -/
theorem replaceBeforeLockWithoutReschedule (base : StartEvidence) (booking : BookingEvidence) :
    Workflow.Booking.Step (beforeReplacement base booking)
      (.replaceTutorBeforeLock groupLesson (replacement false) none register)
      (replaced base booking false) ∧
    (replaced base booking false).scheduleHistory = [original] ∧
    (replaced base booking false).groupRoster = none ∧
    EffectiveTutorAt groupLesson (replaced base booking false) (tick 11) tutor := by
  exact ⟨⟨bookingScoped base booking, rfl, rfl, registerConforms, rfl, by simp [beforeReplacement],
    originalAtAgreement base booking, rfl, replacementActive base booking false, rfl⟩,
    rfl, rfl, some (replacement false), replacementActive base booking false, rfl⟩

private theorem combinedChangeRecords (base : StartEvidence) (booking : BookingEvidence) :
    change.records groupLesson (replaced base booking true) none [groupForm] := by
  refine ⟨?_, rfl, revisedValid, by simp [replaced, change], rfl, by decide, by decide,
    by decide, ?_, by simp [replaced, observed, beforeReplacement], rfl, ?_, ?_, ?_⟩
  · exact ⟨by simp [replaced, observed, beforeReplacement], register,
      by simp [replaced, observed], rfl, registerConforms, rfl, rfl⟩
  · intro row member _ h
    have which : row = original ∨ row = revised := by simpa [replaced] using member
    rcases which with rfl | rfl
    · decide
    · exact False.elim ((by decide : ¬revised.effectiveAt.before revised.effectiveAt) h)
  · intro actor _
    exact ⟨replacement true, by simp [replaced], rfl, rfl, rfl, rfl,
      replacementConforms base booking true⟩
  · intro place member
    have same : place = groupForm.place.id := by simpa [change, replacement] using member
    exact ⟨groupForm, by simp, same⟩
  · simp [change, replacement]

private theorem originalAgreedAfterCombined (base : StartEvidence) (booking : BookingEvidence) :
    ScheduleWasAgreed groupLesson (replaced base booking true) original := by
  refine originalAgreed _ ?_ (by simp [replaced, observed]) rfl
  intro row member _
  have which : row = original ∨ row = revised := by simpa [replaced] using member
  rcases which with rfl | rfl <;> decide

private theorem combinedChangeAllowed (base : StartEvidence) (booking : BookingEvidence) :
    change.allowed groupLesson (replaced base booking true) := by
  constructor
  · change ([original].map (·.effectiveAt)).Nodup ∧
      ∀ row ∈ [original], ScheduleWasAgreed groupLesson (replaced base booking true) row
    exact ⟨by simp, by simpa using originalAgreedAfterCombined base booking⟩
  · left
    refine ⟨none, [groupForm], tutor, combinedChangeRecords base booking, ?_, ?_, ?_⟩
    · intro form member
      obtain rfl := List.mem_singleton.mp member
      refine ⟨.fixed (tick 18), rfl, ?_⟩
      simp [AdvanceWindow.allowsFrom, AdvanceWindow.allows, AdvanceWindow.validAt,
        groupForm, change, replacement, scheduleFor, revised, Moment.by, Moment.before, tick]
    · exact ⟨some (replacement true), replacementActive base booking true, rfl⟩
    · refine ⟨rfl, by simp, rfl, revisedValid, ?_, ?_, ?_⟩
      · intro person member
        have which : person = tutor ∨ person = groupLesson.provider := by simpa using member
        rcases which with rfl | rfl
        · exact ⟨⟨revised.confirmationTarget, tutor, tick 9⟩, by simp [change],
            rfl, rfl, by decide⟩
        · exact ⟨⟨revised.confirmationTarget, groupLesson.provider, tick 9⟩, by simp [change],
            rfl, rfl, by decide⟩
      · simp [replaced, observed, beforeReplacement]
      · intro place member
        obtain rfl := List.mem_singleton.mp member
        exact ⟨rfl, consent revised.confirmationTarget,
          by simp [change, replacement, scheduleFor], ⟨rfl, rfl⟩, rfl, by decide⟩

private theorem revisedEffective (base : StartEvidence) (booking : BookingEvidence) :
    EffectiveSchedule groupLesson (replaced base booking true) revised revised.effectiveAt := by
  have nextAgreed : ScheduleWasAgreed groupLesson (replaced base booking true) revised :=
    ⟨rfl, revisedValid, Or.inr (Or.inr ⟨change, by simp [replaced], rfl,
      (combinedChangeAllowed base booking).2⟩)⟩
  refine ⟨rfl, ⟨by simp [replaced], revisedValid, by decide, ?_⟩, ?_, ?_⟩
  · intro row member _ _ _
    have which : row = original ∨ row = revised := by simpa [replaced] using member
    rcases which with rfl | rfl <;> decide
  · change [original.effectiveAt, revised.effectiveAt].Nodup
    decide
  · intro row member _ _
    have which : row = original ∨ row = revised := by simpa [replaced] using member
    rcases which with rfl | rfl
    · exact originalAgreedAfterCombined base booking
    · exact nextAgreed

/-- A tutor replacement and rescheduling can use the same verified agreement register. -/
theorem replaceBeforeLockWithReschedule (s : Workflow.State) (base : StartEvidence)
    (booking : BookingEvidence) :
    let prior := { s.withCourse groupLesson.id (beforeReplacement base booking) with cancelled := [] }
    Workflow.Step prior
      (.booking (.replaceTutorBeforeLock groupLesson (replacement true) (some change) register))
      (prior.withCourse groupLesson.id (replaced base booking true)) ∧
    EffectiveSchedule groupLesson (replaced base booking true) revised revised.effectiveAt ∧
    EffectiveTutorAt groupLesson (replaced base booking true) revised.effectiveAt tutor := by
  let prior := { s.withCourse groupLesson.id (beforeReplacement base booking) with cancelled := [] }
  have stored : prior.course groupLesson.id = beforeReplacement base booking := by
    simp [prior, Workflow.State.course, Workflow.State.withCourse]
  have localStep : Workflow.Booking.Step (beforeReplacement base booking)
      (.replaceTutorBeforeLock groupLesson (replacement true) (some change) register)
      (replaced base booking true) :=
    ⟨bookingScoped base booking, rfl, rfl, registerConforms, rfl, by simp [beforeReplacement],
      originalAtAgreement base booking, ⟨rfl, rfl, originalAtAgreement base booking,
        combinedChangeAllowed base booking, revisedEffective base booking⟩,
      replacementActive base booking true, rfl⟩
  have live : (Workflow.Booking.Event.replaceTutorBeforeLock groupLesson
      (replacement true) (some change) register).usesEffectivePlaces
      (beforeReplacement base booking) [] := by
    simp [Workflow.Booking.Event.usesEffectivePlaces, Workflow.Cancellation.PlaceCancelledAt,
      register, beforeReplacement]
  exact ⟨Workflow.Step.booking (s := prior) trivial trivial (stored ▸ live)
    (stored ▸ localStep) rfl trivial trivial trivial,
    revisedEffective base booking, some (replacement true), replacementActive base booking true,
    rfl⟩

/-- The agreement register cannot include a place with a retained cancellation at that time. -/
theorem cancelledPlaceRejected (base : StartEvidence) (booking : BookingEvidence)
    (history : Workflow.Cancellation.History)
    (cancelled : Workflow.Cancellation.PlaceCancelledAt history groupForm.place register.atTime) :
    ¬Workflow.Booking.Event.usesEffectivePlaces
      (.replaceTutorBeforeLock groupLesson (replacement false) none register)
      (beforeReplacement base booking) history := by
  intro live
  exact live.1 groupForm (by simp [register]) cancelled

/-- An earlier live place cannot be omitted even if the supplied snapshot is independently marked. -/
theorem omittedLivePlaceRejected (base : StartEvidence) (booking : BookingEvidence) :
    let second := { groupForm with place := { groupForm.place with id := 2, student := 302 } }
    let earlier := { beforeReplacement base booking with bookings := [(groupForm, booking),
      (second, booking)] }
    ¬Workflow.Booking.Event.usesEffectivePlaces
      (.replaceTutorBeforeLock groupLesson (replacement false) none register) earlier [] := by
  dsimp only
  intro live
  let second := { groupForm with place := { groupForm.place with id := 2, student := 302 } }
  have required := live.2 second (by simp [beforeReplacement, second])
    (show groupForm.confirmedAt.by register.atTime by decide)
    (by simp [Workflow.Cancellation.PlaceCancelledAt])
  have same := congrArg (fun form : PartOne ↦ form.place.id) (List.mem_singleton.mp required)
  exact (by decide : (2 : PlaceId) ≠ 1) same

theorem wrongAgreementCutRejected (base next : StartEvidence) (booking : BookingEvidence)
    (proposal : GroupRegisterSnapshot) (wrongCut : proposal.atTime ≠ (replacement false).agreedAt) :
    ¬Workflow.Booking.Step (beforeReplacement base booking)
      (.replaceTutorBeforeLock groupLesson (replacement false) none proposal) next :=
  fun step ↦ wrongCut step.2.2.1

theorem unverifiedReplacementRegisterRejected (base next : StartEvidence)
    (booking : BookingEvidence) (proposal : GroupRegisterSnapshot) (unverified : proposal ≠ register) :
    ¬Workflow.Booking.Step (beforeReplacement base booking)
      (.replaceTutorBeforeLock groupLesson (replacement false) none proposal) next :=
  fun step ↦ unverified step.2.2.2.2.1

private def newPlaceForm : PartOne :=
  { groupForm with
    place := ⟨2, groupLesson.id, 102, 202, 302, 402, 100, 100⟩
    confirmedAt := ⟨11, 4⟩
    tutorAtBooking := some (tutor, 80)
    tutorAgreementRef := "replacement agreement"
    deadlines := { groupForm.deadlines with tutorPay := replacementPaymentTerms } }

private def enrollmentPlan (second : Bool) : Roster :=
  ⟨groupLesson.id, 9, if second then [groupForm.place, newPlaceForm.place] else [groupForm.place],
    tick 20⟩

private def enrollmentForm (second : Bool) : PartOne :=
  if second then newPlaceForm else groupForm

private def enrollmentDebit (second : Bool) : CreditPosting :=
  let form := enrollmentForm second
  ⟨form.place.id, form.place.account, .lessonDebit groupLesson.id form.place.id,
    form.place.feePayable, form.confirmedAt⟩

private def enrollmentOpening (_ : AccountId) : Amount := 100

private def enrollmentCredit : CreditRecords :=
  { topUps := []
    grants := []
    topUpReturns := []
    closed := []
    ownsAccount := fun _ _ ↦ False
    courseProviderAt := fun _ _ ↦ False
    verifiedRefunds := []
    payments := { posted := [], returned := [] }
    paymentAuthorities := {
      corePartner := fun _ _ ↦ False
      initialFinding := fun _ _ _ ↦ False
      reviewer := fun _ _ _ ↦ False
      approvesPayment := fun _ _ _ ↦ False
      interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
      originalDecisionMaker := fun _ ↦ none
      originalSettlementProposers := fun _ ↦ []
      originalSettlementApprovers := fun _ ↦ [] } }

private def enrollmentSigned (second : Bool) : Moment := if second then ⟨11, 2⟩ else tick 3
private def enrollmentProvided (second : Bool) : Moment := if second then ⟨11, 1⟩ else tick 1

private def enrollmentSignatures (second : Bool) : Signatures :=
  let form := enrollmentForm second
  let provided := enrollmentProvided second
  let signed := enrollmentSigned second
  ⟨form.lesson.id, form.place.id, form.lesson.coordinator, form.place.customer,
    provided, provided, form.lesson.provider, signed, form.agreedTutor, signed,
    signed, form.place.customer, some (form.place.payer, signed)⟩

private def enrollmentDocuments (second : Bool) : List BookingTermDocument :=
  let form := enrollmentForm second
  [⟨.rules form.rulesVersion, 1⟩, ⟨.tutorAgreement form.tutorAgreementRef, 2⟩]

private def enrollmentProvision (second : Bool) (recipient : ActorId) : BookingTermsProvision :=
  let form := enrollmentForm second
  let provided := enrollmentProvided second
  ⟨form, form.lesson.coordinator, recipient, provided, provided, enrollmentDocuments second⟩

private def enrollmentAgreement (second : Bool) : TutorAgreement :=
  let form := enrollmentForm second
  { teachingTerms form form.agreedTutor form.tutorAgreementRef with fee := form.agreedTutorFee }

private def enrollmentBooking (second : Bool) (funding : FundingCheck) : BookingEvidence :=
  let form := enrollmentForm second
  ⟨enrollmentSignatures second, enrollmentAgreement second,
    ⟨form.lesson.id, form.lesson.provider, form.applicableStartTerms, enrollmentProvided second,
      true⟩, funding, some (enrollmentDebit second), enrollmentDocuments second,
    [enrollmentProvision second form.place.customer, enrollmentProvision second form.agreedTutor]⟩

private theorem enrollmentMatches (second : Bool) : (enrollmentForm second).matches := by
  cases second
  · exact groupFormMatches
  · simp [PartOne.matches, enrollmentForm, newPlaceForm, groupForm, groupLesson, original,
      paymentTerms, replacementPaymentTerms, Place.matches, Place.validFees, Schedule.valid,
      Contacts.complete, PayAndReviewTerms.valid, PaymentTerms.valid, PaymentDeadline.valid,
      AdvanceWindow.validAt, Moment.by, Moment.before, tick]
    all_goals decide +kernel

private theorem enrollmentSignaturesValid (second : Bool) :
    (enrollmentSignatures second).valid (enrollmentForm second)
      (some (enrollmentDebit second).point) := by
  refine ⟨rfl, rfl, rfl, Or.inl rfl, rfl, rfl, Or.inl rfl, fun _ ↦ rfl, ?_, ?_⟩
  · intro acceptance exactPayer
    exact (congrArg Prod.fst (Option.some.inj exactPayer)).symm
  · cases second <;> simp [TermsProvidedInTime, enrollmentSignatures, enrollmentDebit,
      enrollmentForm, enrollmentSigned, enrollmentProvided, groupForm, newPlaceForm,
      Moment.before, tick]

private theorem enrollmentAgreementValid (second : Bool) :
    (enrollmentAgreement second).agreedBeforeAcceptance (enrollmentForm second)
      (enrollmentSignatures second) := by
  refine ⟨rfl, rfl, rfl, rfl, teachingTermsSigned _ _ _, ?_, rfl, rfl, rfl, rfl,
    show "provide teaching" ≠ "" by decide, show "arrange teaching" ≠ "" by decide⟩
  cases second <;> decide

private theorem enrollmentTermsProvided (second : Bool) (funding : FundingCheck) :
    (enrollmentBooking second funding).providedAgreedTerms (enrollmentForm second) := by
  let form := enrollmentForm second
  refine ⟨?_, ⟨enrollmentProvision second form.place.customer, by simp [enrollmentBooking, form],
      ⟨rfl, rfl, rfl, fun _ member ↦ member⟩, rfl, rfl⟩,
    enrollmentProvision second form.agreedTutor, by simp [enrollmentBooking, form],
    ⟨rfl, rfl, rfl, fun _ member ↦ member⟩, ?_⟩
  · intro reference member
    have which : reference = .rules form.rulesVersion ∨
        reference = .tutorAgreement form.tutorAgreementRef := by
      cases second <;> simpa [form, enrollmentForm, groupForm, newPlaceForm] using member
    rcases which with rfl | rfl
    · exact ⟨⟨.rules form.rulesVersion, 1⟩,
        by simp [enrollmentBooking, enrollmentDocuments, form], rfl⟩
    · exact ⟨⟨.tutorAgreement form.tutorAgreementRef, 2⟩,
        by simp [enrollmentBooking, enrollmentDocuments, form], rfl⟩
  · cases second <;> simp [TermsProvidedInTime, enrollmentProvision, enrollmentProvided,
      enrollmentBooking, enrollmentSignatures, enrollmentSigned, enrollmentDebit, enrollmentForm,
      groupForm, newPlaceForm, Moment.before, tick]

private theorem enrollmentPlanValid (second : Bool) :
    (enrollmentPlan second).valid groupLesson original.start := by
  cases second <;> simp [Roster.valid, enrollmentPlan, newPlaceForm, groupForm, groupLesson,
    Place.matches, original, tick, Moment.by, Moment.before]

private theorem enrollmentUsesPlan (second : Bool) :
    FormUsesRoster (enrollmentForm second) (enrollmentPlan second) := by
  cases second <;> exact ⟨by simp [enrollmentForm, enrollmentPlan], rfl, rfl⟩

private def enrollmentLedger (second : Bool) : List CreditPosting :=
  if second then [enrollmentDebit false, enrollmentDebit true] else [enrollmentDebit false]

private theorem enrollmentCreditValid (second : Bool) (visible : Moment → Prop) :
    ValidCreditHistory enrollmentOpening (enrollmentLedger second) enrollmentCredit visible := by
  cases second <;>
    simp [ValidCreditHistory, enrollmentOpening, enrollmentLedger, enrollmentCredit,
      CreditEvidence.CreditOriginsValid, PaymentHistory.distinctReceipts, returnedFrom,
      balanceBefore, sumAmountsWhere, enrollmentDebit, enrollmentForm, newPlaceForm,
      groupForm, groupLesson, Moment.by, Moment.before, tick]
  all_goals exact ⟨by decide +kernel, fun _ ↦ by decide +kernel⟩

private theorem enrollmentLedgerThrough (second both : Bool) (includes : second = true → both = true) :
    (enrollmentLedger both).filter
      (fun posting ↦ decide (posting.point.by (enrollmentForm second).confirmedAt)) =
      enrollmentLedger second := by
  cases second <;> cases both <;> simp_all [enrollmentLedger, enrollmentDebit, enrollmentForm,
    groupForm, newPlaceForm, Moment.by, Moment.before, tick]

private theorem enrollmentEligible (second both : Bool) (includes : second = true → both = true)
    (funding : FundingCheck)
    (reads : funding.readsForm (enrollmentForm second))
    (secures : funding.securedBefore groupLesson (enrollmentPlan second).places
      (enrollmentForm second).confirmedAt)
    (beforeSignature : funding.checkedAt.before (enrollmentSigned second))
    (began : Option Moment)
    (beforeStart : ∀ point, began = some point → (enrollmentForm second).confirmedAt.before point) :
    CanConfirmPlace (enrollmentForm second) (enrollmentBooking second funding)
      (some (enrollmentPlan second)) enrollmentOpening (enrollmentLedger both)
      enrollmentCredit [] began := by
  refine ⟨enrollmentMatches second, ?_, rfl, rfl, rfl, rfl, ?_, beforeStart,
    enrollmentSignaturesValid second, enrollmentAgreementValid second, ?_, ?_, ?_, ?_, reads, ?_,
    beforeSignature, beforeSignature, ?_, ?_, ?_, enrollmentTermsProvided second funding⟩
  · cases second <;> exact ⟨enrollmentPlanValid _, enrollmentUsesPlan _⟩
  · change (enrollmentProvided second).before (enrollmentForm second).confirmedAt
    cases second <;> decide
  · change (enrollmentSigned second).by (enrollmentForm second).confirmedAt
    cases second <;> decide
  · change (enrollmentSigned second).by (enrollmentForm second).confirmedAt
    cases second <;> decide
  · change (enrollmentSigned second).by (enrollmentForm second).confirmedAt
    cases second <;> decide
  · intro acceptance exactPayer
    have known := congrArg Prod.snd (Option.some.inj exactPayer)
    rw [← known]
    cases second <;> decide
  · cases second <;> exact secures
  · rw [enrollmentLedgerThrough second both includes]
    exact enrollmentCreditValid _ _
  · refine ⟨enrollmentMatches second, ?_, ?_, rfl⟩
    · rw [enrollmentLedgerThrough second both includes]
      unfold PaidInFull
      cases second <;> decide +kernel
    · intro zero
      cases second <;> exact ((by decide : (100 : Amount) ≠ 0) zero).elim
  · cases second <;> cases both
    · exact ⟨by decide +kernel, (enrollmentMatches false).2.2.1, by decide, rfl, rfl, rfl, rfl,
        by decide +kernel⟩
    · exact ⟨by decide +kernel, (enrollmentMatches false).2.2.1, by decide, rfl, rfl, rfl, rfl,
        by decide +kernel⟩
    · cases includes rfl
    · exact ⟨by decide +kernel, (enrollmentMatches true).2.2.1, by decide, rfl, rfl, rfl, rfl,
        by decide +kernel⟩

private def enrollmentBase (base : StartEvidence) : StartEvidence :=
  { base with
    openingCredit := enrollmentOpening
    creditRecords := enrollmentCredit
    ledger := enrollmentLedger false
    discounts := []
    tutorPayAmendments := {}
    rosterReview := none
    bookedRosters := [(groupForm, enrollmentPlan false)] }

private def openEnrollment (base : StartEvidence) (firstFunding : FundingCheck) : StartEvidence :=
  replaced (enrollmentBase base) (enrollmentBooking false firstFunding) false

private def enrolled (base : StartEvidence) (firstFunding nextFunding : FundingCheck) :
    StartEvidence :=
  { openEnrollment base firstFunding with
    ledger := enrollmentLedger true
    bookings := [(groupForm, enrollmentBooking false firstFunding),
      (newPlaceForm, enrollmentBooking true nextFunding)]
    bookedRosters := [(groupForm, enrollmentPlan false), (newPlaceForm, enrollmentPlan true)] }

private theorem sameScheduleAt (ev : StartEvidence) (history : ev.scheduleHistory = [original])
    (stored : register ∈ ev.groupRegisters) (verified : ev.verifiesGroupRegister register)
    (point : Moment) (effective : original.effectiveAt.by point) :
    EffectiveSchedule groupLesson ev original point := by
  have agreed := originalAgreed ev (by simp [history, Moment.by]) stored verified
  refine ⟨rfl, ⟨by simp [history], originalValid, effective, ?_⟩,
    by simp [history, original, groupLesson], ?_⟩
  · simp [history, Moment.by]
  · simpa [history] using (fun (_ : original.lesson = groupLesson.id)
        (_ : original.effectiveAt.by point) ↦ agreed)

private theorem replacementSeen (ev : StartEvidence) (history :
    ev.tutorReplacements = [replacement false]) (agreement : (replacement false).conforms groupLesson ev)
    (point : Moment) (effective : (replacement false).effectiveAt.by point) :
    ev.effectiveReplacement groupLesson point (some (replacement false)) := by
  refine ⟨by simp [history, replacement, groupLesson], ?_, ?_⟩
  · simp [history, replacement, groupLesson]
    exact fun _ ↦ agreement
  · refine ⟨by simp [history], ⟨rfl, effective⟩, ?_⟩
    intro row member _
    obtain rfl := List.mem_singleton.mp (history ▸ member)
    exact Or.inr rfl

private theorem enrollmentBinding (ev : StartEvidence)
    (active : ev.effectiveReplacement groupLesson newPlaceForm.confirmedAt
      (some (replacement false)))
    (noAmendments : ev.tutorPayAmendments = {}) :
    ev.readsTutorAtConfirmation newPlaceForm := by
  refine ⟨some (replacement false), active, rfl, rfl, rfl, by decide, Or.inl ⟨?_, rfl⟩⟩
  simp [noAmendments]

private theorem newPlaceStep (base : StartEvidence) (firstFunding nextFunding : FundingCheck)
    (reads : nextFunding.readsForm newPlaceForm)
    (secures : nextFunding.securedBefore groupLesson (enrollmentPlan true).places
      newPlaceForm.confirmedAt)
    (checked : nextFunding.checkedAt.before (enrollmentSigned true)) :
    Workflow.Booking.Step (openEnrollment base firstFunding)
      (.confirmPlace newPlaceForm (enrollmentBooking true nextFunding) (some (enrollmentPlan true))
        (.debit (enrollmentDebit true)))
      (enrolled base firstFunding nextFunding) := by
  let prior := openEnrollment base firstFunding
  have onlyFirst (form : PartOne)
      (member : form ∈ prior.effectiveForms ∨ ∃ booking, (form, booking) ∈ prior.bookings) :
      form = groupForm := by
    rcases member with fromForms | ⟨booking, fromBookings⟩
    · simp [prior, openEnrollment, replaced, observed, beforeReplacement] at fromForms
    · exact congrArg Prod.fst (List.mem_singleton.mp fromBookings)
  refine ⟨bookingScoped (enrollmentBase base) (enrollmentBooking false firstFunding),
    ?_, Or.inr (sameScheduleAt prior rfl (by simp [prior, openEnrollment, replaced, observed])
      rfl _ (by decide)), by decide, ⟨by decide, ?_⟩, ⟨rfl, ?_⟩,
    enrollmentEligible true true (fun _ ↦ rfl) nextFunding reads secures checked none (by simp),
    enrollmentBinding prior (replacementSeen _ rfl
      (replacementConforms (enrollmentBase base) (enrollmentBooking false firstFunding)
        false) _ (by decide)) rfl, ?_⟩
  · intro row member
    obtain rfl := List.mem_singleton.mp
      (show row ∈ [(groupForm, enrollmentBooking false firstFunding)] from member)
    change groupForm.place.id ≠ newPlaceForm.place.id
    decide
  · intro form known
    rw [onlyFirst _ known]
    exact ⟨by simp [enrollmentPlan], rfl, rfl⟩
  · intro debit member
    obtain rfl := List.mem_singleton.mp (show debit ∈ enrollmentLedger false from member)
    decide
  · rfl

private def lateBookingEvent (funding : FundingCheck) : Workflow.Booking.Event :=
  .confirmPlace newPlaceForm (enrollmentBooking true funding) (some (enrollmentPlan true))
    (.debit (enrollmentDebit true))

/-- The new payer's place confirms through the shared workflow using the replacement's signed
    terms, while the old place, old booking plan and replacement consent remain on file. -/
theorem newPlaceAfterEffectiveReplacement (s : Workflow.State) (base : StartEvidence)
    (firstFunding nextFunding : FundingCheck)
    (reads : nextFunding.readsForm newPlaceForm)
    (secures : nextFunding.securedBefore groupLesson (enrollmentPlan true).places
      newPlaceForm.confirmedAt)
    (checked : nextFunding.checkedAt.before (enrollmentSigned true))
    (funds : Workflow.Reserves.FundingContextMatches s.activeReserves nextFunding.funds)
    (noPendingBudget : s.materials.liveMaterialBudgetsAt s.holds.payments groupLesson.id
      newPlaceForm.confirmedAt s.materialsPrincipalContext = [])
    (receipts : (lateBookingEvent nextFunding).readsFundingReceipts s.holds.payments) :
    let prior := s.withCourse groupLesson.id (openEnrollment base firstFunding)
    let result := { prior.withCourse groupLesson.id (enrolled base firstFunding nextFunding) with
      activeReserves := Workflow.Reserves.reserve prior.activeReserves nextFunding.funds }
    Workflow.Step prior (.booking (lateBookingEvent nextFunding)) result ∧
    (result.course groupLesson.id).bookings =
      [(groupForm, enrollmentBooking false firstFunding),
        (newPlaceForm, enrollmentBooking true nextFunding)] ∧
    (result.course groupLesson.id).bookedRosters =
      [(groupForm, enrollmentPlan false), (newPlaceForm, enrollmentPlan true)] ∧
    (result.course groupLesson.id).groupRegisters = [register] ∧
    (result.course groupLesson.id).tutorReplacements = [replacement false] ∧
    result.credit.ledger = enrollmentLedger true := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
  · have stored : (s.withCourse groupLesson.id (openEnrollment base firstFunding)).course
        groupLesson.id = openEnrollment base firstFunding := by
      simp [Workflow.State.course, Workflow.State.withCourse]
    exact Workflow.Step.booking funds trivial trivial
      (stored ▸ newPlaceStep base firstFunding nextFunding reads secures checked)
      (Or.inl rfl) trivial (by
        intro pending
        exact (pending noPendingBudget).elim) receipts
  · simp [Workflow.State.course, Workflow.State.withCourse, enrolled]
  · simp [Workflow.State.course, Workflow.State.withCourse, enrolled]
  · simp [Workflow.State.course, Workflow.State.withCourse, enrolled, openEnrollment, replaced,
      observed]
  · simp [Workflow.State.course, Workflow.State.withCourse, enrolled, openEnrollment, replaced]

private def outdatedPlaceForm : PartOne :=
  { newPlaceForm with
    tutorAtBooking := none
    tutorAgreementRef := groupForm.tutorAgreementRef
    deadlines := groupForm.deadlines }

/-- Original tutor terms alone cannot confirm a new place once the replacement has taken effect. -/
theorem oldTutorCannotConfirmNewPlace (base after : StartEvidence)
    (firstFunding : FundingCheck) (booking : BookingEvidence)
    (payment : Workflow.Booking.ConfirmationPayment) :
    ¬Workflow.Booking.Step (openEnrollment base firstFunding)
      (.confirmPlace outdatedPlaceForm booking (some (enrollmentPlan true)) payment) after := by
  intro attempted
  obtain ⟨_, _, _, _, _, _, _, binding, _⟩ := attempted
  obtain ⟨active, valid, matched⟩ := binding
  cases active with
  | none =>
    exact valid.2.2 (replacement false)
      (by simp [openEnrollment, replaced]) ⟨rfl, by decide⟩
  | some row =>
    obtain rfl := List.mem_singleton.mp
      (show row ∈ [replacement false] from valid.2.2.1)
    exact (by decide : outdatedPlaceForm.agreedTutor ≠ tutor) matched.1

private def lockedEnrollment (base : StartEvidence) (firstFunding nextFunding : FundingCheck) :
    StartEvidence :=
  { enrolled base firstFunding nextFunding with
    effectiveForms := [groupForm, newPlaceForm]
    groupRoster := some (enrollmentPlan true) }

private theorem replacementConformsAfterLock (base : StartEvidence)
    (firstFunding nextFunding : FundingCheck) :
    (replacement false).conforms groupLesson (lockedEnrollment base firstFunding nextFunding) := by
  have prior := replacementConforms (enrollmentBase base) (enrollmentBooking false firstFunding) false
  obtain ⟨recordLesson, scheduleLesson, scheduleEffective, priorSchedule, priorLesson, priorValid,
    scheduleChange, timing, beforeTeaching, sameBooking, tutorRecorded, sameLesson, sameProvider,
    reference, nonnegative, payment, tutorDuties, providerDuties, signed, agreedBefore, accepted,
    providerConsent, channel, historical⟩ := prior
  refine ⟨recordLesson, scheduleLesson, scheduleEffective, priorSchedule, priorLesson, priorValid,
    scheduleChange, timing, beforeTeaching, sameBooking, tutorRecorded, sameLesson, sameProvider,
    reference, nonnegative, payment, tutorDuties, providerDuties, signed, agreedBefore, accepted,
    providerConsent, channel, ?_⟩
  obtain ⟨roster, forms, priorReplacement, arrangement, scope, latest, distinct, consents⟩ :=
    historical
  have sameForms : forms = [groupForm] := by
    cases roster with
    | none =>
      obtain ⟨_, row, present, _, _, _, same⟩ := arrangement
      obtain rfl := List.mem_singleton.mp (show row ∈ [register] from present)
      exact same
    | some locked =>
      obtain ⟨⟨row, present, _⟩, _⟩ := arrangement
      have impossible : row ∈ (none : Option Roster) := present
      simp at impossible
  subst forms
  refine ⟨none, [groupForm], priorReplacement, ⟨?_, register,
    by simp [lockedEnrollment, enrolled, openEnrollment, replaced, observed],
    rfl, registerConforms, rfl, rfl⟩, scope, latest, distinct, consents⟩
  intro roster member
  obtain rfl := Option.mem_some_iff.mp (show roster ∈ some (enrollmentPlan true) from member)
  decide

private theorem formsInLockedEnrollment (base : StartEvidence)
    (firstFunding nextFunding : FundingCheck) :
    RegisterMatchesForms (enrollmentPlan true) (lockedEnrollment base firstFunding nextFunding)
      groupLesson := by
  have onlyEnrolled (form : PartOne) (known : form ∈ [groupForm, newPlaceForm]) :
      form = groupForm ∨ form = newPlaceForm := by simpa using known
  refine ⟨rfl, rfl, ⟨by simp [lockedEnrollment], ?_⟩, rfl, ?_, ?_, ?_⟩
  · intro form known
    rcases onlyEnrolled form known with rfl | rfl
    · exact ⟨rfl, groupFormMatches⟩
    · exact ⟨rfl, enrollmentMatches true⟩
  · intro place chosen
    have same : place = groupForm.place ∨ place = newPlaceForm.place := by
      simpa [enrollmentPlan] using chosen
    rcases same with rfl | rfl
    · exact ⟨groupForm, by simp [lockedEnrollment], rfl⟩
    · exact ⟨newPlaceForm, by simp [lockedEnrollment], rfl⟩
  · change ([groupForm.place.id, newPlaceForm.place.id]).Nodup
    decide
  · intro form known
    rcases onlyEnrolled form known with rfl | rfl
    · exact ⟨by simp [enrollmentPlan], rfl, rfl⟩
    · exact enrollmentUsesPlan true

private theorem originalBookingBinding (ev : StartEvidence)
    (history : ev.tutorReplacements = [replacement false]) :
    ev.readsTutorAtConfirmation groupForm := by
  refine ⟨none, ?_, rfl, rfl⟩
  simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement, history,
    replacement, groupLesson, groupForm, Moment.by, Moment.before, tick]

private theorem historyAfterLock (base : StartEvidence) (firstFunding nextFunding : FundingCheck)
    (second : Bool)
    (reads : (if second then nextFunding else firstFunding).readsForm (enrollmentForm second))
    (secures : (if second then nextFunding else firstFunding).securedBefore
      groupLesson (enrollmentPlan second).places (enrollmentForm second).confirmedAt)
    (checked : (if second then nextFunding else firstFunding).checkedAt.before
      (enrollmentSigned second)) (observed : Moment := tick 20) :
    (lockedEnrollment base firstFunding nextFunding).confirmedBookingFor
      (enrollmentForm second) (some (enrollmentPlan true)) observed := by
  let ev := lockedEnrollment base firstFunding nextFunding
  let funding := if second then nextFunding else firstFunding
  refine ⟨enrollmentBooking second funding, some (enrollmentPlan second),
    ?_, Or.inl ⟨enrollmentPlan second, by simp, ?_⟩,
    enrollmentEligible second true (fun _ ↦ rfl) funding reads secures checked none (by simp),
    ?_⟩
  · cases second <;> simp [lockedEnrollment, enrolled, funding, enrollmentForm]
  · cases second <;> simp [lockedEnrollment, enrolled, enrollmentForm]
  · cases second
    · exact originalBookingBinding ev rfl
    · exact enrollmentBinding ev (replacementSeen ev rfl
        (replacementConformsAfterLock base firstFunding nextFunding) _ (by decide)) rfl

private theorem sameBookingLesson (base : StartEvidence) (firstFunding nextFunding : FundingCheck)
    {form : PartOne} {booking : BookingEvidence}
    (member : (form, booking) ∈ (enrolled base firstFunding nextFunding).bookings) :
    form = groupForm ∨ form = newPlaceForm := by
  have entries : (form, booking) = (groupForm, enrollmentBooking false firstFunding) ∨
      (form, booking) = (newPlaceForm, enrollmentBooking true nextFunding) := by
    simpa [enrolled] using member
  exact entries.imp (congrArg Prod.fst) (congrArg Prod.fst)

private theorem scopeOfEnrollment (base : StartEvidence) (firstFunding nextFunding : FundingCheck) :
    let ev := enrolled base firstFunding nextFunding
    (∀ form, (form ∈ ev.effectiveForms ∨ ∃ booking, (form, booking) ∈ ev.bookings) →
      form.lesson = groupLesson) ∧
    (∀ roster ∈ ev.groupRoster, roster.lesson = groupLesson.id) ∧
    ∀ schedule ∈ ev.scheduleHistory, schedule.lesson = groupLesson.id := by
  refine ⟨?_, by simp [enrolled, openEnrollment, replaced, observed, beforeReplacement],
    by simp [enrolled, openEnrollment, replaced, original, groupLesson]⟩
  intro form stored
  rcases stored with inForms | ⟨booking, inBookings⟩
  · simp [enrolled, openEnrollment, replaced, observed, beforeReplacement] at inForms
  · rcases sameBookingLesson base firstFunding nextFunding inBookings with rfl | rfl <;> rfl

/-- Fixing the final roster still reads the distinct plans in force when each place was agreed. -/
theorem laterPlaceInLockedEnrollment (base : StartEvidence) (firstFunding nextFunding : FundingCheck)
    (readFirst : firstFunding.readsForm groupForm)
    (secureFirst : firstFunding.securedBefore groupLesson (enrollmentPlan false).places
      groupForm.confirmedAt)
    (checkFirst : firstFunding.checkedAt.before (enrollmentSigned false))
    (readNext : nextFunding.readsForm newPlaceForm)
    (secureNext : nextFunding.securedBefore groupLesson (enrollmentPlan true).places
      newPlaceForm.confirmedAt)
    (checkNext : nextFunding.checkedAt.before (enrollmentSigned true)) :
    Workflow.Booking.Step (enrolled base firstFunding nextFunding)
      (.fixGroupRoster groupLesson (enrollmentPlan true) [groupForm, newPlaceForm])
      (lockedEnrollment base firstFunding nextFunding) := by
  let ev := lockedEnrollment base firstFunding nextFunding
  have scheduled (point : Moment) (effective : original.effectiveAt.by point) :
      EffectiveSchedule groupLesson ev original point :=
    sameScheduleAt ev rfl
      (by simp [ev, lockedEnrollment, enrolled, openEnrollment, replaced, observed]) rfl point
      effective
  refine ⟨scopeOfEnrollment base firstFunding nextFunding, rfl, original,
    formsInLockedEnrollment base firstFunding nextFunding, enrollmentPlanValid true,
    scheduled _ (by decide), ?_, ?_, rfl⟩
  · intro form stored
    have which : form = groupForm ∨ form = newPlaceForm := by
      simpa [enrolled, openEnrollment, replaced, observed, beforeReplacement] using stored
    rcases which with rfl | rfl
    · exact ⟨scheduled _ (by decide), Or.inl ⟨enrollmentBooking false firstFunding,
        by simp [enrolled]⟩⟩
    · exact ⟨scheduled _ (by decide), Or.inl ⟨enrollmentBooking true nextFunding,
        by simp [enrolled]⟩⟩
  · intro row stored
    have which := sameBookingLesson base firstFunding nextFunding stored
    rcases which with same | same
    · rw [same]
      exact ⟨by simp, historyAfterLock base firstFunding nextFunding false
        readFirst secureFirst checkFirst⟩
    · rw [same]
      exact ⟨by simp, historyAfterLock base firstFunding nextFunding true
        readNext secureNext checkNext⟩

private def studentScheduleNotice (second : Bool) : Notice :=
  let form := enrollmentForm second
  ⟨original.confirmationTarget, 50, form.place.student, form.contacts.studentNotice, tick 21⟩

private def tutorScheduleNotice : Notice :=
  ⟨original.confirmationTarget, 50, tutor, "tutor-channel", tick 21⟩

private theorem enrollmentRosterReady (base : StartEvidence) (firstFunding nextFunding : FundingCheck) :
    (lockedEnrollment base firstFunding nextFunding).rosterFormsAt groupLesson original.start
      (some (enrollmentPlan true)) [groupForm, newPlaceForm] := by
  let ev := lockedEnrollment base firstFunding nextFunding
  have byForm (second : Bool) : ev.formForRoster groupLesson (enrollmentPlan true)
      (enrollmentForm second) := by
    have listed : enrollmentForm second ∈ ev.effectiveForms := by
      cases second <;> simp [ev, lockedEnrollment, enrollmentForm]
    refine ⟨?_, enrollmentMatches second, ?_, Or.inl listed, fun _ _ _ ↦ listed⟩
    · cases second <;> rfl
    · cases second
      · exact ⟨by simp [enrollmentPlan, enrollmentForm], rfl, rfl⟩
      · exact enrollmentUsesPlan true
  have byPlace (place : Place) (member : place ∈ (enrollmentPlan true).places) :
      ∃ second, (enrollmentForm second).place = place := by
    have which : place = groupForm.place ∨ place = newPlaceForm.place := by
      simpa [enrollmentPlan] using member
    rcases which with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  refine ⟨⟨⟨enrollmentPlan true, formsInLockedEnrollment base firstFunding nextFunding,
    ?_, rfl⟩, ?_⟩, by decide, ?_, ?_⟩
  · obtain ⟨lesson, _, others⟩ := enrollmentPlanValid true
    exact ⟨lesson, Or.inr rfl, others⟩
  · intro place member
    obtain ⟨second, exactPlace⟩ := byPlace place member
    exact ⟨enrollmentForm second, byForm second, exactPlace⟩
  · intro f member
    have which : f = groupForm ∨ f = newPlaceForm := by simpa using member
    rcases which with rfl | rfl
    · exact byForm false
    · exact byForm true
  · intro place member
    obtain ⟨second, exactPlace⟩ := byPlace place member
    exact ⟨enrollmentForm second, by cases second <;> simp [enrollmentForm], exactPlace⟩

/-- The confirmed new place can take the lesson. It receives the usual schedule notice.
    The replacement notice and its payer consent remain specific to the earlier place. -/
theorem startAfterReplacementEnrollment (base : StartEvidence)
    (firstFunding nextFunding : FundingCheck)
    (readFirst : firstFunding.readsForm groupForm)
    (secureFirst : firstFunding.securedBefore groupLesson (enrollmentPlan false).places
      groupForm.confirmedAt)
    (checkFirst : firstFunding.checkedAt.before (enrollmentSigned false))
    (readNext : nextFunding.readsForm newPlaceForm)
    (secureNext : nextFunding.securedBefore groupLesson (enrollmentPlan true).places
      newPlaceForm.confirmedAt)
    (checkNext : nextFunding.checkedAt.before (enrollmentSigned true)) :
    let ev := { lockedEnrollment base firstFunding nextFunding with
      notices := [studentScheduleNotice false, studentScheduleNotice true, tutorScheduleNotice] }
    Workflow.Booking.StartPermitted ev groupLesson original original.start
      [newPlaceForm.place.student] ∧ newPlaceForm.place.id ∉ (replacement false).record.scope := by
  let ev := { lockedEnrollment base firstFunding nextFunding with
    notices := [studentScheduleNotice false, studentScheduleNotice true, tutorScheduleNotice] }
  have paid (second : Bool) :
      ev.paidAtStart (enrollmentForm second) original.start := by
    refine ⟨100, Or.inl ⟨?_, ?_⟩, Or.inr ⟨by decide, ?_⟩⟩
    · simp [ev, lockedEnrollment, enrolled, openEnrollment, replaced, observed, beforeReplacement,
        enrollmentBase, enrollmentCredit]
    · cases second <;> rfl
    · have ledgerAtStart : (ev.ledger.filter (fun entry ↦ decide (entry.point.before original.start))) =
          enrollmentLedger true := by rfl
      rw [ledgerAtStart]
      cases second <;> decide +kernel
  refine ⟨?_, by decide⟩
  refine ⟨sameScheduleAt ev rfl (by simp [ev, lockedEnrollment, enrolled, openEnrollment,
    replaced, observed]) rfl _ (by decide), Or.inr rfl, some (enrollmentPlan true),
    [groupForm, newPlaceForm], some (replacement false),
    enrollmentRosterReady base firstFunding nextFunding, ?_, enrollmentCreditValid true _,
    ?_, by simp, replacementSeen ev rfl
      (replacementConformsAfterLock base firstFunding nextFunding) _ (by decide), ?_⟩
  · intro roster member
    obtain rfl := List.mem_singleton.mp (show roster ∈ [enrollmentPlan true] from member)
    exact enrollmentPlanValid true
  · intro student member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨newPlaceForm, by simp, rfl⟩
  · intro _ form member
    have selected : ∃ second, form = enrollmentForm second := by
      have which : form = groupForm ∨ form = newPlaceForm := by simpa using member
      rcases which with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    obtain ⟨second, rfl⟩ := selected
    refine ⟨?_, ?_, paid second, ⟨studentScheduleNotice second, ?_, ⟨rfl, rfl, rfl⟩,
      ⟨rfl, rfl⟩, show (tick 21).before original.start by decide⟩,
      ⟨tutorScheduleNotice, ?_, rfl, rfl, by decide, ?_, by decide, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    · cases second <;> decide
    · cases second
      · exact historyAfterLock base firstFunding nextFunding false readFirst secureFirst checkFirst
          original.start
      · exact historyAfterLock base firstFunding nextFunding true readNext secureNext checkNext
          original.start
    · cases second <;> simp [StartEvidence.noticesFor]
    · simp [StartEvidence.noticesFor]
    · simp [replacement]
    · intro row member earlier
      obtain rfl := List.mem_singleton.mp (show row ∈ [replacement false] from member)
      cases second
      · exact ⟨List.mem_singleton.mpr rfl, notice tutorTarget, by simp [replacement],
          ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, Or.inr rfl, by decide⟩
      · exact False.elim ((by decide : ¬newPlaceForm.confirmedAt.before (tick 11)) earlier)

private def soloLesson : Lesson := { groupLesson with id := 43, kind := .oneToOne }
private def soloSchedule : Schedule := { original with lesson := soloLesson.id }

private def soloForm : PartOne :=
  { groupForm with
    lesson := soloLesson
    place := { groupForm.place with lesson := soloLesson.id }
    schedule := soloSchedule
    privateRoster := none
    rosterLock := none
    groupRescheduleCutoff := none
    oneToOneAdvanceCutoff := some (.fixed (tick 18))
    absentGroupPlacePay := none }

private theorem soloFormMatches : soloForm.matches := by
  simp [PartOne.matches, soloForm, soloLesson, soloSchedule, groupForm, groupLesson, original,
    paymentTerms, Place.matches, Place.validFees, Schedule.valid, Contacts.complete,
    PayAndReviewTerms.valid, PaymentTerms.valid, PaymentDeadline.valid, AdvanceWindow.validAt,
    Moment.by, Moment.before, tick]
  all_goals decide +kernel

private def soloSignatures : Signatures :=
  ⟨soloLesson.id, soloForm.place.id, soloLesson.coordinator, soloForm.place.customer, tick 1,
    tick 1, soloLesson.provider, tick 3, soloLesson.tutor, tick 3, tick 4, soloForm.place.customer,
    some (soloForm.place.payer, tick 4)⟩

private def documents : List BookingTermDocument :=
  [⟨.rules soloForm.rulesVersion, 1⟩, ⟨.tutorAgreement soloForm.tutorAgreementRef, 2⟩]

private def provision (recipient : ActorId) : BookingTermsProvision :=
  ⟨soloForm, soloLesson.coordinator, recipient, tick 1, tick 1, documents⟩

private def soloAgreement : Workflow.Booking.OneToOneAgreement :=
  ⟨soloSignatures, teachingTerms soloForm soloLesson.tutor soloForm.tutorAgreementRef,
    documents, [provision soloForm.place.customer, provision soloLesson.tutor]⟩

private theorem signaturesValid : soloSignatures.valid soloForm none := by
  refine ⟨rfl, rfl, rfl, Or.inl rfl, rfl, rfl, Or.inl rfl, fun _ ↦ rfl, ?_, ?_⟩
  · intro acceptance h
    have eq : (soloForm.place.payer, tick 4) = acceptance := Option.some.inj h
    exact (congrArg Prod.fst eq).symm
  · simp [TermsProvidedInTime, soloSignatures, Moment.before, tick]

private theorem tutorAgreed :
    soloAgreement.tutorAgreement.agreedBeforeAcceptance soloForm soloSignatures :=
  ⟨rfl, rfl, rfl, rfl, teachingTermsSigned _ _ _, by decide, rfl, rfl, rfl, rfl,
    by decide, by decide⟩

private theorem provisionsRecorded :
    ProvidedBookingTerms soloForm soloSignatures soloAgreement.agreedDocuments
      soloAgreement.provisions none := by
  refine ⟨?_, ⟨provision soloForm.place.customer, by simp [soloAgreement], ?_, rfl, rfl⟩,
    provision soloLesson.tutor, by simp [soloAgreement], ?_, ?_⟩
  · intro reference member
    have which : reference = .rules soloForm.rulesVersion ∨
        reference = .tutorAgreement soloForm.tutorAgreementRef := by
      simpa [soloForm, groupForm] using member
    rcases which with rfl | rfl
    · exact ⟨⟨.rules soloForm.rulesVersion, 1⟩, by simp [soloAgreement, documents], rfl⟩
    · exact ⟨⟨.tutorAgreement soloForm.tutorAgreementRef, 2⟩,
        by simp [soloAgreement, documents], rfl⟩
  · exact ⟨rfl, rfl, rfl, fun _ member ↦ member⟩
  · exact ⟨rfl, rfl, rfl, fun _ member ↦ member⟩
  · simp [provision, TermsProvidedInTime, soloSignatures, Moment.before, tick]

private def beforeSolo (base : StartEvidence) : StartEvidence :=
  { base with
    effectiveForms := []
    groupRoster := none
    bookings := []
    scheduleHistory := []
    changes := []
    teachingBegan := none
    teachingEnded := none
    ledger := []
    discounts := [] }

private def startedSolo (base : StartEvidence) : StartEvidence :=
  { beforeSolo base with
    effectiveForms := [soloForm]
    scheduleHistory := [soloSchedule]
    teachingBegan := some soloSchedule.start
    studentsTakingLesson := [soloForm.place.student] }

private def unconfirmedStart : Workflow.Booking.Event :=
  .beginUnconfirmedOneToOne soloForm soloAgreement soloSchedule.start [soloForm.place.student]

private theorem observedUnpaidStart (base : StartEvidence) :
    Workflow.Booking.Step (beforeSolo base) unconfirmedStart (startedSolo base) := by
  refine ⟨?_, rfl, ⟨soloFormMatches, by decide, by decide, rfl, rfl, signaturesValid, tutorAgreed,
    by decide, by decide, by decide, ?_, provisionsRecorded⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨?_, by simp [beforeSolo], by simp [beforeSolo]⟩
    intro form known
    rcases known with recorded | ⟨booking, recorded⟩ <;> simp [beforeSolo] at recorded
  · intro acceptance h
    have eq : (soloForm.place.payer, tick 4) = acceptance := Option.mem_some_iff.mp h
    subst acceptance
    decide

private theorem soloRoster (base : StartEvidence) (query : Moment := soloSchedule.start) :
    (startedSolo base).rosterFormsAt soloLesson query none [soloForm] :=
  ⟨⟨⟨by simp [startedSolo], by simpa [startedSolo] using
        (show soloForm.lesson = soloLesson ∧ soloForm.matches from ⟨rfl, soloFormMatches⟩)⟩,
    rfl⟩, rfl⟩

private theorem soloDateEffective (base : StartEvidence) :
    EffectiveSchedule soloLesson (startedSolo base) soloSchedule soloSchedule.start := by
  have agreed : ScheduleWasAgreed soloLesson (startedSolo base) soloSchedule :=
    ⟨rfl, originalValid, Or.inl ⟨rfl, (soloRoster base).1, by simp [startedSolo, soloForm]⟩⟩
  refine ⟨rfl, ⟨by simp [startedSolo], originalValid, by decide, ?_⟩,
    by change [soloSchedule.effectiveAt].Nodup; simp, ?_⟩
  · intro row member _ _ _
    have eq : row = soloSchedule := by simpa [startedSolo] using member
    subst row
    decide
  · intro row member _ _
    have eq : row = soloSchedule := by simpa [startedSolo] using member
    exact eq ▸ agreed

private theorem unconfirmedStartNotPermitted (base : StartEvidence) :
    ¬CanStart soloLesson (startedSolo base) soloSchedule soloSchedule.start := by
  intro wouldPermit
  obtain ⟨_, _, roster, forms, active, recorded, _, _, _, _, _, ready⟩ := wouldPermit
  have same : forms = [soloForm] := by
    cases roster with
    | none => exact recorded.2
    | some locked => exact False.elim recorded
  subst forms
  obtain ⟨_, booked, _⟩ := ready soloForm (by simp)
  simp [StartEvidence.confirmedBookingFor, startedSolo, beforeSolo] at booked

/-- An actual unpaid start travels through the shared workflow with its agreed date and place. -/
theorem unpaidOneToOneObserved (s : Workflow.State) (base : StartEvidence) :
    let prior := s.withCourse soloLesson.id (beforeSolo base)
    let after := prior.withCourse soloLesson.id (startedSolo base)
    Workflow.Step prior (.booking unconfirmedStart) after ∧
    (after.course soloLesson.id).teachingBegan = some soloSchedule.start ∧
    (after.course soloLesson.id).bookings = [] ∧ after.credit.ledger = [] ∧
    after.credit.discounts = [] ∧
    EffectiveSchedule soloLesson (after.course soloLesson.id) soloSchedule soloSchedule.start ∧
    (after.course soloLesson.id).rosterFormsAt soloLesson soloSchedule.start none [soloForm] ∧
    ¬after.startPermitted soloLesson soloSchedule soloSchedule.start [soloForm.place.student] := by
  let prior := s.withCourse soloLesson.id (beforeSolo base)
  let result := prior.withCourse soloLesson.id (startedSolo base)
  have storedBefore : prior.course soloLesson.id = beforeSolo base := by
    simp [prior, Workflow.State.course, Workflow.State.withCourse]
  have storedAfter : result.course soloLesson.id = startedSolo base := by
    simp [result, Workflow.State.course, Workflow.State.withCourse]
  refine ⟨Workflow.Step.booking (s := prior) trivial trivial trivial
    (storedBefore ▸ observedUnpaidStart base) rfl trivial trivial trivial, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · rw [storedAfter]
    rfl
  · rw [storedAfter]
    rfl
  · rw [storedAfter]
    exact soloDateEffective base
  · rw [storedAfter]
    exact soloRoster base
  · intro wouldPermit
    have permit := wouldPermit.1
    change Workflow.Booking.StartPermitted (result.course soloLesson.id)
      soloLesson soloSchedule soloSchedule.start [soloForm.place.student] at permit
    rw [storedAfter] at permit
    exact unconfirmedStartNotPermitted base permit

/-- Settlement can read the actual unpaid occurrence while still requiring its independent
    evidence of provider responsibility, realised service, authority and payment conditions. -/
theorem unpaidOccurrenceCanBeAssessed (base : StartEvidence) (query : Moment)
    (handler : Handler) (assignment : Operations.SettlementAssignment)
    (actuallyWentAhead : Prop) (occurred : actuallyWentAhead)
    (unmet : LessonId → Moment → Prop) (unmetAtStart : unmet soloLesson.id soloSchedule.start)
    (holds : HoldHistory) (holdFacts : HoldFacts)
    (value tutorPay : Amount) (underTerms : PartOne → Amount → Amount → Prop)
    (assessed : underTerms soloForm value tutorPay) (nonnegative : 0 ≤ value)
    (afterStart : soloSchedule.start.by query)
    (authorised : assignment.authorised soloForm handler query)
    (matched : Operations.FeeHoldTermsMatch soloForm holdFacts)
    (carryOut : holds.mayCarryOutDecision assignment.authorities holdFacts assignment.matter
      assignment.decision query)
    (clear : ¬Operations.FeeOnHold holds assignment.authorities holdFacts soloForm.place query) :
    let record : LessonSettlement := ⟨soloLesson.id, soloForm.place.id, value, 0, 0, 0, tutorPay, 0⟩
    Operations.UnauthorisedStartSettlement soloForm (startedSolo base) soloSchedule
      soloSchedule.start query handler assignment actuallyWentAhead unmet holds holdFacts
      value tutorPay underTerms record := by
  refine ⟨⟨none, [soloForm], soloRoster base query, by simp⟩, rfl, soloDateEffective base,
    afterStart, unmetAtStart, unconfirmedStartNotPermitted base, occurred, authorised, matched,
    carryOut, clear, assessed, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_⟩
  grind [grossLessonCreditRestoration]

#print axioms newPlaceAfterEffectiveReplacement
#print axioms oldTutorCannotConfirmNewPlace
#print axioms laterPlaceInLockedEnrollment
#print axioms startAfterReplacementEnrollment

end SourceV14.FidelityBookingChecks
