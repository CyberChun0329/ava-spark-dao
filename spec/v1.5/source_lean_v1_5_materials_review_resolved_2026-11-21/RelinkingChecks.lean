import SourceV14.Workflow

/-! Concrete pre-lock group rescheduling and the historical effective schedule (§§1.4, 2.2,
2.5, and Parts 1–2 of the course confirmation form). -/

namespace SourceV14.RelinkingChecks

open SourceV14.Booking SourceV14.Confirmation SourceV14.Course SourceV14.Settlement

def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩
def lesson : Lesson := ⟨42, .group, 10, 20, 30, 60⟩
def original : Schedule := ⟨42, tick 30, tick 32, "UTC", tick 1, tick 2⟩
def revised : Schedule := ⟨42, tick 40, tick 42, "UTC", tick 10, tick 11⟩

def seat (id : Nat) : Place := ⟨id, 42, 100 + id, 200 + id, 300 + id, 400 + id, 100, 100⟩

private def paymentTerms : PaymentTerms := ⟨.fixed (tick 50), .fixed (tick 60)⟩

def groupForm (id : Nat) (booked : Moment) (schedule : Schedule) : PartOne :=
  { lesson
    place := seat id
    contacts := ⟨"Spark", "provider", "student-channel", none, "coordinator", 50, "lead",
      none, none, 60, "reviewer", 70, "alternative", true, 80, "escalation"⟩
    rulesVersion := "1.5"
    confirmedAt := booked
    customerRepresentatives := []
    schedule
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

def firstForm : PartOne := groupForm 1 (tick 4) original
def laterForm : PartOne := groupForm 2 (tick 15) revised
def register : GroupRegisterSnapshot := ⟨lesson.id, tick 10, [firstForm]⟩
def firstPlan : Roster := ⟨lesson.id, 9, [firstForm.place], tick 20⟩
def expandedPlan : Roster := ⟨lesson.id, 9, [firstForm.place, laterForm.place], tick 20⟩

def consent (actor : ActorId) : Confirmation :=
  ⟨revised.confirmationTarget, firstForm.place.id, actor, tick 9⟩
def studentNotice : Notice :=
  ⟨revised.confirmationTarget, 50, firstForm.place.student, "student-channel", tick 10⟩
def approval (actor : ActorId) : ScheduleApproval := ⟨revised.confirmationTarget, actor, tick 9⟩

def changeBy (actor : ActorId) : AgreedScheduleChange :=
  { previous := original
    record := ⟨lesson.id, revised, lesson.coordinator, tick 8, [firstForm.place.id],
      [consent actor], [studentNotice], none, none, none⟩
    approvals := [approval lesson.tutor, approval lesson.provider]
    compliesWithOneToOneTerms := fun _ ↦ False }

def change := changeBy firstForm.place.payer

/-- The retained booking makes the original seat known before the event. Its booking
and unrelated accounting or review evidence can be any records in this local step. -/
def before (base : StartEvidence) (booking : BookingEvidence) : StartEvidence :=
  { base with
    effectiveForms := []
    groupRoster := none
    bookings := [(firstForm, booking)]
    bookedRosters := [(firstForm, firstPlan)]
    scheduleHistory := [original]
    groupRegisters := []
    verifiesGroupRegister := fun row ↦ row = register
    changes := []
    notices := []
    teachingBegan := none
    teachingEnded := none
    tutorReplacements := []
    academicTeamAt := fun id actor _ ↦ id = lesson.id ∧ actor = 50 }

def observed (base : StartEvidence) (booking : BookingEvidence) : StartEvidence :=
  { before base booking with groupRegisters := [register] }

def after (base : StartEvidence) (booking : BookingEvidence) : StartEvidence :=
  { observed base booking with scheduleHistory := [original, revised], changes := [change] }

private theorem firstMatches : firstForm.matches := by
  simp [PartOne.matches, firstForm, groupForm, lesson, seat, original, paymentTerms,
    Place.matches, Place.validFees, Schedule.valid, Contacts.complete,
    PayAndReviewTerms.valid, PaymentTerms.valid, PaymentDeadline.valid, AdvanceWindow.validAt,
    Moment.by, Moment.before, tick]
  all_goals decide +kernel

private theorem registerConforms : register.conforms lesson := by
  refine ⟨rfl, rfl, by simp [register], by simp [register], by simp [register], ?_⟩
  simpa only [register, List.mem_singleton, forall_eq] using
    (show firstForm.lesson = lesson ∧ firstForm.matches ∧ firstForm.confirmedAt.by (tick 10) from
      ⟨rfl, firstMatches, by decide⟩)

private theorem originalValid : original.valid := by
  simpa only [Schedule.valid] using
    (show original.agreedAt.by original.effectiveAt ∧ original.effectiveAt.by original.start ∧
      original.start.before original.finish ∧ original.timeZone ≠ "" from by decide)

private theorem revisedValid : revised.valid := by
  simpa only [Schedule.valid] using
    (show revised.agreedAt.by revised.effectiveAt ∧ revised.effectiveAt.by revised.start ∧
      revised.start.before revised.finish ∧ revised.timeZone ≠ "" from by decide)

private theorem originalAgreed {ev : StartEvidence}
    (earliest : ∀ row ∈ ev.scheduleHistory, row.lesson = lesson.id →
      original.effectiveAt.by row.effectiveAt)
    (stored : register ∈ ev.groupRegisters) (verified : ev.verifiesGroupRegister register) :
    ScheduleWasAgreed lesson ev original :=
  ⟨rfl, originalValid, Or.inr (Or.inl ⟨rfl, earliest,
    Or.inr ⟨register, stored, registerConforms, verified, firstForm, by simp [register], rfl⟩⟩)⟩

private theorem arrangement (base : StartEvidence) (booking : BookingEvidence) :
    (after base booking).arrangementFormsAt lesson revised.agreedAt none [firstForm] := by
  refine ⟨?_, register, by simp [after, observed], rfl, registerConforms, rfl, rfl⟩
  simp [after, observed, before]

private theorem firstConsent :
    DesignatedConfirmation firstForm.place (consent firstForm.place.payer) :=
  ⟨rfl, rfl⟩

private theorem recordMatches (base : StartEvidence) (booking : BookingEvidence) :
    change.record.matchesFrom firstForm original lesson.tutor
      ((after base booking).academicTeamAt lesson.id) := by
  refine ⟨rfl, revisedValid, by simp [change, changeBy], rfl, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    exact ⟨⟨consent firstForm.place.payer, by simp [change, changeBy], firstConsent, rfl,
      by decide⟩, studentNotice, by simp [change, changeBy], ⟨rfl, rfl, rfl⟩,
      ⟨rfl, rfl⟩, by decide⟩
  · simp [change, changeBy]
  · simp [change, changeBy]
  · intro _
    rfl
  · simp [change, changeBy]

private theorem changeRecords (base : StartEvidence) (booking : BookingEvidence) :
    change.records lesson (after base booking) none [firstForm] := by
  refine ⟨arrangement base booking, rfl, revisedValid, by simp [after, change, changeBy], rfl,
    by decide, by decide, by decide, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [after, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨fun _ _ ↦ by decide, fun _ h ↦
      False.elim ((show ¬revised.effectiveAt.before revised.effectiveAt from by decide) h)⟩
  · simp [after, observed, before]
  · simp [change, changeBy]
  · simp [change, changeBy]
  · intro _ f h
    obtain rfl := List.mem_singleton.mp h
    exact recordMatches base booking

private theorem unanimous :
    GroupReschedule lesson [firstForm.place] change.record.consents revised change.approvals
      none lesson.tutor := by
  refine ⟨rfl, by simp, rfl, revisedValid, ?_, by simp, ?_⟩
  · intro actor member
    rcases List.mem_cons.mp member with h | h
    · subst actor
      exact ⟨approval lesson.tutor, by simp [change, changeBy], rfl, rfl, by decide⟩
    · have h' := List.mem_singleton.mp h
      subst actor
      exact ⟨approval lesson.provider, by simp [change, changeBy], rfl, rfl, by decide⟩
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact ⟨rfl, consent firstForm.place.payer, by simp [change, changeBy], firstConsent, rfl,
      by decide⟩

private theorem originalAgreedAfter (base : StartEvidence) (booking : BookingEvidence) :
    ScheduleWasAgreed lesson (after base booking) original := by
  apply originalAgreed (stored := by simp [after, observed]) (verified := rfl)
  simp only [after, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨fun _ ↦ by decide, fun _ ↦ by decide⟩

private theorem changeAllowed (base : StartEvidence) (booking : BookingEvidence) :
    change.allowed lesson (after base booking) := by
  constructor
  · change ([original].map (·.effectiveAt)).Nodup ∧
      ∀ row ∈ [original], ScheduleWasAgreed lesson (after base booking) row
    exact ⟨by simp, by simpa using originalAgreedAfter base booking⟩
  · left
    refine ⟨none, [firstForm], lesson.tutor, changeRecords base booking, ?_, ?_, unanimous⟩
    · intro f hf
      obtain rfl := List.mem_singleton.mp hf
      refine ⟨.fixed (tick 18), rfl, ?_⟩
      simp [AdvanceWindow.allowsFrom, AdvanceWindow.allows, AdvanceWindow.validAt,
        revised, change, changeBy, Moment.by, Moment.before, tick]
    · exact ⟨none, by simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement,
        after, observed, before], rfl⟩

private theorem originalAtAgreement (base : StartEvidence) (booking : BookingEvidence) :
    EffectiveSchedule lesson (observed base booking) original revised.agreedAt := by
  have agreed : ScheduleWasAgreed lesson (observed base booking) original := by
    apply originalAgreed (stored := by simp [observed]) (verified := rfl)
    simpa [observed, before] using
      (show original.lesson = lesson.id → original.effectiveAt.by original.effectiveAt from
        fun _ ↦ by decide)
  refine ⟨rfl, ⟨by simp [observed, before], originalValid, by decide, ?_⟩,
    by change [original.effectiveAt].Nodup; simp, ?_⟩
  · intro row h _ _ _
    have eq : row = original := by simpa [observed, before] using h
    subst row
    decide
  · intro row h _ _
    have eq : row = original := by simpa [observed, before] using h
    exact eq ▸ agreed

theorem revisedEffective (base : StartEvidence) (booking : BookingEvidence)
    {query : Moment} (effective : revised.effectiveAt.by query) :
    EffectiveSchedule lesson (after base booking) revised query := by
  have nextAgreed : ScheduleWasAgreed lesson (after base booking) revised := by
    refine ⟨rfl, revisedValid, Or.inr (Or.inr ⟨change, by simp [after], rfl,
      (changeAllowed base booking).2⟩)⟩
  refine ⟨rfl, ⟨by simp [after], revisedValid, effective, ?_⟩, ?_, ?_⟩
  · intro row h _ _ _
    have known : row = original ∨ row = revised := by simpa [after] using h
    rcases known with rfl | rfl <;> decide
  · change [original.effectiveAt, revised.effectiveAt].Nodup
    decide
  · intro row h _ _
    have known : row = original ∨ row = revised := by simpa [after] using h
    rcases known with rfl | rfl
    · exact originalAgreedAfter base booking
    · exact nextAgreed

/-- One already booked place consents through its named payer. The new start becomes
effective while the settlement roster is still unlocked. -/
theorem preLockReschedule (base : StartEvidence) (booking : BookingEvidence) :
    Workflow.Booking.Step (before base booking) (.rescheduleBeforeLock lesson change register)
      (after base booking) ∧
    (after base booking).groupRoster = none ∧ original.start ≠ revised.start := by
  refine ⟨⟨?_, rfl, rfl, registerConforms, rfl, by simp [before], rfl,
    ⟨originalAtAgreement base booking, changeAllowed base booking,
      revisedEffective base booking (by decide)⟩,
    rfl⟩, rfl, by decide⟩
  refine ⟨?_, by simp [before], ?_⟩
  · intro f hf
    rcases hf with h | ⟨b, h⟩
    · simp [before] at h
    · have eq : (f, b) = (firstForm, booking) := by simpa [before] using h
      exact congrArg (fun pair : PartOne × BookingEvidence ↦ pair.1.lesson) eq
  · intro sched hs
    have eq : sched = original := by simpa [before] using hs
    exact congrArg Schedule.lesson eq

/-- The composite booking step checks the live place already in the shared course file.
All the other lessons and the ledger may be carried into this check from any workflow state. -/
theorem sharedReschedule (s : Workflow.State) (base : StartEvidence) (booking : BookingEvidence) :
    let prior := { s.withCourse lesson.id (before base booking) with cancelled := [] }
    Workflow.Step prior (.booking (.rescheduleBeforeLock lesson change register))
      (prior.withCourse lesson.id (after base booking)) := by
  let prior := { s.withCourse lesson.id (before base booking) with cancelled := [] }
  have stored : prior.course lesson.id = before base booking := by
    simp [prior, Workflow.State.course, Workflow.State.withCourse]
  have live : (Workflow.Booking.Event.rescheduleBeforeLock lesson change register).usesEffectivePlaces
      (before base booking) [] := by
    simp [Workflow.Booking.Event.usesEffectivePlaces, Workflow.Cancellation.PlaceCancelledAt,
      register, before]
  exact Workflow.Step.booking (s := prior) (after := after base booking) trivial trivial
    (stored ▸ live) (stored ▸ (preLockReschedule base booking).1) rfl trivial trivial trivial

/-- A later customer can sign the revised date at tick 15. The provider's earlier
register still identifies only the first payer when the change is tested. -/
theorem laterDateAndHistoricalConsent (base : StartEvidence) (booking : BookingEvidence) :
    EffectiveSchedule lesson (after base booking) laterForm.schedule laterForm.confirmedAt ∧
    (after base booking).arrangementFormsAt lesson revised.agreedAt none [firstForm] ∧
    laterForm.place.id ∉ change.record.scope :=
  ⟨revisedEffective base booking (by decide), arrangement base booking, by decide⟩

def laterDebit : CreditPosting :=
  ⟨52, laterForm.place.account, .lessonDebit lesson.id laterForm.place.id,
    laterForm.place.feePayable, laterForm.confirmedAt⟩

def joined (base : StartEvidence) (first later : BookingEvidence) : StartEvidence :=
  { after base first with
    bookings := [(firstForm, first), (laterForm, later)]
    bookedRosters := [(firstForm, firstPlan), (laterForm, expandedPlan)]
    ledger := base.ledger ++ [laterDebit] }

/-- The actual booking of seat 2 accepts the revised date. Its own Part 1, funding and
fee evidence must satisfy the ordinary booking rule and the new debit must be fresh. -/
theorem laterPlaceJoins (base : StartEvidence) (first later : BookingEvidence)
    (sameDebit : later.debit = some laterDebit)
    (fresh : ∀ row ∈ base.ledger, row.id ≠ laterDebit.id ∧ row.point ≠ laterDebit.point)
    (eligible : CanConfirmPlace laterForm later (some expandedPlan) base.openingCredit
      (base.ledger ++ [laterDebit]) base.creditRecords base.discounts none) :
    Workflow.Booking.Step (after base first)
      (.confirmPlace laterForm later (some expandedPlan) (.debit laterDebit))
        (joined base first later) := by
  have known : ∀ {f : PartOne}, (f ∈ (after base first).effectiveForms ∨
      ∃ b, (f, b) ∈ (after base first).bookings) → f = firstForm := by
    intro f h
    rcases h with h | ⟨b, h⟩
    · simp [after, observed, before] at h
    · have pair : (f, b) = (firstForm, first) := by simpa [after, observed, before] using h
      exact congrArg Prod.fst pair
  refine ⟨⟨?_, by simp [after, observed, before], ?_⟩, ?_, Or.inr (revisedEffective base first
    (by decide)), by decide, ⟨by decide, ?_⟩, ⟨sameDebit, fresh⟩, eligible, ?_, rfl⟩
  · intro f hf
    obtain rfl := known hf
    rfl
  · intro sched hs
    have which : sched = original ∨ sched = revised := by simpa [after] using hs
    rcases which with rfl | rfl <;> rfl
  · intro row member
    have eq : row = (firstForm, first) := by simpa [after, observed, before] using member
    subst row
    change firstForm.place.id ≠ laterForm.place.id
    decide
  · intro f hf
    obtain rfl := known hf
    exact ⟨by simp [expandedPlan], rfl, rfl⟩
  · refine ⟨none, ?_, rfl, rfl⟩
    simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement, after, observed,
      before]

/-- A forged snapshot cannot acquire the provider's verification by entering the event. -/
theorem unverifiedRegisterRejected (base next : StartEvidence) (booking : BookingEvidence)
    (proposal : GroupRegisterSnapshot) (unverified : proposal ≠ register) :
    ¬Workflow.Booking.Step (before base booking) (.rescheduleBeforeLock lesson change proposal)
      next := by
  intro step
  exact unverified step.2.2.2.2.1

/-- Replacing the designated payer by the contracting customer defeats the actual event,
even with the proper tutor and provider approvals and a genuine full register. -/
theorem wrongPayerRejected (base next : StartEvidence) (booking : BookingEvidence) :
    ¬Workflow.Booking.Step (before base booking)
      (.rescheduleBeforeLock lesson (changeBy firstForm.place.customer) register) next := by
  intro step
  let wrong := changeBy firstForm.place.customer
  let changed :=
    { observed base booking with scheduleHistory := [original, revised], changes := [wrong] }
  have allowed : wrong.allowed lesson changed := step.2.2.2.2.2.2.2.1.2.1
  rcases allowed.2 with ⟨roster, forms, tutor, records, _, _, allPlaces⟩ | ⟨impossible, _⟩
  · have onlyFirst : forms = [firstForm] := by
      have atAgreement := records.1
      cases roster with
      | none =>
        obtain ⟨_, row, member, _, _, _, same⟩ := atAgreement
        have rowEq : row = register := by simpa [changed, observed] using member
        subst row
        exact same
      | some locked =>
        obtain ⟨⟨_, member, _⟩, _⟩ := atAgreement
        simp [changed, observed, before] at member
    subst forms
    obtain ⟨_, c, member, designated, _, _⟩ := allPlaces.2.2.2.2.2.2 firstForm.place (by simp)
    have onlySignature : c = consent firstForm.place.customer := by
      simpa [wrong, changeBy] using member
    subst c
    exact (by decide : firstForm.place.customer ≠ firstForm.place.payer) designated.2
  · cases impossible

/-- A separate earlier booking for seat 2 must be included at the agreement cut.
Changing the retained seat's confirmation time to tick 15 removes this requirement. -/
theorem effectivePlacesAtCut (base : StartEvidence) (booking : BookingEvidence) :
    let event := Workflow.Booking.Event.rescheduleBeforeLock lesson change register
    let secondEarly := groupForm 2 (tick 6) original
    let earlyBook := { before base booking with bookings := [(firstForm, booking),
      (secondEarly, booking)] }
    let lateBook := { before base booking with bookings := [(firstForm, booking),
      (laterForm, booking)] }
    ¬event.usesEffectivePlaces earlyBook [] ∧ event.usesEffectivePlaces lateBook [] := by
  dsimp only
  constructor
  · intro accepted
    have required := accepted.2 (groupForm 2 (tick 6) original) (by simp [before])
      (by decide) (by simp [Workflow.Cancellation.PlaceCancelledAt])
    have equal := congrArg (fun f : PartOne ↦ f.place.id) (List.mem_singleton.mp required)
    exact (by decide : (2 : Nat) ≠ 1) equal
  · refine ⟨by simp [Workflow.Cancellation.PlaceCancelledAt], ?_⟩
    intro f member timely _
    have which : f = firstForm ∨ f = laterForm := by simpa [before] using member
    rcases which with rfl | rfl
    · simp [register]
    · exact False.elim ((by decide : ¬laterForm.confirmedAt.by register.atTime) timely)

/-- A later two-place lock preserves the one-place register for the earlier agreement.
Using the two-place settlement roster to demand a second historical signature fails. -/
theorem laterLockKeepsHistoricalPayer (base : StartEvidence) (first later : BookingEvidence) :
    let locked := { joined base first later with
      groupRoster := some expandedPlan
      effectiveForms := [firstForm, laterForm] }
    locked.arrangementFormsAt lesson revised.agreedAt none [firstForm] ∧
    ¬locked.arrangementFormsAt lesson revised.agreedAt (some expandedPlan) [firstForm, laterForm] := by
  dsimp only
  constructor
  · refine ⟨?_, register, by simp [joined, after, observed], rfl, registerConforms, rfl, rfl⟩
    intro roster member
    obtain rfl := Option.mem_some_iff.mp member
    decide
  · intro useLocked
    obtain ⟨roster, member, premature⟩ := useLocked.1
    obtain rfl := Option.mem_some_iff.mp member
    exact (by decide : ¬expandedPlan.lockedAt.by revised.agreedAt) premature

/-- An already-cancelled seat cannot be presented as a live payer in the full register. -/
theorem cancelledMemberExcluded (base : StartEvidence) (booking : BookingEvidence)
    (history : Workflow.Cancellation.History)
    (cancelled : Workflow.Cancellation.PlaceCancelledAt history firstForm.place register.atTime) :
    ¬(Workflow.Booking.Event.rescheduleBeforeLock lesson change register).usesEffectivePlaces
      (before base booking) history := by
  intro accepted
  exact accepted.1 firstForm (by simp [register]) cancelled

/-- Even a locked roster whose form has the right date cannot establish the group's
original schedule without a signed booking or a verified provider register. -/
theorem unsignedGroupOriginRejected (base : StartEvidence) :
    let unsigned := { base with
      effectiveForms := [firstForm], groupRoster := some firstPlan
      bookings := [], groupRegisters := [], verifiesGroupRegister := fun _ ↦ False
      changes := [], scheduleHistory := [original] }
    ¬ScheduleWasAgreed lesson unsigned original := by
  simp [ScheduleWasAgreed, GroupOriginalSchedule, StartEvidence.verifiedLockedRegister, lesson]

/-- A verified relative deadline after the revised date keeps its within-second order. -/
theorem revisedBoundaryFeedsBothHistories (base : Workflow.State) :
    let boundary : ClockBoundary := ⟨revised.start, .after, 7, ⟨47, 2⟩⟩
    let initial := { base.withCourse lesson.id { base.course lesson.id with clockBoundaries := [] } with
      holds := { base.holds with clockBoundaries := [] }
      verifiesClockBoundary := fun recorded ↦ recorded = boundary }
    let after := (initial.withCourse lesson.id { initial.course lesson.id with
      clockBoundaries := [boundary] }).withHolds { initial.holds with clockBoundaries := [boundary] }
    Workflow.Step initial (.clockBoundary lesson.id boundary) after ∧
    ¬ClockBoundary.reachedAfter (after.course lesson.id).clockBoundaries revised.start 7 ⟨47, 1⟩ ∧
    after.holds.metDeadline (.period 7 (.exact ⟨47, 2⟩)) revised.start ⟨47, 1⟩ ∧
    ClockBoundary.reachedAfter (after.course lesson.id).clockBoundaries revised.start 7 ⟨47, 3⟩ := by
  let boundary : ClockBoundary := ⟨revised.start, .after, 7, ⟨47, 2⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Workflow.Step.clockBoundary (proved := rfl) (elapsed := by decide)
    · change ClockBoundary.find [boundary] revised.start .after 7 = some ⟨47, 2⟩
      decide
    · change ClockBoundary.find [boundary] revised.start .after 7 = some ⟨47, 2⟩
      decide
  · change ¬ClockBoundary.reachedAfter [boundary] revised.start 7 ⟨47, 1⟩
    simp [boundary, ClockBoundary.reachedAfter, ClockBoundary.find, revised, tick, Moment.by,
      Moment.before]
  · change ({ base.holds with clockBoundaries := [boundary] }).metDeadline
      (.period 7 (.exact ⟨47, 2⟩)) revised.start ⟨47, 1⟩
    simp [HoldHistory.metDeadline, HoldHistory.resolvesDeadline, DeadlineTerm.cutoff, boundary, ClockBoundary.after,
      ClockBoundary.find, ClockCutoff.metBy, revised, tick, Moment.by, Moment.before]
  · change ClockBoundary.reachedAfter [boundary] revised.start 7 ⟨47, 3⟩
    simp [boundary, ClockBoundary.reachedAfter, ClockBoundary.find, revised, tick, Moment.by,
      Moment.before]

/-- An evidenced transfer to the former holder stays visible without clearing another payee. -/
theorem actualMaterialsTransferRemainsVisible (base : Workflow.State) :
    let part : PaymentPartRef := ⟨42, 10, 1, .materialsShare 5 20⟩
    let paid : PostedPayment := ⟨7, ⟨part, .person 20, 30, 10, tick 61⟩, some 8⟩
    let initial := { base with holds := { base.holds with payments := ⟨[], [], []⟩ } }
    let after := { initial.withHolds { initial.holds with payments := ⟨[paid], [], []⟩ } with
      paymentRecords := initial.paymentRecords ++ [.post paid] }
    Workflow.Step initial (.payment (.post paid)) after ∧
    after.materialsPaymentOccurrences 42 5 10 = [paid] ∧
    ¬after.holds.payments.recipientReceived (.person 21 none) paid := by
  refine ⟨Workflow.Step.payment trivial (.post _ (by decide) (by simp)), rfl, ?_⟩
  simp [PaymentHistory.recipientReceived, Workflow.State.withHolds]

/-- The same exclusion from available funds cannot serve a material provision and a
different lesson's existing commitment. -/
theorem materialPostingCannotCountTheSameExcludedFunds
    {before after : Workflow.State} {lesson : LessonId} {row : Workflow.Materials.Receipt}
    (accepted : Workflow.Step before (.materials lesson (.post row)) after)
    {entry : FundingEntry} (present : entry ∈ row.funds.entries) :
    Workflow.Reserves.occupiedElsewhere before.activeReserves row.funds entry.id +
      row.provisionFundsOutsideAvailable entry.id ≤ entry.committedElsewhere := by
  cases accepted with
  | materials _ funds _ _ => exact funds entry present

theorem materialCombinationCheckStaysWithItsLesson
    {before after : Workflow.State} {lesson : LessonId} {row : Workflow.Materials.CombinationCheck}
    (accepted : Workflow.Step before (.materials lesson (.checkCombination row)) after) :
    row.lesson.id = lesson := by
  cases accepted with
  | materials same _ _ _ => exact same row.lesson.id (by simp [Workflow.Materials.Event.recordLesson])

#print axioms materialPostingCannotCountTheSameExcludedFunds
#print axioms materialCombinationCheckStaysWithItsLesson
#print axioms revisedBoundaryFeedsBothHistories
#print axioms actualMaterialsTransferRemainsVisible

end SourceV14.RelinkingChecks

