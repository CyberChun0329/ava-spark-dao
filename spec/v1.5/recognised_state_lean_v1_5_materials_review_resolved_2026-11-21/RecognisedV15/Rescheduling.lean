import RecognisedV15.Evidence
import SourceV14.Workflow

namespace RecognisedV15.Rescheduling

open SourceV14 SourceV14.Booking SourceV14.Confirmation SourceV14.Course SourceV14.Settlement
open SourceV14.Workflow

/-- The change uses this lesson's forms, bookings, roster and schedule history. -/
private def sameLesson (before : BookingScheduleEvidence) (lesson : Lesson) : Prop :=
  (∀ form, (form ∈ before.effectiveForms ∨ ∃ booking, (form, booking) ∈ before.bookings) →
    form.lesson = lesson) ∧
  (∀ roster ∈ before.groupRoster, roster.lesson = lesson.id) ∧
  ∀ schedule ∈ before.scheduleHistory, schedule.lesson = lesson.id

/-- Read the exact register at agreement before lock. After lock, read the
roster with any corrections effective then. One-to-one uses its own form. -/
private def formsAtAgreement (evidence : LessonEvidence) (lesson : Lesson)
    (agreedAt : Moment) (roster : Option Roster) (forms : List PartOne) : Prop :=
  let b := evidence.bookingSchedule
  match lesson.kind, roster with
  | .group, none =>
    (∀ locked ∈ b.groupRoster, agreedAt.before locked.lockedAt) ∧
    ∃ snapshot ∈ b.groupRegisters,
      snapshot.atTime = agreedAt ∧ snapshot.conforms lesson ∧ b.verifiesGroupRegister snapshot ∧
      forms = snapshot.forms
  | .group, some fixed =>
    (∃ original ∈ b.groupRoster, original.lockedAt.by agreedAt) ∧
    evidence.toDirect.rosterFormsAt lesson agreedAt (some fixed) forms
  | _, _ => evidence.toDirect.rosterFormsAt lesson agreedAt roster forms

/-- The coordinator was contacted by agreement. The payer named for the
place agreed to this specific time, and the academic team notified its student
using the agreed channel. Contact, consent and notice are distinct evidence. -/
private def placeConfirmedAndNotified (before : BookingScheduleEvidence)
    (lesson : Lesson) (form : PartOne) (record : ChangeRecord) : Prop :=
  let date := record.nextSchedule
  let target := date.confirmationTarget
  record.originalLesson = form.lesson.id ∧ date.valid ∧ form.place.id ∈ record.scope ∧
  record.contactedCoordinator = form.lesson.coordinator ∧
  record.contactedAt.by date.agreedAt ∧
  (∃ consent ∈ record.consents, DesignatedConfirmation form.place consent ∧
    consent.target = target ∧ consent.point.by date.agreedAt) ∧
  (∃ notice ∈ record.notices,
    NoticePerformed notice target form.place.student form.contacts.studentNotice ∧
    before.academicTeamAt lesson.id notice.sender notice.point ∧ date.agreedAt.by notice.point) ∧
  date.lesson = form.lesson.id

private def earlierDates (before : BookingScheduleEvidence) (lesson : Lesson)
    (effectiveAt : Moment) : List Schedule :=
  before.scheduleHistory.filter fun date ↦
    date.lesson == lesson.id && decide (date.effectiveAt.before effectiveAt)

/-- No date or place outside this change is substituted. Any actual start
must follow agreement and must not precede the new effective time. -/
private def changeFitsHistory (before : LessonEvidence) (lesson : Lesson)
    (change : AgreedScheduleChange) (forms : List PartOne) : Prop :=
  let b := before.bookingSchedule
  let next := change.record.nextSchedule
  next.lesson = lesson.id ∧ next.valid ∧
  change.previous ∈ b.scheduleHistory ∧ change.previous.lesson = lesson.id ∧
  change.previous.effectiveAt.by next.agreedAt ∧
  change.previous.effectiveAt.before next.effectiveAt ∧
  change.previous.confirmationTarget ≠ next.confirmationTarget ∧
  (∀ earlier ∈ b.scheduleHistory, earlier.lesson = lesson.id →
    earlier.effectiveAt.before next.effectiveAt →
    earlier.effectiveAt.by change.previous.effectiveAt) ∧
  (∀ began, before.teaching.teachingBegan = some began →
    next.agreedAt.before began ∧ next.effectiveAt.by began) ∧
  change.record.separateBooking = none ∧
  (∀ place ∈ change.record.scope, ∃ form ∈ forms, place = form.place.id) ∧
  ∀ form ∈ forms, placeConfirmedAndNotified b lesson form change.record

private def tutorAndProviderAgreed (lesson : Lesson) (change : AgreedScheduleChange)
    (tutor : ActorId) : Prop :=
  let next := change.record.nextSchedule
  ∀ actor ∈ [tutor, lesson.provider], ∃ approval ∈ change.approvals,
    approval.forActor actor next.confirmationTarget next.agreedAt

/-- All places on the effective register agree within their own windows.
The tutor is the one in office when agreement is reached. -/
private def groupAgreement (evidence : LessonEvidence) (lesson : Lesson)
    (change : AgreedScheduleChange) : Prop :=
  let next := change.record.nextSchedule
  let dates := earlierDates evidence.bookingSchedule lesson next.effectiveAt
  ∃ roster forms tutor,
    formsAtAgreement evidence lesson next.agreedAt roster forms ∧
    changeFitsHistory evidence lesson change forms ∧
    (∀ f ∈ forms, ∃ window ∈ f.groupRescheduleCutoff,
      window.allowsFrom f.schedule change.previous dates next.agreedAt f.confirmedAt
        evidence.bookingSchedule.clockBoundaries) ∧
    EffectiveTutorAt lesson evidence.toDirect next.agreedAt tutor ∧
    lesson.kind = .group ∧ forms ≠ [] ∧ tutorAndProviderAgreed lesson change tutor

/-- The agreed terms and any applicable window govern the one place.
Tutor and provider approvals are for this exact new date. -/
private def oneToOneAgreement (evidence : LessonEvidence) (lesson : Lesson)
    (change : AgreedScheduleChange) : Prop :=
  let b := evidence.bookingSchedule
  let next := change.record.nextSchedule
  let dates := earlierDates b lesson next.effectiveAt
  lesson.kind = .oneToOne ∧
  formsAtAgreement evidence lesson next.agreedAt none b.effectiveForms ∧
  changeFitsHistory evidence lesson change b.effectiveForms ∧
  (∀ f ∈ b.effectiveForms, change.compliesWithOneToOneTerms f.cancelChangeTerms ∧
    ∀ window ∈ f.oneToOneRescheduleWindow,
      window.allowsFrom f.schedule change.previous dates next.agreedAt f.confirmedAt
        b.clockBoundaries) ∧
  ∃ tutor, EffectiveTutorAt lesson evidence.toDirect next.effectiveAt tutor ∧
    tutorAndProviderAgreed lesson change tutor

/-- Before lock the supplied register must have been independently verified
at this exact agreement time. Include each known live form and exclude
cancellations already in force. This records evidence and leaves the roster unlocked. -/
private def canUseRegister (before : BookingScheduleEvidence) (cancelled : Cancellation.History)
    (lesson : Lesson) (agreedAt : Moment) (register : GroupRegisterSnapshot) : Prop :=
  before.groupRoster = none ∧ register.atTime = agreedAt ∧ register.conforms lesson ∧
  before.verifiesGroupRegister register ∧
  (∀ old ∈ before.groupRegisters, old.atTime ≠ register.atTime) ∧
  (∀ form ∈ register.forms, ¬ Cancellation.PlaceCancelledAt cancelled form.place register.atTime) ∧
  ∀ form ∈ before.effectiveForms ++ before.bookings.map Prod.fst,
    form.confirmedAt.by register.atTime →
    ¬ Cancellation.PlaceCancelledAt cancelled form.place register.atTime →
    form ∈ register.forms

private def withRegister (before : LessonEvidence) (register : Option GroupRegisterSnapshot) :
    LessonEvidence :=
  match register with
  | none => before
  | some snapshot => { before with bookingSchedule := { before.bookingSchedule with
      groupRegisters := before.bookingSchedule.groupRegisters ++ [snapshot] } }

/-- Keep earlier schedules and all other lesson evidence. Append
the agreement and the new timetable entry. -/
private def addDate (before : LessonEvidence) (change : AgreedScheduleChange) : LessonEvidence :=
  { before with bookingSchedule := { before.bookingSchedule with
      scheduleHistory := before.bookingSchedule.scheduleHistory ++ [change.record.nextSchedule]
      changes := before.bookingSchedule.changes ++ [change] } }

private def priorDatesAgreed (evidence : LessonEvidence) (lesson : Lesson)
    (date : Schedule) : Prop :=
  let prior := earlierDates evidence.bookingSchedule lesson date.effectiveAt
  (prior.map (·.effectiveAt)).Nodup ∧ ∀ row ∈ prior, ScheduleWasAgreed lesson evidence.toDirect row

/-- Standalone rescheduling, including a change before the group register locks.
The previous date is still effective at agreement. A valid change adds the
new date at its recorded effective time and preserves the earlier history. -/
def Step (before : LessonEvidence) (cancelled : Cancellation.History) (lesson : Lesson)
    (change : AgreedScheduleChange) (register : Option GroupRegisterSnapshot)
    (after : LessonEvidence) : Prop :=
  let date := change.record.nextSchedule
  let observed := withRegister before register
  let updated := addDate observed change
  sameLesson before.bookingSchedule lesson ∧
  change.record.replacementTutor = none ∧
  (∀ snapshot ∈ register, canUseRegister before.bookingSchedule cancelled lesson
    date.agreedAt snapshot) ∧
  EffectiveSchedule lesson observed.toDirect change.previous date.agreedAt ∧
  priorDatesAgreed updated lesson date ∧
  (groupAgreement updated lesson change ∨ oneToOneAgreement updated lesson change) ∧
  EffectiveSchedule lesson updated.toDirect date date.effectiveAt ∧
  after = updated

private theorem formsAtAgreement_iff (evidence : LessonEvidence) (lesson : Lesson)
    (agreedAt : Moment) (roster : Option Roster) (forms : List PartOne) :
    formsAtAgreement evidence lesson agreedAt roster forms ↔
      evidence.toDirect.arrangementFormsAt lesson agreedAt roster forms := by
  cases kind : lesson.kind <;> cases roster <;> rfl

private theorem matchesRecord_iff (before : LessonEvidence) (lesson : Lesson)
    (record : ChangeRecord) (previous : Schedule) (form : PartOne)
    (sameBooking : record.separateBooking = none) (sameTutor : record.replacementTutor = none) :
    record.matchesFrom form previous lesson.tutor (before.toDirect.academicTeamAt lesson.id) ↔
      placeConfirmedAndNotified before.bookingSchedule lesson form record := by
  simp [ChangeRecord.matchesFrom, placeConfirmedAndNotified, sameBooking, sameTutor,
    LessonEvidence.toDirect, and_assoc]

private theorem records_iff (before : LessonEvidence) (lesson : Lesson)
    (change : AgreedScheduleChange) (roster : Option Roster) (forms : List PartOne)
    (sameTutor : change.record.replacementTutor = none) :
    change.records lesson before.toDirect roster forms ↔
      formsAtAgreement before lesson change.record.nextSchedule.agreedAt roster forms ∧
      changeFitsHistory before lesson change forms := by
  simp only [AgreedScheduleChange.records, changeFitsHistory, sameTutor, forall_const, ← formsAtAgreement_iff]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨date, valid, prev, prevLesson, prevBy, prevBefore, distinct, latest, teaching,
      sameBooking, _, scope, places⟩
    exact ⟨date, valid, prev, prevLesson, prevBy, prevBefore, distinct, latest, teaching,
      sameBooking, scope, fun f hf ↦ (matchesRecord_iff before lesson _ _ f sameBooking
        sameTutor).mp (places f hf)⟩
  · rintro ⟨date, valid, prev, prevLesson, prevBy, prevBefore, distinct, latest, teaching,
      sameBooking, scope, places⟩
    exact ⟨date, valid, prev, prevLesson, prevBy, prevBefore, distinct, latest, teaching,
      sameBooking, (fun _ equal ↦ by cases equal), scope,
      fun f hf ↦ (matchesRecord_iff before lesson _ _ f sameBooking sameTutor).mpr (places f hf)⟩

private theorem groupFormMatches (evidence : LessonEvidence) (lesson : Lesson)
    (atAgreement : Moment) (roster : Option Roster) (forms : List PartOne)
    (kind : lesson.kind = .group)
    (selected : formsAtAgreement evidence lesson atAgreement roster forms)
    (form : PartOne) (inRegister : form ∈ forms) :
    form.place.matches lesson := by
  have h := (formsAtAgreement_iff evidence lesson atAgreement roster forms).mp selected
  cases roster with
  | none =>
    rcases (by simpa [StartEvidence.arrangementFormsAt, kind] using h :
      (∀ locked ∈ evidence.toDirect.groupRoster, atAgreement.before locked.lockedAt) ∧
      ∃ snapshot ∈ evidence.toDirect.groupRegisters,
        snapshot.atTime = atAgreement ∧ snapshot.conforms lesson ∧
        evidence.toDirect.verifiesGroupRegister snapshot ∧ forms = snapshot.forms)
      with ⟨_, snapshot, _, _, conform, _, equal⟩
    rw [equal] at inRegister
    obtain ⟨same, formMatches, _⟩ := conform.2.2.2.2.2 form inRegister
    simpa [same] using formMatches.2.1
  | some fixed =>
    simp only [StartEvidence.arrangementFormsAt, kind, StartEvidence.rosterFormsAt] at h
    obtain ⟨same, formMatches, _⟩ := h.2.2.2.1 form inRegister
    simpa [same] using formMatches.2.1

private theorem groupReschedule_iff (before : LessonEvidence) (lesson : Lesson)
    (change : AgreedScheduleChange) (roster : Option Roster) (forms : List PartOne)
    (tutor : ActorId)
    (selected : formsAtAgreement before lesson change.record.nextSchedule.agreedAt roster forms)
    (history : changeFitsHistory before lesson change forms) :
    GroupReschedule lesson (forms.map (·.place)) change.record.consents change.record.nextSchedule
      change.approvals before.toDirect.teachingBegan tutor ↔
    lesson.kind = .group ∧ forms ≠ [] ∧ tutorAndProviderAgreed lesson change tutor := by
  constructor
  · rintro ⟨kind, nonempty, _, _, approvals, _, _⟩
    exact ⟨kind, by simpa using nonempty, approvals⟩
  · rintro ⟨kind, nonempty, approvals⟩
    rcases history with ⟨date, valid, _, _, _, _, _, _, teaching, _, _, evidence⟩
    refine ⟨kind, by simpa using nonempty, date, valid, approvals,
      fun began hb ↦ (teaching began hb).1, ?_⟩
    intro place hp
    obtain ⟨form, hf, rfl⟩ := List.mem_map.mp hp
    exact ⟨groupFormMatches before lesson _ roster forms kind selected form hf,
      (evidence form hf).2.2.2.2.2.1⟩

private theorem allowed_iff (before : LessonEvidence) (lesson : Lesson)
    (change : AgreedScheduleChange) (sameTutor : change.record.replacementTutor = none) :
    change.allowed lesson before.toDirect ↔
      priorDatesAgreed before lesson change.record.nextSchedule ∧
      (groupAgreement before lesson change ∨ oneToOneAgreement before lesson change) := by
  let next := change.record.nextSchedule
  let dates := earlierDates before.bookingSchedule lesson next.effectiveAt
  change ((_ ∧ ∀ row ∈ dates, ScheduleWasAgreed lesson before.toDirect row) ∧
    ((∃ roster forms tutor, change.records lesson before.toDirect roster forms ∧
      (∀ f ∈ forms, ∃ window ∈ f.groupRescheduleCutoff,
        window.allowsFrom f.schedule change.previous dates next.agreedAt
          f.confirmedAt before.bookingSchedule.clockBoundaries) ∧
      EffectiveTutorAt lesson before.toDirect
        (if change.record.replacementTutor.isSome then next.effectiveAt else next.agreedAt) tutor ∧
      GroupReschedule lesson (forms.map (·.place)) change.record.consents next change.approvals
        before.toDirect.teachingBegan tutor) ∨
     (lesson.kind = .oneToOne ∧
      change.records lesson before.toDirect none before.bookingSchedule.effectiveForms ∧
      (∀ f ∈ before.bookingSchedule.effectiveForms,
        change.compliesWithOneToOneTerms f.cancelChangeTerms ∧
        ∀ window ∈ f.oneToOneRescheduleWindow,
          window.allowsFrom f.schedule change.previous dates next.agreedAt
            f.confirmedAt before.bookingSchedule.clockBoundaries) ∧
      ∃ tutor, EffectiveTutorAt lesson before.toDirect next.effectiveAt tutor ∧
        tutorAndProviderAgreed lesson change tutor))) ↔ _
  simp only [sameTutor, Option.isSome_none, Bool.false_eq_true, ite_false,
    records_iff before lesson change _ _ sameTutor, groupAgreement, oneToOneAgreement]
  apply and_congr_right
  intro _
  apply or_congr
  · constructor
    · rintro ⟨roster, forms, tutor, ⟨selected, history⟩, window, effective, limits⟩
      exact ⟨roster, forms, tutor, selected, history, window, effective,
        (groupReschedule_iff before lesson change roster forms tutor selected history).mp limits⟩
    · rintro ⟨roster, forms, tutor, selected, history, window, effective, limits⟩
      exact ⟨roster, forms, tutor, ⟨selected, history⟩, window, effective,
        (groupReschedule_iff before lesson change roster forms tutor selected history).mpr limits⟩
  · constructor
    · rintro ⟨kind, ⟨selected, history⟩, window, approvals⟩
      exact ⟨kind, selected, history, window, approvals⟩
    · rintro ⟨kind, selected, history, window, approvals⟩
      exact ⟨kind, ⟨selected, history⟩, window, approvals⟩

/-- The local decision and update have exactly the frozen rule's two-way meaning. -/
theorem step_iff (before : LessonEvidence) (cancelled : Cancellation.History) (lesson : Lesson)
    (change : AgreedScheduleChange) (register : Option GroupRegisterSnapshot)
    (after : LessonEvidence) :
    Step before cancelled lesson change register after ↔
      let event := match register with
        | none => Booking.Event.reschedule lesson change
        | some snapshot => Booking.Event.rescheduleBeforeLock lesson change snapshot
      event.usesEffectivePlaces before.toDirect cancelled ∧
      Booking.Step before.toDirect event after.toDirect := by
  let next := change.record.nextSchedule
  have outcome (updated : LessonEvidence) : after = updated ↔ after.toDirect = updated.toDirect :=
    ⟨congrArg LessonEvidence.toDirect, fun h ↦ by
      simpa using congrArg LessonEvidence.fromDirect h⟩
  cases register with
  | none =>
    let updated := addDate before change
    change
      (sameLesson before.bookingSchedule lesson ∧ change.record.replacementTutor = none ∧
        (∀ snapshot ∈ (none : Option GroupRegisterSnapshot),
          canUseRegister before.bookingSchedule cancelled lesson next.agreedAt snapshot) ∧
        EffectiveSchedule lesson before.toDirect change.previous next.agreedAt ∧
        priorDatesAgreed updated lesson next ∧
        (groupAgreement updated lesson change ∨ oneToOneAgreement updated lesson change) ∧
        EffectiveSchedule lesson updated.toDirect next next.effectiveAt ∧ after = updated) ↔
      (True ∧ sameLesson before.bookingSchedule lesson ∧ change.record.replacementTutor = none ∧
        (EffectiveSchedule lesson before.toDirect change.previous next.agreedAt ∧
          change.allowed lesson updated.toDirect ∧
          EffectiveSchedule lesson updated.toDirect next next.effectiveAt) ∧
        after.toDirect = updated.toDirect)
    constructor
    · rintro ⟨courseScope, noTutor, _, old, prior, decision, new, result⟩
      exact ⟨trivial, courseScope, noTutor,
        ⟨old, (allowed_iff updated lesson change noTutor).mpr ⟨prior, decision⟩, new⟩,
        (outcome updated).mp result⟩
    · rintro ⟨_, courseScope, noTutor, ⟨old, allowed, new⟩, result⟩
      exact ⟨courseScope, noTutor, by simp, old,
        ((allowed_iff updated lesson change noTutor).mp allowed).1,
        ((allowed_iff updated lesson change noTutor).mp allowed).2,
        new, (outcome updated).mpr result⟩
  | some register =>
    let observed := withRegister before (some register)
    let updated := addDate observed change
    change
      (sameLesson before.bookingSchedule lesson ∧ change.record.replacementTutor = none ∧
        (∀ snapshot ∈ some register,
          canUseRegister before.bookingSchedule cancelled lesson next.agreedAt snapshot) ∧
        EffectiveSchedule lesson observed.toDirect change.previous next.agreedAt ∧
        priorDatesAgreed updated lesson next ∧
        (groupAgreement updated lesson change ∨ oneToOneAgreement updated lesson change) ∧
        EffectiveSchedule lesson updated.toDirect next next.effectiveAt ∧ after = updated) ↔
      (((∀ form ∈ register.forms, ¬ Cancellation.PlaceCancelledAt cancelled form.place register.atTime) ∧
        (∀ form ∈ before.bookingSchedule.effectiveForms ++ before.bookingSchedule.bookings.map Prod.fst,
          form.confirmedAt.by register.atTime →
          ¬ Cancellation.PlaceCancelledAt cancelled form.place register.atTime →
          form ∈ register.forms)) ∧
        sameLesson before.bookingSchedule lesson ∧ before.bookingSchedule.groupRoster = none ∧
        register.atTime = next.agreedAt ∧ register.conforms lesson ∧
        before.bookingSchedule.verifiesGroupRegister register ∧
        (∀ old ∈ before.bookingSchedule.groupRegisters, old.atTime ≠ register.atTime) ∧
        change.record.replacementTutor = none ∧
        (EffectiveSchedule lesson observed.toDirect change.previous next.agreedAt ∧
          change.allowed lesson updated.toDirect ∧
          EffectiveSchedule lesson updated.toDirect next next.effectiveAt) ∧
        after.toDirect = updated.toDirect)
    constructor
    · rintro ⟨courseScope, noTutor, snapshot, old, prior, decision, new, result⟩
      obtain ⟨unlocked, atAgreement, valid, verified, fresh, live, complete⟩ :=
        snapshot register (by simp)
      exact ⟨⟨live, complete⟩, courseScope, unlocked, atAgreement, valid, verified, fresh, noTutor,
        ⟨old, (allowed_iff updated lesson change noTutor).mpr ⟨prior, decision⟩, new⟩,
        (outcome updated).mp result⟩
    · rintro ⟨⟨live, complete⟩, courseScope, unlocked, atAgreement, valid, verified, fresh, noTutor,
        ⟨old, allowed, new⟩, result⟩
      refine ⟨courseScope, noTutor, ?_, old,
        ((allowed_iff updated lesson change noTutor).mp allowed).1,
        ((allowed_iff updated lesson change noTutor).mp allowed).2,
        new, (outcome updated).mpr result⟩
      intro snapshot mem
      have equal : register = snapshot := by simpa using mem
      subst snapshot
      exact ⟨unlocked, atAgreement, valid, verified, fresh, live, complete⟩

end RecognisedV15.Rescheduling
