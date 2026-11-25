import SourceV14.Operations

namespace SourceV14.Workflow.Booking

open SourceV14.Booking SourceV14.Confirmation SourceV14.Course SourceV14.Settlement
open SourceV14.Operations SourceV14.Workflow.AttendanceFacts

/-- §2.3 and Form Part 2. The payment evidence used to confirm a place. -/
inductive ConfirmationPayment where
  | debit (posting : CreditPosting)
  | fullDiscount (record : DiscountRecord)

private def ConfirmationPayment.record (payment : ConfirmationPayment) (ev : StartEvidence) :
    StartEvidence :=
  match payment with
  | .debit posting => { ev with ledger := ev.ledger ++ [posting] }
  | .fullDiscount record => { ev with discounts := ev.discounts ++ [record] }

private def ConfirmationPayment.matches (payment : ConfirmationPayment) (form : PartOne)
    (booking : BookingEvidence) (before : StartEvidence) : Prop :=
  match payment with
  | .debit posting =>
      booking.debit = some posting ∧
      ∀ existing ∈ before.ledger, existing.id ≠ posting.id ∧ existing.point ≠ posting.point
  | .fullDiscount record =>
      booking.debit = none ∧ record.covers form.place form.confirmedAt ∧
      form.discountBasis = some record.basis ∧ record ∉ before.discounts

/-- The agreed Part 1 terms can be evidenced before a place is booked under §2.3. -/
structure OneToOneAgreement where
  signatures : Signatures
  tutorAgreement : TutorAgreement
  agreedDocuments : List BookingTermDocument
  provisions : List BookingTermsProvision

private def OneToOneAgreement.recordedBefore (agreement : OneToOneAgreement)
    (form : PartOne) (point : Moment) : Prop :=
  let a := agreement.signatures
  form.matches ∧ form.schedule.agreedAt.by form.confirmedAt ∧ form.confirmedAt.before point ∧
  form.agreedTutor = form.lesson.tutor ∧ form.agreedTutorFee = form.lesson.normalTutorFee ∧
  a.valid form none ∧ agreement.tutorAgreement.agreedBeforeAcceptance form a ∧
  a.providerAccepted.by form.confirmedAt ∧ a.tutorAccepted.by form.confirmedAt ∧
  a.customerAccepted.by form.confirmedAt ∧
  (∀ acceptance ∈ a.payerAccepted, acceptance.2.by form.confirmedAt) ∧
  ProvidedBookingTerms form a agreement.agreedDocuments agreement.provisions none

/-- The local events for one lesson. The credit ledger can contain entries for other lessons. -/
inductive Event where
  | confirmPlace (form : PartOne) (booking : BookingEvidence)
      (plannedRoster : Option Roster) (payment : ConfirmationPayment)
  | fixGroupRoster (lesson : Lesson) (roster : Roster) (addedForms : List PartOne)
  | reschedule (lesson : Lesson) (change : AgreedScheduleChange)
  | rescheduleBeforeLock (lesson : Lesson) (change : AgreedScheduleChange)
      (register : GroupRegisterSnapshot)
  | replaceTutor (lesson : Lesson) (replacement : TutorReplacement)
      (scheduleChange : Option AgreedScheduleChange)
  | replaceTutorBeforeLock (lesson : Lesson) (replacement : TutorReplacement)
      (scheduleChange : Option AgreedScheduleChange) (register : GroupRegisterSnapshot)
  | notify (lesson : Lesson) (notice : Notice)
  | beginTeaching (lesson : Lesson) (point : Moment) (studentsTakingLesson : List ActorId)
  | beginUnconfirmedOneToOne (form : PartOne) (agreement : OneToOneAgreement)
      (point : Moment) (studentsTakingLesson : List ActorId)
  | endTeaching (lesson : Lesson) (point : Moment)
  | verifyOneToOneAbsence (form : PartOne) (schedule : Schedule) (start checkedAt : Moment)
      (facts : AbsenceFacts) (reason : AbsenceReasonEvidence)
      (handler : Handler) (assignment : SettlementAssignment)
  | tutorReport (lesson : Lesson) (report : TutorDeliveryReport)
  | attendance (form : PartOne) (report : AttendanceReport)
  | serviceFeedback (form : PartOne) (report : DeliveryReport)
  | studentCompletion (form : PartOne) (report : StudentCompletionReport)
  | coordinatorCompletion (lesson : Lesson) (coordinator : ActorId) (point : Moment)
  | followUp (form : PartOne) (record : StudentFollowUp)

def Event.lesson : Event → Lesson
  | .confirmPlace form .. | .attendance form _ | .serviceFeedback form _ |
    .studentCompletion form _ | .followUp form _ | .verifyOneToOneAbsence form .. |
    .beginUnconfirmedOneToOne form .. => form.lesson
  | .fixGroupRoster lesson .. | .reschedule lesson _ | .rescheduleBeforeLock lesson .. |
    .replaceTutor lesson .. | .replaceTutorBeforeLock lesson .. |
    .notify lesson _ | .beginTeaching lesson .. | .endTeaching lesson _ |
    .tutorReport lesson _ | .coordinatorCompletion lesson .. => lesson

private def HasForm (ev : StartEvidence) (form : PartOne) : Prop :=
  form ∈ ev.effectiveForms ∨ ∃ booking, (form, booking) ∈ ev.bookings

private def HasLesson (ev : StartEvidence) (lesson : Lesson) : Prop :=
  ∃ form, HasForm ev form ∧ form.lesson = lesson

private def ScopedTo (ev : StartEvidence) (lesson : Lesson) : Prop :=
  (∀ form, HasForm ev form → form.lesson = lesson) ∧
  (∀ roster ∈ ev.groupRoster, roster.lesson = lesson.id) ∧
  ∀ schedule ∈ ev.scheduleHistory, schedule.lesson = lesson.id

private def recordOriginalSchedule (history : List Schedule) (schedule : Schedule) :
    List Schedule :=
  if schedule ∈ history then history else history ++ [schedule]

private def recordScheduleChange (ev : StartEvidence) (change : AgreedScheduleChange) :
    StartEvidence :=
  { ev with
    scheduleHistory := ev.scheduleHistory ++ [change.record.nextSchedule]
    changes := ev.changes ++ [change] }

private def ValidScheduleStep (before after : StartEvidence) (lesson : Lesson)
    (change : AgreedScheduleChange) : Prop :=
  let next := change.record.nextSchedule
  EffectiveSchedule lesson before change.previous next.agreedAt ∧
  change.allowed lesson after ∧ EffectiveSchedule lesson after next next.effectiveAt

private def ReplacementStep (before : StartEvidence) (lesson : Lesson)
    (replacement : TutorReplacement) (scheduleChange : Option AgreedScheduleChange)
    (after : StartEvidence) : Prop :=
  let withTutor := { before with
    tutorReplacements := before.tutorReplacements ++ [replacement] }
  let changed := (scheduleChange.map (recordScheduleChange withTutor)).getD withTutor
  EffectiveSchedule lesson before replacement.previous replacement.agreedAt ∧
  (match scheduleChange with
  | none => replacement.record.nextSchedule = replacement.previous
  | some change =>
      change.record = replacement.record ∧ change.previous = replacement.previous ∧
      ValidScheduleStep before changed lesson change) ∧
  changed.effectiveReplacement lesson replacement.effectiveAt (some replacement) ∧
  after = changed

private def NoticeConcerns (lesson : Lesson) (notice : Notice) : Prop :=
  match notice.target with
  | .schedule id .. | .replacementTutor id _ => id = lesson.id

/-- §2.5. Evaluate permission with the conditions in force before the recorded start.
    The reported students taking the lesson are part of the occurrence evidence. -/
def StartPermitted (before : StartEvidence) (lesson : Lesson) (schedule : Schedule)
    (point : Moment) (studentsTakingLesson : List ActorId) : Prop :=
  CanStart lesson { before with studentsTakingLesson := studentsTakingLesson } schedule point

/-- Keep the exact outcome of the reason verification for any later §6.3 correction. -/
private def absenceReasonOutcome (form : PartOne) (reason : AbsenceReasonEvidence)
    (handler : Handler) (assignment : SettlementAssignment) (checkedAt : Moment)
    (goodReason : Bool) (outcome : RecordedSettlementOutcome) : Prop :=
  outcome.matter.sameCase assignment.matter ∧ outcome.outcome = assignment.decision ∧
  ((¬reason.decisionNeeded ∧
      outcome = ⟨assignment.matter, assignment.decision, handler.actor, checkedAt⟩) ∨
    (reason.decisionNeeded ∧ ReviewTerms.matchesForm reason.decisions.terms form ∧
      ∃ row ∈ reason.recordedReasons,
        row.applies reason.decisions form checkedAt ∧ row.goodReason = goodReason ∧
        (∀ other ∈ reason.recordedReasons, other.applies reason.decisions form checkedAt →
          other.effectiveAt.by row.effectiveAt ∧
          (other.effectiveAt = row.effectiveAt → other.goodReason = row.goodReason)) ∧
        (match row.review with
        | none => outcome = ⟨row.finding.matter, assignment.decision,
            row.finding.decider, row.finding.decidedAt⟩
        | some finding =>
          outcome = ⟨finding.matter, finding.outcome, finding.reviewer, finding.decidedAt⟩)))

/-- Local evidence transitions for §§1–2 and Form Parts 1–2. Each event records its
    own evidence and keeps the remaining fields. Event times come from the records.
    The agreed schedule and the actual teaching interval are distinct. -/
def Step (before : StartEvidence) (event : Event) (after : StartEvidence) : Prop :=
  ScopedTo before event.lesson ∧
  match event with
  | .confirmPlace form booking plannedRoster payment =>
      -- §§1.3, 2.1, 2.3, 2.5 and 4.4. Part 1 and the fee evidence travel together.
      let paid := payment.record before
      let confirmed := { paid with
        bookings := before.bookings ++ [(form, booking)]
        bookedRosters := before.bookedRosters ++ plannedRoster.toList.map (fun roster ↦ (form, roster))
        effectiveForms := match form.lesson.kind with
          | .oneToOne => [form]
          | .group => before.effectiveForms
        scheduleHistory := recordOriginalSchedule before.scheduleHistory form.schedule }
      (∀ earlier ∈ before.bookings, earlier.1.place.id ≠ form.place.id) ∧
      ((before.scheduleHistory = [] ∧
          ∀ existing, HasForm before existing → existing.schedule = form.schedule) ∨
        EffectiveSchedule form.lesson before form.schedule form.confirmedAt) ∧
      form.schedule.agreedAt.by form.confirmedAt ∧
      (match form.lesson.kind, plannedRoster, before.groupRoster with
      | .oneToOne, none, none => before.effectiveForms = [] ∨ before.effectiveForms = [form]
      | .group, some plan, none =>
          form.confirmedAt.by plan.lockedAt ∧
          ∀ existing, HasForm before existing → FormUsesRoster existing plan
      | .group, some plan, some locked =>
          plan = locked ∧ RegisterMatchesForms locked before form.lesson ∧
          form ∈ before.effectiveForms
      | _, _, _ => False) ∧
      payment.matches form booking before ∧
      CanConfirmPlace form booking plannedRoster before.openingCredit paid.ledger
        before.creditRecords paid.discounts before.teachingBegan ∧
      before.readsTutorAtConfirmation form ∧
      after = confirmed
  | .fixGroupRoster lesson roster addedForms =>
      -- Form Part 1 and §4.2. Lock the register of agreed places, including absentees.
      let forms := before.effectiveForms ++ addedForms
      before.groupRoster = none ∧
      ∃ current,
        let locked := { before with
          effectiveForms := forms
          groupRoster := some roster
          scheduleHistory := if before.scheduleHistory = [] then [current] else before.scheduleHistory }
        RegisterMatchesForms roster locked lesson ∧ roster.valid lesson current.start ∧
        EffectiveSchedule lesson locked current roster.lockedAt ∧
        (∀ form ∈ forms, EffectiveSchedule lesson locked form.schedule form.confirmedAt ∧
          ((∃ booking, (form, booking) ∈ before.bookings) ∨
            locked.verifiedLockedRegister lesson roster)) ∧
        (∀ booked ∈ before.bookings, booked.1 ∈ forms ∧
          locked.confirmedBookingFor booked.1 (some roster) roster.lockedAt) ∧
        after = locked
  | .reschedule lesson change =>
      -- §§1.4, 2.2 and 2.5. Keep the earlier schedules for already-started periods.
      let changed := recordScheduleChange before change
      change.record.replacementTutor = none ∧
      ValidScheduleStep before changed lesson change ∧ after = changed
  | .rescheduleBeforeLock lesson change register =>
      -- §§1.4 and 2.2, and the form's full provider register. This is a
      -- snapshot at agreement, with no write to the §4.2 locked roster.
      let observed := { before with groupRegisters := before.groupRegisters ++ [register] }
      let changed := recordScheduleChange observed change
      before.groupRoster = none ∧ register.atTime = change.record.nextSchedule.agreedAt ∧
      register.conforms lesson ∧ before.verifiesGroupRegister register ∧
      (∀ old ∈ before.groupRegisters, old.atTime ≠ register.atTime) ∧
      change.record.replacementTutor = none ∧
      ValidScheduleStep observed changed lesson change ∧ after = changed
  | .replaceTutor lesson replacement scheduleChange =>
      -- Part 2. A combined schedule and tutor change records both before taking effect.
      ReplacementStep before lesson replacement scheduleChange after
  | .replaceTutorBeforeLock lesson replacement scheduleChange register =>
      -- The effective group register at agreement is independent of the later roster lock.
      let observed := { before with groupRegisters := before.groupRegisters ++ [register] }
      before.groupRoster = none ∧ register.atTime = replacement.agreedAt ∧
      register.conforms lesson ∧ before.verifiesGroupRegister register ∧
      (∀ old ∈ before.groupRegisters, old.atTime ≠ register.atTime) ∧
      ReplacementStep observed lesson replacement scheduleChange after
  | .notify lesson notice =>
      -- §§1.4 and 2.5. The start check verifies the notice's recipient, sender and channel.
      HasLesson before lesson ∧ NoticeConcerns lesson notice ∧
      after = { before with notices := before.notices ++ [notice] }
  | .beginTeaching lesson point students =>
      -- §2.5 provides for teaching that goes ahead with unmet start conditions.
      -- Who arranged it and which conditions were unmet remain separate evidence.
      HasLesson before lesson ∧ before.teachingBegan = none ∧ before.teachingEnded = none ∧
      after = { before with teachingBegan := some point, studentsTakingLesson := students }
  | .beginUnconfirmedOneToOne form agreement point students =>
      -- §2.5. The dated Part 1 records agreement on the terms. A confirmed place
      -- would require its separate §2.3 booking and payment evidence.
      form.lesson.kind = .oneToOne ∧ agreement.recordedBefore form point ∧
      before.effectiveForms = [] ∧ before.groupRoster = none ∧ before.bookings = [] ∧
      before.scheduleHistory = [] ∧ before.teachingBegan = none ∧ before.teachingEnded = none ∧
      after = { before with
        effectiveForms := [form]
        scheduleHistory := [form.schedule]
        teachingBegan := some point
        studentsTakingLesson := students }
  | .endTeaching lesson point =>
      HasLesson before lesson ∧ before.teachingEnded = none ∧
      (∃ began ∈ before.teachingBegan, began.by point) ∧
      after = { before with teachingEnded := some point }
  | .verifyOneToOneAbsence form schedule start checkedAt facts reason handler assignment =>
      -- §3.1. Verify the failed one-to-one occurrence for the same dated lesson.
      let row : OneToOneAbsence := ⟨form, schedule, start, checkedAt, facts⟩
      form ∈ before.effectiveForms ∧ form.lesson.kind = .oneToOne ∧ start.by checkedAt ∧
      before.teachingBegan = none ∧ before.teachingEnded = none ∧
      before.oneToOneAbsenceReasons = [] ∧
      (∀ earlier ∈ before.verifiedOneToOneAbsence, row.resolvesReason earlier) ∧
      CanStart form.lesson before schedule start ∧
      verifiedStudentAbsence form.lesson form.place facts ∧
      facts.couldNotProceedSolelyForNonattendance ∧ assignment.authorised form handler checkedAt ∧
      ∃ recorded : List OneToOneAbsenceReason,
        (match facts.verifiedGoodReason with
        | none => recorded = []
        | some goodReason =>
          ∃ outcome, absenceReasonOutcome form reason handler assignment checkedAt goodReason outcome ∧
            recorded = [⟨checkedAt, outcome, goodReason⟩]) ∧
        after = { before with
          verifiedOneToOneAbsence := before.verifiedOneToOneAbsence <|> some row
          oneToOneAbsenceReasons := recorded }
  | .tutorReport lesson report =>
      -- §2.4 and Form Part 2. Keep the tutor's account, including partial delivery.
      let recorded := { before with afterLesson := { before.afterLesson with
        tutorReports := before.afterLesson.tutorReports ++ [report] } }
      HasLesson before lesson ∧ TutorDeliveryRecorded recorded lesson report.point report ∧
      after = recorded
  | .attendance form report =>
      let recorded := { before with afterLesson := { before.afterLesson with
        attendance := before.afterLesson.attendance ++ [report] } }
      HasForm before form ∧ AttendanceConcerns form.lesson form.place report ∧
      before.reportedStudentOccurrence form report.point ∧ after = recorded
  | .serviceFeedback form report =>
      let recorded := { before with afterLesson := { before.afterLesson with
        serviceFeedback := before.afterLesson.serviceFeedback ++ [report] } }
      HasForm before form ∧ ServiceFeedbackConcerns form report ∧
      before.reportedStudentOccurrence form report.point ∧ after = recorded
  | .studentCompletion form report =>
      let recorded := { before with afterLesson := { before.afterLesson with
        studentCompletions := before.afterLesson.studentCompletions ++ [report] } }
      HasForm before form ∧ StudentCompletionRecorded recorded form report.point report ∧
      after = recorded
  | .coordinatorCompletion lesson coordinator point =>
      -- §4.1. The coordinator supplies its own completion record.
      HasLesson before lesson ∧ coordinator = lesson.coordinator ∧
      before.reportedAfterLesson point point ∧
      after = { before with afterLesson := { before.afterLesson with
        coordinatorConfirmations := before.afterLesson.coordinatorConfirmations ++
          [(coordinator, point)] } }
  | .followUp form record =>
      HasForm before form ∧
      (∃ ended ∈ before.teachingEnded, before.reportedAfterLesson record.point record.point ∧
        FollowUpPerformed record form.lesson form.place ended record.point) ∧
      after = { before with afterLesson := { before.afterLesson with
        followUps := before.afterLesson.followUps ++ [record] } }

end SourceV14.Workflow.Booking
