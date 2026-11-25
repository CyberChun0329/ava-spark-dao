import SourceV14.Workflow
import RecognisedV15.Evidence
import RecognisedV15.Payments
import RecognisedV15.Rescheduling
import RecognisedV15.SeparateBooking
import RecognisedV15.Settlement
import RecognisedV15.Redress
import RecognisedV15.PlaceConfirmation
import RecognisedV15.MaterialPayments

namespace RecognisedV15.Workflow

open SourceV14
open SourceV14.Workflow (LessonFile CreditBook)
open SourceV14.Workflow

universe u

/-- A lesson's local information can change without replacing the shared
account or the records of other lessons. -/
structure LessonState where
  arrangements : BookingScheduleEvidence
  delivery : TeachingEvidence
  payTerms : Course.TutorPayAmendments

def LessonState.fromDirect (f : LessonFile) : LessonState :=
  ⟨⟨f.effectiveForms, f.groupRoster, f.bookings, f.scheduleHistory, f.changes,
      f.notices, f.academicTeamAt, f.tutorReplacements, f.rosterReview, f.clockBoundaries,
      f.groupRegisters, f.verifiesGroupRegister, f.bookedRosters⟩,
    ⟨f.teachingBegan, f.teachingEnded, f.verifiedOneToOneAbsence,
      f.studentsTakingLesson, f.afterLesson, f.studentFaults, f.oneToOneAbsenceReasons⟩,
    f.tutorPayAmendments⟩

def LessonState.toDirect (s : LessonState) : LessonFile :=
  let a := s.arrangements
  let t := s.delivery
  ⟨a.effectiveForms, a.groupRoster, a.bookings, a.scheduleHistory, a.changes,
    a.notices, a.academicTeamAt, t.teachingBegan, t.teachingEnded, t.verifiedOneToOneAbsence,
    t.studentsTakingLesson, t.afterLesson, t.studentFaults, a.tutorReplacements,
    a.rosterReview, a.clockBoundaries, s.payTerms, a.groupRegisters, a.verifiesGroupRegister,
    a.bookedRosters, t.oneToOneAbsenceReasons⟩

@[simp] theorem LessonState.toDirect_fromDirect (f : LessonFile) :
    (fromDirect f).toDirect = f := by cases f; rfl

@[simp] theorem LessonState.fromDirect_toDirect (s : LessonState) :
    fromDirect s.toDirect = s := by
  cases s with
  | mk arrangements delivery terms => cases arrangements; cases delivery; rfl

/-- Local records of arrangements, obligations and actual effects. The two
payment projections see the same receipts on synchronised histories. -/
structure State where
  lessons : LessonId → LessonState
  credit : CreditBook
  payment : PaymentEvidence
  cancelled : Cancellation.History
  settlement : SourceV14.Workflow.Settlement.History
  redress : SourceV14.Workflow.Redress.History
  materials : Materials.History
  review : Review.History
  debts : Debt.History
  activeReserves : List Reserves.Reservation
  paymentRecords : List Payment.Event
  separateBookings : List SourceV14.Workflow.SeparateBooking.Link
  tutorFaults : TutorFaultHistory.History
  verifiedContractualDiscount : Confirmation.PartOne → Moment → Prop
  verifiesClockBoundary : ClockBoundary → Prop
  verifiesServiceReserve : ServiceReserve.Account → Operations.ServiceReserveTransfer → Prop
  serviceReserveFilings : List ServiceReserve.Filing
  verifiedAbsenceOutcome : ReviewFinding → PlaceId → Option Bool
  verifiedAgreedRefundTrigger : SourceV14.Workflow.Redress.RefundTriggerEvidence
  verifiedTutorReview : TutorFaultHistory.ReviewInterpretation
  verifiedMaterialsGross : MaterialsGrossEvidence

def State.fromDirect (s : SourceV14.Workflow.State) : State :=
  ⟨fun lesson ↦ LessonState.fromDirect (s.lessons lesson), s.credit, PaymentEvidence.fromDirect s.holds,
    s.cancelled, s.settlement, s.redress, s.materials, s.review, s.debts, s.activeReserves,
    s.paymentRecords, s.separateBookings, s.tutorFaults, s.verifiedContractualDiscount,
    s.verifiesClockBoundary, s.verifiesServiceReserve, s.serviceReserveFilings,
    s.verifiedAbsenceOutcome, s.verifiedAgreedRefundTrigger, s.verifiedTutorReview,
    s.verifiedMaterialsGross⟩

def State.toDirect (s : State) : SourceV14.Workflow.State :=
  ⟨fun lesson ↦ (s.lessons lesson).toDirect, s.credit, s.payment.toDirect, s.cancelled,
    s.settlement, s.redress, s.materials, s.review, s.debts, s.activeReserves,
    s.paymentRecords, s.separateBookings, s.tutorFaults, s.verifiedContractualDiscount,
    s.verifiesClockBoundary, s.verifiesServiceReserve, s.serviceReserveFilings,
    s.verifiedAbsenceOutcome, s.verifiedAgreedRefundTrigger, s.verifiedTutorReview,
    s.verifiedMaterialsGross⟩

@[simp] theorem State.toDirect_fromDirect (s : SourceV14.Workflow.State) :
    (fromDirect s).toDirect = s := by cases s; simp [fromDirect, toDirect]

@[simp] theorem State.fromDirect_toDirect (s : State) :
    fromDirect s.toDirect = s := by cases s; simp [fromDirect, toDirect]

def State.materialsPrincipalContext (s : State) : MaterialsPrincipalContext :=
  ⟨s.review.paymentCorrections, s.verifiedMaterialsGross⟩

def State.lessonEvidence (s : State) (lesson : LessonId) : LessonEvidence :=
  let file := s.lessons lesson
  ⟨file.arrangements,
    ⟨s.credit.openingCredit, s.credit.creditRecords, s.credit.ledger, s.credit.discounts,
      file.payTerms⟩,
    file.delivery⟩

def State.course (s : State) (lesson : LessonId) : Course.StartEvidence :=
  (s.lessons lesson).toDirect.evidence s.credit

@[simp] theorem State.lessonEvidence_toDirect (s : State) (id : LessonId) :
    (s.lessonEvidence id).toDirect = s.course id :=
  rfl

def State.recordCourse (s : State) (lesson : LessonId) (ev : Course.StartEvidence) : State :=
  { s with
    lessons := fun key ↦ if key = lesson then LessonState.fromDirect (LessonFile.fromEvidence ev)
      else s.lessons key
    credit := CreditBook.fromEvidence ev }

def State.recordPayment (s : State) (holds : HoldHistory) : State :=
  { s with
    payment := PaymentEvidence.fromDirect holds
    credit := { s.credit with creditRecords := { s.credit.creditRecords with payments := holds.payments } } }

@[simp] theorem State.direct_course (s : State) (id : LessonId) :
    s.toDirect.course id = s.course id :=
  rfl

@[simp] theorem State.fromDirect_course (s : SourceV14.Workflow.State) (id : LessonId) :
    (fromDirect s).course id = s.course id := by simp [course, fromDirect, SourceV14.Workflow.State.course]

@[simp] theorem State.fromDirect_payment (s : SourceV14.Workflow.State) :
    (fromDirect s).payment.toDirect = s.holds :=
  PaymentEvidence.toDirect_fromDirect s.holds

@[simp] theorem State.fromDirect_recordCourse (s : SourceV14.Workflow.State)
    (id : LessonId) (ev : Course.StartEvidence) :
    fromDirect (s.withCourse id ev) = (fromDirect s).recordCourse id ev := by
  simp [fromDirect, recordCourse, SourceV14.Workflow.State.withCourse, apply_ite]

@[simp] theorem State.fromDirect_recordPayment (s : SourceV14.Workflow.State) (holds : HoldHistory) :
    fromDirect (s.withHolds holds) = (fromDirect s).recordPayment holds :=
  rfl

@[simp] theorem State.direct_recordCourse (s : State) (id : LessonId) (ev : Course.StartEvidence) :
    (s.recordCourse id ev).toDirect = s.toDirect.withCourse id ev := by
  have matched := fromDirect_recordCourse s.toDirect id ev
  rw [fromDirect_toDirect] at matched
  rw [← matched, toDirect_fromDirect]

@[simp] theorem State.direct_recordPayment (s : State) (holds : HoldHistory) :
    (s.recordPayment holds).toDirect = s.toDirect.withHolds holds := by
  have matched := fromDirect_recordPayment s.toDirect holds
  rw [fromDirect_toDirect] at matched
  rw [← matched, toDirect_fromDirect]

def State.synchronised (s : State) : Prop := s.credit.creditRecords.payments = s.payment.payments

def State.startPermitted (s : State) (lesson : Lesson) (schedule : SourceV14.Booking.Schedule)
    (atTime : Moment) (students : List ActorId) : Prop :=
  Booking.StartPermitted (s.course lesson.id) lesson schedule atTime students ∧
  Cancellation.CompatibleWithStart s.cancelled (s.course lesson.id) lesson atTime students

def State.usesSelectedCourse (s : State) : SourceV14.Workflow.Redress.Event → Prop
  | .recordDiscountUse booking selected => selected = s.course booking.agreed.lesson.id
  | _ => True

theorem State.selected_course_iff (s : State) (event : SourceV14.Workflow.Redress.Event) :
    s.usesSelectedCourse event ↔ event.usesCurrentSelectedCourse s.toDirect := by
  cases event <;> rfl

/-- Confirmation changes both the lesson and its funding reservation.
Rescheduling uses the lesson history and leaves the current reservations in place. -/
def State.bookingStep (s : State) (event : Booking.Event) (after : Course.StartEvidence)
    (reserves : List Reserves.Reservation) : Prop :=
  match event with
  | .confirmPlace form booking roster payment =>
    PlaceConfirmation.Step (s.lessonEvidence form.lesson.id) s.activeReserves
      form booking roster payment (LessonEvidence.fromDirect after) reserves
  | .reschedule lesson change =>
    Rescheduling.Step (s.lessonEvidence lesson.id) s.cancelled lesson change none
      (LessonEvidence.fromDirect after) ∧ reserves = s.activeReserves
  | .rescheduleBeforeLock lesson change register =>
    Rescheduling.Step (s.lessonEvidence lesson.id) s.cancelled lesson change (some register)
      (LessonEvidence.fromDirect after) ∧ reserves = s.activeReserves
  | _ =>
    event.fundingContext s.activeReserves ∧
    event.usesEffectivePlaces (s.course event.lesson.id) s.cancelled ∧
    Booking.Step (s.course event.lesson.id) event after ∧
    reserves = event.reservations s.activeReserves

theorem State.bookingStep_iff (s : State) (event : Booking.Event) (after : Course.StartEvidence)
    (reserves : List Reserves.Reservation) :
    s.bookingStep event after reserves ↔
      event.fundingContext s.activeReserves ∧
      event.usesEffectivePlaces (s.course event.lesson.id) s.cancelled ∧
      Booking.Step (s.course event.lesson.id) event after ∧
      reserves = event.reservations s.activeReserves := by
  cases event with
  | confirmPlace form booking roster payment =>
    simpa only [bookingStep, lessonEvidence_toDirect, LessonEvidence.toDirect_fromDirect,
      Booking.Event.lesson, Booking.Event.usesEffectivePlaces, true_and] using
      (PlaceConfirmation.step_iff (s.lessonEvidence form.lesson.id) s.activeReserves
        form booking roster payment (LessonEvidence.fromDirect after) reserves)
  | reschedule lesson change =>
    simp only [bookingStep, Rescheduling.step_iff, lessonEvidence_toDirect,
      LessonEvidence.toDirect_fromDirect, Booking.Event.lesson, Booking.Event.fundingContext,
      true_and, Booking.Event.reservations, and_assoc]
  | rescheduleBeforeLock lesson change register =>
    simp only [bookingStep, Rescheduling.step_iff, lessonEvidence_toDirect,
      LessonEvidence.toDirect_fromDirect, Booking.Event.lesson, Booking.Event.fundingContext,
      true_and, Booking.Event.reservations, and_assoc]
  | _ => rfl

private def retainHoldClockBoundary (holds : HoldHistory) (row : ClockBoundary) : HoldHistory :=
  let boundaries := holds.clockBoundaries
  { holds with clockBoundaries := if row ∈ boundaries then boundaries else boundaries ++ [row] }

/-- Apply the shared institutional checks to the selected local records.
Each successor writes only the affected records, including linked payment
and credit changes where required. -/
inductive Step : State → Event → State → Prop where
  | credit {s : State} {event : Credit.Event} {next : CreditBook}
      (rule : Credit.Step s.credit event next) :
    Step s (.credit event) { s with credit := next }
  | booking {s : State} {event : Booking.Event} {after : Course.StartEvidence}
      {reserves : List Reserves.Reservation}
      {discount : Option SourceV14.Workflow.Redress.DiscountBooking}
      (active : event.respectsCancellation s.cancelled)
      (rule : s.bookingStep event after reserves)
      (price : BookingEntitlements.confirmationAllowed s.course s.verifiedContractualDiscount
        s.redress event discount after)
      (findings : event.usesRecordedAbsenceFindings s.review)
      (materials : event.securesPendingMaterials s.toDirect)
      (receipts : event.readsFundingReceipts s.payment.payments) :
    Step s (.booking event discount)
      { s.recordCourse event.lesson.id after with
        activeReserves := reserves
        redress := BookingEntitlements.recordConfirmation s.redress discount }
  | cancellation {s : State} {event : Cancellation.Event} {next : Cancellation.History}
      (checked : BookingEntitlements.noTimelyRearrangement (s.course event.form.lesson.id)
        s.separateBookings event)
      (rule : Cancellation.Step s.cancelled (s.course event.form.lesson.id) event next) :
    Step s (.cancellation event) { s with cancelled := next }
  | separateBooking {s : State} {link : SourceV14.Workflow.SeparateBooking.Link}
      {next : List SourceV14.Workflow.SeparateBooking.Link}
      (rule : RecognisedV15.SeparateBooking.Step
        (s.lessonEvidence link.original.lesson.id) (s.lessonEvidence link.next.lesson.id)
        s.separateBookings link next) :
    Step s (.separateBooking link) { s with separateBookings := next }
  | settlement {s : State} {event : SourceV14.Workflow.Settlement.Event}
      {next : SourceV14.Workflow.Settlement.History}
      (rule : RecognisedV15.Settlement.Step (s.lessonEvidence event.lesson) s.payment.toDirect
        s.cancelled s.debts s.settlement event next)
      (faults : TutorFaultHistory.settlementUses s.course s.review s.tutorFaults s.settlement
        s.verifiedTutorReview event)
      (recordedRedress : TutorFaultHistory.retainedRedressUses s.course s.tutorFaults s.redress event)
      (accounts : LessonAccounts.uses s.settlement s.redress s.review s.materials
        (s.course event.lesson) event s.verifiedMaterialsGross)
      (absence : event.usesCurrentAbsence s.toDirect) :
    Step s (.settlement event) { s with settlement := next }
  | payment {s : State} {event : Payment.Event} {next : HoldHistory}
      (separate : event.independentCreditChange s.credit)
      (rule : Payment.Step s.payment.toDirect event next) :
    Step s (.payment event)
      { s.recordPayment next with paymentRecords := s.paymentRecords ++ [event] }
  | redress {s : State} {event : SourceV14.Workflow.Redress.Event}
      {next : SourceV14.Workflow.Redress.History} {after : LessonEvidence} {holds : HoldHistory}
      (cancellation : event.usesRecordedCancellation s.cancelled s.settlement)
      (selected : s.usesSelectedCourse event)
      (review : event.usesRecordedReviews s.review)
      (absence : event.usesCurrentAbsence s.toDirect)
      (rule : RecognisedV15.Redress.Step s.redress (s.lessonEvidence event.form.lesson.id)
        s.payment.toDirect event next after holds s.verifiedAgreedRefundTrigger s.review) :
    Step s (.redress event)
      { (s.recordCourse event.form.lesson.id after.toDirect).recordPayment holds with redress := next }
  | refundReturned {s : State} {paid : PostedPayment} {returned : ReturnedPayment}
      {posting : SourceV14.Booking.CreditPosting} {next : HoldHistory}
      (matchCredit : SourceV14.Workflow.Redress.refundReturnMatches (s.course paid.instruction.part.lesson)
        paid returned posting)
      (returnedPayment : Payment.Step s.payment.toDirect (.returnPayment returned) next) :
    Step s (.refundReturned paid returned posting)
      { s.recordPayment next with
        credit := { (s.recordPayment next).credit with ledger := s.credit.ledger ++ [posting] }
        paymentRecords := s.paymentRecords ++ [.returnPayment returned] }
  | materials {s : State} {lesson : LessonId} {event : Materials.Event}
      {next : Materials.History} {payment : PaymentEvidence}
      (sameLesson : ∀ id ∈ event.recordLesson, id = lesson)
      (funds : event.fundingContext s.activeReserves)
      (rule : MaterialPayments.Step (s.lessonEvidence lesson) s.payment s.materials event next payment
        s.materialsPrincipalContext) :
    Step s (.materials lesson event)
      { s.recordPayment payment.toDirect with
        materials := next, activeReserves := event.reservations s.activeReserves }
  | review {s : State} {evidence : Review.Evidence} {event : Review.Event} {next : Review.History}
      (funds : event.fundingContext s.activeReserves)
      (materials : event.readsMaterialsTerms s.materials)
      (tutorPay : ∀ row, event = .fileCorrectedPayment row →
        TutorFaultHistory.correctedPayoutUses s.course s.review s.tutorFaults s.settlement
          s.verifiedTutorReview row ∧
        TutorFaultHistory.retainedRedressCorrectedPayoutUses s.course s.tutorFaults s.redress row)
      (rule : Review.Step (s.toDirect.reviewEvidence evidence) (s.course event.lesson)
        s.payment.toDirect s.review event next) :
    Step s (.review evidence event)
      { s with review := next
               payment := PaymentEvidence.fromDirect (event.updateHoldParts s.payment.toDirect) }
  | debt {s : State} {event : Debt.Event} {next : Debt.History}
      (rule : Debt.Step (s.course event.form.lesson.id) s.redress s.debts event next) :
    Step s (.debt event) { s with debts := next }
  | tutorFault {s : State} {event : TutorFaultHistory.Event} {next : TutorFaultHistory.History}
      (rule : TutorFaultHistory.Step s.course s.review s.verifiedTutorReview s.tutorFaults event next) :
    Step s (.tutorFault event) { s with tutorFaults := next }
  | correctedRefund {s : State} {evidence : Review.Evidence} {row : Review.CorrectedPayout}
      {posting : SourceV14.Booking.CreditPosting} {file : Course.VerifiedLessonRefund}
      {next : Review.History} {scope : CorrectedMonetaryScope}
      (basis : row.paymentScope s.review (s.toDirect.reviewEvidence evidence) = some scope)
      (mayFile : s.credit.mayFileCorrectedRefund s.payment.payments posting file row scope)
      (rule : Review.Step (s.toDirect.reviewEvidence evidence)
        ((s.lessons row.form.lesson.id).toDirect.evidence
          (s.credit.withCorrectedRefund s.payment.payments posting file))
        s.payment.toDirect s.review (.fileCorrectedPayment row) next) :
    Step s (.correctedRefund evidence row posting file)
      { s with review := next, credit := s.credit.withCorrectedRefund s.payment.payments posting file }
  | clockBoundary {s : State} {lesson : LessonId} {row : ClockBoundary}
      (proved : s.verifiesClockBoundary row) (elapsed : 0 < row.duration)
      (courseBoundary : ClockBoundary.find ((s.course lesson).clockBoundaries ++ [row])
        row.anchor row.direction row.duration = some row.cutoff)
      (holdBoundary : ClockBoundary.find (retainHoldClockBoundary s.payment.toDirect row).clockBoundaries
        row.anchor row.direction row.duration = some row.cutoff) :
    Step s (.clockBoundary lesson row)
      ((s.recordCourse lesson { s.course lesson with
        clockBoundaries := (s.course lesson).clockBoundaries ++ [row] }).recordPayment
          (retainHoldClockBoundary s.payment.toDirect row))
  | reserveReleased {s : State} {row : Reserves.Release} {verification : Reserves.Release → Prop}
      {earlier suffix : List Reserves.Reservation} {reservation : Reserves.Reservation}
      (retained : s.activeReserves = earlier ++ reservation :: suffix)
      (same : row.matches reservation) (verified : verification row) :
    Step s (.reserveReleased row verification)
      { s with activeReserves := earlier ++ { reservation with amount := reservation.amount - row.amount } :: suffix }
  | fileServiceReserve {s : State} {entry : ServiceReserve.Filing}
      (accounted : entry.conforms s.verifiesServiceReserve
        (s.course entry.form.lesson.id) s.redress s.review s.tutorFaults s.payment.toDirect)
      (funds : Reserves.FundingContextMatches s.activeReserves entry.account.funds)
      (prior : entry.account.priorTransfers =
        (s.serviceReserveFilings.filter (fun earlier ↦ decide
          (earlier.transfer.lesson = entry.transfer.lesson ∧
            earlier.transfer.point.before entry.transfer.point))).map (·.transfer))
      (fresh : ∀ earlier ∈ s.serviceReserveFilings,
        earlier.transfer.evidence ≠ entry.transfer.evidence ∧
          earlier.transfer.point ≠ entry.transfer.point) :
    Step s (.fileServiceReserve entry)
      { s with serviceReserveFilings := s.serviceReserveFilings ++ [entry] }
  | correctAbsenceReason {s : State} {change : AbsenceReasonCorrection}
      (verified : change.conforms s.toDirect) :
    Step s (.correctAbsenceReason change)
      (let lesson := change.form.lesson.id
       let course := s.course lesson
       s.recordCourse lesson { course with
         oneToOneAbsenceReasons := course.oneToOneAbsenceReasons ++ [change.reason] })

theorem step_to_direct {s t : State} {event : Event}
    (step : Step s event t) : SourceV14.Workflow.Step s.toDirect event t.toDirect := by
  cases step with
  | credit rule => exact .credit rule
  | @booking event after reserves discount active rule price findings materials receipts =>
    obtain ⟨funds, places, booking, rfl⟩ := (s.bookingStep_iff event after reserves).mp rule
    simpa [State.recordCourse, State.toDirect, SourceV14.Workflow.State.withCourse, apply_ite] using!
      (SourceV14.Workflow.Step.booking (s := s.toDirect)
        funds active places booking price findings materials receipts)
  | cancellation checked rule => exact .cancellation checked rule
  | @separateBooking link after rule =>
    exact .separateBooking ((RecognisedV15.SeparateBooking.step_iff
      (s.lessonEvidence link.original.lesson.id) (s.lessonEvidence link.next.lesson.id)
      s.separateBookings link after).mp rule)
  | @settlement event next rule faults recordedRedress accounts absence =>
    obtain ⟨active, debts, settlement⟩ := (RecognisedV15.Settlement.step_iff
      (s.lessonEvidence event.lesson) s.payment.toDirect s.cancelled s.debts
      s.settlement event next).mp rule
    exact .settlement active debts faults recordedRedress accounts absence settlement
  | payment separate rule => exact .payment separate rule
  | @redress event next after holds cancellation selected review absence rule =>
    have condition := (s.selected_course_iff event).mp selected
    have redress := (RecognisedV15.Redress.step_iff s.redress
      (s.lessonEvidence event.form.lesson.id) s.payment.toDirect event next after holds
      s.verifiedAgreedRefundTrigger s.review).mp rule
    simpa [State.recordCourse, State.recordPayment, State.toDirect,
      SourceV14.Workflow.State.withCourse, SourceV14.Workflow.State.withHolds, apply_ite] using!
      (SourceV14.Workflow.Step.redress cancellation condition review absence redress)
  | refundReturned credit returnedPayment => exact .refundReturned credit returnedPayment
  | @materials lesson event next payment sameLesson funds rule =>
    obtain ⟨materials, recorded⟩ := (MaterialPayments.step_iff
      (s.lessonEvidence lesson) s.payment s.materials event next payment s.materialsPrincipalContext).mp rule
    exact .materials sameLesson funds materials recorded
  | review funds materials tutorPay rule =>
    simpa [State.toDirect] using!
      (SourceV14.Workflow.Step.review (s := s.toDirect) funds materials tutorPay rule)
  | debt rule => exact .debt rule
  | tutorFault rule => exact .tutorFault rule
  | correctedRefund basis mayFile rule => exact .correctedRefund basis mayFile rule
  | clockBoundary proved elapsed courseBoundary holdBoundary =>
    simpa only [State.direct_recordPayment, State.direct_recordCourse] using!
      (SourceV14.Workflow.Step.clockBoundary (s := s.toDirect)
        proved elapsed courseBoundary holdBoundary)
  | reserveReleased retained same verified => exact .reserveReleased retained same verified
  | fileServiceReserve accounted funds prior fresh =>
    exact .fileServiceReserve accounted funds prior fresh
  | correctAbsenceReason verified =>
    simpa only [State.direct_recordCourse] using!
      (SourceV14.Workflow.Step.correctAbsenceReason (s := s.toDirect) verified)

theorem step_from_direct {s t : SourceV14.Workflow.State} {event : Event}
    (step : SourceV14.Workflow.Step s event t) : Step (State.fromDirect s) event (State.fromDirect t) := by
  cases step with
  | credit rule => exact .credit rule
  | @booking event after discount funds active places rule price findings materials receipts =>
    have rule' : Booking.Step ((State.fromDirect s).course event.lesson.id) event after := by
      simpa only [State.fromDirect_course] using! rule
    have places' : event.usesEffectivePlaces ((State.fromDirect s).course event.lesson.id)
        (State.fromDirect s).cancelled := by
      rw [State.fromDirect_course]
      exact places
    have booking := ((State.fromDirect s).bookingStep_iff event after
      (event.reservations s.activeReserves)).mpr ⟨funds, places', rule', rfl⟩
    have price' := show BookingEntitlements.confirmationAllowed (State.fromDirect s).course
        s.verifiedContractualDiscount s.redress event discount after from by
      simpa only [State.fromDirect_course] using! price
    have recognised := Step.booking (s := State.fromDirect s) active booking price' findings
      (by simpa only [State.toDirect_fromDirect] using! materials)
      (by simpa only [State.fromDirect_payment] using! receipts)
    simpa only [← State.fromDirect_recordCourse] using! recognised
  | cancellation checked rule =>
    exact .cancellation (by simpa only [State.fromDirect_course] using! checked)
      (by simpa only [State.fromDirect_course] using! rule)
  | @separateBooking link after rule =>
    apply Step.separateBooking
    apply (RecognisedV15.SeparateBooking.step_iff
      ((State.fromDirect s).lessonEvidence link.original.lesson.id)
      ((State.fromDirect s).lessonEvidence link.next.lesson.id) s.separateBookings link after).mpr
    simpa only [State.lessonEvidence_toDirect, State.fromDirect_course] using! rule
  | @settlement event next active debts faults recordedRedress accounts absence rule =>
    have localStep := (RecognisedV15.Settlement.step_iff ((State.fromDirect s).lessonEvidence event.lesson)
      (State.fromDirect s).payment.toDirect s.cancelled s.debts s.settlement event next).mpr (by
        exact ⟨active, debts, by simpa only [State.lessonEvidence_toDirect, State.fromDirect_course,
          State.fromDirect_payment] using! rule⟩)
    exact .settlement localStep (by simpa only [State.fromDirect_course] using! faults)
      (by simpa only [State.fromDirect_course] using! recordedRedress)
      (by simpa only [State.fromDirect_course] using! accounts)
      (by simpa only [State.toDirect_fromDirect] using! absence)
  | payment separate rule => exact .payment separate rule
  | @redress event next after holds cancellation selected review absence rule =>
    have second : event.usesCurrentSelectedCourse (State.fromDirect s).toDirect := by simpa using! selected
    have condition := ((State.fromDirect s).selected_course_iff event).mpr second
    have redress := (RecognisedV15.Redress.step_iff s.redress
      ((State.fromDirect s).lessonEvidence event.form.lesson.id) (State.fromDirect s).payment.toDirect
      event next (LessonEvidence.fromDirect after) holds s.verifiedAgreedRefundTrigger s.review).mpr (by
        simpa only [State.lessonEvidence_toDirect, State.fromDirect_course, State.fromDirect_payment,
          LessonEvidence.toDirect_fromDirect] using! rule)
    have step := Step.redress (s := State.fromDirect s) cancellation condition review
      (by simpa only [State.toDirect_fromDirect] using! absence) redress
    simpa [State.fromDirect, State.recordCourse, State.recordPayment,
      SourceV14.Workflow.State.withCourse, SourceV14.Workflow.State.withHolds, apply_ite] using! step
  | refundReturned credit returnedPayment => exact .refundReturned credit returnedPayment
  | @materials lesson event next holds sameLesson funds rule payment =>
    have matched := (MaterialPayments.step_iff ((State.fromDirect s).lessonEvidence lesson)
      (State.fromDirect s).payment s.materials event next (PaymentEvidence.fromDirect holds)
      (State.fromDirect s).materialsPrincipalContext).mpr (by
        simpa only [State.lessonEvidence_toDirect, State.fromDirect_course,
          State.fromDirect_payment, PaymentEvidence.toDirect_fromDirect] using!
          And.intro rule payment)
    simpa [State.fromDirect, State.recordPayment, SourceV14.Workflow.State.withHolds] using!
      (Step.materials (s := State.fromDirect s) sameLesson funds matched)
  | review funds materials tutorPay rule =>
    exact .review funds materials
      (by simpa only [State.fromDirect_course] using! tutorPay)
      (by simpa only [State.toDirect_fromDirect, State.fromDirect_course,
        State.fromDirect_payment] using! rule)
  | debt rule => exact .debt rule
  | tutorFault rule =>
    exact .tutorFault (by simpa only [State.fromDirect_course] using! rule)
  | correctedRefund basis mayFile rule =>
    exact .correctedRefund (by simpa only [State.toDirect_fromDirect] using! basis) mayFile
      (by simpa only [State.toDirect_fromDirect, LessonState.toDirect_fromDirect,
        State.fromDirect_payment] using! rule)
  | @clockBoundary lesson row proved elapsed courseBoundary holdBoundary =>
    have corresponding := Step.clockBoundary (s := State.fromDirect s) (lesson := lesson) (row := row)
      proved elapsed (by simpa only [State.fromDirect_course] using! courseBoundary)
      (by simpa only [State.fromDirect_payment] using! holdBoundary)
    simpa only [State.fromDirect_recordPayment, State.fromDirect_recordCourse,
      State.fromDirect_course, State.fromDirect_payment] using! corresponding
  | reserveReleased retained same verified => exact .reserveReleased retained same verified
  | fileServiceReserve accounted funds prior fresh =>
    exact .fileServiceReserve (by simpa only [State.fromDirect_course,
      State.fromDirect_payment] using! accounted) funds prior fresh
  | @correctAbsenceReason change verified =>
    have corresponding := Step.correctAbsenceReason (s := State.fromDirect s) (change := change)
      (by simpa only [State.toDirect_fromDirect] using! verified)
    simpa only [State.fromDirect_recordCourse, State.fromDirect_course] using! corresponding

/-- Exact equality of the labelled transition relations under the state
bijection. There is no bound on evidence, amounts, the time or case. -/
theorem step_iff (s t : SourceV14.Workflow.State) (event : Event) :
    SourceV14.Workflow.Step s event t ↔ Step (State.fromDirect s) event (State.fromDirect t) :=
  ⟨step_from_direct, fun step ↦ by simpa using step_to_direct step⟩

def Related (s : SourceV14.Workflow.State) (t : State) : Prop := t.toDirect = s

/-- Both models match every labelled successor with the same resulting view. -/
theorem bisimulation {s : SourceV14.Workflow.State} {t : State} (related : Related s t) :
    (∀ event s', SourceV14.Workflow.Step s event s' →
        ∃ t', Step t event t' ∧ Related s' t') ∧
    (∀ event t', Step t event t' →
        ∃ s', SourceV14.Workflow.Step s event s' ∧ Related s' t') := by
  change t.toDirect = s at related
  have same : t = State.fromDirect s := calc
    t = State.fromDirect t.toDirect := (State.fromDirect_toDirect t).symm
    _ = State.fromDirect s := congrArg State.fromDirect related
  subst t
  constructor
  · intro event s' step
    exact ⟨State.fromDirect s', step_from_direct step, by simp [Related]⟩
  · intro event t' step
    exact ⟨t'.toDirect, by simpa using step_to_direct step, rfl⟩

theorem synchronised_iff (s : SourceV14.Workflow.State) :
    (State.fromDirect s).synchronised ↔ s.synchronised :=
  Iff.rfl

theorem startPermitted_iff (s : SourceV14.Workflow.State) (lesson : Lesson)
    (schedule : SourceV14.Booking.Schedule) (point : Moment) (students : List ActorId) :
    (State.fromDirect s).startPermitted lesson schedule point students ↔
      s.startPermitted lesson schedule point students :=
  Iff.rfl

theorem observation_equal {α : Sort u} {s : SourceV14.Workflow.State} {t : State}
    (same : Related s t) (read : SourceV14.Workflow.State → α) : read t.toDirect = read s :=
  congrArg read same

/-- The labelled paths keep every event, in order, including observational
events that do not establish compliance. -/
inductive Path {S : Type} (step : S → Event → S → Prop) : S → List Event → S → Prop where
  | nil (s : S) : Path step s [] s
  | next {s m t : S} {e : Event} {events : List Event}
      (first : step s e m) (rest : Path step m events t) : Path step s (e :: events) t

theorem path_to_direct {s t : State} {events : List Event} (path : Path Step s events t) :
    Path SourceV14.Workflow.Step s.toDirect events t.toDirect := by
  induction path with
  | nil s => exact .nil s.toDirect
  | next first _ ih => exact .next (step_to_direct first) ih

theorem path_from_direct {s t : SourceV14.Workflow.State} {events : List Event}
    (path : Path SourceV14.Workflow.Step s events t) :
    Path Step (State.fromDirect s) events (State.fromDirect t) := by
  induction path with
  | nil s => exact .nil (State.fromDirect s)
  | next first _ ih => exact .next (step_from_direct first) ih

theorem path_iff (s t : SourceV14.Workflow.State) (events : List Event) :
    Path SourceV14.Workflow.Step s events t ↔ Path Step (State.fromDirect s) events (State.fromDirect t) :=
  ⟨path_from_direct, fun proof ↦ by simpa using path_to_direct proof⟩

end RecognisedV15.Workflow
