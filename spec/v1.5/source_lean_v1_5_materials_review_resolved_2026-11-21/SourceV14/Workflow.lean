import SourceV14.Workflow.Records
import SourceV14.Workflow.Booking
import SourceV14.Workflow.Cancellation
import SourceV14.Workflow.Settlement
import SourceV14.Workflow.Payment
import SourceV14.Workflow.Materials
import SourceV14.Workflow.Redress
import SourceV14.Workflow.Review
import SourceV14.Workflow.Reserves
import SourceV14.Workflow.ServiceReserve
import SourceV14.Workflow.Debt
import SourceV14.Workflow.SeparateBooking
import SourceV14.Workflow.TutorFaultHistory
import SourceV14.Workflow.BookingEntitlements
import SourceV14.Workflow.LessonAccounts

namespace SourceV14.Workflow

open Course Confirmation

structure State where
  lessons : LessonId → LessonFile
  credit : CreditBook
  holds : HoldHistory
  cancelled : Cancellation.History
  settlement : Settlement.History
  redress : Redress.History
  materials : Materials.History
  review : Review.History
  debts : Debt.History
  activeReserves : List Reserves.Reservation
  paymentRecords : List Payment.Event
  separateBookings : List SeparateBooking.Link
  tutorFaults : TutorFaultHistory.History := TutorFaultHistory.History.empty
  verifiedContractualDiscount : PartOne → Moment → Prop := fun _ _ ↦ False
  verifiesClockBoundary : ClockBoundary → Prop := fun _ ↦ False
  verifiesServiceReserve : ServiceReserve.Account → Operations.ServiceReserveTransfer → Prop :=
    fun _ _ ↦ False
  serviceReserveFilings : List ServiceReserve.Filing := []
  verifiedAbsenceOutcome : ReviewFinding → PlaceId → Option Bool := fun _ _ ↦ none
  verifiedAgreedRefundTrigger : Redress.RefundTriggerEvidence := {}
  verifiedTutorReview : TutorFaultHistory.ReviewInterpretation := {}
  verifiedMaterialsGross : MaterialsGrossEvidence := {}

def State.course (s : State) (lesson : LessonId) : StartEvidence :=
  (s.lessons lesson).evidence s.credit

def State.materialsPrincipalContext (s : State) : MaterialsPrincipalContext :=
  ⟨s.review.paymentCorrections, s.verifiedMaterialsGross⟩

/-- Form Part 2 can retrieve an actual materials transfer even if the recipient's
    entitlement is disputed or later corrected. It is not an entitlement credit. -/
def State.materialsPaymentOccurrences (s : State) (lesson : LessonId)
    (material : MaterialId) (obligation : ObligationId) : List PostedPayment :=
  s.holds.payments.posted.filter fun paid ↦
    let part := paid.instruction.part
    paid.evidence.isSome && part.lesson == lesson && part.obligation == obligation &&
      (match part.purpose with
      | .materialsShare id _ | .materialsShortfall id _ _ => id == material
      | _ => false)

def State.synchronised (s : State) : Prop :=
  s.credit.creditRecords.payments = s.holds.payments

def State.withCourse (s : State) (lesson : LessonId) (ev : StartEvidence) : State :=
  { s with lessons := fun key ↦ if key = lesson then LessonFile.fromEvidence ev else s.lessons key
           credit := CreditBook.fromEvidence ev }

def State.withHolds (s : State) (holds : HoldHistory) : State :=
  { s with holds := holds
           credit := { s.credit with creditRecords :=
             { s.credit.creditRecords with payments := holds.payments } } }

/-- Read permission for this particular start while retaining the ability to
observe an unauthorised start. -/
def State.startPermitted (s : State) (lesson : Lesson) (schedule : SourceV14.Booking.Schedule)
    (atTime : Moment) (students : List ActorId) : Prop :=
  Booking.StartPermitted (s.course lesson.id) lesson schedule atTime students ∧
  Cancellation.CompatibleWithStart s.cancelled (s.course lesson.id) lesson atTime students

def Booking.Event.respectsCancellation (event : Booking.Event) (history : Cancellation.History) :
    Prop :=
  match event with
  | .verifyOneToOneAbsence form _ start .. => ¬Cancellation.PlaceCancelledAt history form.place start
  | _ => True

/-- A full provider register is the evidence for the effective places at
agreement. It cannot omit a known live place or include a place already cancelled. -/
def Booking.Event.usesEffectivePlaces (event : Booking.Event) (course : StartEvidence)
    (history : Cancellation.History) : Prop :=
  match event with
  | .rescheduleBeforeLock _ _ register | .replaceTutorBeforeLock _ _ _ register =>
    (∀ form ∈ register.forms, ¬Cancellation.PlaceCancelledAt history form.place register.atTime) ∧
    ∀ form ∈ course.effectiveForms ++ course.bookings.map Prod.fst,
      form.confirmedAt.by register.atTime →
      ¬Cancellation.PlaceCancelledAt history form.place register.atTime →
      form ∈ register.forms
  | _ => True

def Settlement.Event.respectsCancellation (event : Settlement.Event) (history : Cancellation.History) :
    Prop :=
  match event with
  | .assessFee entry => entry.decision.respectsCancellation history
  | _ => True

def Redress.Event.usesRecordedCancellation (event : Redress.Event) (history : Cancellation.History)
    (settlement : Settlement.History) :
    Prop :=
  match event with
  | .assessRefund assessment _ =>
    match assessment.evidence with
    | .noFault entry => Cancellation.HasNoFaultCancellation history assessment.amount.form entry
    | .agreedChange fee => fee ∈ settlement.fees ∧ fee.decision.respectsCancellation history
    | _ => True
  | _ => True

/-- A return of a verified refund has a separate joint refund-return event. -/
def Payment.Event.independentCreditChange (event : Payment.Event) (credit : CreditBook) : Prop :=
  match event with
  | .returnPayment entry =>
    ∀ old ∈ credit.creditRecords.verifiedRefunds, old.payment.id ≠ entry.paidReceipt
  | _ => True

def Materials.Event.recordLesson : Materials.Event → Option LessonId
  | .adopt lesson _ | .report lesson _ => some lesson.id
  | .checkCombination row => some row.lesson.id
  | .verify row => some row.use.lesson.id
  | .provision _ row => some row.pending.lesson
  | .settle row => some row.record.lesson
  | .transfer _ => none
  | .identifyShortfall row => some row.record.lesson
  | .establish row => some row.original.record.lesson
  | .post row | .verifyReceipt row _ _ => some row.form.lesson.id
  | .file paid _ => some paid.instruction.part.lesson

def Redress.Event.usesCurrentSelectedCourse (s : State) : Redress.Event → Prop
  | .recordDiscountUse booking selected => selected = s.course booking.agreed.lesson.id
  | _ => True

def Materials.Event.recordsPayment (event : Materials.Event) (before after : HoldHistory) : Prop :=
  match event with
  | .post row =>
    ∃ posted, Payment.Step before (.post row.paid) posted ∧
      match row.recipientReceipt with
      | none => after = posted
      | some recipient => Payment.Step posted (.agreedRecipient recipient) after
  | _ => after = before

def Review.Event.lesson : Review.Event → LessonId
  | .publishContacts lesson .. | .retainOriginal lesson _ | .decideReview lesson .. |
    .recordCorrection lesson _ => lesson.id
  | .receive entry | .acknowledge entry _ | .requestAppointment entry _ |
    .reply entry _ | .escalateReply entry .. => entry.lesson.id
  | .appoint appointment => appointment.matter.lesson
  | .decideInitial form .. => form.lesson.id
  | .checkRefundFunding row _ => row.form.lesson.id
  | .notifyShortage row _ => row.form.lesson.id
  | .fileCorrectedPayment row => row.form.lesson.id
  | .fileRecovery lesson .. => lesson.id
  | .escalateHeldReview form .. => form.lesson.id
  | .escalateRequestedReview entry .. => entry.lesson.id
  | .escalatePayment row => row.form.lesson.id

def Review.Event.readsMaterialsTerms (event : Review.Event) (history : Materials.History) : Prop :=
  match event with
  | .escalatePayment row => ∀ terms ∈ row.adoptedMaterials, terms ∈ history.terms
  | .fileCorrectedPayment row => ∀ terms ∈ row.adoptedMaterials, terms ∈ history.terms
  | _ => True

private def DecisionRecords.usesReviewHistory (records : CreditEvidence.DecisionRecords)
    (history : Review.History) : Prop :=
  records.appointments = history.appointments ∧
  records.initialFindings = history.initialFindings ∧ records.reviewFindings = history.reviewFindings

def Booking.Event.usesRecordedAbsenceFindings (event : Booking.Event) (history : Review.History) :
    Prop :=
  match event with
  | .verifyOneToOneAbsence _ _ _ _ facts reason .. =>
    facts.verifiedGoodReason.isSome → reason.decisionNeeded →
      DecisionRecords.usesReviewHistory reason.decisions history
  | _ => True

def Redress.Event.usesRecordedReviews (event : Redress.Event) (history : Review.History) : Prop :=
  ∀ records ∈ event.assessmentDecisions, DecisionRecords.usesReviewHistory records history

/-- A provision protects the funds against other lessons using the same entry.
Verifying or filing an observed payment leaves reservations unchanged. -/
def Materials.Event.fundingContext (event : Materials.Event) (active : List Reserves.Reservation) : Prop :=
  match event with
  | .provision _ row => Reserves.FundingContextMatches active row.funds
  | .post row => ∀ entry ∈ row.funds.entries,
    Reserves.occupiedElsewhere active row.funds entry.id +
      row.provisionFundsOutsideAvailable entry.id ≤ entry.committedElsewhere
  | _ => True

def Materials.Event.reservations (event : Materials.Event) (active : List Reserves.Reservation) :
    List Reserves.Reservation :=
  match event with
  | .provision _ row => Reserves.reserve active row.funds
  | _ => active

def Review.Event.fundingContext (event : Review.Event) (active : List Reserves.Reservation) : Prop :=
  match event with
  | .checkRefundFunding row _ => Reserves.FundingContextMatches active row.funds
  | .notifyShortage row _ => Reserves.FundingContextMatches active row.funds
  | _ => True

def Booking.Event.fundingContext (event : Booking.Event) (active : List Reserves.Reservation) : Prop :=
  match event with
  | .confirmPlace _ booking .. => Reserves.FundingContextMatches active booking.funding.funds
  | _ => True

/-- The booking check reads verified payments for its own lesson and check time. -/
private def fundingReceiptsBefore (history : PaymentHistory) (lesson : LessonId)
    (checkedAt : Moment) : PaymentHistory :=
  let posted := history.posted.filter (fun row ↦ row.instruction.part.lesson == lesson &&
    row.evidence.isSome && decide (row.instruction.atTime.before checkedAt))
  { posted
    returned := history.returned.filter (fun row ↦ decide (row.returnedAt.before checkedAt) &&
      posted.any (fun receipt ↦ receipt.id == row.paidReceipt))
    agreedRecipientReceipts := history.agreedRecipientReceipts.filter (fun row ↦
      decide (row.paid ∈ posted)) }

def Booking.Event.readsFundingReceipts (event : Booking.Event) (history : PaymentHistory) : Prop :=
  match event with
  | .confirmPlace form booking .. =>
    let supplied := fundingReceiptsBefore booking.funding.terms.payments form.lesson.id
      booking.funding.checkedAt
    let recorded := fundingReceiptsBefore history form.lesson.id booking.funding.checkedAt
    supplied.posted.Perm recorded.posted ∧ supplied.returned.Perm recorded.returned ∧
      supplied.agreedRecipientReceipts.Perm recorded.agreedRecipientReceipts
  | _ => True

/-- A new commitment cannot reuse the same funds against a material provision
already retained for that lesson. Use the new booking's possible cases and
count an existing provision within the same booked expense only once. -/
def Booking.Event.securesPendingMaterials (event : Booking.Event) (s : State) : Prop :=
  match event with
  | .confirmPlace form booking plan _ =>
    let payments := s.holds.payments
    let budgets := s.materials.liveMaterialBudgetsAt payments form.lesson.id form.confirmedAt
      s.materialsPrincipalContext
    let funding := { booking.funding with terms := { booking.funding.terms with payments } }
    budgets ≠ [] →
      funding.funds.secures (sumAmounts budgets Prod.snd) ∧
      funding.casesSecuredWithMaterials form.lesson
        ((plan.map (·.places)).getD [form.place]) budgets False
  | _ => True

def Booking.Event.reservations (event : Booking.Event) (active : List Reserves.Reservation) :
    List Reserves.Reservation :=
  match event with
  | .confirmPlace _ booking .. => Reserves.reserve active booking.funding.funds
  | _ => active

/-- Review reads the basis and portions of the refund actually assessed for this place. -/
def State.reviewEvidence (s : State) (evidence : Review.Evidence) : Review.Evidence :=
  let assessmentAt := fun (form : PartOne) obligation query ↦
    s.redress.assessments.find? (fun row ↦ decide
      (row.amount.form.lesson.id = form.lesson.id ∧ row.amount.form.place = form.place ∧
        row.amount.obligation = obligation ∧ row.amount.recordedAt.by query))
  { evidence with
    refundPortionsAt := fun form obligation query ↦
      (assessmentAt form obligation query).map (fun row ↦ (row.amount.recordedAt, row.amount.parts))
    refundOriginAt := fun form ref query ↦ do
      if ref.lesson ≠ form.lesson.id ∨ ref.purpose ≠ .lessonRefund form.place.id then none
      else
        let row ← assessmentAt form ref.obligation query
        some (row.amount.basis, row.amount.trigger,
          refundDeadline row.amount.schedule.originalExecutionDeadline row.amount.schedule.legalDeadline)
    refundPriorPrincipals := fun form obligation query ↦
      s.redress.otherRefundPrincipals form obligation s.review query }

/-- A recorded monetary correction supplies the dated payment-part link used by hold checks. -/
def Review.Event.updateHoldParts (event : Review.Event) (holds : HoldHistory) : HoldHistory :=
  match event with
  | .recordCorrection _ (.monetary original correction) =>
    holds.withPartRevision original.outcome correction
  | _ => holds

/-- §6.3 and Form Part 2. A reviewed refund can file an already evidenced
payment into the original credit account once, retaining exact reversals. -/
def CreditBook.withCorrectedRefund (book : CreditBook) (history : PaymentHistory)
    (posting : SourceV14.Booking.CreditPosting) (file : VerifiedLessonRefund) : CreditBook :=
  let reversals := (history.returned.filter (fun row ↦ row.paidReceipt == file.payment.id)).map
    (Redress.refundReturnPosting posting)
  { book with
    ledger := book.ledger ++ posting :: reversals
    creditRecords := { book.creditRecords with
      verifiedRefunds := book.creditRecords.verifiedRefunds ++ [file] } }

def CreditBook.mayFileCorrectedRefund (book : CreditBook) (history : PaymentHistory)
    (posting : SourceV14.Booking.CreditPosting) (file : VerifiedLessonRefund)
    (row : Review.CorrectedPayout) (scope : CorrectedMonetaryScope) : Prop :=
  row.payment.refundCredit = some posting ∧ file.payment = row.payment.paid ∧
  file.form = row.form ∧ file.obligation = row.correction.money.corrected.ref.obligation ∧
  file.settlement.amount = scope.principal ∧
  posting.id ∉ book.ledger.map (·.id) ∧
  (∀ earlier ∈ book.creditRecords.verifiedRefunds, earlier.payment.id ≠ file.payment.id) ∧
  let next := book.withCorrectedRefund history posting file
  book.creditRecords.payments = history ∧
  file.matches next.ledger history book.creditRecords.paymentAuthorities posting ∧
  ValidCreditHistory next.openingCredit next.ledger next.creditRecords

def Settlement.Event.readsConfirmedDebts (event : Settlement.Event) (debts : Debt.History) : Prop :=
  match event with
  | .assessTutor due =>
    ∀ debt, debt.debtor = due.agreement.tutor → debt.creditor = due.form.lesson.provider →
      debt.recordedAt.by due.settledAt →
      (debt ∈ due.basis.confirmedDebts due.form.lesson.id due.agreement.tutor ↔ debt ∈ debts.confirmed)
  | _ => True

/-- Evidence of an adopted factual correction for the same absence. -/
structure AbsenceReasonCorrection where
  form : PartOne
  schedule : SourceV14.Booking.Schedule
  start : Moment
  original : Review.OriginalRecord
  finding : ReviewFinding
  correction : SettlementCorrection
  goodReason : Bool

def AbsenceReasonCorrection.reason (change : AbsenceReasonCorrection) :
    AttendanceFacts.OneToOneAbsenceReason :=
  ⟨change.correction.recordedAt,
    ⟨change.finding.matter, change.finding.outcome, change.finding.reviewer, change.finding.decidedAt⟩,
    change.goodReason⟩

def AbsenceReasonCorrection.conforms (change : AbsenceReasonCorrection) (s : State) : Prop :=
  let f := change.form
  let course := s.course f.lesson.id
  let decided := change.finding.decidedAt
  let recorded := change.correction.recordedAt
  (.nonmonetary change.original change.finding change.correction : Review.Correction) ∈
    s.review.corrections ∧
  s.verifiedAbsenceOutcome change.finding f.place.id = some change.goodReason ∧
  decided.by recorded ∧
  (∃ occurrence ∈ course.verifiedOneToOneAbsence,
    occurrence.matchesAt f change.start recorded ∧ occurrence.schedule = change.schedule) ∧
  ∃ prior, course.oneToOneAbsenceReasons.getLast? = some prior ∧
    prior.outcome = change.original.outcome ∧
    prior.outcome.decidedAt.before decided ∧ prior.recordedAt.before recorded ∧
    prior.goodReason ≠ change.goodReason

/-- A known and applicable review must be reflected before making a new
assessment from the reason. Previously filed assessments remain in history. -/
def State.absenceReasonCurrentAt (s : State) (f : PartOne) (query : Moment) : Prop :=
  let course := s.course f.lesson.id
  ∀ prior ∈ AttendanceFacts.OneToOneAbsenceReason.latestAt course.oneToOneAbsenceReasons query,
    ∀ revision ∈ s.review.corrections,
      match revision with
      | .nonmonetary original finding record =>
        original.outcome = prior.outcome → record.recordedAt.by query →
          ∀ goodReason ∈ s.verifiedAbsenceOutcome finding f.place.id, goodReason = prior.goodReason
      | .monetary .. => True

def Settlement.Event.usesCurrentAbsence (event : Settlement.Event) (s : State) : Prop :=
  match event with
  | .assessFee entry =>
    match entry.decision.basis with
    | .absence .. | .agreedChange (.goodReasonAbsence ..) _ =>
      s.absenceReasonCurrentAt entry.decision.form entry.decision.decidedAt
    | _ => True
  | .assessTutor due =>
    due.basis.absenceWithoutTeaching.isSome →
      s.absenceReasonCurrentAt due.form due.settledAt
  | _ => True

def Redress.Event.usesCurrentAbsence (event : Redress.Event) (s : State) : Prop :=
  match event with
  | .assessRefund row _ =>
    match row.evidence with
    | .absence _ => s.absenceReasonCurrentAt row.amount.form row.amount.trigger
    | _ => True
  | _ => True

inductive Event where
  | credit (event : Credit.Event)
  | booking (event : Booking.Event) (discount : Option Redress.DiscountBooking := none)
  | cancellation (event : Cancellation.Event)
  | separateBooking (link : SeparateBooking.Link)
  | settlement (event : Settlement.Event)
  | payment (event : Payment.Event)
  | redress (event : Redress.Event)
  | refundReturned (paid : PostedPayment) (returned : ReturnedPayment) (posting : SourceV14.Booking.CreditPosting)
  | materials (lesson : LessonId) (event : Materials.Event)
  | review (evidence : Review.Evidence) (event : Review.Event)
  | debt (event : Debt.Event)
  | tutorFault (event : TutorFaultHistory.Event)
  | correctedRefund (evidence : Review.Evidence) (row : Review.CorrectedPayout)
      (posting : SourceV14.Booking.CreditPosting) (file : VerifiedLessonRefund)
  | clockBoundary (lesson : LessonId) (row : ClockBoundary)
  | reserveReleased (row : Reserves.Release) (verification : Reserves.Release → Prop)
  | fileServiceReserve (entry : ServiceReserve.Filing)
  | correctAbsenceReason (change : AbsenceReasonCorrection)

private def State.recordPayment (s : State) (holds : HoldHistory) (event : Payment.Event) : State :=
  { s.withHolds holds with paymentRecords := s.paymentRecords ++ [event] }

private def recordHoldClockBoundary (holds : HoldHistory) (row : ClockBoundary) :
    HoldHistory :=
  let boundaries := holds.clockBoundaries
  { holds with clockBoundaries := if row ∈ boundaries then boundaries else boundaries ++ [row] }

/-- Records change only at the responsible local step. The common account and
receipt histories are shared by all lessons, including a later booking. -/
inductive Step : State → Event → State → Prop where
  | credit {s : State} {event : Credit.Event} {next : CreditBook}
      (rule : Credit.Step s.credit event next) :
    Step s (.credit event) { s with credit := next }
  | booking {s : State} {event : Booking.Event} {after : StartEvidence}
      {discount : Option Redress.DiscountBooking}
      (funds : event.fundingContext s.activeReserves)
      (active : event.respectsCancellation s.cancelled)
      (places : event.usesEffectivePlaces (s.course event.lesson.id) s.cancelled)
      (rule : Booking.Step (s.course event.lesson.id) event after)
      (price : BookingEntitlements.confirmationAllowed s.course s.verifiedContractualDiscount
        s.redress event discount after)
      (findings : event.usesRecordedAbsenceFindings s.review)
      (materials : event.securesPendingMaterials s)
      (receipts : event.readsFundingReceipts s.holds.payments) :
    Step s (.booking event discount)
      { s.withCourse event.lesson.id after with
        activeReserves := event.reservations s.activeReserves
        redress := BookingEntitlements.recordConfirmation s.redress discount }
  | cancellation {s : State} {event : Cancellation.Event} {next : Cancellation.History}
      (checked : BookingEntitlements.noTimelyRearrangement (s.course event.form.lesson.id)
        s.separateBookings event)
      (rule : Cancellation.Step s.cancelled (s.course event.form.lesson.id) event next) :
    Step s (.cancellation event) { s with cancelled := next }
  | separateBooking {s : State} {link : SeparateBooking.Link} {next : List SeparateBooking.Link}
      (rule : SeparateBooking.Step (s.course link.original.lesson.id) (s.course link.next.lesson.id)
        s.separateBookings link next) :
    Step s (.separateBooking link) { s with separateBookings := next }
  | settlement {s : State} {event : Settlement.Event} {next : Settlement.History}
      (active : event.respectsCancellation s.cancelled)
      (debts : event.readsConfirmedDebts s.debts)
      (faults : TutorFaultHistory.settlementUses s.course s.review s.tutorFaults s.settlement
        s.verifiedTutorReview event)
      (recordedRedress : TutorFaultHistory.retainedRedressUses s.course s.tutorFaults s.redress event)
      (accounts : LessonAccounts.uses s.settlement s.redress s.review s.materials
        (s.course event.lesson) event s.verifiedMaterialsGross)
      (absence : event.usesCurrentAbsence s)
      (rule : Settlement.Step (s.course event.lesson) s.holds s.settlement event next) :
    Step s (.settlement event) { s with settlement := next }
  | payment {s : State} {event : Payment.Event} {next : HoldHistory}
      (separate : event.independentCreditChange s.credit)
      (rule : Payment.Step s.holds event next) :
    Step s (.payment event)
      (s.recordPayment next event)
  | redress {s : State} {event : Redress.Event} {next : Redress.History}
      {after : StartEvidence} {holds : HoldHistory}
      (cancellation : event.usesRecordedCancellation s.cancelled s.settlement)
      (selected : event.usesCurrentSelectedCourse s)
      (review : event.usesRecordedReviews s.review)
      (absence : event.usesCurrentAbsence s)
      (rule : Redress.Step s.redress (s.course event.form.lesson.id) s.holds event next after holds
        s.verifiedAgreedRefundTrigger s.review) :
    Step s (.redress event) ({ (s.withCourse event.form.lesson.id after).withHolds holds with redress := next })
  | refundReturned {s : State} {paid : PostedPayment} {returned : ReturnedPayment}
      {posting : SourceV14.Booking.CreditPosting} {next : HoldHistory}
      (matchCredit : Redress.refundReturnMatches (s.course paid.instruction.part.lesson)
        paid returned posting)
      (returnedPayment : Payment.Step s.holds (.returnPayment returned) next) :
    Step s (.refundReturned paid returned posting)
      (let recorded := s.recordPayment next (.returnPayment returned)
       { recorded with credit := { recorded.credit with ledger := s.credit.ledger ++ [posting] } })
  | materials {s : State} {lesson : LessonId} {event : Materials.Event} {next : Materials.History} {holds : HoldHistory}
      (sameLesson : ∀ id ∈ event.recordLesson, id = lesson)
      (funds : event.fundingContext s.activeReserves)
      (rule : Materials.Step (s.course lesson) s.holds s.materials event next
        s.materialsPrincipalContext)
      (payment : event.recordsPayment s.holds holds) :
    Step s (.materials lesson event)
      { s.withHolds holds with materials := next, activeReserves := event.reservations s.activeReserves }

  | review {s : State} {evidence : Review.Evidence} {event : Review.Event} {next : Review.History}
      (funds : event.fundingContext s.activeReserves)
      (materials : event.readsMaterialsTerms s.materials)
      (tutorPay : ∀ row, event = .fileCorrectedPayment row →
        TutorFaultHistory.correctedPayoutUses s.course s.review s.tutorFaults s.settlement
          s.verifiedTutorReview row ∧
        TutorFaultHistory.retainedRedressCorrectedPayoutUses s.course s.tutorFaults s.redress row)
      (rule : Review.Step (s.reviewEvidence evidence) (s.course event.lesson) s.holds s.review event next) :
    Step s (.review evidence event) { s with review := next, holds := event.updateHoldParts s.holds }
  | debt {s : State} {event : Debt.Event} {next : Debt.History}
      (rule : Debt.Step (s.course event.form.lesson.id) s.redress s.debts event next) :
    Step s (.debt event) { s with debts := next }
  | tutorFault {s : State} {event : TutorFaultHistory.Event} {next : TutorFaultHistory.History}
      (rule : TutorFaultHistory.Step s.course s.review s.verifiedTutorReview s.tutorFaults event next) :
    Step s (.tutorFault event) { s with tutorFaults := next }
  | correctedRefund {s : State} {evidence : Review.Evidence} {row : Review.CorrectedPayout}
      {posting : SourceV14.Booking.CreditPosting} {file : VerifiedLessonRefund} {next : Review.History}
      {scope : CorrectedMonetaryScope}
      (basis : row.paymentScope s.review (s.reviewEvidence evidence) = some scope)
      (mayFile : s.credit.mayFileCorrectedRefund s.holds.payments posting file row scope)
      (rule : Review.Step (s.reviewEvidence evidence)
        ((s.lessons row.form.lesson.id).evidence (s.credit.withCorrectedRefund s.holds.payments posting file))
        s.holds s.review (.fileCorrectedPayment row) next) :
    Step s (.correctedRefund evidence row posting file)
      { s with review := next, credit := s.credit.withCorrectedRefund s.holds.payments posting file }
  /-- Later evidence may establish the order of a duration boundary at its actual anchor. -/
  | clockBoundary {s : State} {lesson : LessonId} {row : ClockBoundary}
      (proved : s.verifiesClockBoundary row) (elapsed : 0 < row.duration)
      (courseBoundary : ClockBoundary.find ((s.course lesson).clockBoundaries ++ [row])
        row.anchor row.direction row.duration = some row.cutoff)
      (holdBoundary : ClockBoundary.find (recordHoldClockBoundary s.holds row).clockBoundaries
        row.anchor row.direction row.duration = some row.cutoff) :
    Step s (.clockBoundary lesson row)
      ((s.withCourse lesson { s.course lesson with
        clockBoundaries := (s.course lesson).clockBoundaries ++ [row] }).withHolds
          (recordHoldClockBoundary s.holds row))
  | reserveReleased {s : State} {row : Reserves.Release} {verification : Reserves.Release → Prop}
      {earlier suffix : List Reserves.Reservation} {reservation : Reserves.Reservation}
      (retained : s.activeReserves = earlier ++ reservation :: suffix)
      (same : row.matches reservation) (verified : verification row) :
    Step s (.reserveReleased row verification)
      { s with activeReserves := earlier ++ { reservation with amount := reservation.amount - row.amount } :: suffix }


  | fileServiceReserve {s : State} {entry : ServiceReserve.Filing}
      (accounted : entry.conforms s.verifiesServiceReserve
        (s.course entry.form.lesson.id) s.redress s.review s.tutorFaults s.holds)
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
      (verified : change.conforms s) :
    Step s (.correctAbsenceReason change)
      (let lesson := change.form.lesson.id
       let course := s.course lesson
       s.withCourse lesson { course with
         oneToOneAbsenceReasons := course.oneToOneAbsenceReasons ++ [change.reason] })

end SourceV14.Workflow
