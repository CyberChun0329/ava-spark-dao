import SourceV14.Workflow.Settlement

/-!
Source v1.5 §§2.2, 3.1, 3.5–3.6 and 4.3. Assessments, remedy delivery, and retained
credit are separate occurrences. The confirmed account, actual receipt, and filing
of an approved lesson refund refer to the same posting.
-/

namespace SourceV14.Workflow.Redress

open Booking _root_.SourceV14.Settlement Confirmation Course CreditEvidence Operations

/-- Verified facts for the affected place, including an authorised finding when required. -/
structure FaultFacts where
  form : PartOne
  fault : FaultBasis
  authority : Option FaultDecisionRecord
  disputed : Bool
  decisions : DecisionRecords
  teaching : TeachingReceived

def FaultFacts.established (facts : FaultFacts) (ev : StartEvidence) (atTime : Moment) : Prop :=
  let f := facts.form
  (∃ roster forms, ev.rosterFormsAt f.lesson atTime roster forms ∧ f ∈ forms) ∧
  FaultDecisionWhenRequired facts.fault facts.disputed facts.authority facts.decisions f atTime ∧
  FaultMatchesEvidence f facts.fault facts.decisions ev.ledger ev.discounts
    ev.creditRecords.lessonFees atTime

structure AcceptedRemedy where
  id : Nat
  facts : FaultFacts
  agreement : RemedyAgreement
  dates : Option CompensationDates

structure RecordedDelivery where
  remedy : Nat
  atTime : Moment
  delivery : RemedyDelivery

structure RefundAssessment where
  form : PartOne
  obligation : ObligationId
  basis : RefundBasis
  reason : String
  trigger : Moment
  recordedAt : Moment
  schedule : PaymentSchedule
  finalFee : Amount
  principal : Amount
  parts : List PaymentPart

structure AbsenceAssessment where
  schedule : Schedule
  start : Moment
  handler : Handler
  assignment : SettlementAssignment
  facts : AbsenceFacts
  reason : AbsenceReasonEvidence
  settlement : LessonSettlement

inductive AssessmentEvidence where
  | noFault (cancellation : NoFaultCancellationRecord)
  | agreedChange (fee : SourceV14.Workflow.Settlement.AdoptedFee)
  | absence (absence : AbsenceAssessment)
  | originalCompensation (fault : FaultFacts) (relief : OriginalCompensationSettlement)
  | faultRefund (fault : FaultFacts) (cause : RefundCause) (acceptanceEvent : Option PaymentTrigger)

/-- Trusted interpretation of the signed refund term and independently verified occurrences. -/
structure RefundTriggerEvidence where
  cancellationTerm : PartOne → PaymentDeadline → Prop := fun _ _ ↦ False
  otherOccurrence : PartOne → PaymentDeadline → PaymentTrigger → Prop := fun _ _ _ ↦ False

/-- A non-start relative term uses its verified occurrence and the retained clock. -/
def RefundTriggerEvidence.applies (evidence : RefundTriggerEvidence) (f : PartOne)
    (ev : StartEvidence) (term : PaymentDeadline) (event : Option PaymentTrigger)
    (cancellation : Option CancellationRequest) (observed : Moment) : Prop :=
  match term with
  | .after _ _ false =>
    ∃ actual ∈ event, actual.boundaries = ev.clockBoundaries ∧ actual.point.by observed ∧
      ((evidence.cancellationTerm f term ∧
        ∃ request ∈ cancellation, actual.point = request.point) ∨
       (¬ evidence.cancellationTerm f term ∧ evidence.otherOccurrence f term actual))
  | _ => True

structure AssessedRefund where
  amount : RefundAssessment
  evidence : AssessmentEvidence
  dueEvent : Option PaymentTrigger
  executionEvent : Option PaymentTrigger

structure History where
  remedies : List AcceptedRemedy := []
  extensions : List (Nat × RemedyExtension) := []
  unable : List (Nat × Moment) := []
  deliveries : List RecordedDelivery := []
  requests : List DirectRefundRequest := []
  availableDiscounts : List (Nat × LaterBenefitAvailability) := []
  usedDiscounts : List LaterBenefitUse := []
  assessments : List AssessedRefund := []
  pendingDiscountUses : List LaterBenefitUse := []

def FaultFacts.evidence (facts : FaultFacts) (ev : StartEvidence) : RemedyEvidence where
  lesson := facts.fault.lessonWithResponsibleTutor facts.form.lesson
  fault := facts.fault
  ledger := ev.ledger
  ownsAccount := ev.creditRecords.ownsAccount
  closed := ev.creditRecords.closed
  teaching := facts.teaching
  feeAt := ev.feeAt facts.form

/-- The pre-event history supplies the currently recorded delivery and any earlier extensions. -/
def History.progress (h : History) (ev : StartEvidence) (entry : AcceptedRemedy) : RemedyProgress where
  agreement := entry.agreement
  extensions := (h.extensions.filter (fun row ↦ row.1 == entry.id)).map Prod.snd
  delivery := (h.deliveries.find? (fun row ↦ row.remedy == entry.id)).map (·.delivery)
  providerConfirmedUnableAt := (h.unable.find? (fun row ↦ row.1 == entry.id)).map Prod.snd
  stillOwedAt := fun query ↦
    entry.agreement.acceptedAt.by query ∧
    (∀ row ∈ h.deliveries, row.remedy = entry.id → ¬ row.atTime.by query) ∧
    ¬fullRefundClosedBy entry.facts.form.place ev.creditRecords.closed query

def History.remediesFor (h : History) (form : PartOne) : List AcceptedRemedy :=
  h.remedies.filter (fun entry ↦ entry.agreement.lesson == form.lesson.id &&
    entry.agreement.place == form.place.id)

private def RefundAssessment.partRef (a : RefundAssessment) : PaymentPartRef :=
  ⟨a.form.lesson.id, a.obligation, 0, .lessonRefund a.form.place.id⟩

/-- Read the principal from the retained assessment and its adopted corrections. -/
def RefundAssessment.principalAt (a : RefundAssessment) (reviews : Review.History)
    (query : Moment) : Option Amount :=
  reviews.refundPrincipalAt a.partRef (.lessonRefund a.form.place.account)
    a.recordedAt a.parts query

/-- A revision of this obligation must still be operative for its exact part. -/
def RefundAssessment.currentReviewAt (a : RefundAssessment) (reviews : Review.History)
    (query : Moment) : List ReviewFinding :=
  let revised := reviews.paymentCorrections.filter fun row ↦
    row.originalPart.ref.sameObligation a.partRef &&
      row.money.corrected.recipient.samePayee (.lessonRefund a.form.place.account) &&
      (reviews.correctedScopeAt row query (some (a.recordedAt, a.parts))).isSome
  ((revised.filter fun row ↦ !revised.any fun later ↦
    decide (row.finding.decidedAt.before later.finding.decidedAt)).map (·.finding)).eraseDups

/-- The typed refund outcome can be retained with the correction or with its verified receipt. -/
def RefundAssessment.reviewedOutcomeAt (a : RefundAssessment) (reviews : Review.History)
    (finding : ReviewFinding) (query : Moment) : Option AssessedFaultRefund :=
  let sameRefund := fun row : PaymentCorrectionCase ↦
    row.finding == finding && row.originalPart.ref.lesson == a.form.lesson.id &&
      row.originalPart.ref.obligation == a.obligation &&
      row.originalPart.ref.purpose == .lessonRefund a.form.place.id &&
      row.money.corrected.recipient == .lessonRefund a.form.place.account &&
      decide (row.correction.recordedAt.by query)
  (reviews.refundAssessments.findSome? fun (row, outcome) ↦
    if sameRefund row then some outcome else none).orElse fun _ ↦
      reviews.correctedPayouts.findSome? fun file ↦
        if sameRefund file.correction && decide (file.recordedAt.by query) then
          match file.reviewedRefund with
          | some (.faultRefund outcome) => some outcome
          | _ => none
        else none

private def RefundAssessment.feeFromReview (a : RefundAssessment) (principal : Option Amount)
    (findings : List ReviewFinding) (outcomeFor : ReviewFinding → Option AssessedFaultRefund) :
    Option Amount :=
  let original := if principal = some a.principal then some a.finalFee else none
  match findings with
  | [] => original
  | [finding] => ((outcomeFor finding).map (·.finalFee)).or original
  | _ => none

/-- A reviewed principal alone does not settle what fee applies or whether a remedy remains. -/
def AssessedRefund.feeAt (assessment : AssessedRefund) (reviews : Review.History)
    (query : Moment) : Option Amount :=
  let a := assessment.amount
  a.feeFromReview (a.principalAt reviews query) (a.currentReviewAt reviews query)
    (fun finding ↦ a.reviewedOutcomeAt reviews finding query)

def History.refundsFor (h : History) (form : PartOne) : List RefundAssessment :=
  (h.assessments.map (·.amount)).filter fun row ↦ decide
    (row.form.lesson.id = form.lesson.id ∧ row.form.place.id = form.place.id ∧
      row.form.place.account = form.place.account)

private def earlierRefundsFrom (refunds : List RefundAssessment) (a : RefundAssessment)
    (reviews : Review.History) : Option (List EarlierFeeRefund) :=
  refunds.filter (fun row ↦ decide (row.trigger.before a.trigger)) |>.mapM
    fun row ↦ do
      let amount ← row.principalAt reviews a.recordedAt
      pure { id := row.obligation
             lesson := row.form.lesson.id
             place := row.form.place.id
             trigger := row.trigger
             due := row.schedule.dueAt
             executionDeadline := row.schedule.originalExecutionDeadline
             legalDeadline := row.schedule.legalDeadline
             amount }

def History.earlierRefunds (h : History) (a : RefundAssessment) (reviews : Review.History) :
    Option (List EarlierFeeRefund) :=
  earlierRefundsFrom (h.refundsFor a.form) a reviews

def History.otherRefundPrincipals (h : History) (form : PartOne) (obligation : ObligationId)
    (reviews : Review.History) (query : Moment) : Option (List (ObligationId × Amount)) := do
  let assessments := h.refundsFor form
  let assessed ← (assessments.filter (fun row ↦
    row.obligation != obligation && decide (row.recordedAt.by query))).mapM fun row ↦ do
      let amount ← row.principalAt reviews query
      pure (row.obligation, amount)
  let reviewed ← reviews.priorRefundPrincipalsFromOriginals form.place
    (obligation :: assessments.map (·.obligation)) query query
  pure (assessed ++ reviewed)

def AssessedRefund.refundEvents (assessment : AssessedRefund) : List PaymentTrigger :=
  (assessment.dueEvent.toList ++ assessment.executionEvent.toList).eraseDups

noncomputable def AssessedRefund.faultCase (assessment : AssessedRefund) (h : History)
    (ev : StartEvidence) (facts : FaultFacts) (cause : RefundCause)
    (acceptance : Option PaymentTrigger) (earlier : List EarlierFeeRefund) : FaultRefundCase := by
  classical
  let a := assessment.amount
  let remedies := h.remediesFor a.form
  exact
    { form := a.form
      fault := facts.fault
      authority := facts.authority
      disputed := facts.disputed
      decisions := facts.decisions
      ledger := ev.ledger
      discounts := ev.discounts
      teaching := facts.teaching
      ownsAccount := ev.creditRecords.ownsAccount
      closed := ev.creditRecords.closed
      remedies := remedies.map (h.progress ev)
      benefits := h.availableDiscounts.map Prod.snd
      requests := h.requests
      refundEvents := assessment.refundEvents
      acceptanceEvent := acceptance
      lessonEvidence := ev
      compensationDates := fun agreement ↦
        ((remedies.find? fun entry ↦ decide (entry.agreement = agreement))).bind
          (·.dates)
      obligation := a.obligation
      cause := cause
      establishedEarlier := earlier }

/-- The established payment parts refer to this refund, original account and assessed total. -/
def RefundAssessment.partsMatch (a : RefundAssessment) (facts : HoldFacts) : Prop :=
  let purpose := PaymentPurpose.lessonRefund a.form.place.id
  let stated := (facts.establishedParts a.form.lesson.id purpose).filter
    (fun part ↦ part.ref.obligation == a.obligation)
  stated = a.parts ∧
  (a.parts.map PaymentPart.ref).Nodup ∧ sumAmounts a.parts PaymentPart.amount = a.principal ∧
  ∀ part ∈ a.parts, part.ref.lesson = a.form.lesson.id ∧ part.ref.purpose = purpose ∧
    part.recipient = .lessonRefund a.form.place.account ∧ 0 < part.amount

/-- Calculate the refund once at assessment, using actual prior receipts and earlier obligations. -/
def AssessedRefund.conforms (assessment : AssessedRefund) (h : History) (ev : StartEvidence)
    (holds : HoldHistory) (holdFacts : HoldFacts)
    (clockEvidence : RefundTriggerEvidence := {}) (reviews : Review.History := .empty) : Prop :=
  let a := assessment.amount
  let f := a.form
  let refunds := h.refundsFor f
  let represented := a.obligation :: refunds.map (·.obligation)
  let independent := reviews.priorRefundPrincipalsFromOriginals f.place represented
    a.trigger a.recordedAt
  match earlierRefundsFrom refunds a reviews, independent with
  | some earlier, some independent =>
    let dated := f.deadlines.refund.due.appliesForLesson f.lesson ev a.recordedAt
        assessment.dueEvent a.schedule.dueAt ∧
      f.deadlines.refund.latestExecution.appliesForLesson f.lesson ev a.recordedAt
        assessment.executionEvent a.schedule.originalExecutionDeadline
    let reduced := fun settlement : LessonSettlement ↦
      a.finalFee = settlement.feePayable ∧
      a.principal = feeAdjustmentRefundPrincipal f.place ev.ledger a.trigger
        a.obligation settlement.creditDueBack earlier independent
    f.matches ∧ a.reason ≠ "" ∧ a.trigger.by a.recordedAt ∧
    0 ≤ a.finalFee ∧ 0 ≤ a.principal ∧ a.principal ≤ debitTotal f.place ev.ledger a.trigger ∧
    EarlierFeeRefundsFor f.place a.trigger earlier ∧ a.partsMatch holdFacts ∧
    postLiftTermMatches f.deadlines.postLiftPay a.schedule ∧
    (∀ old ∈ h.assessments, old.amount.form.lesson.id = f.lesson.id →
      old.amount.form.place.id = f.place.id →
      old.amount.obligation ≠ a.obligation ∧
        (old.amount.basis ≠ a.basis ∨ old.amount.trigger ≠ a.trigger)) ∧
    match assessment.evidence with
    | .noFault cancellation =>
      a.basis = .noFaultCancellation ∧ a.reason = "no-fault cancellation" ∧
      a.trigger = cancellation.cancellation.point ∧
      a.obligation = cancellation.refundObligation ∧ cancellation.conforms f ev ∧
      a.principal = cancellation.refundAmount f ev ∧
      (∃ fee, ev.feeAt f a.trigger fee ∧ a.finalFee =
        (if cancellation.noneTaught then 0 else fee - a.principal)) ∧
      noFaultRefundDeadline f ev f.deadlines.noFaultRefundTerms.due assessment.refundEvents
        a.trigger a.recordedAt a.schedule.dueAt ∧
      noFaultRefundDeadline f ev f.deadlines.noFaultRefundTerms.latestExecution
        assessment.refundEvents a.trigger a.recordedAt a.schedule.originalExecutionDeadline
    | .agreedChange fee =>
      a.basis = .agreedChange ∧ fee.decision.form = f ∧
      fee.decision.agreedChangeAt = some a.trigger ∧ fee.decision.decidedAt.by a.recordedAt ∧
      dated ∧
      clockEvidence.applies f ev f.deadlines.refund.due assessment.dueEvent
        fee.decision.agreedCancellation a.recordedAt ∧
      clockEvidence.applies f ev f.deadlines.refund.latestExecution assessment.executionEvent
        fee.decision.agreedCancellation a.recordedAt ∧
      reduced fee.decision.amounts
    | .absence absence =>
      a.basis = .absence ∧ dated ∧ reduced absence.settlement ∧
      HalfFeeAbsenceRecorded f ev absence.schedule absence.start a.trigger absence.handler
        absence.assignment absence.facts absence.reason holds holdFacts ev.ledger absence.settlement
    | .originalCompensation facts relief =>
      facts.form = f ∧ facts.established ev relief.settledAt ∧
      a.basis = .standardCompensation ∧ a.trigger = relief.settledAt ∧ dated ∧
      reduced relief.settlement ∧
      (∃ fee, ev.feeAt f relief.settledAt fee ∧
        relief.amountsRecorded f.place facts.teaching ev.ledger a.recordedAt fee) ∧
      AppliesOriginalCompensation f facts.fault facts.authority facts.disputed facts.decisions
        ev.ledger ev.discounts ev.creditRecords.lessonFees relief.settledAt a.recordedAt facts.teaching
        ((h.remediesFor f).map (·.agreement)) relief.settlement
    | .faultRefund facts cause acceptance =>
      facts.form = f ∧ facts.established ev a.recordedAt ∧ a.basis = cause.basis ∧
      let c := assessment.faultCase h ev facts cause acceptance earlier
      c.newObligationAt a.trigger ∧
      PaymentDeadline.fromRefundTrigger f.deadlines.refund.due c.refundEvents
        a.trigger a.schedule.dueAt ∧
      c.amountDue a.recordedAt a.trigger a.schedule.originalExecutionDeadline
        (refundDeadline a.schedule.originalExecutionDeadline a.schedule.legalDeadline)
        a.schedule.legalDeadline a.finalFee a.principal independent
  | _, _ => False

/-- Materialise only the refund event and its matching payment and approval evidence. -/
def receiveRefund (ev : StartEvidence) (posting : CreditPosting)
    (file : VerifiedLessonRefund) (payments : PaymentHistory) : StartEvidence :=
  { ev with
    ledger := ev.ledger ++ [posting]
    creditRecords := { ev.creditRecords with
      payments
      verifiedRefunds := ev.creditRecords.verifiedRefunds ++ [file] } }

/-- A posting cannot reuse a prior ledger ID or be inserted before an actual posting. -/
def FreshPosting (ev : StartEvidence) (posting : CreditPosting) : Prop :=
  ∀ old ∈ ev.ledger, old.id ≠ posting.id ∧ old.point.before posting.point

def usedApproval : PaymentApprovalRoute → PaymentApproval
  | .ordinary approval | .liftOriginal approval _ | .liftFirst approval _ => approval
  | .liftReplacement _ replacement _ => replacement

structure RefundPosting where
  assessment : AssessedRefund
  posting : CreditPosting
  filing : VerifiedLessonRefund
  part : PaymentPart
  route : Option PaymentApprovalRoute := none
  postLift : Option PostLiftPaymentRecord

/-- The form row and evidenced receipt match the assessed refund and the original debit. -/
def RefundPosting.verifiedFiling (post : RefundPosting) (h : History) (ev : StartEvidence)
    (ledger : List CreditPosting) (payments : PaymentHistory) (facts : HoldFacts)
    (a : ReviewAuthorities) (knownAt : Moment := post.posting.point) : Prop :=
  let assessment := post.assessment.amount
  let f := assessment.form
  let file := post.filing
  let receipt := post.posting
  let record := file.settlement
  let originalWaiver := match post.assessment.evidence with
    | .originalCompensation fault _ => fault.teaching = .none
    | _ => False
  post.assessment ∈ h.assessments ∧
  (assessment.recordedAt.by knownAt ∧ assessment.trigger.by receipt.point) ∧
  file.form = f ∧ file.obligation = assessment.obligation ∧
  post.part ∈ assessment.parts ∧
  assessment.partsMatch facts ∧ ev.creditRecords.paymentAuthorities = a ∧
  (∀ old ∈ ev.creditRecords.verifiedRefunds, old.payment.id ≠ file.payment.id) ∧
  record.basis = assessment.basis ∧ record.finalFee = assessment.finalFee ∧
  record.closesCase = false ∧
  (record.originalWaivedCompensationContinues = true ↔
    originalWaiver ∧ ∃ remedy ∈ h.remediesFor f, remedy.agreement.acceptedStandardFor f.place ∧
      (h.progress ev remedy).stillOwedAt receipt.point) ∧
  record.matches f ledger receipt.point assessment.reason assessment.trigger
    (refundDeadline assessment.schedule.originalExecutionDeadline assessment.schedule.legalDeadline)
    assessment.principal (some assessment.obligation) ∧
  file.matches ledger payments a receipt

/-- A frozen assessment supplies the obligation and clock. Filing never reassesses them. -/
def RefundPosting.validFiling (post : RefundPosting) (h : History) (ev : StartEvidence)
    (ledger : List CreditPosting) (holds : HoldHistory) (facts : HoldFacts) (a : ReviewAuthorities)
    (conditions : PaymentInstruction → Prop) (reviews : Review.History := .empty) : Prop :=
  let assessment := post.assessment.amount
  (post.verifiedFiling h ev ledger holds.payments facts a ∧
    ∃ principals ∈ h.otherRefundPrincipals assessment.form assessment.obligation reviews
        post.posting.point,
      ValidLessonRefund assessment.form.place ledger post.posting assessment.obligation
        assessment.principal false principals) ∧
  ∃ route ∈ post.route, post.filing.approval = some (usedApproval route) ∧
    LessonRefundFiled assessment.form a facts holds post.part assessment.schedule route conditions
      post.posting assessment.obligation assessment.principal post.filing.payment post.postLift.toList

/-- Actual payment and credit to the original account are appended together. -/
def RefundPosting.conforms (post : RefundPosting) (h : History) (ev : StartEvidence)
    (before after : HoldHistory) (facts : HoldFacts) (a : ReviewAuthorities)
    (conditions : PaymentInstruction → Prop) (reviews : Review.History := .empty) : Prop :=
  let paid := post.filing.payment
  FreshPosting ev post.posting ∧ paid.id ∉ before.payments.posted.map PostedPayment.id ∧
  after = { before with payments := { before.payments with
    posted := before.payments.posted ++ [paid] } } ∧
  ev.creditRecords.payments = before.payments ∧
  post.validFiling h ev (ev.ledger ++ [post.posting]) after facts a conditions reviews

/-- The same account and receipt identify the credit removed by an actual return. -/
def refundReturnPosting (receipt : CreditPosting) (returned : ReturnedPayment) : CreditPosting where
  id := returned.id
  account := receipt.account
  kind := .creditReturned receipt.id
  amount := returned.amount
  point := returned.returnedAt

/-- Apply a return only to its already filed refund credit and to the very same account. -/
def refundReturnMatches (ev : StartEvidence) (paid : PostedPayment) (returned : ReturnedPayment)
    (reversal : CreditPosting) : Prop :=
  (∀ old ∈ ev.ledger, old.id ≠ reversal.id ∧ old.point ≠ reversal.point) ∧
  returned.paidReceipt = paid.id ∧
  paid.instruction.atTime.before returned.returnedAt ∧ 0 < returned.amount ∧
  ∃ file ∈ ev.creditRecords.verifiedRefunds, file.payment = paid ∧
    ∃ receipt ∈ ev.ledger,
      LessonRefundReceiptMatches file.form.place receipt file.obligation paid
        ev.creditRecords.payments ∧
      reversal = refundReturnPosting receipt returned ∧
      returnedFrom ev.ledger receipt reversal.point + reversal.amount ≤ receipt.amount ∧
      reversal.amount ≤ balanceBefore ev.openingCredit ev.ledger reversal.account reversal.point

def observedRefundReturns (receipt : CreditPosting) (payments : PaymentHistory) :
    List CreditPosting :=
  (payments.returned.filter (fun row ↦ row.paidReceipt == receipt.id)).map
    (refundReturnPosting receipt)

/-- Insert the observed credit and its already observed returns once, at their actual times. -/
def ledgerWithObservedRefund (ev : StartEvidence) (posting : CreditPosting)
    (payments : PaymentHistory) : List CreditPosting :=
  let actual := posting :: observedRefundReturns posting payments
  ev.ledger ++ actual.filter (fun entry ↦ !ev.ledger.contains entry)

/-- File the actual amount received for the assessed obligation, including any excess.
An approval cited in the filing must be on record. The separate execution step enforces its limits. -/
def RefundPosting.observedFiling (post : RefundPosting) (h : History) (ev : StartEvidence)
    (holds : HoldHistory) (recordedAt : Moment) (facts : HoldFacts) (a : ReviewAuthorities) : Prop :=
  let ledger := ledgerWithObservedRefund ev post.posting holds.payments
  let paid := post.filing.payment.instruction
  post.posting.point.by recordedAt ∧ (ledger.map CreditPosting.id).Nodup ∧
  (ledger.map CreditPosting.point).Nodup ∧ ev.creditRecords.payments = holds.payments ∧
  (∀ entry ∈ observedRefundReturns post.posting holds.payments, entry.point.by recordedAt ∧
    entry.amount ≤ balanceBefore ev.openingCredit ledger entry.account entry.point) ∧
  post.verifiedFiling h ev ledger holds.payments facts a recordedAt ∧
  (∀ approval ∈ post.filing.approval, holds.approvalRecorded approval) ∧
  paid.part = post.part.ref ∧ post.part.recipient.accepts paid.destination ∧
  holds.payments.distinctReceipts ∧ holds.payments.validReturns

def fileRefund (ev : StartEvidence) (posting : CreditPosting)
    (file : VerifiedLessonRefund) : StartEvidence :=
  { ev with
    ledger := ledgerWithObservedRefund ev posting ev.creditRecords.payments
    creditRecords := { ev.creditRecords with
      verifiedRefunds := ev.creditRecords.verifiedRefunds ++ [file] } }

/-- Only credit that can be used for booking affects the customer's usable balance. -/
def issueCourseCredit (ev : StartEvidence) (grant : CompensationCreditOrigin)
    (posting : CreditPosting) : StartEvidence :=
  { ev with
    ledger := ev.ledger ++ [posting]
    creditRecords := { ev.creditRecords with grants := ev.creditRecords.grants ++ [grant] } }

def AcceptedRemedy.creditOrigin (remedy : AcceptedRemedy) (issue : CourseCreditIssue)
    (ev : StartEvidence) : CompensationCreditOrigin where
  originalForm := remedy.facts.form
  lesson := remedy.facts.form.lesson
  original := remedy.facts.form.place
  fault := remedy.facts.fault
  authority := remedy.facts.authority
  disputed := remedy.facts.disputed
  decisions := remedy.facts.decisions
  originalDiscounts := ev.discounts
  agreement := remedy.agreement
  issue := issue

/-- Record a real credit removal for each prescribed unused-credit treatment being applied. -/
def closeRefund (ev : StartEvidence) (closure : FullRefundClosure)
    (removals : List CreditPosting) : StartEvidence :=
  { ev with
    ledger := ev.ledger ++ removals
    creditRecords := { ev.creditRecords with closed := ev.creditRecords.closed ++ [closure] } }

def closureRemovalsMatch (closure : FullRefundClosure) (ev : StartEvidence)
    (removals : List CreditPosting) : Prop :=
  let ledger := (closeRefund ev closure removals).ledger
  (removals.map (·.id)).Nodup ∧ (removals.map (·.point)).Nodup ∧
  ∀ posting ∈ removals, FreshPosting ev posting ∧ posting.point.by closure.closedAt ∧
    compensationClosureRemovalPosting ledger [closure] posting ∧
    posting.amount ≤ balanceBefore ev.openingCredit ledger posting.account posting.point

private def AssessedRefund.reviewedFeeConformsWithPrincipal (assessment : AssessedRefund)
    (h : History) (ev : StartEvidence) (reviews : Review.History) (finding : ReviewFinding)
    (outcome : AssessedFaultRefund) (principal : Option Amount) (closing : Bool) : Prop :=
  let a := assessment.amount
  let refunds := h.refundsFor a.form
  let c := outcome.faultCase
  let decisions := reviews.decisionRecords c.decisions.authorities c.decisions
  let evidence : FaultFacts := ⟨c.form, c.fault, c.authority, c.disputed, decisions, c.teaching⟩
  c.form = a.form ∧ c.obligation = a.obligation ∧ outcome.trigger = a.trigger ∧
  outcome.agreedDeadline = a.schedule.originalExecutionDeadline ∧
  outcome.legalDeadline = a.schedule.legalDeadline ∧
  reviewFindingRecordedConforms decisions.authorities (some a.form.contacts.reviewer)
    decisions.appointments decisions.initialFindings decisions.reviewFindings finding ∧
  0 ≤ outcome.finalFee ∧
  ∃ earlier ∈ earlierRefundsFrom refunds a reviews,
  ∃ independent ∈ reviews.priorRefundPrincipalsFromOriginals a.form.place
      (refunds.map (·.obligation)) a.trigger finding.decidedAt,
    let current := assessment.faultCase h ev evidence c.cause c.acceptanceEvent earlier
    current.amountDue finding.decidedAt a.trigger outcome.agreedDeadline outcome.deadline
      outcome.legalDeadline outcome.finalFee outcome.refund independent ∧
    principal =
      some (current.assessedAmount a.trigger outcome.finalFee (some a.obligation) independent) ∧
    (closing = true → c.cause.assess a.form c.fault ev c.acceptanceEvent (evidence.evidence ev)
      current.remedies h.requests finding.decidedAt a.trigger 0)

/-- Recheck the retained review against the original trigger, deadline and case facts. -/
def AssessedRefund.reviewedFeeConforms (assessment : AssessedRefund) (h : History)
    (ev : StartEvidence) (reviews : Review.History) (finding : ReviewFinding)
    (outcome : AssessedFaultRefund) (query : Moment) (closing : Bool := false) : Prop :=
  assessment.reviewedFeeConformsWithPrincipal h ev reviews finding outcome
    (assessment.amount.principalAt reviews query) closing

/-- Filing a final fee uses the same reviewed facts as refund closure. -/
def AssessedRefund.feeEvidenceAt (assessment : AssessedRefund) (h : History)
    (ev : StartEvidence) (reviews : Review.History) (query : Moment) : Prop :=
  match assessment.amount.currentReviewAt reviews query with
  | [finding] => ∀ outcome ∈ assessment.amount.reviewedOutcomeAt reviews finding query,
    assessment.reviewedFeeConforms h ev reviews finding outcome query
  | _ => True

/-- Closure is a separate effect after the original account has retained its full restoration. -/
def AssessedRefund.closureConforms (assessment : AssessedRefund) (h : History)
    (ev : StartEvidence) (settlement : LessonSettlement) (closure : FullRefundClosure)
    (removals : List CreditPosting) (termsAndLawPermitClosure : Prop)
    (reviews : Review.History) : Prop :=
  let a := assessment.amount
  let f := a.form
  let query := closure.closedAt
  let effectivePrincipal := a.principalAt reviews query
  let findings := a.currentReviewAt reviews query
  let outcomeFor := fun finding ↦ a.reviewedOutcomeAt reviews finding query
  let ledger := (closeRefund ev closure removals).ledger
  assessment ∈ h.assessments ∧ a.recordedAt.by query ∧
  a.feeFromReview effectivePrincipal findings outcomeFor = some 0 ∧
  ¬fullRefundClosedBy f.place ev.creditRecords.closed query ∧
  settlement.matchesPaymentHistory f.place ev.ledger query ∧
  closureRemovalsMatch closure ev removals ∧
  (∀ row ∈ closure.discounts,
    let applied := sumAmounts ((h.usedDiscounts ++ h.pendingDiscountUses).filter (fun use ↦ decide
      (use.originalLesson = f.lesson.id ∧ use.originalPlace = f.place.id ∧
        use.bookedAt.by row.treatment.settledAt))) LaterBenefitUse.applied
    row.unusedAmount ≤ row.benefit.amount - applied) ∧
  ∃ principal ∈ effectivePrincipal,
  ∃ others ∈ h.otherRefundPrincipals f a.obligation reviews query,
    let after := { ev with ledger }
    let remedies := (h.remediesFor f).map (h.progress after)
    let principals := (a.obligation, principal) :: others
    (let original := match assessment.evidence with
      | .faultRefund facts cause acceptance =>
        cause.assess f facts.fault after acceptance (facts.evidence after) remedies h.requests
          query a.trigger 0
      | _ => False
    match findings with
    | [] => original
    | [finding] =>
      match outcomeFor finding with
      | none => original
      | some outcome =>
        assessment.reviewedFeeConformsWithPrincipal h after reviews finding outcome
          effectivePrincipal true
    | _ => False) ∧
    RefundPrincipalsRestored f.place ev.ledger query principals ∧
    closedByFullRefund f.place ledger remedies (h.availableDiscounts.map (·.2)) settlement.debited
      (sumAmounts principals Prod.snd) settlement.feePayable termsAndLawPermitClosure closure

def AcceptedRemedy.conforms (entry : AcceptedRemedy) (h : History) (ev : StartEvidence) : Prop :=
  let f := entry.facts.form
  let agreement := entry.agreement
  entry.facts.established ev agreement.acceptedAt ∧
  agreement.validForFault (entry.facts.fault.lessonWithResponsibleTutor f.lesson)
    f.place entry.facts.fault ∧
  agreement.acceptedAt.by agreement.deliveryDeadline ∧
  (∀ other ∈ h.remedies, other.id ≠ entry.id ∧ other.agreement ≠ agreement) ∧
  ¬fullRefundClosedBy f.place ev.creditRecords.closed agreement.acceptedAt ∧
  (agreement.kind = .standardCompensation → ∃ dates ∈ entry.dates,
    dates.matches agreement f ev agreement.acceptedAt)

def RecordedDelivery.conforms (record : RecordedDelivery) (h : History) (ev : StartEvidence)
    (remedy : AcceptedRemedy) : Prop :=
  let f := remedy.facts.form
  let progress := h.progress ev remedy
  record.remedy = remedy.id ∧ progress.stillOwedAt record.atTime ∧
  (∀ unable ∈ h.unable, unable.1 = remedy.id → record.atTime.by unable.2) ∧
  (∃ deadline, progress.deadlineBy f.lesson.provider record.atTime deadline ∧
    record.atTime.by deadline) ∧
  record.delivery.completedBy remedy.agreement f.place (remedy.facts.evidence ev) record.atTime ∧
  match record.delivery with
  | .standardCompensation relief benefit _ =>
    (∃ known ∈ h.assessments, ∃ filed, relief = some filed ∧
      known.evidence = .originalCompensation remedy.facts filed) ∧
    (remedy.facts.teaching = .none → ∃ recorded ∈ h.availableDiscounts,
      recorded.1 = remedy.id ∧ benefit = some recorded.2)
  | .remedialTeaching atTime _ | .otherRemedy atTime _ => atTime = record.atTime

/-- The already recorded selected booking uses the fixed benefit in its ordinary fee calculation. -/
structure DiscountBooking where
  remedy : AcceptedRemedy
  selected : PartOne
  agreed : PartOne
  originalStart : Moment
  selectedStart : Moment
  selectedIsSparkCourse : Prop
  booking : BookingEvidence
  use : LaterBenefitUse
  remainderHandledUnderTerms : LaterBenefitUse → Prop

/-- The retained price and payment evidence for applying the discount at confirmation. -/
def DiscountBooking.appliesAtBooking (discount : DiscountBooking) (h : History)
    (ev selected : StartEvidence) (priorUses : List LaterBenefitUse) : Prop :=
  let remedy := discount.remedy
  let original := remedy.facts
  remedy ∈ h.remedies ∧
  (discount.agreed, discount.booking) ∈ selected.bookings ∧
  ev.ledger = selected.ledger ∧
  (∃ schedule, EffectiveSchedule original.form.lesson ev schedule discount.use.bookedAt ∧
    schedule.start = discount.originalStart) ∧
  (∃ schedule, EffectiveSchedule discount.agreed.lesson selected schedule discount.use.bookedAt ∧
    schedule.start = discount.selectedStart) ∧
  (∃ recorded ∈ h.availableDiscounts, recorded.1 = remedy.id ∧
    recorded.2.deliveredBy original.form.place original.teaching
      remedy.agreement discount.use.bookedAt ∧
    ∃ roster, selected.readsBookedRoster discount.agreed selected.groupRoster
        discount.use.bookedAt roster ∧
      LaterCompensationBooking original.form original.fault original.authority original.disputed
        original.decisions ev.ledger ev.discounts ev.creditRecords.closed discount.selected
        discount.agreed discount.originalStart discount.selectedStart recorded.2.availableAt
        original.teaching remedy.agreement discount.selectedIsSparkCourse priorUses
        discount.use discount.booking { selected with groupRoster := roster })

def DiscountBooking.conforms (discount : DiscountBooking) (h : History)
    (ev selected : StartEvidence) : Prop :=
  discount.appliesAtBooking h ev selected h.usedDiscounts ∧
  LaterBenefitRemainderHandled discount.remedy.facts.form.place discount.selected selected
    discount.use discount.remainderHandledUnderTerms

/-- Record the customer's election, actual remedy effects and restoration to the debit account. -/
inductive Event where
  | acceptRemedy (entry : AcceptedRemedy)
  | extendRemedy (entry : AcceptedRemedy) (extension : RemedyExtension) (agreedAt : Moment)
  | confirmUnable (entry : AcceptedRemedy) (provider : ActorId) (point : Moment)
  | deliverRemedy (entry : AcceptedRemedy) (record : RecordedDelivery)
  | requestRefund (form : PartOne) (request : DirectRefundRequest)
  | makeDiscountUsable (entry : AcceptedRemedy) (discount : LaterBenefitAvailability)
  | recordDiscountUse (booking : DiscountBooking) (selected : StartEvidence)
  | issueCourseCredit (entry : AcceptedRemedy) (issue : CourseCreditIssue) (posting : CreditPosting)
  | assessRefund (assessment : AssessedRefund) (facts : HoldFacts)
  | postRefund (post : RefundPosting) (facts : HoldFacts) (authorities : ReviewAuthorities)
      (conditions : PaymentInstruction → Prop)
  | fileObservedRefund (post : RefundPosting) (recordedAt : Moment) (facts : HoldFacts)
      (authorities : ReviewAuthorities)
  | closeFullRefund (assessment : AssessedRefund) (settlement : LessonSettlement)
      (closed : FullRefundClosure) (removals : List CreditPosting)
      (termsAndLawPermitClosure : Prop)

def Event.atTime : Event → Moment
  | .acceptRemedy entry => entry.agreement.acceptedAt
  | .extendRemedy _ _ agreedAt | .confirmUnable _ _ agreedAt => agreedAt
  | .deliverRemedy _ record => record.atTime
  | .requestRefund _ request => request.receivedAt
  | .makeDiscountUsable _ discount => discount.availableAt
  | .recordDiscountUse booking _ => booking.use.bookedAt
  | .issueCourseCredit _ _ posting => posting.point
  | .assessRefund assessment _ => assessment.amount.recordedAt
  | .closeFullRefund _ _ closed _ _ => closed.closedAt
  | .postRefund post .. => post.posting.point
  | .fileObservedRefund _ recordedAt .. => recordedAt

def Event.form : Event → PartOne
  | .acceptRemedy entry | .extendRemedy entry .. | .confirmUnable entry .. | .deliverRemedy entry .. |
    .makeDiscountUsable entry .. | .issueCourseCredit entry .. => entry.facts.form
  | .requestRefund form _ => form
  | .recordDiscountUse booking _ => booking.remedy.facts.form
  | .assessRefund assessment _ | .closeFullRefund assessment .. => assessment.amount.form
  | .postRefund post .. | .fileObservedRefund post .. => post.assessment.amount.form

/-- New assessments read the recorded decisions. Later execution uses the established right. -/
def Event.assessmentDecisions : Event → Option DecisionRecords
  | .acceptRemedy entry => some entry.facts.decisions
  | .assessRefund assessment _ =>
    match assessment.evidence with
    | .noFault _ | .agreedChange _ => none
    | .absence absence => some absence.reason.decisions
    | .originalCompensation facts _ | .faultRefund facts .. => some facts.decisions
  | _ => none

/-- Every successor appends the event's own evidence or makes its specified account change. -/
def Step (h : History) (ev : StartEvidence) (holds : HoldHistory) (event : Event)
    (next : History) (after : StartEvidence) (followingHolds : HoldHistory)
    (clockEvidence : RefundTriggerEvidence := {}) (reviews : Review.History := .empty) : Prop :=
  let recordOnly := fun updated ↦ next = updated ∧ after = ev ∧ followingHolds = holds
  match event with
  | .acceptRemedy entry =>
    entry.conforms h ev ∧ recordOnly { h with remedies := h.remedies ++ [entry] }
  | .extendRemedy entry extension atTime =>
    let progress := h.progress ev entry
    entry ∈ h.remedies ∧ progress.stillOwedAt atTime ∧
    (∃ deadline, progress.deadlineBy entry.facts.form.lesson.provider atTime deadline ∧
      extension.applies entry.agreement entry.facts.form.lesson.provider deadline atTime) ∧
    recordOnly { h with extensions := h.extensions ++ [(entry.id, extension)] }
  | .confirmUnable entry provider atTime =>
    entry ∈ h.remedies ∧ provider = entry.facts.form.lesson.provider ∧
    (h.progress ev entry).stillOwedAt atTime ∧
    (∀ prior ∈ h.unable, prior.1 ≠ entry.id) ∧
    recordOnly { h with unable := h.unable ++ [(entry.id, atTime)] }
  | .deliverRemedy entry record =>
    entry ∈ h.remedies ∧ record.conforms h ev entry ∧
    (∀ prior ∈ h.deliveries, prior.remedy ≠ entry.id) ∧
    recordOnly { h with deliveries := h.deliveries ++ [record] }
  | .requestRefund form request =>
    (∃ roster forms,
      ev.rosterFormsAt form.lesson request.receivedAt roster forms ∧ form ∈ forms) ∧
    request.validFor form.place ∧ request ∉ h.requests ∧
    recordOnly { h with requests := h.requests ++ [request] }
  | .makeDiscountUsable entry discount =>
    let original := entry.facts.form.place
    entry ∈ h.remedies ∧ (h.progress ev entry).stillOwedAt discount.availableAt ∧
    discount.deliveredBy original entry.facts.teaching entry.agreement discount.availableAt ∧
    (∀ row ∈ h.availableDiscounts, row.2.originalLesson = original.lesson →
      row.2.originalPlace ≠ original.id) ∧
    recordOnly { h with availableDiscounts := h.availableDiscounts ++ [(entry.id, discount)] }
  | .recordDiscountUse booking selected =>
    booking.conforms h ev selected ∧
    ∃ earlier later, h.pendingDiscountUses = earlier ++ booking.use :: later ∧
      recordOnly { h with
        usedDiscounts := h.usedDiscounts ++ [booking.use]
        pendingDiscountUses := earlier ++ later }
  | .issueCourseCredit entry issue posting =>
    let grant := entry.creditOrigin issue ev
    entry ∈ h.remedies ∧ (h.progress ev entry).stillOwedAt posting.point ∧
    FreshPosting ev posting ∧
    grant.matchesPosting ev.ledger ev.creditRecords.closed ev.creditRecords.ownsAccount
      posting ev.creditRecords.lessonFees ∧
    (∀ prior ∈ ev.creditRecords.grants, prior.original.lesson = grant.original.lesson →
      prior.original.id ≠ grant.original.id) ∧
    (∀ prior ∈ ev.ledger, prior.kind ≠ .compensation grant.original.lesson grant.original.id) ∧
    next = h ∧ followingHolds = holds ∧ after = issueCourseCredit ev grant posting
  | .assessRefund assessment facts =>
    assessment.conforms h ev holds facts clockEvidence reviews ∧
    recordOnly { h with assessments := h.assessments ++ [assessment] }
  | .postRefund post facts authorities conditions =>
    post.conforms h ev holds followingHolds facts authorities conditions reviews ∧
    next = h ∧ after = receiveRefund ev post.posting post.filing followingHolds.payments
  | .fileObservedRefund post recordedAt facts authorities =>
    post.observedFiling h ev holds recordedAt facts authorities ∧
    next = h ∧ followingHolds = holds ∧ after = fileRefund ev post.posting post.filing
  | .closeFullRefund assessment settlement closure removals permitted =>
    assessment.closureConforms h ev settlement closure removals permitted reviews ∧
    next = h ∧ followingHolds = holds ∧ after = closeRefund ev closure removals

end SourceV14.Workflow.Redress
