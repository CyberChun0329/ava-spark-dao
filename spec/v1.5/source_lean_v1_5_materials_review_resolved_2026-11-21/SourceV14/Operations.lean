import SourceV14.Course
import SourceV14.Fault
import SourceV14.Materials
import SourceV14.Review

namespace SourceV14.Operations

open Booking Settlement Confirmation Course CreditEvidence

/-- The triggering event for a refund is already established by §3.6. -/
def PaymentDeadline.fromRefundTrigger (term : PaymentDeadline) (recorded : List PaymentTrigger)
    (trigger deadline : Moment) : Prop :=
  match term with
  | .fixed _ => term.applies none deadline
  | .after _ _ true => False
  | .after _ _ false =>
    ∃ actual ∈ recorded, actual.point = trigger ∧
      (∀ other ∈ recorded, other.reference = actual.reference → other.point = trigger → other = actual) ∧
      term.applies (some actual) deadline

/-- Signed review contacts and deadlines give the terms for this place's complaint. -/
def ReviewTerms.matchesForm (terms : ReviewTerms) (f : PartOne) : Prop :=
  terms.coordinator = f.lesson.coordinator ∧ terms.alternativeContact = f.contacts.alternativeContact ∧
  terms.leadAcademicTutor = f.contacts.leadAcademicTutor ∧
  (∀ deadline, f.deadlines.finalReply = .fixed deadline → terms.finalReplyDeadline = deadline) ∧
  terms.finalReviewDeadline = f.deadlines.finalReview ∧
  terms.temporaryHoldExpiry = f.deadlines.temporaryHoldExpiry ∧
  terms.handoffDeadline = f.deadlines.reviewerHandoff ∧ terms.escalationContact = f.contacts.escalationContact

/-- For a place's dealings, use its applicable confirmed review terms. -/
def HoldFacts.matchesForm (facts : HoldFacts) (f : PartOne) (part : PaymentPartRef) : Prop :=
  ∀ matter, matter.lesson = f.lesson.id →
    (facts.paymentAffected matter part ∨
      (∃ actor time, facts.temporaryAuthority matter actor part time) ∨
      ∃ decision, facts.partFallsUnderDecision matter decision part) →
    facts.termsApply matter ∧ ReviewTerms.matchesForm (facts.terms matter) f ∧
    (∀ actor time, facts.temporaryAuthority matter actor part time →
      f.contacts.alternativeCanTemporarilyHold = true ∧ actor = f.contacts.alternativeContact)


/-- The credit posting and payment receipt refer to the same actual lesson refund. -/
def LessonRefundReceiptMatches (p : Place) (entry : CreditPosting) (refund : ObligationId)
    (payment : PostedPayment) (history : PaymentHistory) : Prop :=
  entry.kind = .lessonRefund p.lesson p.id refund ∧ entry.account = p.account ∧
  payment.instruction.part.lesson = p.lesson ∧ payment.instruction.part.obligation = refund ∧
  payment.instruction.part.purpose = .lessonRefund p.id ∧ payment.id = entry.id ∧
  payment.instruction.atTime = entry.point ∧ payment.instruction.amount = entry.amount ∧
  payment.instruction.destination = .account p.account ∧
  history.actualPaymentWithEvidence payment

/-- Compare the same seat or class scope, irrespective of the caller's name for a portion. -/
def FeeOnHold (history : HoldHistory) (a : ReviewAuthorities) (facts : HoldFacts)
    (p : Place) (time : Moment) : Prop :=
  ∃ part : PaymentPartRef, part.lesson = p.lesson ∧ part.purpose = .customerFee p.id ∧
    history.paymentOnHold a facts part time

/-- Use the settled terms for a held fee's place rather than a detached review timetable. -/
def FeeHoldTermsMatch (f : PartOne) (facts : HoldFacts) : Prop :=
  ∀ part : PaymentPartRef, part.lesson = f.lesson.id → part.purpose = .customerFee f.place.id →
    HoldFacts.matchesForm facts f part

def AppliesOriginalCompensation (f : PartOne) (basis : FaultBasis) (authority : Option FaultDecisionRecord)
    (disputed : Bool) (records : DecisionRecords) (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (fees : LessonFeeAmendments) (assessedAt query : Moment)
    (teaching : TeachingReceived) (agreements : List RemedyAgreement)
    (entry : LessonSettlement) : Prop :=
  f.matches ∧ FaultDecisionWhenRequired basis disputed authority records f query ∧
  FaultMatchesEvidence f basis records ledger discounts fees assessedAt ∧
  entry.matchesPaymentHistory f.place ledger query ∧ assessedAt.by query ∧
  (∃ otherwiseDue, fees.feeAt f assessedAt otherwiseDue ∧
    originalCompensationRelief (basis.lessonWithResponsibleTutor f.lesson) f.place basis
      teaching agreements assessedAt otherwiseDue entry.feePayable) ∧
  entry.creditDueBack = grossLessonCreditRestoration entry.debited entry.feePayable

/-- A choice about another course changes where the fixed benefit is used. -/
def LaterCompensationBooking (original : PartOne) (basis : FaultBasis)
    (authority : Option FaultDecisionRecord) (disputed : Bool) (records : DecisionRecords)
    (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (closed : List FullRefundClosure) (selected agreed : PartOne) (originalAt selectedAt availableAt : Moment)
    (teaching : TeachingReceived) (acceptance : RemedyAgreement)
    (verifiedSelectedSparkCourse : Prop) (priorUses : List LaterBenefitUse)
    (use : LaterBenefitUse) (booking : BookingEvidence) (ev : StartEvidence) : Prop :=
  original.matches ∧ selected.matches ∧ agreed.matches ∧ agreed.confirmedAt = use.bookedAt ∧
  CanConfirmPlace agreed booking ev.groupRoster ev.openingCredit ev.ledger ev.creditRecords
    ev.discounts ev.teachingBegan ∧
  basis.standardCompensationOffered (basis.lessonWithResponsibleTutor original.lesson) original.place ∧
  FaultMatchesEvidence original basis records ledger discounts ev.creditRecords.lessonFees use.bookedAt ∧
  FaultDecisionWhenRequired basis disputed authority records original use.bookedAt ∧
  (∀ closure ∈ closed, closure.lesson = original.lesson.id →
    closure.place = original.place.id → ¬ closure.closedAt.by use.bookedAt) ∧
  selected.lesson = agreed.lesson ∧
  ∃ otherwiseDue, ev.feeAt selected use.bookedAt otherwiseDue ∧
    let selectedPlace := { selected.place with feePayable := otherwiseDue }
    agreed.place = { selectedPlace with feePayable := feeAfterHalfPriceBenefit original.place otherwiseDue } ∧
    laterBenefitApplied original.place selectedPlace originalAt selectedAt teaching acceptance
      availableAt verifiedSelectedSparkCourse priorUses use agreed.place.feePayable

/-- Applicable terms determine what is done with any unused part of the half-price benefit. -/
def LaterBenefitRemainderHandled (original : Place) (selected : PartOne)
    (ev : StartEvidence) (use : LaterBenefitUse)
    (handledUnderApplicableTerms : LaterBenefitUse → Prop) : Prop :=
  use.originalLesson = original.lesson ∧ use.originalPlace = original.id ∧
  use.lesson = selected.lesson.id ∧ use.place = selected.place.id ∧
  ev.feeAt selected use.bookedAt use.feeOtherwiseDue ∧
  use.unapplied = unappliedHalfPriceBenefit original use.feeOtherwiseDue ∧
  (0 < use.unapplied → handledUnderApplicableTerms use)

/-- Claim-level scope for exercising an existing settlement decision. -/
structure SettlementAssignment where
  matter : ReviewMatter
  decision : Nat
  authorities : ReviewAuthorities
  appointment : Option ReviewAppointment
  recusal : Option RecusalRecord
  covers : PlaceId → Prop

def SettlementAssignment.authorised (assignment : SettlementAssignment) (f : PartOne)
    (handler : Handler) (query : Moment) : Prop :=
  assignment.matter.lesson = f.lesson.id ∧ assignment.covers f.place.id ∧
  handler.maySettle f.lesson ∧ assignment.authorities.disinterested assignment.matter handler.actor query ∧
  (handler.actor = f.lesson.coordinator ∨
    ∃ appointed ∈ assignment.appointment,
      appointed.applies assignment.authorities assignment.matter handler.actor query) ∧
  ((assignment.authorities.interest assignment.matter f.lesson.coordinator query).affected →
    ∃ recusal ∈ assignment.recusal, recusal.replacement.handler = handler.actor ∧
      recusalConforms assignment.authorities assignment.matter f.lesson.coordinator query recusal)

/-- The recorded decision or review of the good reason for this place. -/
structure AbsenceReasonDecision where
  finding : InitialFinding
  review : Option ReviewFinding
  place : PlaceId
  goodReason : Bool

def AbsenceReasonDecision.applies (row : AbsenceReasonDecision) (records : DecisionRecords)
    (f : PartOne) (atTime : Moment) : Prop :=
  row.place = f.place.id ∧ row.finding.matter.lesson = f.lesson.id ∧
  row.finding.issue = .absenceReason ∧ row.finding.decidedAt.by atTime ∧
  initialFindingRecordedConforms records.authorities records.terms
    f.contacts.substitute records.appointments records.initialFindings row.finding ∧
  match row.review with
  | none => True
  | some r =>
    r.matter.sameCase row.finding.matter ∧ row.finding.decidedAt.before r.decidedAt ∧
    r.decidedAt.by atTime ∧
    reviewFindingRecordedConforms records.authorities (some f.contacts.reviewer)
      records.appointments records.initialFindings records.reviewFindings r

def AbsenceReasonDecision.effectiveAt (row : AbsenceReasonDecision) : Moment :=
  (row.review.map (·.decidedAt)).getD row.finding.decidedAt

structure AbsenceReasonEvidence where
  decisionNeeded : Prop
  decisions : DecisionRecords
  recordedReasons : List AbsenceReasonDecision

def AbsenceReasonEvidence.applies (e : AbsenceReasonEvidence) (f : PartOne)
    (facts : AbsenceFacts) (query : Moment) : Prop :=
  e.decisionNeeded →
    ReviewTerms.matchesForm e.decisions.terms f ∧
    ∃ row ∈ e.recordedReasons, row.applies e.decisions f query ∧
      facts.verifiedGoodReason = some row.goodReason ∧
      ∀ other ∈ e.recordedReasons, other.applies e.decisions f query →
        other.effectiveAt.by row.effectiveAt ∧
        (other.effectiveAt = row.effectiveAt → other.goodReason = row.goodReason)

def HalfFeeAbsenceRecorded (f : PartOne) (ev : StartEvidence) (s : Schedule)
    (start query : Moment) (handler : Handler) (assignment : SettlementAssignment)
    (facts : AbsenceFacts) (reason : AbsenceReasonEvidence) (holds : HoldHistory) (holdFacts : HoldFacts)
    (ledger : List CreditPosting) (record : LessonSettlement) : Prop :=
  (∃ roster forms, ev.rosterFormsAt f.lesson query roster forms ∧ f ∈ forms) ∧
  ledger = ev.ledger ∧ assignment.authorised f handler query ∧
  FeeHoldTermsMatch f holdFacts ∧
  holds.mayCarryOutDecision assignment.authorities holdFacts assignment.matter assignment.decision query ∧
  ¬FeeOnHold holds assignment.authorities holdFacts f.place query ∧
  CanStart f.lesson ev s start ∧ start.by query ∧
  record.matchesPaymentHistory f.place ledger query ∧
  (∃ fee, ev.feeAt f start fee ∧
    ((ev.teachingBegan = some start ∧ ∃ agreedPay, f.absentGroupPlacePay = some agreedPay ∧
        groupAbsenceAmounts f.lesson f.place facts fee agreedPay record.feePayable record.tutorPay) ∨
      (oneToOneAbsenceHalfFee f.lesson f.place facts ∧ reason.applies f facts query ∧
        ev.retainsOneToOneAbsence f s start query facts ∧
        record.feePayable = absenceCustomerFee fee ∧
        ∃ tutor reference normalFee terms,
          EffectiveTutorAgreementAt f ev start tutor reference normalFee terms ∧
          record.tutorPay = normalFee / 2))) ∧
  record.creditDueBack = grossLessonCreditRestoration record.debited record.feePayable

/-- A historical refund already assessed under its applicable terms, for this same fee. -/
structure EarlierFeeRefund where
  id : Nat
  lesson : LessonId
  place : PlaceId
  trigger : Moment
  due : Moment
  executionDeadline : Moment
  legalDeadline : Option Moment
  amount : Amount

def earlierOutstanding (p : Place) (ledger : List CreditPosting)
    (earlier : List EarlierFeeRefund) (trigger : Moment)
    (otherPrincipals : List (ObligationId × Amount) := []) : Amount :=
  sumAmounts (earlier.map (fun old ↦ (old.id, old.amount)) ++ otherPrincipals)
    (fun (refund, amount) ↦ refundBalanceDue p ledger trigger amount (some refund))

def EarlierFeeRefundsFor (p : Place) (before : Moment) (refunds : List EarlierFeeRefund) : Prop :=
  (refunds.map (·.id)).Nodup ∧
  ∀ old ∈ refunds,
    old.lesson = p.lesson ∧ old.place = p.id ∧ old.trigger.before before ∧ 0 ≤ old.amount

/-- Compute the newly due reduction in the original fee. Credit on an earlier refund
    counts toward that refund's principal, and its unpaid portion remains due separately. -/
def feeAdjustmentRefundPrincipal (place : Place) (ledger : List CreditPosting)
    (atTime : Moment) (refund : ObligationId) (gross : Amount)
    (earlier : List EarlierFeeRefund) (otherPrincipals : List (ObligationId × Amount) := []) : Amount :=
  let prior := ledger.filter (fun entry ↦ decide (entry.point.before atTime))
  let otherDebts := earlier.filter (fun old ↦ old.id != refund)
  let otherPrincipals := otherPrincipals.filter (fun row ↦ row.1 != refund)
  let known := otherDebts.map (fun old ↦ (old.id, old.amount)) ++ otherPrincipals
  let receivedForOtherRefunds := creditsAppliedToLessonRefunds place prior atTime known -
    creditsRestoredFor place prior atTime (some refund)
  additionalRefundDue gross receivedForOtherRefunds
    (earlierOutstanding place prior otherDebts atTime otherPrincipals)

/-- The excess actually restored for a verified absence uses that seat's original account. -/
def AbsenceRefundReceived (f : PartOne) (ev : StartEvidence) (s : Schedule)
    (start : Moment) (handler : Handler) (assignment : SettlementAssignment)
    (facts : AbsenceFacts) (reason : AbsenceReasonEvidence) (holds : HoldHistory) (holdFacts : HoldFacts)
    (settlement : LessonSettlement) (entry : CreditPosting) (refund : ObligationId) (payment : PostedPayment)
    (history : PaymentHistory) (earlier : List EarlierFeeRefund) : Prop :=
  HalfFeeAbsenceRecorded f ev s start entry.point handler assignment facts reason holds holdFacts ev.ledger settlement ∧
  ValidLessonRefund f.place ev.ledger entry refund
    (feeAdjustmentRefundPrincipal f.place ev.ledger entry.point refund settlement.creditDueBack earlier) false ∧
  LessonRefundReceiptMatches f.place entry refund payment history

/-- The record contains the verified facts for this place, including any applicable exception.
    An unresolved matter is dealt with separately under the hold and review rules. -/
structure PlaceFeeFacts where
  cancellations : List CancellationRequest
  noFaultChanges : List NoFaultCancellationRecord
  feeChangedUnderTerms : AgreedScheduleChange → String → PlaceId → Prop
  absence : Option AbsenceFacts
  faultRecords : DecisionRecords
  undisputedProviderErrors : List ProviderFaultFacts

def PlaceFeeFacts.exceptionApplies (facts : PlaceFeeFacts) (f : PartOne)
    (ev : StartEvidence) (query : Moment) : Prop :=
  (∃ request ∈ facts.cancellations, request.point.by query ∧ CanCancelOneToOne f request ev) ∨
  (∃ change ∈ facts.noFaultChanges, change.cancellation.point.by query ∧ change.conforms f ev) ∨
  (∃ change ∈ ev.changes, change.allowed f.lesson ev ∧
    change.record.nextSchedule.effectiveAt.by query ∧
    facts.feeChangedUnderTerms change f.cancelChangeTerms f.place.id) ∨
  (∃ absence ∈ facts.absence, groupAbsenceHalfFee f.lesson f.place absence ∨
    oneToOneAbsenceHalfFee f.lesson f.place absence ∨ oneToOneAbsenceUsesChangeTerms f.lesson f.place absence) ∨
  (∃ row ∈ facts.faultRecords.faultOutcomes, row.place = f.place.id ∧
    row.decision.effectiveForForm facts.faultRecords f query ∧
    ∃ fault, row.disposition = .fault fault ∧
      FaultMatchesEvidence f fault facts.faultRecords ev.ledger ev.discounts ev.creditRecords.lessonFees query) ∨
  ∃ fault ∈ facts.undisputedProviderErrors, fault.applies f.lesson f.place

/-- Ordinary one-to-one settlement uses actual confirmation or the later verified route. -/
def OrdinaryOneToOneCharge (f : PartOne) (ev : StartEvidence) (s : Schedule)
    (actualStart expiry query : Moment) (handler : Handler) (assignment : SettlementAssignment)
    (studentConfirmed tutorConfirmed coordinatorConfirmed factsVerified : Bool)
    (verifiedAgreedTeaching : Prop) (feeFacts : PlaceFeeFacts) (hold : HoldHistory) (a : ReviewAuthorities)
    (holdFacts : HoldFacts) (record : LessonSettlement) : Prop :=
  f ∈ ev.effectiveForms ∧ assignment.authorised f handler query ∧
  FeeHoldTermsMatch f holdFacts ∧
  hold.mayCarryOutDecision a holdFacts assignment.matter assignment.decision query ∧
  OneToOneSettlementAvailable f.lesson ev s actualStart expiry query studentConfirmed
    tutorConfirmed coordinatorConfirmed factsVerified handler ∧
  CanStart f.lesson ev s actualStart ∧ verifiedAgreedTeaching ∧
  ¬feeFacts.exceptionApplies f ev query ∧ ¬FeeOnHold hold a holdFacts f.place query ∧
  record.matchesPaymentHistory f.place ev.ledger query ∧
  ev.feeAt f query record.feePayable

def OrdinaryGroupCharge (f : PartOne) (ev : StartEvidence) (s : Schedule)
    (r : Roster) (start expiry query : Moment) (handler : Handler)
    (assignment : SettlementAssignment) (completion factsVerified didGoAhead serviceAvailable : Bool)
    (confirmed studentFault : List PlaceId)
    (feeFacts : PlaceFeeFacts) (hold : HoldHistory) (a : ReviewAuthorities)
    (holdFacts : HoldFacts) (record : LessonSettlement) : Prop :=
  ev.formForRoster f.lesson r f ∧ assignment.authorised f handler query ∧
  FeeHoldTermsMatch f holdFacts ∧
  hold.mayCarryOutDecision a holdFacts assignment.matter assignment.decision query ∧
  GroupSettlementAvailable f.lesson ev s r start expiry query completion factsVerified
    handler confirmed studentFault ∧
  CanStart f.lesson ev s start ∧
  ev.paidInFull f query ∧ ¬feeFacts.exceptionApplies f ev query ∧
  ¬FeeOnHold hold a holdFacts f.place query ∧ didGoAhead = true ∧ serviceAvailable = true ∧
  record.matchesPaymentHistory f.place ev.ledger query ∧
  ev.feeAt f query record.feePayable

/-- Provider responsibility after an unauthorised start follows the terms for verified teaching. -/
def UnauthorisedStartSettlement (f : PartOne) (ev : StartEvidence) (s : Schedule)
    (actualStart query : Moment) (handler : Handler) (assignment : SettlementAssignment)
    (providerActuallyWentAhead : Prop)
    (verifiedUnmetStartCondition : LessonId → Moment → Prop)
    (hold : HoldHistory) (holdFacts : HoldFacts)
    (verifiedServiceValue providerTutorPay : Amount)
    (establishedUnderProviderTerms : PartOne → Amount → Amount → Prop)
    (record : LessonSettlement) : Prop :=
  (∃ roster forms, ev.rosterFormsAt f.lesson query roster forms ∧ f ∈ forms) ∧
  ev.teachingBegan = some actualStart ∧ EffectiveSchedule f.lesson ev s actualStart ∧ actualStart.by query ∧
  verifiedUnmetStartCondition f.lesson.id actualStart ∧
  ¬CanStart f.lesson ev s actualStart ∧ providerActuallyWentAhead ∧
  assignment.authorised f handler query ∧ FeeHoldTermsMatch f holdFacts ∧
  hold.mayCarryOutDecision assignment.authorities holdFacts assignment.matter assignment.decision query ∧
  ¬FeeOnHold hold assignment.authorities holdFacts f.place query ∧
  establishedUnderProviderTerms f verifiedServiceValue providerTutorPay ∧
  record.matchesPaymentHistory f.place ev.ledger query ∧ record.feePayable = verifiedServiceValue ∧
  record.tutorPay = providerTutorPay ∧
  record.creditDueBack = grossLessonCreditRestoration record.debited record.feePayable

/-- Restoring excess original credit is a distinct action under §3.5. -/
def OriginalCompensationRefundReceived (f : PartOne) (basis : FaultBasis)
    (authority : Option FaultDecisionRecord) (disputed : Bool) (records : DecisionRecords)
    (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (fees : LessonFeeAmendments) (assessedAt : Moment)
    (teaching : TeachingReceived) (agreements : List RemedyAgreement)
    (settlement : LessonSettlement) (entry : CreditPosting) (refund : ObligationId)
    (payment : PostedPayment) (history : PaymentHistory) (earlier : List EarlierFeeRefund) : Prop :=
  AppliesOriginalCompensation f basis authority disputed records ledger discounts
    fees assessedAt entry.point teaching agreements settlement ∧
  ValidLessonRefund f.place ledger entry refund
    (feeAdjustmentRefundPrincipal f.place ledger entry.point refund settlement.creditDueBack earlier) false ∧
  LessonRefundReceiptMatches f.place entry refund payment history

inductive RefundCause where
  | direct (request : DirectRefundRequest) (outstanding : OutstandingOriginalServices)
  | noAgreement (outstanding : OutstandingOriginalServices)
  | failedDelivery (progress : RemedyProgress)
  | madeGood (separate : SeparateMadeGoodRefund)

def RefundCause.basis : RefundCause → RefundBasis
  | .direct .. => .directRequest
  | .noAgreement .. => .noAgreement
  | .failedDelivery .. => .failedDelivery
  | .madeGood .. => .afterMadeGood

def RefundCause.assess (cause : RefundCause) (f : PartOne) (fault : FaultBasis)
    (ev : StartEvidence) (acceptanceEvent : Option PaymentTrigger) (evidence : RemedyEvidence) (remedies : List RemedyProgress)
    (requests : List DirectRefundRequest) (query trigger : Moment) (fee : Amount) : Prop :=
  match cause with
  | .direct request outstanding =>
    request ∈ requests ∧
    directRefundTrigger (fault.lessonWithResponsibleTutor f.lesson) f.place fault outstanding remedies evidence request query trigger ∧
    (∀ other ∈ requests, ∀ earlier,
      directRefundTrigger (fault.lessonWithResponsibleTutor f.lesson) f.place fault outstanding remedies evidence other query earlier →
      trigger.by earlier) ∧
    outstandingRefundFee f.place evidence.teaching outstanding remedies evidence trigger fee
  | .noAgreement outstanding =>
    f.deadlines.remedyAcceptance.appliesForLesson f.lesson ev query acceptanceEvent trigger ∧
    noRemedyAgreedRefundTrigger (fault.lessonWithResponsibleTutor f.lesson) f.place fault outstanding remedies evidence requests
      trigger query trigger ∧
    outstandingRefundFee f.place evidence.teaching outstanding remedies evidence trigger fee
  | .failedDelivery claimed =>
    ∃ progress ∈ remedies, progress.agreement = claimed.agreement ∧
      failedAcceptedRemedyRefund (fault.lessonWithResponsibleTutor f.lesson)
        f.place fault progress evidence query trigger fee
  | .madeGood separate =>
    separateMadeGoodRefund (fault.lessonWithResponsibleTutor f.lesson) f.place fault separate remedies evidence query trigger fee

/-- The due date and delivery deadline for this accepted compensation on the confirmed form. -/
structure CompensationDates where
  dueAt : Moment
  dueTrigger : Option PaymentTrigger
  deliveryTrigger : Option PaymentTrigger

def CompensationDates.matches (dates : CompensationDates) (agreement : RemedyAgreement)
    (f : PartOne) (ev : StartEvidence) (observed : Moment) : Prop :=
  agreement.forPlace f.place ∧ agreement.acceptedAt.by observed ∧
  f.deadlines.compensation.due.appliesForLesson f.lesson ev observed dates.dueTrigger dates.dueAt ∧
  f.deadlines.compensation.latestExecution.appliesForLesson f.lesson ev observed
    dates.deliveryTrigger agreement.deliveryDeadline

structure FaultRefundCase where
  form : PartOne
  fault : FaultBasis
  authority : Option FaultDecisionRecord
  disputed : Bool
  decisions : DecisionRecords
  ledger : List CreditPosting
  discounts : List DiscountRecord
  teaching : TeachingReceived
  ownsAccount : ActorId → AccountId → Prop
  closed : List FullRefundClosure
  remedies : List RemedyProgress
  benefits : List LaterBenefitAvailability
  requests : List DirectRefundRequest
  refundEvents : List PaymentTrigger
  acceptanceEvent : Option PaymentTrigger
  lessonEvidence : StartEvidence
  compensationDates : RemedyAgreement → Option CompensationDates
  obligation : ObligationId
  cause : RefundCause
  /-- Earlier assessments covering this refund. A full fee waiver includes all earlier refunds
      for that fee. Independent refund assessments keep their own scope and amount. -/
  establishedEarlier : List EarlierFeeRefund

/-- The accepted standard package uses its own Part 1 compensation terms.
    A separately agreed remedy keeps the timeline in its agreement. -/
def FaultRefundCase.remedyDatesMatch (c : FaultRefundCase) (progress : RemedyProgress)
    (observed : Moment) : Prop :=
  progress.agreement.kind = .standardCompensation →
    ∃ dates ∈ c.compensationDates progress.agreement,
      dates.matches progress.agreement c.form c.lessonEvidence observed

/-- For a correction of the same obligation, exclude that obligation from the
    earlier amounts. Its own retained receipts are deducted once at settlement. -/
def FaultRefundCase.assessedAmount (c : FaultRefundCase) (trigger : Moment)
    (effectiveFee : Amount) (correcting : Option ObligationId)
    (otherPrincipals : List (ObligationId × Amount) := []) : Amount :=
  let f := c.form
  let others := c.establishedEarlier.filter (fun row ↦ correcting != some row.id)
  let otherPrincipals := otherPrincipals.filter (fun row ↦ correcting != some row.1)
  let known := others.map (fun old ↦ (old.id, old.amount)) ++ otherPrincipals
  let gross := grossLessonCreditRestoration (debitTotal f.place c.ledger trigger) effectiveFee
  let priorRestored := if effectiveFee = 0 then
    creditsAppliedToLessonRefunds f.place c.ledger trigger known -
      (match correcting with
      | none => 0
      | some id => creditsRestoredFor f.place c.ledger trigger (some id))
  else sumAmounts known (fun (refund, amount) ↦ min amount
    (creditsRestoredFor f.place c.ledger trigger (some refund)))
  additionalRefundDue gross priorRestored
    (earlierOutstanding f.place c.ledger others trigger otherPrincipals)

def FaultRefundCase.newObligationAt (c : FaultRefundCase) (trigger : Moment) : Prop :=
  (∀ old ∈ c.establishedEarlier, old.id ≠ c.obligation) ∧
  ∀ entry ∈ c.ledger,
    entry.kind = .lessonRefund c.form.lesson.id c.form.place.id c.obligation →
    trigger.before entry.point

def FaultRefundCase.amountDue (c : FaultRefundCase) (query trigger agreedDue due : Moment)
    (legalDeadline : Option Moment) (effectiveFee amount : Amount)
    (otherPrincipals : List (ObligationId × Amount) := []) : Prop :=
  let f := c.form
  f.matches ∧
  FaultDecisionWhenRequired c.fault c.disputed c.authority c.decisions f query ∧
  FaultMatchesEvidence f c.fault c.decisions c.ledger c.discounts c.lessonEvidence.creditRecords.lessonFees trigger ∧
  (∀ progress ∈ c.remedies, progress.agreement.acceptedAt.by query →
    c.remedyDatesMatch progress query) ∧
  (∃ assessedFee otherwiseDue, c.lessonEvidence.feeAt f trigger otherwiseDue ∧
    c.cause.assess f c.fault c.lessonEvidence c.acceptanceEvent
      { lesson := c.fault.lessonWithResponsibleTutor f.lesson, fault := c.fault,
        ledger := c.ledger, teaching := c.teaching, ownsAccount := c.ownsAccount,
        closed := c.closed, feeAt := c.lessonEvidence.feeAt f }
      c.remedies c.requests query trigger assessedFee ∧
    let reduced := feeAfterOriginalCompensation f.place c.teaching otherwiseDue
    let standard := originalCompensationRelief (c.fault.lessonWithResponsibleTutor f.lesson)
      f.place c.fault c.teaching (c.remedies.map (·.agreement)) trigger otherwiseDue reduced
    ((standard ∧ effectiveFee = min reduced assessedFee) ∨
      (¬standard ∧ effectiveFee = assessedFee))) ∧
  PaymentDeadline.fromRefundTrigger f.deadlines.refund.latestExecution c.refundEvents trigger agreedDue ∧
  due = refundDeadline agreedDue legalDeadline ∧
  EarlierFeeRefundsFor f.place trigger c.establishedEarlier ∧
  amount = c.assessedAmount trigger effectiveFee none otherPrincipals

/-- Fulfilment is separate from a timely obligation. Late valid receipts still count. -/
def FaultRefundCase.restores (c : FaultRefundCase) (posting : CreditPosting)
    (obligation : Nat) (trigger agreedDue due : Moment) (legalDeadline : Option Moment)
    (effectiveFee amount : Amount) : Prop :=
  c.amountDue posting.point trigger agreedDue due legalDeadline effectiveFee amount ∧
  obligation = c.obligation ∧ c.newObligationAt trigger ∧
  ValidLessonRefund c.form.place c.ledger posting obligation amount false

/-- An actual waiver and restoration are both needed for closure. -/
def FullRefundCaseClosed (c : FaultRefundCase)
    (trigger agreedDue due : Moment) (legalDeadline : Option Moment) (refund : Amount)
    (settlement : LessonSettlement) (termsAndLawPermitClosure : Prop)
    (closure : FullRefundClosure) : Prop :=
  let principals := (c.obligation, refund) :: c.establishedEarlier.map (fun old ↦ (old.id, old.amount))
  c.amountDue closure.closedAt trigger agreedDue due legalDeadline 0 refund ∧
  c.cause.assess c.form c.fault c.lessonEvidence c.acceptanceEvent
    { lesson := c.fault.lessonWithResponsibleTutor c.form.lesson, fault := c.fault, ledger := c.ledger, teaching := c.teaching,
      ownsAccount := c.ownsAccount, closed := c.closed, feeAt := c.lessonEvidence.feeAt c.form }
    c.remedies c.requests closure.closedAt trigger 0 ∧
  settlement.matchesPaymentHistory c.form.place c.ledger closure.closedAt ∧
  RefundPrincipalsRestored c.form.place c.ledger closure.closedAt principals ∧
  closedByFullRefund c.form.place c.ledger c.remedies c.benefits settlement.debited
    (sumAmounts principals Prod.snd) settlement.feePayable termsAndLawPermitClosure closure

/-- A tutor deduction uses the original signed lesson and the authorised fault decision. -/
structure TutorFaultDecisionEvidence where
  original : PartOne
  lessonEvidence : StartEvidence
  effectiveSchedule : Schedule
  decision : FaultDecisionRecord
  records : DecisionRecords

def TutorFaultDecisionEvidence.establishes (e : TutorFaultDecisionEvidence) (fault : TutorFaultCase)
    (query : Moment) : Prop :=
  (∃ roster forms, e.lessonEvidence.rosterFormsAt e.original.lesson
    e.decision.decision.decidedAt roster forms ∧ e.original ∈ forms) ∧
  fault.originalLesson = { e.original.lesson with
    tutor := fault.originalLesson.tutor, normalTutorFee := fault.originalLesson.normalTutorFee } ∧
  EffectiveSchedule e.original.lesson e.lessonEvidence e.effectiveSchedule fault.originalLessonAt ∧
  fault.originalLessonAt = e.lessonEvidence.teachingEnded.getD e.effectiveSchedule.start ∧
  (∃ reference terms, EffectiveTutorAgreementAt e.original e.lessonEvidence
    (e.lessonEvidence.teachingBegan.getD e.effectiveSchedule.start) fault.originalLesson.tutor
    reference fault.originalLesson.normalTutorFee terms e.decision.decision.decidedAt) ∧
  fault.finding.establishedFor fault.originalLesson ∧
  e.decision ∈ e.records.faultOutcomes ∧ e.decision.place = e.original.place.id ∧
  e.decision.decision.effectiveForForm e.records e.original query ∧
  ∃ facts, e.decision.disposition = .fault (.tutor fault.finding facts)

/-- The form references the confirmed liabilities without deducting them from tutor pay. -/
def ConfirmedTutorDebtsReferenced (lesson : Lesson) (tutor : ActorId) (observed : Moment)
    (confirmed : List TutorDebtRecord) (references : List Nat) : Prop :=
  references.Nodup ∧
  ∀ loss, loss ∈ references ↔
    ∃ debt ∈ confirmed, debt.loss = loss ∧ debt.debtor = tutor ∧
      debt.creditor = lesson.provider ∧ debt.recordedAt.by observed

/-- A zero-pay original settlement still records the agreed fee and full deduction. -/
def OriginalTutorDeductionRecorded (decision : TutorFaultDecisionEvidence) (fault : TutorFaultCase)
    (settledAt : Moment) (settlement : LessonSettlement) (deduction : Amount)
    (confirmedDebts : LessonId → ActorId → List TutorDebtRecord) (debtReferences : List Nat) : Prop :=
  decision.establishes fault settledAt ∧
  ConfirmedTutorDebtsReferenced fault.originalLesson fault.originalLesson.tutor settledAt
    (confirmedDebts fault.originalLesson.id fault.originalLesson.tutor) debtReferences ∧
  settlement.matchesPaymentHistory decision.original.place decision.lessonEvidence.ledger settledAt ∧
  originalFaultTutorSettlement fault deduction settlement.tutorPay

/-- The applicable teaching agreement governs what happens to a recorded deduction shortfall. -/
def TutorDeductionRemainderHandled (fault : TutorFaultCase) (next : TutorLessonRecord)
    (record : NextTutorDeductionRecord) (agreementTerms : Option String)
    (recordedTreatment : String → Amount → Prop) : Prop :=
  record.matches fault next ∧
  (0 < record.unappliedAmount →
    ∃ terms ∈ agreementTerms, record.shortfallTerms = some terms ∧
      recordedTreatment terms record.unappliedAmount)

/-- The new lesson is only where the fixed deduction is applied. -/
def TutorAmountsForSettlement (history : List TutorLessonRecord) (next : TutorLessonRecord)
    (faults : List TutorFaultCase) (deductions : List NextTutorDeductionRecord)
    (otherwisePayable result : Amount) : Prop :=
  next.feeOtherwisePayable = otherwisePayable ∧
  ((∃ fault ∈ faults, fault.originalLesson.id = next.lesson.id ∧
      fault.originalLesson.tutor = next.lesson.tutor ∧
      originalFaultTutorSettlement fault (originalTutorDeduction fault) result ∧ deductions = []) ∨
    ((∀ fault ∈ faults, fault.originalLesson.id = next.lesson.id →
      fault.originalLesson.tutor = next.lesson.tutor →
      ¬ fault.finding.establishedFor fault.originalLesson) ∧
      nextTutorDeductionsSettled history next [] faults deductions result))

/-- Historical approval is rechecked against actual posting and the current hold. -/
inductive PaymentApprovalRoute where
  | ordinary (approval : PaymentApproval)
  | liftOriginal (approval : PaymentApproval) (releasedAt : Moment)
  | liftReplacement (approval newApproval : PaymentApproval) (releasedAt : Moment)
  | liftFirst (approval : PaymentApproval) (releasedAt : Moment)

def PaymentApprovalRoute.allows (route : PaymentApprovalRoute) (a : ReviewAuthorities)
    (facts : HoldFacts) (history : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (conditions : PaymentInstruction → Prop) (entry : PaymentInstruction) : Prop :=
  match route with
  | .ordinary approval => originalExecutorMayPay a facts history approval part schedule
      conditions entry
  | .liftOriginal approval releasedAt =>
    originalApprovalAfterLift a facts history approval part schedule releasedAt conditions entry
  | .liftReplacement approval replacement releasedAt =>
    newApprovalAfterLift a facts history approval replacement part schedule releasedAt
      conditions entry
  | .liftFirst approval releasedAt =>
    firstApprovalAfterLift a facts history approval part schedule releasedAt conditions entry

/-- The form supplies the window. Relative terms retain the actual, verified expiry order. -/
def postLiftTermMatches (form : DeadlineTerms) (schedule : PaymentSchedule) : Prop :=
  match form, schedule.postLiftDeadline with
  | .fixed deadline, .date recorded => recorded = deadline
  | .after seconds, .period recorded _ => recorded = seconds
  | _, _ => False

/-- Use the receipt's actual approval in the form's after-lift record. -/
def PaymentApprovalRoute.recordMatches (route : PaymentApprovalRoute) (row : PostLiftPaymentRecord) :
    Prop :=
  match route with
  | .ordinary approval =>
    row.usedApproval = some approval
  | .liftOriginal approval releasedAt =>
    row.originalApproval = some approval ∧ row.replacementApproval = none ∧
    row.releasedAt = releasedAt
  | .liftReplacement approval replacement releasedAt =>
    row.originalApproval = some approval ∧ row.replacementApproval = some replacement ∧
    row.releasedAt = releasedAt
  | .liftFirst approval releasedAt =>
    row.originalApproval = none ∧ row.replacementApproval = some approval ∧
    row.releasedAt = releasedAt

/-- Part 2 records and traces the actual payment to a lawful approval.
    The fact of a ledger receipt is available separately for corrections. -/
def PaymentApprovalRoute.filedPayment (route : PaymentApprovalRoute) (a : ReviewAuthorities)
    (facts : HoldFacts) (history : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (conditions : PaymentInstruction → Prop) (paid : PostedPayment)
    (afterLift : List PostLiftPaymentRecord) : Prop :=
  history.payments.actualPaymentWithEvidence paid ∧
  history.payments.recipientReceived part.recipient paid ∧ route.allows a facts history part schedule conditions paid.instruction ∧
  (match route with
  | .ordinary _ =>
    (∃ releasedAt, history.paymentReleasedAt a facts part.ref releasedAt paid.instruction.atTime ∧
      releasedAt.by paid.instruction.atTime) →
      ∃ row ∈ afterLift, row.paid = paid ∧ route.recordMatches row ∧
        row.approvalArrangementRecorded a facts history part ∧ postLiftPaymentRecordConforms a facts history part schedule row
  | .liftOriginal .. | .liftReplacement .. | .liftFirst .. =>
    ∃ row ∈ afterLift, row.paid = paid ∧ route.recordMatches row ∧
      row.approvalArrangementRecorded a facts history part ∧ postLiftPaymentRecordConforms a facts history part schedule row)

/-- A retained approval and actual receipt can be filed after a missed deadline.
    This records what was received; it grants no permission to execute. -/
def PaymentApprovalRoute.observedPayment (route : PaymentApprovalRoute) (a : ReviewAuthorities)
    (facts : HoldFacts) (history : HoldHistory) (part : PaymentPart) (paid : PostedPayment) : Prop :=
  let approval := match route with
    | .ordinary grant | .liftOriginal grant _ | .liftFirst grant _ => grant
    | .liftReplacement _ grant _ => grant
  (history.factsAt facts paid.instruction.atTime).isCanonicalPart part ∧
  history.approvalRecorded approval ∧
  approval.authorisedAtGrant a ∧ approval.grantedAt.by paid.instruction.atTime ∧
  approval.originallyCovered part ∧
  history.payments.actualPaymentWithEvidence paid ∧ history.payments.recipientReceived part.recipient paid ∧
  history.payments.validOutstandingPayment part paid.instruction

/-- Resolve the applicable form term from the same verified lift. -/
def PostLiftCutoffMatches (terms : DeadlineTerms) (history : HoldHistory)
    (releasedAt : Moment) (cutoff : ClockCutoff) : Prop :=
  match terms with
  | .fixed specified => cutoff = .exact specified
  | .after duration => cutoff = ClockBoundary.after history.clockBoundaries releasedAt duration

/-- A route after lifting a hold uses the same original payment and legal dates. -/
def FiledReleaseMatches (f : PartOne) (a : ReviewAuthorities) (facts : HoldFacts)
    (history : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (row : PostLiftPaymentRecord) : Prop :=
  row.schedule.dueAt = schedule.dueAt ∧
  row.schedule.originalExecutionDeadline = schedule.originalExecutionDeadline ∧
  row.schedule.legalDeadline = schedule.legalDeadline ∧
  postLiftTermMatches f.deadlines.postLiftPay row.schedule ∧
  postLiftPaymentRecordConforms a facts history part row.schedule row

/-- Earlier legal dates and prompt deadlines are tested without erasing actual receipts. -/
def FiledPaymentOnTime (f : PartOne) (a : ReviewAuthorities) (facts : HoldFacts)
    (history : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (paid : PostedPayment) (afterLift : List PostLiftPaymentRecord) : Prop :=
  let matchesSchedule := fun row : PostLiftPaymentRecord ↦
    row.paid = paid ∧ FiledReleaseMatches f a facts history part schedule row
  (paymentMeetsApplicableDeadlines a facts history part schedule none paid ∨
    ∃ row ∈ afterLift, matchesSchedule row ∧
      paymentMeetsApplicableDeadlines a facts history part row.schedule
        (some row.releasedAt) paid) ∧
  ∀ releasedAt, releasedAt.by paid.instruction.atTime →
    postLiftPromptPaymentDue a facts history part schedule releasedAt paid.instruction.atTime →
    ∃ row ∈ afterLift, matchesSchedule row ∧ row.releasedAt = releasedAt ∧
      history.metDeadline row.schedule.postLiftDeadline releasedAt paid.instruction.atTime

/-- A timely receipt and timely completion of the full payable portion are separate checks. -/
def FiledPaymentCompletedOnTime (f : PartOne) (a : ReviewAuthorities) (facts : HoldFacts)
    (history : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (afterLift : List PostLiftPaymentRecord) (through : Moment := schedule.originalExecutionDeadline) :
    Prop :=
  let matchesSchedule := FiledReleaseMatches f a facts history part schedule
  (paymentCompletedByApplicableDeadlines a facts history part schedule none through ∨
    ∃ row ∈ afterLift, matchesSchedule row ∧
      paymentCompletedByApplicableDeadlines a facts history part row.schedule (some row.releasedAt)
        through) ∧
  ∀ releasedAt, postLiftPromptPaymentDue a facts history part schedule releasedAt through →
    ∃ row ∈ afterLift, matchesSchedule row ∧ row.releasedAt = releasedAt ∧
      history.resolvesDeadline row.schedule.postLiftDeadline releasedAt ∧
      history.fullyRetainedPortionBy part row.schedule.postLiftDeadline.cutoff through

/-- Common filing requirements for credit restored to the original lesson account. -/
def LessonRefundFiled (f : PartOne) (a : ReviewAuthorities) (facts : HoldFacts)
    (history : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (approval : PaymentApprovalRoute) (conditions : PaymentInstruction → Prop)
    (posting : CreditPosting) (obligation : ObligationId) (amount : Amount)
    (paid : PostedPayment) (afterLift : List PostLiftPaymentRecord) : Prop :=
  LessonRefundReceiptMatches f.place posting obligation paid history.payments ∧
  part.ref = paid.instruction.part ∧ part.recipient = .lessonRefund f.place.account ∧
  facts.coversObligation part.ref part.recipient amount ∧ HoldFacts.matchesForm facts f part.ref ∧
  postLiftTermMatches f.deadlines.postLiftPay schedule ∧
  approval.filedPayment a facts history part schedule conditions paid afterLift

/-- A no-fault cancellation follows the form. A term expressly tied to the lesson
    start retains its own clock, while a cancellation-relative term uses the actual request. -/
def noFaultRefundDeadline (f : PartOne) (ev : StartEvidence) (term : PaymentDeadline)
    (recorded : List PaymentTrigger) (cancellation observed deadline : Moment) : Prop :=
  match term with
  | .after _ _ true => ∃ event ∈ recorded,
      term.appliesForLesson f.lesson ev observed (some event) deadline
  | _ => PaymentDeadline.fromRefundTrigger term recorded cancellation deadline

/-- An actual receipt and the originally agreed no-fault clock use the same place and debit. -/
def NoFaultRefundPosted (f : PartOne) (ev : StartEvidence) (cancellation : NoFaultCancellationRecord)
    (posting : CreditPosting) (refund : ObligationId) (row : RefundRecord) (part : PaymentPart)
    (paid : PostedPayment) (history : HoldHistory) (a : ReviewAuthorities) (facts : HoldFacts)
    (approval : PaymentApprovalRoute) (schedule : PaymentSchedule)
    (refundEvents : List PaymentTrigger) (conditions : PaymentInstruction → Prop)
    (afterLift : List PostLiftPaymentRecord) (onTime completedOnTime : Prop) : Prop :=
  NoFaultRefundReceipt f ev cancellation posting refund row ∧
  refund = cancellation.refundObligation ∧
  (cancellation.noneTaught = true →
    ValidLessonRefund f.place ev.ledger posting refund (cancellation.refundAmount f ev) true) ∧
  noFaultRefundDeadline f ev f.deadlines.noFaultRefundTerms.due refundEvents
    cancellation.cancellation.point posting.point schedule.dueAt ∧
  noFaultRefundDeadline f ev f.deadlines.noFaultRefundTerms.latestExecution refundEvents
    cancellation.cancellation.point posting.point schedule.originalExecutionDeadline ∧
  row.due = refundDeadline schedule.originalExecutionDeadline schedule.legalDeadline ∧
  LessonRefundFiled f a facts history part schedule approval conditions posting refund
    (cancellation.refundAmount f ev) paid afterLift ∧
  (onTime ↔ FiledPaymentOnTime f a facts history part schedule paid afterLift) ∧
  (completedOnTime ↔ FiledPaymentCompletedOnTime f a facts history part schedule afterLift)

/-- The excess credit from an absence is posted under the original account and refund clock. -/
def AbsenceRefundPosted (f : PartOne) (ev : StartEvidence) (s : Schedule)
    (start : Moment) (handler : Handler) (assignment : SettlementAssignment)
    (absence : AbsenceFacts) (reason : AbsenceReasonEvidence)
    (settlement : LessonSettlement) (posting : CreditPosting) (refund : ObligationId)
    (paid : PostedPayment) (part : PaymentPart) (history : HoldHistory) (facts : HoldFacts)
    (approval : PaymentApprovalRoute) (schedule : PaymentSchedule)
    (dueTrigger executionTrigger : Option PaymentTrigger)
    (conditions : PaymentInstruction → Prop) (afterLift : List PostLiftPaymentRecord)
    (onTime completedOnTime : Prop) (filing : RefundRecord)
    (refundFor : LessonId → PlaceId → RefundBasis → Moment → Option ObligationId)
    (earlier : List EarlierFeeRefund) : Prop :=
  let principal := feeAdjustmentRefundPrincipal f.place ev.ledger filing.trigger refund settlement.creditDueBack earlier
  EarlierFeeRefundsFor f.place filing.trigger earlier ∧
  filing.basis = .absence ∧ filing.finalFee = settlement.feePayable ∧ filing.reason ≠ "" ∧
  refundFor f.lesson.id f.place.id .absence filing.trigger = some refund ∧
  filing.trigger.by posting.point ∧
  filing.matches f ev.ledger posting.point filing.reason filing.trigger
    (refundDeadline schedule.originalExecutionDeadline schedule.legalDeadline)
    principal (some refund) ∧
  AbsenceRefundReceived f ev s start handler assignment absence reason history facts
    settlement posting refund paid history.payments earlier ∧
  f.deadlines.refund.due.appliesForLesson f.lesson ev posting.point dueTrigger schedule.dueAt ∧
  f.deadlines.refund.latestExecution.appliesForLesson f.lesson ev posting.point
    executionTrigger schedule.originalExecutionDeadline ∧
  LessonRefundFiled f assignment.authorities facts history part schedule approval conditions
    posting refund principal paid afterLift ∧
  (onTime ↔ FiledPaymentOnTime f assignment.authorities facts history part schedule paid afterLift) ∧
  (completedOnTime ↔ FiledPaymentCompletedOnTime f assignment.authorities facts history part schedule afterLift)

/-- Record the treatment of the unallocated part under the applicable terms.
    This duty does not withhold an independently due restoration to the original account. -/
def OriginalBenefitRemainderHandled (form : PartOne) (ev : StartEvidence)
    (relief : OriginalCompensationSettlement)
    (teaching : TeachingReceived) (ledger : List CreditPosting) (query : Moment) : Prop :=
  form.matches ∧
  (∃ fee, ev.feeAt form relief.settledAt fee ∧ relief.amountsRecorded form.place teaching ledger query fee) ∧
  (0 < relief.unappliedFromOriginalUse →
    relief.unappliedAmountHandledUnderTerms relief.unappliedFromOriginalUse)

/-- The automatic §3.5 refund uses its own actual trigger and confirmed deadlines. -/
def OriginalCompensationRefundPosted (f : PartOne) (ev : StartEvidence) (basis : FaultBasis)
    (authority : Option FaultDecisionRecord) (disputed : Bool) (records : DecisionRecords)
    (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (teaching : TeachingReceived) (agreements : List RemedyAgreement)
    (relief : OriginalCompensationSettlement) (entry : CreditPosting) (refund : ObligationId) (payment : PostedPayment)
    (part : PaymentPart) (history : HoldHistory) (facts : HoldFacts)
    (approval : PaymentApprovalRoute) (schedule : PaymentSchedule)
    (dueTrigger executionTrigger : Option PaymentTrigger)
    (conditions : PaymentInstruction → Prop) (afterLift : List PostLiftPaymentRecord)
    (onTime completedOnTime : Prop) (filing : RefundRecord)
    (refundFor : LessonId → PlaceId → RefundBasis → Moment → Option ObligationId)
    (earlier : List EarlierFeeRefund) : Prop :=
  let settlement := relief.settlement
  let principal := feeAdjustmentRefundPrincipal f.place ledger filing.trigger refund settlement.creditDueBack earlier
  EarlierFeeRefundsFor f.place filing.trigger earlier ∧
  (∃ fee, ev.feeAt f relief.settledAt fee ∧
    relief.amountsRecorded f.place teaching ledger entry.point fee) ∧
  filing.basis = .standardCompensation ∧ filing.finalFee = settlement.feePayable ∧
  filing.reason ≠ "" ∧
  refundFor f.lesson.id f.place.id .standardCompensation filing.trigger = some refund ∧
  filing.trigger.by entry.point ∧ filing.closesCase = false ∧
  (filing.originalWaivedCompensationContinues = true ↔
    teaching = .none ∧ ∃ agreement ∈ agreements,
      agreement.acceptedStandardFor f.place ∧ agreement.acceptedAt.by entry.point) ∧
  filing.matches f ledger entry.point filing.reason filing.trigger
    (refundDeadline schedule.originalExecutionDeadline schedule.legalDeadline)
    principal (some refund) ∧
  OriginalCompensationRefundReceived f basis authority disputed records ledger discounts
    ev.creditRecords.lessonFees relief.settledAt teaching agreements settlement entry refund
    payment history.payments earlier ∧
  f.deadlines.refund.due.appliesForLesson f.lesson ev entry.point dueTrigger schedule.dueAt ∧
  f.deadlines.refund.latestExecution.appliesForLesson f.lesson ev entry.point
    executionTrigger schedule.originalExecutionDeadline ∧
  LessonRefundFiled f records.authorities facts history part schedule approval conditions
    entry refund principal payment afterLift ∧
  (onTime ↔ FiledPaymentOnTime f records.authorities facts history part schedule payment afterLift) ∧
  (completedOnTime ↔ FiledPaymentCompletedOnTime f records.authorities facts history part schedule afterLift)

/-- An approved refund also has to be credited to the original account.
    Legal timeliness is checked against the unchanged deadline, separately from payment. -/
def FaultRefundPosted (c : FaultRefundCase) (posting : CreditPosting)
    (obligation : Nat) (trigger agreedDue due : Moment) (legalDeadline : Option Moment)
    (effectiveFee amount : Amount) (part : PaymentPart) (record : PostedPayment)
    (history : HoldHistory) (facts : HoldFacts) (approval : PaymentApprovalRoute)
    (schedule : PaymentSchedule) (agreedPaymentConditions : PaymentInstruction → Prop)
    (afterLift : List PostLiftPaymentRecord) (onTime : Prop)
    (filing : RefundRecord) : Prop :=
  filing.reason ≠ "" ∧ filing.basis = c.cause.basis ∧ filing.finalFee = effectiveFee ∧
  (filing.closesCase = true ↔ fullRefundClosedBy c.form.place c.closed posting.point) ∧
  (filing.originalWaivedCompensationContinues = true ↔ effectiveFee = 0 ∧
    ¬fullRefundClosedBy c.form.place c.closed posting.point ∧
    ∃ remedy ∈ c.remedies, remedy.agreement.acceptedStandardFor c.form.place ∧
      remedy.agreement.acceptedAt.by posting.point ∧ remedy.stillOwedAt posting.point) ∧
  filing.matches c.form c.ledger posting.point filing.reason trigger due amount (some obligation) ∧
  c.restores posting obligation trigger agreedDue due legalDeadline effectiveFee amount ∧
  PaymentDeadline.fromRefundTrigger c.form.deadlines.refund.due c.refundEvents trigger schedule.dueAt ∧
  schedule.legalDeadline = legalDeadline ∧ schedule.originalExecutionDeadline = agreedDue ∧
  LessonRefundFiled c.form c.decisions.authorities facts history part schedule approval
    agreedPaymentConditions posting obligation amount record afterLift ∧
  (onTime ↔ FiledPaymentOnTime c.form c.decisions.authorities facts history part schedule record afterLift)

/-- Updating a fee does not change the confirmed clock of an earlier refund. -/
def EarlierFeeRefund.paid (old : EarlierFeeRefund) (c : FaultRefundCase) (posting : CreditPosting)
    (payment : PostedPayment) (part : PaymentPart) (history : HoldHistory)
    (facts : HoldFacts) (approval : PaymentApprovalRoute) (schedule : PaymentSchedule)
    (conditions : PaymentInstruction → Prop) (afterLift : List PostLiftPaymentRecord) : Prop :=
  old ∈ c.establishedEarlier ∧ old.lesson = c.form.lesson.id ∧ old.place = c.form.place.id ∧
  old.trigger.before posting.point ∧ ValidLessonRefund c.form.place c.ledger posting old.id old.amount false ∧
  schedule.dueAt = old.due ∧ schedule.originalExecutionDeadline = old.executionDeadline ∧
  schedule.legalDeadline = old.legalDeadline ∧
  LessonRefundFiled c.form c.decisions.authorities facts history part schedule approval conditions
    posting old.id old.amount payment afterLift

/-- Facts extracted from the applicable agreed payment terms and actual trigger record. -/
structure AgreedTutorPayment where
  lesson : LessonId
  tutor : ActorId
  agreementRef : String
  recipient : Option ActorId
  dueTrigger : Option PaymentTrigger
  executionTrigger : Option PaymentTrigger
  /-- The applicable agreement's recorded provision for any unapplied deduction. -/
  shortfallTerms : Option String

/-- A review checks current spendable funds against the still-unpaid refund.
    A shortfall leaves the obligation in place. -/
def FaultRefundFundingChecked (c : FaultRefundCase)
    (trigger agreedDue due : Moment) (legalDeadline : Option Moment) (effectiveFee amount : Amount)
    (obligation : ObligationId) (checked : Moment) (funds : CurrentLessonFunds)
    (covered : Prop) : Prop :=
  c.amountDue checked trigger agreedDue due legalDeadline effectiveFee amount ∧
  obligation = c.obligation ∧ c.newObligationAt trigger ∧
  funds.validFor c.form.lesson ∧ funds.checkedAt = checked ∧
  (covered ↔ reviewRefundFunding c.form.lesson checked funds
    (refundBalanceDue c.form.place c.ledger checked amount (some obligation)))

/-- The coordinator files one account for this lesson and place (§4.3). -/
structure FiledLessonAccount where
  lesson : LessonId
  place : PlaceId
  account : AccountId
  filedBy : ActorId
  filedAt : Moment
  settlementEvidence : Option EvidenceRef
  feePayable : Option Amount
  debited : Amount
  /-- The total assessed for each refund before deducting actual receipts. -/
  refunds : List (ObligationId × Option Amount)
  creditDueBack : Option Amount
  restored : Amount
  tutorPay : Option Amount
  materialShare : Amount
  materialsPending : Bool
  deriving DecidableEq, Repr

def FiledLessonAccount.matches (file : FiledLessonAccount) (form : PartOne)
    (ledger : List CreditPosting) : Prop :=
  form.matches ∧ form.confirmedAt.by file.filedAt ∧ file.filedBy = form.lesson.coordinator ∧
  file.lesson = form.lesson.id ∧ file.place = form.place.id ∧ file.account = form.place.account ∧
  file.debited = debitTotal form.place ledger file.filedAt ∧
  file.restored = creditsRestoredFor form.place ledger file.filedAt

/-- Verified amounts individually determined at settlement under the teaching agreement.
    A class-wide total is formed from the place records before applying the deduction. -/
structure TutorSettlementBasis where
  paymentsByPlace : List LessonSettlement
  hadTutorPayUnderTerms : TutorPayTerms → LessonSettlement → Prop
  nowIndependentlyPayable : PaymentPartRef → Prop
  tutorPartsForPlace : PlaceId → List PaymentPartRef
  absenceWithoutTeaching : Option (Moment × AbsenceFacts × AbsenceReasonEvidence)
  /-- A separately established net portion under the actual agreed terms, including
      any applicable deduction. No allocation of a whole-lesson deduction is inferred. -/
  agreedNetPortion : PaymentPartRef → Option Amount
  operativeSettlement : PlaceId → Moment → Option (LessonSettlement × Moment)
  confirmedDebts : LessonId → ActorId → List TutorDebtRecord
  separateDebtReferences : List Nat

/-- Recording a debt reference does not deduct the debt from the tutor's fee. -/
def TutorSettlementBasis.debtsReferenced (basis : TutorSettlementBasis) (lesson : Lesson)
    (tutor : ActorId) (observed : Moment) : Prop :=
  ConfirmedTutorDebtsReferenced lesson tutor observed
    (basis.confirmedDebts lesson.id tutor) basis.separateDebtReferences

def TutorSettlementBasis.totals (basis : TutorSettlementBasis) (f : PartOne)
    (ev : StartEvidence) (observed : Moment) (forms : List PartOne) (agreement : TutorPayTerms)
    (total : Amount) : Prop :=
  basis.paymentsByPlace ≠ [] ∧ (basis.paymentsByPlace.map (·.place)).Nodup ∧
  (∀ row ∈ basis.paymentsByPlace, ∃ pf ∈ forms,
    pf.lesson = f.lesson ∧ pf.tutorAgreementRef = f.tutorAgreementRef ∧
    basis.hadTutorPayUnderTerms agreement row ∧
    (∃ settled, basis.operativeSettlement row.place observed = some (row, settled) ∧
      settled.by observed ∧ row.matchesPaymentHistory pf.place ev.ledger settled) ∧
    0 ≤ row.tutorPay) ∧ total = sumAmounts basis.paymentsByPlace (·.tutorPay)

/-- Identify the separate part and check the total of its seat's parts once. -/
def TutorSettlementBasis.separatePartMatches (basis : TutorSettlementBasis) (lesson : Lesson)
    (tutor : ActorId) (part : PaymentPart) (facts : HoldFacts) : Prop :=
  basis.nowIndependentlyPayable part.ref ∧ basis.agreedNetPortion part.ref = some part.amount ∧
  ∃ source ∈ basis.paymentsByPlace,
    let parts := basis.tutorPartsForPlace source.place
    part.ref ∈ parts ∧ parts.Nodup ∧
    (∀ other ∈ basis.paymentsByPlace, other.place ≠ source.place →
      ∀ ref ∈ parts, ref ∉ basis.tutorPartsForPlace other.place) ∧
    (∀ ref ∈ parts, ∃ net ∈ basis.agreedNetPortion ref, 0 ≤ net ∧
      ref.lesson = lesson.id ∧ ref.purpose = .tutorPay tutor ∧
      facts.isCanonicalPart { ref := ref, recipient := part.recipient, amount := net }) ∧
    sumAmounts parts (fun ref ↦ (basis.agreedNetPortion ref).getD 0) ≤ source.tutorPay

/-- A separate group payment leaves an actually held, not yet settled seat outside its basis. -/
def TutorSettlementBasis.hasOtherHeldPlace (basis : TutorSettlementBasis) (lesson : Lesson)
    (tutor : ActorId) (forms : List PartOne) (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (settledAt paidAt : Moment) : Prop :=
  ∃ held ∈ forms,
    (∀ row ∈ basis.paymentsByPlace, row.place ≠ held.place.id) ∧
    ((FeeHoldTermsMatch held facts ∧
      (FeeOnHold history a facts held.place settledAt ∨ FeeOnHold history a facts held.place paidAt)) ∨
      ∃ ref ∈ basis.tutorPartsForPlace held.place.id, ref.lesson = lesson.id ∧
        ref.purpose = .tutorPay tutor ∧ HoldFacts.matchesForm facts held ref ∧
        (history.paymentOnHold a facts ref settledAt ∨ history.paymentOnHold a facts ref paidAt))

def TutorSettlementOccurrence (f : PartOne) (ev : StartEvidence) (scheduleUsed : Schedule)
    (actualStart settledAt : Moment) (basis : TutorSettlementBasis) (next : TutorLessonRecord) : Prop :=
  EffectiveSchedule f.lesson ev scheduleUsed actualStart ∧ actualStart.by settledAt ∧
  (ev.teachingBegan = some actualStart ∨
    (ev.teachingBegan = none ∧ next.completedAt = none ∧ next.completedForSparkDAO = false ∧
      ∃ facts reason, basis.absenceWithoutTeaching = some (actualStart, facts, reason) ∧
      ev.retainsOneToOneAbsence f scheduleUsed actualStart settledAt facts ∧
      CanStart f.lesson ev scheduleUsed actualStart ∧ reason.applies f facts settledAt ∧
      (oneToOneAbsenceUsesChangeTerms f.lesson f.place facts ∨
        (oneToOneAbsenceHalfFee f.lesson f.place facts ∧
          ∃ row ∈ basis.paymentsByPlace, row.place = f.place.id ∧
            row.tutorPay = next.lesson.normalTutorFee / 2))))

/-- A zero settlement is recorded without inventing a payment or a receipt. -/
def ZeroTutorSettlementRecorded (f : PartOne) (ev : StartEvidence) (scheduleUsed : Schedule)
    (actualStart recordedAt : Moment)
    (basis : TutorSettlementBasis) (roster : Option Roster) (forms : List PartOne)
    (completionHistory : List TutorLessonRecord) (next : TutorLessonRecord)
    (faultDecisions : List TutorFaultDecisionEvidence) (faults : List TutorFaultCase)
    (deductions : List NextTutorDeductionRecord) (agreedFee : Amount)
    (agreementReference : String) (terms : PaymentTerms) (shortfallTerms : Option String) (handler : Handler)
    (assignment : SettlementAssignment) (holds : HoldHistory) (facts : HoldFacts) : Prop :=
  assignment.authorised f handler recordedAt ∧
  (f.lesson.kind = .group → facts.decisionConcernsWholeGroup assignment.matter assignment.decision) ∧
  holds.mayCarryOutDecision assignment.authorities facts assignment.matter assignment.decision recordedAt ∧
  f ∈ forms ∧ ev.rosterFormsAt f.lesson recordedAt roster forms ∧
  facts.groupSettlementScopeMatches f.lesson (forms.map (·.place)) ∧ next ∈ completionHistory ∧
  next.lesson = { f.lesson with
    tutor := next.lesson.tutor, normalTutorFee := next.lesson.normalTutorFee } ∧
  TutorSettlementOccurrence f ev scheduleUsed actualStart recordedAt basis next ∧
  (∀ deduction ∈ deductions, 0 < deduction.unappliedAmount →
    deduction.shortfallTerms = shortfallTerms) ∧
  EffectiveTutorAgreementAt f ev actualStart next.lesson.tutor agreementReference
    next.lesson.normalTutorFee terms recordedAt recordedAt ∧
  basis.debtsReferenced f.lesson next.lesson.tutor recordedAt ∧
  basis.totals f ev recordedAt forms ⟨agreementReference, next.lesson.normalTutorFee, terms⟩ agreedFee ∧
  (∀ pf ∈ forms, ∃ row ∈ basis.paymentsByPlace, row.place = pf.place.id) ∧
  (∀ fault, fault ∈ faults ↔ ∃ decision ∈ faultDecisions, decision.establishes fault recordedAt) ∧
  TutorAmountsForSettlement completionHistory next faults deductions agreedFee 0

/-- Use the actual lesson and the reduced fee in the payout, not merely in a calculation.
    The fault and completion histories contain the verified decisions and teaching records. -/
def TutorPaymentPosted (f : PartOne) (ev : StartEvidence) (scheduleUsed : Schedule)
    (actualStart settledAt clockBase expiry : Moment)
    (completionHistory : List TutorLessonRecord) (next : TutorLessonRecord)
    (faults : List TutorFaultCase) (deductions : List NextTutorDeductionRecord)
    (agreedFee netPay : Amount)
    (faultDecisions : List TutorFaultDecisionEvidence) (agreed : AgreedTutorPayment)
    (basis : TutorSettlementBasis) (settledRoster : Option Roster) (settledForms : List PartOne)
    (record : PostedPayment) (part : PaymentPart) (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (approval : PaymentApprovalRoute)
    (schedule : PaymentSchedule) (tutorTerms : PaymentTerms)
    (additionalAgreedConditions : PaymentInstruction → Prop)
    (applicableLawRequiresEarlierPayment : Moment → Prop)
    (afterLift : List PostLiftPaymentRecord) (onTime completedOnTime : Prop) : Prop :=
  let instruction := record.instruction
  f ∈ ev.effectiveForms ∧ next ∈ completionHistory ∧
  next.lesson = { f.lesson with tutor := agreed.tutor, normalTutorFee := next.lesson.normalTutorFee } ∧
  TutorSettlementOccurrence f ev scheduleUsed actualStart settledAt basis next ∧
  AgreedStartClock f.lesson ev instruction.atTime clockBase ∧
  expiry.seconds = clockBase.seconds + thirtyDays ∧
  (∀ fault, fault ∈ faults ↔ ∃ decision ∈ faultDecisions, decision.establishes fault settledAt) ∧
  (∀ deduction ∈ deductions, 0 < deduction.unappliedAmount →
    deduction.shortfallTerms = agreed.shortfallTerms) ∧
  agreed.lesson = f.lesson.id ∧
  EffectiveTutorAgreementAt f ev actualStart agreed.tutor agreed.agreementRef
    next.lesson.normalTutorFee tutorTerms instruction.atTime instruction.atTime ∧
  ev.rosterFormsAt f.lesson settledAt settledRoster settledForms ∧
  facts.groupSettlementScopeMatches f.lesson (settledForms.map (·.place)) ∧
  (∀ pf ∈ settledForms, part.ref ∈ basis.tutorPartsForPlace pf.place.id →
    FeeHoldTermsMatch pf facts ∧
    (¬FeeOnHold history a facts pf.place instruction.atTime ∨
      approval.observedPayment a facts history part record)) ∧
  basis.debtsReferenced f.lesson agreed.tutor instruction.atTime ∧
  basis.nowIndependentlyPayable part.ref ∧ HoldFacts.matchesForm facts f part.ref ∧
  tutorTerms.due.appliesForLesson f.lesson ev instruction.atTime agreed.dueTrigger schedule.dueAt ∧
  part.ref.lesson = f.lesson.id ∧ part.ref.purpose = .tutorPay agreed.tutor ∧
  part.recipient = .person agreed.tutor agreed.recipient ∧
  ((basis.totals f ev settledAt settledForms
      ⟨agreed.agreementRef, next.lesson.normalTutorFee, tutorTerms⟩ agreedFee ∧
    (∀ pf ∈ settledForms, ∃ row ∈ basis.paymentsByPlace, row.place = pf.place.id) ∧
    TutorAmountsForSettlement completionHistory next faults deductions agreedFee netPay ∧
    (f.lesson.kind = .group → ∀ pf ∈ settledForms,
      FeeHoldTermsMatch pf facts ∧
    (¬FeeOnHold history a facts pf.place instruction.atTime ∨
      approval.observedPayment a facts history part record)) ∧
    facts.coversPurpose f.lesson.id (.tutorPay agreed.tutor) part.recipient netPay ∧
    instruction.amount ≤ history.payments.remainingPurposeBefore f.lesson.id
      (.tutorPay agreed.tutor) part.recipient netPay instruction.atTime) ∨
  (f.lesson.kind = .group ∧
    basis.hasOtherHeldPlace f.lesson agreed.tutor settledForms history a facts settledAt instruction.atTime ∧
    (∀ fault ∈ faults, fault.originalLesson.id ≠ next.lesson.id ∨
      fault.originalLesson.tutor ≠ next.lesson.tutor) ∧
    (∃ subtotal, basis.totals f ev settledAt settledForms
      ⟨agreed.agreementRef, next.lesson.normalTutorFee, tutorTerms⟩ subtotal) ∧
    basis.separatePartMatches f.lesson agreed.tutor part facts ∧
    deductions = [] ∧ netPay = part.amount)) ∧
  tutorTerms.latestExecution.appliesForLesson f.lesson ev instruction.atTime agreed.executionTrigger
    schedule.originalExecutionDeadline ∧
  postLiftTermMatches f.deadlines.postLiftPay schedule ∧
  settledAt.by instruction.atTime ∧
  (approval.filedPayment a facts history part schedule
    (fun entry ↦ settledAt.by entry.atTime ∧ additionalAgreedConditions entry ∧
      (ClockBoundary.reachedAfter ev.clockBoundaries clockBase thirtyDays entry.atTime ∨
        ∃ earlier ∈ schedule.legalDeadline, applicableLawRequiresEarlierPayment earlier)) record afterLift ∨
    approval.observedPayment a facts history part record) ∧
  (onTime ↔ FiledPaymentOnTime f a facts history part schedule record afterLift) ∧
  (completedOnTime ↔ FiledPaymentCompletedOnTime f a facts history part schedule afterLift)

/-- A pending use or entitlement retains the same subject through verification. -/
structure PendingMaterialsShare where
  lesson : LessonId
  place : PlaceId
  material : MaterialId
  termsReference : String
  checkedAt : Moment
  status : MaterialsShareStatus
  budget : Amount

def PendingMaterialsShare.resolvedBy (pending : PendingMaterialsShare)
    (original : MaterialsSettlementRecord) (verifiedAt : Moment) : Prop :=
  pending.lesson = original.lesson ∧ pending.material = original.material ∧
  pending.termsReference = original.termsReference ∧ pending.place ∈ original.places ∧
  pending.checkedAt.by verifiedAt

def PendingMaterialsProvision (f : PartOne) (terms : MaterialsTerms) (pending : PendingMaterialsShare)
    (otherAmountsOwed : Amount) (funds : CurrentLessonFunds)
    (estimatedUnderApplicableTerms : PendingMaterialsShare → Prop) : Prop :=
  f.matches ∧ f.materialsTermsRef = some terms.agreementReference ∧
  f.materialsPayer = some terms.accountingAndPaymentParty ∧ terms.lesson = f.lesson.id ∧
  pending.lesson = f.lesson.id ∧ pending.place = f.place.id ∧
  pending.termsReference = terms.agreementReference ∧ terms.pricing.covers pending.material ∧
  pending.status.provisionRequired ∧ estimatedUnderApplicableTerms pending ∧
  0 ≤ pending.budget ∧ 0 ≤ otherAmountsOwed ∧
  funds.checkedAt = pending.checkedAt ∧ funds.validFor f.lesson ∧
  funds.secures (pending.budget + otherAmountsOwed)

structure PendingMaterialsFundingRecord where
  pending : PendingMaterialsShare
  form : PartOne
  otherAmountsOwed : Amount
  funds : CurrentLessonFunds
  verifiedEstimate : PendingMaterialsShare → Prop

/-- The adopted materials agreement itself can record the exact resolved date.
    A separate clock record, when present, must agree. -/
def MaterialDeadlineMatches (term : PaymentDeadline) (f : PartOne) (ev : StartEvidence)
    (observed : Moment) (actual : Option PaymentTrigger) (adoptedDate : Moment) : Prop :=
  term.appliesForLesson f.lesson ev observed actual adoptedDate ∨
  ∃ duration reference fromStart event, term = .after duration reference fromStart ∧
    actual = some event ∧ event.reference = reference ∧ reference ≠ "" ∧ 0 < duration ∧
    event.point.seconds + duration = adoptedDate.seconds ∧
    (∀ row ∈ event.boundaries, row.anchor = event.point → row.direction = .after →
      row.duration = duration → row.cutoff = adoptedDate) ∧
    (fromStart = true → event.boundaries = ev.clockBoundaries ∧
      LessonDeadlineAnchor f.lesson ev observed event.point)

/-- Material amounts use the lesson's adopted terms and actual use before payment. -/
def MaterialsPaymentPosted (f : PartOne) (ev : StartEvidence)
    (use : VerifiedMaterialsUse) (terms : MaterialsTerms)
    (material : MaterialId) (holder : ActorId) (evidence : MaterialsShareEvidence material)
    -- These are retained records of obligations established under the adopted terms.
    (original : MaterialsSettlementRecord) (settled : List MaterialsSettlementRecord)
    (shortfalls : List MaterialsShortfall)
    (pendingHistory : List PendingMaterialsShare) (earlierFunding : List PendingMaterialsFundingRecord)
    (provisionPerformed : Prop) (amount : Amount) (agreedRecipient : Option ActorId)
    (earlierRecipients : ActorId → Moment → Option ActorId) (part : PaymentPart)
    (record : PostedPayment) (history : HoldHistory) (authority : ReviewAuthorities)
    (facts : HoldFacts) (approval : PaymentApprovalRoute) (schedule : PaymentSchedule)
    (dueTrigger executionTrigger : Option PaymentTrigger)
    (applicablePayConditions : PaymentInstruction → Prop)
    (afterLift : List PostLiftPaymentRecord) (onTime completedOnTime : Prop)
    (funds : CurrentLessonFunds) (knownAt : Moment := record.instruction.atTime)
    (observed : Bool := false)
    (useBasisVerified : Prop := terms.calculatesVerifiedUse use evidence.advanceCheck
      ((evidence.shortfall.map MaterialsShortfall.identifiedAt).getD
        evidence.originalSettlementAt))
    (principal : MaterialsPrincipalContext := {}) : Prop :=
  let instruction := record.instruction
  let obligation := (evidence.shortfall.map MaterialsShortfall.obligation).getD original.obligation
  let purposeFor := fun payee ↦ match evidence.shortfall with
    | none => PaymentPurpose.materialsShare material payee
    | some shortfall => PaymentPurpose.materialsShortfall material payee shortfall.reference
  let purpose := purposeFor holder
  (∃ roster forms, ev.rosterFormsAt f.lesson instruction.atTime roster forms ∧ f ∈ forms ∧
    ∀ place ∈ use.places, use.materialsAt place.id ≠ [] →
      ∃ pf ∈ forms, pf.place = place ∧ pf.lesson = f.lesson ∧
        pf.materialsOrBundle = f.materialsOrBundle ∧ pf.materialsTermsRef = f.materialsTermsRef ∧
        pf.materialsPayer = f.materialsPayer) ∧
  use.lesson = { f.lesson with tutor := use.lesson.tutor } ∧ f.matches ∧
  EffectiveTutorAt f.lesson ev use.startedAt use.lesson.tutor ∧
  ev.teachingBegan = some use.startedAt ∧ ev.teachingEnded = some use.endedAt ∧
  f.materialsOrBundle = some terms.materialsOrBundle ∧
  (∀ feedback ∈ use.deliveryReports, feedback ∈ ev.afterLesson.serviceFeedback) ∧
  f.materialsTermsRef = some terms.agreementReference ∧
  f.materialsPayer = some terms.accountingAndPaymentParty ∧
  original ∈ settled ∧
  (∀ other ∈ settled, other.lesson = original.lesson → other.material = material →
    (other.obligation = original.obligation ∨ (other.termsReference = original.termsReference ∧
      (other.reference = original.reference ∨ ∃ place ∈ original.places, place ∈ other.places))) →
    other = original) ∧
  evidence.eligibleAt use terms original holder amount instruction.atTime knownAt useBasisVerified
    shortfalls principal ∧
  (match evidence.shortfall with
    | none => True
    | some shortfall =>
      ∀ other ∈ shortfalls, other.lesson = shortfall.lesson →
        other.material = shortfall.material → other.reference = shortfall.reference →
        (other.obligation = shortfall.obligation ∨
          (other.termsReference = shortfall.termsReference ∧
            other.originalSettlementReference = shortfall.originalSettlementReference)) →
        other = shortfall) ∧
  (provisionPerformed ↔ ∀ prior ∈ pendingHistory,
    prior.resolvedBy original evidence.entitlementVerifiedAt →
    prior.status.provisionRequired →
    ∃ funding ∈ earlierFunding, funding.pending = prior ∧ funding.form.lesson = f.lesson ∧
      (∃ roster forms, ev.rosterFormsAt f.lesson funding.funds.checkedAt roster forms ∧
        funding.form ∈ forms) ∧
      PendingMaterialsProvision funding.form terms funding.pending funding.otherAmountsOwed
        funding.funds funding.verifiedEstimate) ∧
  MaterialDeadlineMatches f.deadlines.materialsShares.due f ev instruction.atTime
    dueTrigger terms.paymentDue ∧
  MaterialDeadlineMatches f.deadlines.materialsShares.latestExecution f ev instruction.atTime
    executionTrigger terms.paymentDeadline ∧
  schedule.dueAt = terms.paymentDue ∧ schedule.originalExecutionDeadline = terms.paymentDeadline ∧
  postLiftTermMatches f.deadlines.postLiftPay schedule ∧ HoldFacts.matchesForm facts f part.ref ∧
  part.ref.lesson = use.lesson.id ∧ part.ref.purpose = purpose ∧
  part.ref.obligation = obligation ∧ part.recipient = .person holder agreedRecipient ∧
  evidence.collectionsMatch use terms instruction.atTime (fun priorHolder point ↦
    history.payments.receivedForObligationBefore use.lesson.id obligation
      (.person priorHolder (earlierRecipients priorHolder point)) point (some (purposeFor priorHolder))) ∧
  facts.coversObligation part.ref part.recipient amount ∧
  instruction.amount ≤ history.payments.remainingObligationBefore use.lesson.id obligation
    part.recipient amount instruction.atTime (some purpose) ∧
  (funds.validFor use.lesson ∧ funds.checkedAt = instruction.atTime ∧ funds.covers instruction.amount ∧
    approval.filedPayment authority facts history part schedule applicablePayConditions record afterLift ∨
    (observed = true ∧ approval.observedPayment authority facts history part record)) ∧
  (onTime ↔ FiledPaymentOnTime f authority facts history part schedule record afterLift) ∧
  (completedOnTime ↔ FiledPaymentCompletedOnTime f authority facts history part schedule afterLift)

def applicablePaymentTerms (f : PartOne) : PaymentPurpose → PaymentTerms
  | .lessonRefund _ | .customerFee _ => f.deadlines.refund
  | .tutorPay _ => f.deadlines.tutorPay
  | .materialsShare .. | .materialsShortfall .. => f.deadlines.materialsShares
  | .other => f.deadlines.compensation

/-- The retained handoff and decision use the temporary limit and contact on this form. -/
def LessonTemporaryHoldHandoffRecorded (f : PartOne) (a : ReviewAuthorities)
    (facts : HoldFacts) (history : HoldHistory) (temp : TemporaryHold)
    (governingForm : ReviewMatter → PartOne → Prop)
    (notice : TemporaryHoldNotice) (appointment : ReviewAppointment)
    (decision : TemporaryHoldDecision) : Prop :=
  f.matches ∧ temp.matter.lesson = f.lesson.id ∧ governingForm temp.matter f ∧
  (match temp.part.ref.purpose with
    | .lessonRefund place | .customerFee place => place = f.place.id
    | _ => True) ∧
  ReviewTerms.matchesForm (facts.terms temp.matter) f ∧
  f.contacts.alternativeCanTemporarilyHold = true ∧ temp.contact = f.contacts.alternativeContact ∧
  HoldFacts.matchesForm facts f temp.part.ref ∧
  history.temporaryHoldHandled a facts temp notice appointment decision

/-- The reply deadline uses the term on the confirmed form and the verified trigger for this concern.
    The agreed lesson clock decides whether a linked period follows a reschedule. -/
def ComplaintReplyDeadlineMatches (f : PartOne) (ev : StartEvidence) (concern : Concern)
    (asOf : Moment) (event : Option PaymentTrigger)
    (verifiedEvent : Concern → PaymentTrigger → Prop) (deadline : Moment) : Prop :=
  let term := f.deadlines.finalReply
  match term with
  | .fixed _ => term.applies none deadline
  | .after _ reference true =>
    ∃ base, term.appliesForLesson f.lesson ev asOf
      (some { reference, point := base, boundaries := ev.clockBoundaries }) deadline
  | .after _ _ false =>
    ∃ actual ∈ event, actual.point.by asOf ∧ verifiedEvent concern actual ∧
      term.applies (some actual) deadline

/-- A verified anchor determines the cutoff second even if the within-second order remains unknown. -/
def ComplaintReplyCutoffSecond (f : PartOne) (ev : StartEvidence) (concern : Concern)
    (asOf : Moment) (event : Option PaymentTrigger)
    (verifiedEvent : Concern → PaymentTrigger → Prop) (second : Nat) : Prop :=
  match f.deadlines.finalReply with
  | .fixed cutoff => cutoff.seconds = second
  | .after duration reference true =>
    reference ≠ "" ∧ ∃ base, LessonDeadlineAnchor f.lesson ev asOf base ∧
      base.seconds + duration = second
  | .after duration reference false =>
    reference ≠ "" ∧ ∃ actual ∈ event, actual.point.by asOf ∧ verifiedEvent concern actual ∧
      actual.reference = reference ∧ actual.point.seconds + duration = second

def ComplaintReplyCutoff (f : PartOne) (ev : StartEvidence) (concern : Concern)
    (asOf : Moment) (event : Option PaymentTrigger)
    (verifiedEvent : Concern → PaymentTrigger → Prop) (cutoff : ClockCutoff) : Prop :=
  let exactMatch := ComplaintReplyDeadlineMatches f ev concern asOf event verifiedEvent
  match cutoff with
  | .exact deadline => exactMatch deadline
  | .second second => (¬∃ deadline, exactMatch deadline) ∧
    ComplaintReplyCutoffSecond f ev concern asOf event verifiedEvent second

/-- Acknowledgment states the deadline actually applicable when notice was given. -/
def ComplaintAcknowledgmentDeadlineMatches (f : PartOne) (ev : StartEvidence) (concern : Concern)
    (ackAt : Moment) (event : Option PaymentTrigger) (verifiedEvent : Concern → PaymentTrigger → Prop)
    (legalDeadline : Option Moment) (stated : ClockCutoff) : Prop :=
  let applies := ComplaintReplyCutoff f ev concern ackAt event verifiedEvent
  (∃ agreed, applies agreed ∧ stated =
    match agreed, legalDeadline with
    | .exact deadline, _ => .exact (deadlineUnderEarlierLaw deadline legalDeadline)
    | .second second, none => .second second
    | .second second, some law =>
      if law.seconds < second ∨ (law.seconds = second ∧ law.order = 0)
      then .exact law else .second second) ∨
  ((¬∃ agreed, applies agreed) ∧ ∃ law ∈ legalDeadline, stated = .exact law)

/-- Takeover for the confirmed place uses the governing deadline and designated contact. -/
def LessonReplyEscalationRecorded (f : PartOne) (ev : StartEvidence)
    (terms : ReviewTerms) (concern : Concern)
    (eventAt : Moment → Option PaymentTrigger) (verifiedEvent : Concern → PaymentTrigger → Prop)
    (facts : ConcernFacts) (publication : ConcernContactPublication) (a : ReviewAuthorities)
    (appointments : List ReviewAppointment) (verifiedCheck : ConcernFactCheck → Prop)
    (ack : Option ConcernAcknowledgment) (actualReplies : List ConcernHandlingRecord)
    (initialFindings : List InitialFinding) (reviewFindings : List ReviewFinding)
    (applicableLegalDeadline : Option Moment) (notice : EscalationNotice) (assignment : EscalationAssignment) : Prop :=
  f.matches ∧ ReviewTerms.matchesForm terms f ∧
  (match concern.subject with
    | .customer place _ | .student place _ => place = f.place
    | _ => True) ∧
  let agreedAt := fun atTime deadline ↦
    ComplaintReplyCutoff f ev concern atTime (eventAt atTime) verifiedEvent deadline
  (∃ cutoff, (agreedAt notice.takenOverAt cutoff ∨
      ∃ law ∈ applicableLegalDeadline, cutoff = .exact law) ∧
    cutoff.hasPassed notice.takenOverAt) ∧
  (∀ row ∈ ack,
    concernAcknowledgmentConforms { terms with finalReplyDeadline := row.finalReplyDeadline }
      concern row.handler row ∧
    ComplaintAcknowledgmentDeadlineMatches f ev concern row.acknowledgmentAt
      (eventAt row.acknowledgmentAt) verifiedEvent applicableLegalDeadline row.finalReplyDeadline ∧
    row.acknowledgmentAt.by notice.takenOverAt) ∧
  concernAccepted f.lesson terms facts publication concern ∧
  escalationDetailsConform terms concern.matter (.reply concern.matter.id) notice ∧
  assignment.matches notice ∧ concern.receivedAt.by notice.takenOverAt ∧
  ¬∃ reply ∈ actualReplies, reply.concern = concern ∧
    let prior := reply.acknowledgment
    reply.recorded f.lesson { terms with finalReplyDeadline := prior.finalReplyDeadline }
      facts publication a appointments verifiedCheck (some f.contacts.reviewer) initialFindings reviewFindings ∧
    reply.response.sentAt.by notice.takenOverAt

/-- Match an overdue review to the hold and the case's confirmed terms. -/
def LessonReviewEscalationRecorded (f : PartOne) (a : ReviewAuthorities)
    (facts : HoldFacts) (history : HoldHistory) (hold : FormalHold)
    (decisions : List ReviewFinding) (appointments : List ReviewAppointment)
    (initialFindings : List InitialFinding)
    (governingForm : ReviewMatter → PartOne → Prop)
    (applicableLegalDeadline : Option Moment) (notice : EscalationNotice) (assignment : EscalationAssignment) : Prop :=
  f.matches ∧ hold.matter.lesson = f.lesson.id ∧ governingForm hold.matter f ∧
  ReviewTerms.matchesForm (facts.terms hold.matter) f ∧
  reviewEscalationConforms a facts history hold decisions appointments (some f.contacts.reviewer)
    initialFindings applicableLegalDeadline notice assignment

/-- A review may miss its deadline even when no payment was put on hold. -/
def LessonReviewRequestEscalationRecorded (f : PartOne) (terms : ReviewTerms) (concern : Concern)
    (facts : ConcernFacts) (publication : ConcernContactPublication) (reviewAt : Moment)
    (records : DecisionRecords)
    (applicableLegalDeadline : Option Moment) (notice : EscalationNotice)
    (assignment : EscalationAssignment) : Prop :=
  f.matches ∧ ReviewTerms.matchesForm terms f ∧ concernAccepted f.lesson terms facts publication concern ∧
  (match concern.subject with
    | .customer place _ | .student place _ => place = f.place
    | _ => True) ∧
  (∃ event ∈ facts.appointmentTriggers, event.atTime = reviewAt ∧
    event.applies concern notice.takenOverAt ∧ ∃ party, event.cause = .partyRequestedReview party) ∧
  concern.receivedAt.by reviewAt ∧
  reviewAt.by notice.takenOverAt ∧ assignment.matches notice ∧
  independentReviewer records.authorities concern.matter assignment.assignedTo assignment.assignedAt ∧
  (∀ original ∈ records.initialFindings, original.matter.sameCase concern.matter →
    original.decidedAt.by assignment.assignedAt → original.decider ≠ assignment.assignedTo) ∧
  escalationConforms terms concern.matter (.reviewRequest concern.matter.id)
    (deadlineUnderEarlierLaw terms.finalReviewDeadline applicableLegalDeadline) none notice ∧
  ¬∃ finding ∈ records.reviewFindings, finding.matter.sameCase concern.matter ∧
    reviewAt.by finding.decidedAt ∧ finding.decidedAt.by notice.takenOverAt ∧
    reviewFindingRecordedConforms records.authorities (some f.contacts.reviewer)
      records.appointments records.initialFindings records.reviewFindings finding

/-- Takeover does not choose a new due date for the same obligation. -/
def LessonPaymentEscalationRecorded (f : PartOne) (ev : StartEvidence) (a : ReviewAuthorities) (facts : HoldFacts)
    (history : HoldHistory) (matter : ReviewMatter) (part : PaymentPart)
    (terms : PaymentTerms)
    (establishedTerms : ReviewMatter → PaymentPartRef → PartOne → PaymentTerms → Prop)
    (dueTrigger executionTrigger : Option PaymentTrigger) (schedule : PaymentSchedule)
    (applicableLegalDeadline : Option Moment) (postLiftCutoff : Moment → ClockCutoff)
    (notice : EscalationNotice) (assignment : EscalationAssignment)
    (adoptedMaterials : Option MaterialsTerms := none)
    (tutorSettlements : List RecordedSettlementOutcome := [])
    (tutorAmounts : EvidenceRef → Option PaymentPart := fun _ ↦ none) : Prop :=
  f.matches ∧ matter.lesson = f.lesson.id ∧ ReviewTerms.matchesForm (facts.terms matter) f ∧
  establishedTerms matter part.ref f terms ∧
  (match part.ref.purpose with
    | .tutorPay tutor =>
      let recordedForPart := fun row : RecordedSettlementOutcome ↦
        row.matter.lesson = f.lesson.id ∧ row.decidedAt.by notice.takenOverAt ∧
          ∃ amount ∈ tutorAmounts row.outcome, amount.ref = part.ref
      ∃ settled ∈ tutorSettlements, recordedForPart settled ∧
        tutorAmounts settled.outcome = some part ∧
        (∀ other ∈ tutorSettlements, recordedForPart other → other.decidedAt.by settled.decidedAt) ∧
        ∃ actualStart reference normalFee,
        (ev.teachingBegan = some actualStart ∨
          (ev.teachingBegan = none ∧ ev.verifiedOneToOneAbsenceAt = some actualStart)) ∧
        EffectiveTutorAgreementAt f ev actualStart tutor reference normalFee terms
          notice.takenOverAt notice.takenOverAt
    | .lessonRefund place =>
      place = f.place.id ∧ (terms = f.deadlines.refund ∨ terms = f.deadlines.noFaultRefundTerms)
    | .customerFee place => place = f.place.id ∧ terms = f.deadlines.refund
    | _ => terms = applicablePaymentTerms f part.ref.purpose) ∧
  (match part.ref.purpose with
    | .materialsShare material holder | .materialsShortfall material holder _ =>
      ∃ adopted ∈ adoptedMaterials, adopted.adoptedFor f.lesson ∧
        adopted.agreedAt.by notice.takenOverAt ∧ adopted.pricing.covers material ∧
        (∃ designee, part.recipient = .person holder designee) ∧
        f.materialsOrBundle = some adopted.materialsOrBundle ∧
        f.materialsTermsRef = some adopted.agreementReference ∧
        f.materialsPayer = some adopted.accountingAndPaymentParty ∧
        schedule.dueAt = adopted.paymentDue ∧
        schedule.originalExecutionDeadline = adopted.paymentDeadline ∧
        MaterialDeadlineMatches terms.due f ev notice.takenOverAt dueTrigger adopted.paymentDue ∧
        MaterialDeadlineMatches terms.latestExecution f ev notice.takenOverAt
          executionTrigger adopted.paymentDeadline
    | _ =>
      terms.due.appliesForLesson f.lesson ev notice.takenOverAt dueTrigger schedule.dueAt ∧
      terms.latestExecution.appliesForLesson f.lesson ev notice.takenOverAt
        executionTrigger schedule.originalExecutionDeadline) ∧
  schedule.legalDeadline = applicableLegalDeadline ∧
  paymentEscalationConforms a facts history matter part schedule
    (fun releasedAt ↦ (PostLiftCutoffMatches f.deadlines.postLiftPay history releasedAt
      (postLiftCutoff releasedAt), postLiftCutoff releasedAt))
    notice assignment

/-- Source amounts due in a particular customer redress case. -/
structure AssessedFaultRefund where
  faultCase : FaultRefundCase
  trigger : Moment
  agreedDeadline : Moment
  deadline : Moment
  legalDeadline : Option Moment
  finalFee : Amount
  refund : Amount

inductive ReviewedRefundAssessment where
  | originalCompensation (basis : FaultRefundCase) (settlement : LessonSettlement)
  | faultRefund (assessment : AssessedFaultRefund)

def ReviewedRefundAssessment.matches (assessment : ReviewedRefundAssessment) (f : PartOne)
    (fault : FaultBasis) (finding : ReviewFinding) (decisions : DecisionRecords)
    (credits : List CreditPosting) (part : PaymentPart) (schedule : PaymentSchedule) : Prop :=
  match assessment with
  | .originalCompensation c settlement =>
    c.form = f ∧ c.fault = fault ∧ c.decisions = decisions ∧ c.ledger = credits ∧
    c.obligation = part.ref.obligation ∧
    EarlierFeeRefundsFor f.place finding.decidedAt c.establishedEarlier ∧
    part.amount = feeAdjustmentRefundPrincipal f.place credits finding.decidedAt
      part.ref.obligation settlement.creditDueBack c.establishedEarlier ∧
    AppliesOriginalCompensation f c.fault c.authority c.disputed decisions credits c.discounts
      c.lessonEvidence.creditRecords.lessonFees finding.decidedAt finding.decidedAt
      c.teaching (c.remedies.map (·.agreement)) settlement
  | .faultRefund assessed =>
    let c := assessed.faultCase
    c.form = f ∧ c.fault = fault ∧ c.decisions = decisions ∧ c.ledger = credits ∧
    c.obligation = part.ref.obligation ∧
    part.amount = c.assessedAmount assessed.trigger assessed.finalFee (some part.ref.obligation) ∧
    schedule.originalExecutionDeadline = assessed.agreedDeadline ∧
    schedule.legalDeadline = assessed.legalDeadline ∧
    PaymentDeadline.fromRefundTrigger f.deadlines.refund.due c.refundEvents
      assessed.trigger schedule.dueAt ∧
    c.amountDue finding.decidedAt assessed.trigger assessed.agreedDeadline assessed.deadline
      assessed.legalDeadline assessed.finalFee assessed.refund

/-- Retain the original charge and the revised charge separately from credit owed back. -/
def GroupAbsenceCorrectionRecorded (f : PartOne) (ev : StartEvidence)
    (previous revised : LessonSettlement) (previousAt : Moment)
    (verifiedRevisedFee : EvidenceRef → PlaceId → Amount → Prop)
    (couldNotProvide : ReviewFinding → PlaceId → Prop) (correction : PaymentCorrectionCase)
    (records : DecisionRecords) (outcomes : List RecordedSettlementOutcome)
    (amountRecords : EvidenceRef → Option PaymentPart) (history : PaymentHistory)
    (earlier : List EarlierFeeRefund) (originalRefund : RefundRecord)
    (originalPrincipal : Amount := correction.originalPart.amount)
    (correctedPrincipal : Amount := correction.money.corrected.amount) : Prop :=
  (∃ roster forms, ev.rosterFormsAt f.lesson previousAt roster forms ∧ f ∈ forms) ∧
  (∃ old ∈ outcomes, old.outcome = correction.correction.originalOutcome ∧
    old.matter.sameCase correction.finding.matter ∧ old.decidedAt = previousAt) ∧
  reviewFindingRecordedConforms records.authorities (some f.contacts.reviewer)
    records.appointments records.initialFindings records.reviewFindings correction.finding ∧
  groupPreviousAbsenceCorrectionRequired f.lesson f.place
    (previous.matchesPaymentHistory f.place ev.ledger previousAt)
    (couldNotProvide correction.finding f.place.id) ∧
  revised.matchesPaymentHistory f.place ev.ledger correction.correction.recordedAt ∧
  verifiedRevisedFee correction.finding.outcome f.place.id revised.feePayable ∧
  previous.creditDueBack = grossLessonCreditRestoration previous.debited previous.feePayable ∧
  revised.creditDueBack = grossLessonCreditRestoration revised.debited revised.feePayable ∧
  correction.originalPart.ref.purpose = .lessonRefund f.place.id ∧
  correction.originalPart.recipient = .lessonRefund f.place.account ∧
  EarlierFeeRefundsFor f.place correction.finding.decidedAt earlier ∧
  originalRefund.basis = .absence ∧ originalRefund.lesson = f.lesson.id ∧
  originalRefund.place = f.place.id ∧ originalRefund.account = f.place.account ∧
  originalRefund.finalFee = previous.feePayable ∧
  originalPrincipal = originalRefund.amount ∧
  correction.money.corrected.recipient = .lessonRefund f.place.account ∧
  correctedPrincipal = feeAdjustmentRefundPrincipal f.place ev.ledger correction.finding.decidedAt
    correction.money.corrected.ref.obligation revised.creditDueBack earlier ∧
  correction.retained f.lesson records.authorities records.appointments outcomes amountRecords history

/-- Recompute corrected tutor pay from the same settled amounts, actual completion
    record and fixed deductions used for ordinary tutor settlement. -/
structure TutorCorrectionAmounts where
  settlement : TutorSettlementBasis
  nextLesson : TutorLessonRecord
  completionHistory : List TutorLessonRecord
  faultEvidence : List TutorFaultDecisionEvidence
  faults : List TutorFaultCase
  deductions : List NextTutorDeductionRecord
  gross : Amount
  net : Amount

def TutorCorrectionAmounts.matches (amounts : TutorCorrectionAmounts) (f : PartOne) (ev : StartEvidence)
    (tutor : ActorId) (agreement : TutorPayTerms) (actualStart decidedAt : Moment)
    (part : PaymentPart) (facts : HoldFacts) (history : HoldHistory) (authority : ReviewAuthorities)
    (originallySettledAt paidAt : Moment) : Prop :=
  amounts.nextLesson ∈ amounts.completionHistory ∧
  amounts.nextLesson.lesson = { f.lesson with tutor, normalTutorFee := agreement.normalFee } ∧
  (∃ schedule, TutorSettlementOccurrence f ev schedule actualStart decidedAt
    amounts.settlement amounts.nextLesson) ∧
  (∀ fault, fault ∈ amounts.faults ↔ ∃ evidence ∈ amounts.faultEvidence,
    evidence.establishes fault decidedAt) ∧
  ∃ roster forms, ev.rosterFormsAt f.lesson decidedAt roster forms ∧
    amounts.settlement.totals f ev decidedAt forms agreement amounts.gross ∧
    amounts.settlement.debtsReferenced f.lesson tutor paidAt ∧
    ((∀ form ∈ forms, ∃ row ∈ amounts.settlement.paymentsByPlace, row.place = form.place.id) ∧
      TutorAmountsForSettlement amounts.completionHistory amounts.nextLesson amounts.faults
        amounts.deductions amounts.gross amounts.net ∧
      (f.lesson.kind = .group → ∀ form ∈ forms,
        FeeHoldTermsMatch form facts ∧ ¬FeeOnHold history authority facts form.place paidAt) ∧
      facts.coversPurpose f.lesson.id (.tutorPay tutor) part.recipient amounts.net ∨
    (f.lesson.kind = .group ∧ amounts.deductions = [] ∧
      amounts.settlement.hasOtherHeldPlace f.lesson tutor forms history authority facts originallySettledAt paidAt ∧
      (∀ fault ∈ amounts.faults, fault.originalLesson.id ≠ f.lesson.id ∨ fault.originalLesson.tutor ≠ tutor) ∧
      amounts.settlement.separatePartMatches f.lesson tutor part facts ∧
      (∀ form ∈ forms, part.ref ∈ amounts.settlement.tutorPartsForPlace form.place.id →
        FeeHoldTermsMatch form facts ∧ ¬FeeOnHold history authority facts form.place paidAt)))

/-- A corrected payout requires funds, a retained approval and a clear hold scope at payment. -/
def CorrectedPaymentAuthorised (f : PartOne) (c : PaymentCorrectionCase) (part : PaymentPart)
    (payment : CorrectionPaymentRecord) (history : HoldHistory) (credits : List CreditPosting)
    (authority : ReviewAuthorities) (funds : CurrentLessonFunds) (facts : HoldFacts)
    (approval : PaymentApprovalRoute) (schedule : PaymentSchedule)
    (agreedConditions : PaymentInstruction → Prop) (afterLift : List PostLiftPaymentRecord)
    (scope : CorrectedMonetaryScope) (otherPrincipals : List (ObligationId × Amount) := []) : Prop :=
  let instruction := payment.paid.instruction
  c.additionalPaymentPosted f.lesson history.payments credits (some f.place) payment scope
    otherPrincipals ∧
    funds.validFor f.lesson ∧ funds.checkedAt = instruction.atTime ∧
    funds.covers instruction.amount ∧
    approval.filedPayment authority facts history part schedule agreedConditions payment.paid afterLift

/-- File an evidenced receipt and its actual timing under an adopted correction. -/
def CorrectedPaymentPosted (f : PartOne) (ev : StartEvidence) (c : PaymentCorrectionCase)
    (part : PaymentPart) (applicable : PaymentTerms)
    (settledAbsence : Option (Moment × AbsenceFacts × AbsenceReasonEvidence))
    (reviewedRefund : Option ReviewedRefundAssessment)
    (reviewedGroupAbsence : Option (LessonSettlement × LessonSettlement × Moment))
    (reviewedFee : EvidenceRef → PlaceId → Amount → Prop)
    (reviewedUnavailable : ReviewFinding → PlaceId → Prop)
    (earlierGroupRefunds : List EarlierFeeRefund)
    (reviewedTutorAmounts : Option TutorCorrectionAmounts)
    (retainedRefund : PaymentPartRef → Option RefundRecord)
    (retainedNoFault : Option (Moment × Moment))
    (payment : CorrectionPaymentRecord) (history : HoldHistory) (credits : List CreditPosting)
    (review : DecisionRecords) (outcomes : List RecordedSettlementOutcome)
    (monetaryOutcome : EvidenceRef → Option PaymentPart) (facts : HoldFacts)
    (schedule : PaymentSchedule) (afterLift : List PostLiftPaymentRecord)
    (dueTrigger executionTrigger : Option PaymentTrigger) (onTime completedOnTime : Prop)
    (scope : CorrectedMonetaryScope) (adoptedMaterials : Option MaterialsTerms := none) : Prop :=
  let instruction := payment.paid.instruction
  let reviewedFault := fun fault : FaultBasis ↦
    ∃ row ∈ review.faultOutcomes, row.place = f.place.id ∧
      row.decision = .review c.finding ∧ row.disposition = .fault fault
  let noFaultFiling := fun trigger due : Moment ↦
    (retainedNoFault = some (trigger, due) ∨
      ∃ old, retainedRefund c.originalPart.ref = some old ∧ old.basis = .noFaultCancellation ∧
        old.lesson = f.lesson.id ∧ old.place = f.place.id ∧ old.account = f.place.account ∧
        old.trigger = trigger ∧ old.due = due) ∧
    ¬∃ fault, reviewedFault fault
  let datesMatch := fun terms : PaymentTerms ↦
    terms.due.appliesForLesson f.lesson ev instruction.atTime dueTrigger schedule.dueAt ∧
    terms.latestExecution.appliesForLesson f.lesson ev instruction.atTime
      executionTrigger schedule.originalExecutionDeadline
  (∃ original ∈ outcomes, original.outcome = c.correction.originalOutcome ∧
    original.matter.sameCase c.finding.matter ∧
    ∃ roster forms, ev.rosterFormsAt f.lesson original.decidedAt roster forms ∧ f ∈ forms) ∧
  f.matches ∧ reviewFindingRecordedConforms review.authorities (some f.contacts.reviewer)
    review.appointments review.initialFindings review.reviewFindings c.finding ∧
  history.temporarySettersRecorded review.authorities facts c.finding.matter c.finding.decidedAt ∧
  c.retained f.lesson review.authorities review.appointments outcomes
    monetaryOutcome history.payments scope.selected.prior ∧
  (∀ fault : FaultBasis, c.money.corrected.ref.purpose = .lessonRefund f.place.id →
    reviewedFault fault →
    ∃ assessed ∈ reviewedRefund,
      assessed.matches f fault c.finding review credits
        { c.money.corrected with amount := scope.reviewedPrincipal } schedule) ∧
  (∀ old, retainedRefund c.originalPart.ref = some old → old.basis = .absence →
    f.lesson.kind = .group → reviewedUnavailable c.finding f.place.id →
    ∃ assessment ∈ reviewedGroupAbsence,
      GroupAbsenceCorrectionRecorded f ev assessment.1 assessment.2.1 assessment.2.2
        reviewedFee reviewedUnavailable c review outcomes monetaryOutcome history.payments
          earlierGroupRefunds old scope.previousPrincipal scope.reviewedPrincipal) ∧
  (c.additionalPaymentPosted f.lesson history.payments credits (some f.place) payment scope ∨
    c.observedRefundPosted f.place history.payments credits payment) ∧
  part.ref = instruction.part ∧ part.recipient = c.money.corrected.recipient ∧
  part.amount = c.money.corrected.amount ∧
  HoldFacts.matchesForm facts f part.ref ∧
  (match part.ref.purpose with
    | .tutorPay tutor =>
      (∀ row ∈ review.faultOutcomes, row.decision = .review c.finding →
        ∀ finding facts, row.disposition = .fault (.tutor finding facts) →
          finding.establishedFor { f.lesson with tutor := tutor } →
          c.money.corrected.amount = 0) ∧
      ∃ claimedAt reference fee,
      (ev.teachingBegan = some claimedAt ∨
        (ev.teachingBegan = none ∧ ∃ absent reason,
          settledAbsence = some (claimedAt, absent, reason) ∧
          oneToOneAbsenceHalfFee f.lesson f.place absent ∧
          ∃ old ∈ outcomes, old.outcome = c.correction.originalOutcome ∧
            old.matter.sameCase c.finding.matter ∧ claimedAt.by old.decidedAt ∧
            (∃ schedule, ev.retainsOneToOneAbsence f schedule claimedAt old.decidedAt absent) ∧
            reason.applies f absent old.decidedAt)) ∧
      EffectiveTutorAgreementAt f ev claimedAt tutor reference fee applicable
        instruction.atTime instruction.atTime ∧
      (∃ amounts ∈ reviewedTutorAmounts, ∃ original ∈ outcomes,
        original.outcome = c.correction.originalOutcome ∧ original.matter.sameCase c.finding.matter ∧
        amounts.matches f ev tutor ⟨reference, fee, applicable⟩ claimedAt c.finding.decidedAt part facts history
          review.authorities original.decidedAt instruction.atTime) ∧
      datesMatch applicable
    | .lessonRefund _ =>
      ((∃ trigger due, noFaultFiling trigger due ∧ applicable = f.deadlines.noFaultRefundTerms ∧
        noFaultRefundDeadline f ev applicable.due dueTrigger.toList
          trigger instruction.atTime schedule.dueAt ∧
        noFaultRefundDeadline f ev applicable.latestExecution executionTrigger.toList
          trigger instruction.atTime schedule.originalExecutionDeadline ∧
        (refundDeadline schedule.originalExecutionDeadline schedule.legalDeadline).by due) ∨
      ((¬∃ trigger due, noFaultFiling trigger due) ∧
        applicable = f.deadlines.refund ∧ datesMatch applicable))
    | .materialsShare material _ | .materialsShortfall material _ _ =>
      applicable = f.deadlines.materialsShares ∧
      if c.changesMaterialsCreditor then
        ∃ adopted ∈ adoptedMaterials, adopted.adoptedFor f.lesson ∧
          adopted.agreedAt.by instruction.atTime ∧ adopted.pricing.covers material ∧
          f.materialsOrBundle = some adopted.materialsOrBundle ∧
          f.materialsTermsRef = some adopted.agreementReference ∧
          f.materialsPayer = some adopted.accountingAndPaymentParty ∧
          schedule.dueAt = adopted.paymentDue ∧
          schedule.originalExecutionDeadline = adopted.paymentDeadline ∧
          MaterialDeadlineMatches applicable.due f ev instruction.atTime
            dueTrigger adopted.paymentDue ∧
          MaterialDeadlineMatches applicable.latestExecution f ev instruction.atTime
            executionTrigger adopted.paymentDeadline
      else datesMatch applicable
    | _ => applicable = applicablePaymentTerms f part.ref.purpose ∧ datesMatch applicable) ∧
  postLiftTermMatches f.deadlines.postLiftPay schedule ∧
  (onTime ↔ FiledPaymentOnTime f review.authorities facts history part schedule payment.paid afterLift) ∧
  (completedOnTime ↔ FiledPaymentCompletedOnTime f review.authorities facts history part schedule
    afterLift instruction.atTime)

/-- The investigation is recorded whether or not the account ultimately supports fault. -/
structure TutorInvestigation where
  lesson : LessonId
  incidentAt : Moment
  tutor : ActorId
  coordinator : ActorId
  tutorCheckedAt : Moment
  opportunityToRespondAt : Moment
  studentsChecked : List (ActorId × Moment)

def TutorIssueInvestigated (f : PartOne) (ev : StartEvidence) (query : Moment)
    (failedAgreedTeaching seriousProblem : Prop)
    (affectedPlaces : List PlaceId) (check : TutorInvestigation) : Prop :=
  tutorFaultInvestigationRequired failedAgreedTeaching seriousProblem →
    check.lesson = f.lesson.id ∧ check.coordinator = f.lesson.coordinator ∧
    EffectiveTutorAt f.lesson ev check.incidentAt check.tutor ∧
    check.incidentAt.by check.tutorCheckedAt ∧ check.tutorCheckedAt.by query ∧
    check.incidentAt.by check.opportunityToRespondAt ∧ check.opportunityToRespondAt.by query ∧
    ∃ roster forms, ev.rosterFormsAt f.lesson query roster forms ∧
      ∀ place ∈ affectedPlaces, ∃ form ∈ forms, form.place.id = place ∧
        ∃ contact ∈ check.studentsChecked, contact.1 = form.place.student ∧
          check.incidentAt.by contact.2 ∧ contact.2.by query

/-- Complaint handling depends on the retained concern and the applicable terms.
    It can be recorded independently of ordinary lesson reporting or settlement. -/
def LessonConcernHandled (f : PartOne) (ev : StartEvidence) (terms : ReviewTerms) (facts : ConcernFacts)
    (eventAt : Moment → Option PaymentTrigger) (verifiedEvent : Concern → PaymentTrigger → Prop)
    (applicableLegalDeadline : Option Moment) (published : ConcernContactPublication) (authority : ReviewAuthorities)
    (appointments : List ReviewAppointment) (verifiedCheck : ConcernFactCheck → Prop)
    (initialFindings : List InitialFinding) (reviewFindings : List ReviewFinding)
    (record : ConcernHandlingRecord) : Prop :=
  f.matches ∧ ReviewTerms.matchesForm terms f ∧
  (match record.concern.subject with
    | .customer place _ | .student place _ => place = f.place
    | _ => True) ∧
  let replyAt := record.response.sentAt
  let ackAt := record.acknowledgment.acknowledgmentAt
  let agreed := ComplaintReplyCutoff f ev record.concern replyAt (eventAt replyAt) verifiedEvent
  ((∃ cutoff, agreed cutoff) ∨ applicableLegalDeadline.isSome = true) ∧
  (∀ cutoff, agreed cutoff → cutoff.metBy replyAt) ∧
  (∀ law ∈ applicableLegalDeadline, replyAt.by law) ∧
  ComplaintAcknowledgmentDeadlineMatches f ev record.concern ackAt (eventAt ackAt) verifiedEvent
    applicableLegalDeadline record.acknowledgment.finalReplyDeadline ∧
  record.recorded f.lesson { terms with finalReplyDeadline := record.acknowledgment.finalReplyDeadline }
    facts published authority appointments verifiedCheck (some f.contacts.reviewer) initialFindings reviewFindings

/-- Actual reporting and complaint handling are duties alongside the settlement gate.
    Missing feedback never turns a valid attendance confirmation into acceptance of service. -/
def LessonReportingRecorded (f : PartOne) (ev : StartEvidence) (observed : Moment)
    (handled : List ConcernHandlingRecord) (reportedConcerns : List Concern)
    (terms : Concern → ReviewTerms) (facts : ConcernFacts) (published : ConcernContactPublication)
    (eventFor : Concern → Moment → Option PaymentTrigger) (verifiedEvent : Concern → PaymentTrigger → Prop)
    (authority : ReviewAuthorities) (appointments : List ReviewAppointment)
    (verifiedCheck : ConcernFactCheck → Prop) (applicableLegalReply : Concern → Option Moment)
    (initialFindings : List InitialFinding) (reviewFindings : List ReviewFinding) : Prop :=
  f ∈ ev.effectiveForms ∧ TutorAndCoordinatorReported ev f.lesson observed ∧
    ∀ concern ∈ reportedConcerns, concern.matter.lesson = f.lesson.id →
      ReviewTerms.matchesForm (terms concern) f ∧
      (concernAccepted f.lesson (terms concern) facts published concern →
        let replyRecorded := fun report : ConcernHandlingRecord ↦
          report.concern = concern ∧
          report.recorded f.lesson { terms concern with
            finalReplyDeadline := report.acknowledgment.finalReplyDeadline }
            facts published authority appointments verifiedCheck (some f.contacts.reviewer)
              initialFindings reviewFindings ∧ report.response.sentAt.by observed ∧
          ComplaintAcknowledgmentDeadlineMatches f ev concern report.acknowledgment.acknowledgmentAt
            (eventFor concern report.acknowledgment.acknowledgmentAt) verifiedEvent
            (applicableLegalReply concern) report.acknowledgment.finalReplyDeadline
        let agreed :=
          ComplaintReplyCutoff f ev concern observed (eventFor concern observed) verifiedEvent
        ∀ cutoff, (agreed cutoff ∨ ∃ law ∈ applicableLegalReply concern, cutoff = .exact law) →
          cutoff.mayHavePassed observed →
          ∃ report ∈ handled, replyRecorded report ∧ cutoff.metBy report.response.sentAt)

/-- A student's §2.4 duty is evaluated apart from the coordinator's follow-up
    and apart from permission to settle a class. -/
def StudentAfterLessonReported (f : PartOne) (ev : StartEvidence) (observed : Moment) : Prop :=
  (∃ roster forms, ev.rosterFormsAt f.lesson observed roster forms ∧ f ∈ forms) ∧
  StudentReportingComplete ev f observed

/-- The form records the denominator and actual qualifying confirmations in the roster. -/
def GroupCountsRecorded (l : Lesson) (ev : StartEvidence) (roster : Roster)
    (query : Moment) (reportedCompletion : Bool) (confirmed foundAtFault : List PlaceId)
    (recordedPlaces recordedConfirmations : Nat) : Prop :=
  EffectiveRosterAt roster ev l query ∧
  GroupReportsMatch ev l roster query reportedCompletion confirmed foundAtFault ∧
  ValidCreditHistory ev.openingCredit ev.ledger ev.creditRecords (fun point ↦ point.by query) ∧
  (∀ f, ev.formForRoster l roster f → ev.paidInFull f query → f.confirmedAt.by query ∧
    ev.confirmedBookingFor f (some roster) query) ∧
  recordedPlaces = roster.places.length ∧
  recordedConfirmations = ev.groupConfirmationCount roster l query confirmed foundAtFault

/-- Check the remaining refund against the funds actually available after review.
    The result records coverage or shortage; it does not change the amount owed. -/
def ReviewedRefundFundingChecked (f : PartOne) (c : PaymentCorrectionCase)
    (review : DecisionRecords) (outcomes : List RecordedSettlementOutcome)
    (monetaryOutcome : EvidenceRef → Option PaymentPart) (history : PaymentHistory)
    (credits : List CreditPosting) (funds : CurrentLessonFunds) (covered : Prop)
    (scope : CorrectedMonetaryScope) : Prop :=
  f.matches ∧ c.money.corrected.ref.purpose = .lessonRefund f.place.id ∧
  c.money.corrected.recipient = .lessonRefund f.place.account ∧
  reviewFindingRecordedConforms review.authorities (some f.contacts.reviewer)
    review.appointments review.initialFindings review.reviewFindings c.finding ∧
  c.retained f.lesson review.authorities review.appointments outcomes monetaryOutcome history ∧
  c.finding.decidedAt.by funds.checkedAt ∧ funds.validFor f.lesson ∧
  ∃ outstanding, c.money.outstandingBefore history credits (some f.place)
      funds.checkedAt outstanding scope ∧ (covered ↔ funds.covers outstanding)

/-- §6.3 shortage is measured against the recorded corrected outstanding obligation. -/
def CorrectionShortfallRecorded (f : PartOne) (c : PaymentCorrectionCase) (funds : CurrentLessonFunds)
    (review : DecisionRecords) (outcomes : List RecordedSettlementOutcome)
    (monetaryOutcome : EvidenceRef → Option PaymentPart) (history : PaymentHistory)
    (credits : List CreditPosting) (notice : CorrectionShortageNotice)
    (refundOwedTo : Place → ActorId → Prop) (scope : CorrectedMonetaryScope) : Prop :=
  f.matches ∧ reviewFindingRecordedConforms review.authorities (some f.contacts.reviewer)
    review.appointments review.initialFindings review.reviewFindings c.finding ∧
  c.retained f.lesson review.authorities review.appointments outcomes monetaryOutcome history
    scope.selected.prior ∧
  funds.validFor f.lesson ∧
  correctionShortageNoticeConforms c f.lesson history credits (some f.place)
    funds.checkedAt refundOwedTo notice scope ∧
  ¬funds.covers notice.outstanding

def AssessedFaultRefund.fulfilledBy (assessment : AssessedFaultRefund)
    (query : Moment) : Prop :=
  let c := assessment.faultCase
  c.amountDue query assessment.trigger assessment.agreedDeadline assessment.deadline
    assessment.legalDeadline assessment.finalFee assessment.refund ∧
  c.newObligationAt assessment.trigger ∧
  FeeRefundCompleted c.form.place c.ledger query assessment.refund (some c.obligation)

def FaultCaseResolvedBy (c : FaultRefundCase) (query : Moment) : Prop :=
  let accepted := fun row : RemedyProgress ↦ row.agreement.forPlace c.form.place ∧
    row.agreement.acceptedAt.by query
  fullRefundClosedBy c.form.place c.closed query ∨
  ((∃ row ∈ c.remedies, accepted row) ∧
    ∀ row ∈ c.remedies, accepted row →
      c.remedyDatesMatch row query ∧ row.deliveredBy c.form.place
        { lesson := c.fault.lessonWithResponsibleTutor c.form.lesson, fault := c.fault,
          ledger := c.ledger, teaching := c.teaching, ownsAccount := c.ownsAccount,
          closed := c.closed, feeAt := c.lessonEvidence.feeAt c.form } query)

/-- A due refund is released by actual retained credit. A remedy needs actual delivery. -/
def CustomerRedressDelivery.matchesFaultCase (delivery : CustomerRedressDelivery)
    (assessment : AssessedFaultRefund) : Prop :=
  let c := assessment.faultCase
  delivery.lesson = c.form.lesson.id ∧ delivery.provider = c.form.lesson.provider ∧
  delivery.place = c.form.place.id ∧ delivery.obligation = c.obligation ∧
  assessment.fulfilledBy delivery.fulfilledAt

/-- The reserve transfer uses an actual closed case and all independently established liabilities. -/
structure ServiceReserveTransfer where
  lesson : LessonId
  provider : ActorId
  point : Moment
  postedAmount : Amount
  evidence : EvidenceRef

def FaultReserveTransferRecorded (c : FaultRefundCase) (balance : FaultCaseBalance)
    (ev : StartEvidence) (history : PaymentHistory) (due : List PaymentPart)
    (actuallyDue : PaymentPart → Moment → Prop)
    (funds : CurrentLessonFunds) (assessment : Option AssessedFaultRefund)
    (availableCompensation : LessonId → Moment → Amount) (row : ServiceReserveTransfer) : Prop :=
  row.lesson = c.form.lesson.id ∧ row.provider = c.form.lesson.provider ∧
  (∃ roster forms, ev.rosterFormsAt c.form.lesson row.point roster forms ∧ c.form ∈ forms) ∧
  c.ledger = ev.ledger ∧
  (due.map PaymentPart.ref).Nodup ∧
  (∀ part, part ∈ due ↔ part.ref.lesson = row.lesson ∧ actuallyDue part row.point) ∧
  balance.refunds = sumAmounts
    (ev.ledger.filter (fun entry ↦ match entry.kind with
      | .lessonRefund lesson _ _ => lesson == row.lesson && decide (entry.point.by row.point)
      | _ => false))
    (fun entry ↦ entry.amount - returnedFrom ev.ledger entry row.point) ∧
  funds.validFor c.form.lesson ∧ funds.checkedAt = row.point ∧
  balance.lessonFeesBeforeRefunds =
    funds.amountFrom .lessonFees FundingEntry.available + balance.refunds ∧
  balance.otherAmountsDue = sumAmounts due (fun part ↦ history.remainingBefore part row.point) ∧
  balance.issuedCourseCreditStillAvailable = availableCompensation row.lesson row.point ∧
  balance.transfersToServiceReserve
    (FaultCaseResolvedBy c row.point ∨ ∃ refund ∈ assessment,
      refund.faultCase = c ∧ refund.fulfilledBy row.point) row.postedAmount

/-- A pending budget is not a hold on an amount established under the materials terms. -/
def EstablishedMaterialsPaymentHeld (f : PartOne) (terms : MaterialsTerms)
    (authority : ReviewAuthorities) (history : HoldHistory) (facts : HoldFacts)
    (part : PaymentPart) (atTime : Moment) : Prop :=
  f.matches ∧ terms.adoptedFor f.lesson ∧ f.materialsTermsRef = some terms.agreementReference ∧
  part.ref.lesson = f.lesson.id ∧
  (match part.ref.purpose with
    | .materialsShare material _ | .materialsShortfall material _ _ => terms.pricing.covers material
    | _ => False) ∧
  facts.isCanonicalPart part ∧ 0 < history.payments.remainingBefore part atTime ∧
  HoldFacts.matchesForm facts f part.ref ∧ history.paymentOnHold authority facts part.ref atTime

/-- Link actual teaching or other remedy fulfilment to its own obligation and scope. -/
structure AssessedRemedy where
  faultCase : FaultRefundCase
  progress : RemedyProgress
  obligation : ObligationId

def CustomerRedressDelivery.matchesRemedy (delivery : CustomerRedressDelivery)
    (assessment : AssessedRemedy) : Prop :=
  let c := assessment.faultCase
  delivery.lesson = c.form.lesson.id ∧ delivery.provider = c.form.lesson.provider ∧
  delivery.place = c.form.place.id ∧ delivery.obligation = assessment.obligation ∧
  assessment.progress ∈ c.remedies ∧
  c.remedyDatesMatch assessment.progress delivery.fulfilledAt ∧
  assessment.progress.deliveredBy c.form.place
    { lesson := c.fault.lessonWithResponsibleTutor c.form.lesson, fault := c.fault, ledger := c.ledger, teaching := c.teaching,
      ownsAccount := c.ownsAccount, closed := c.closed, feeAt := c.lessonEvidence.feeAt c.form } delivery.fulfilledAt

/-- Recovery uses the evidenced redress obligations of this breach, which remain separate
    from the tutor's pay and from one another. -/
def TutorDebtRecoveryPosted (f : PartOne) (ev : StartEvidence)
    (loss : TutorBreachLoss) (breachAt : Moment)
    (authorised : LessonId → String → ActorId → Moment → Prop) (finding : TutorLossFinding)
    (debts : List TutorDebtRecord) (debt : TutorDebtRecord) (recoveries : List TutorDebtRecovery)
    (refunds : List AssessedFaultRefund) (remedies : List AssessedRemedy)
    (establishedRedress : LessonId → PlaceId → ObligationId → Prop)
    (delivered : List CustomerRedressDelivery) (record : TutorDebtRecovery) : Prop :=
  f.matches ∧ breachAt.by loss.incurredAt ∧
  loss.lesson = { f.lesson with
    tutor := loss.lesson.tutor, normalTutorFee := loss.lesson.normalTutorFee } ∧
  (∃ terms, EffectiveTutorAgreementAt f ev breachAt loss.lesson.tutor loss.agreement
    loss.lesson.normalTutorFee terms) ∧
  ((refunds.map (fun refund ↦ (refund.faultCase.form.place.id, refund.faultCase.obligation))) ++
    (remedies.map (fun remedy ↦ (remedy.faultCase.form.place.id, remedy.obligation)))).Nodup ∧
  (∀ place obligation, establishedRedress f.lesson.id place obligation →
    (∃ refund ∈ refunds, refund.faultCase.form.lesson.id = f.lesson.id ∧
      refund.faultCase.form.place.id = place ∧ refund.faultCase.obligation = obligation) ∨
    (∃ remedy ∈ remedies, remedy.faultCase.form.lesson.id = f.lesson.id ∧
      remedy.faultCase.form.place.id = place ∧ remedy.obligation = obligation)) ∧
  tutorDebtRecoveryConforms loss.lesson loss.agreement loss authorised finding debts debt
    recoveries establishedRedress
    (fun delivery ↦
      (∃ refund ∈ refunds, CustomerRedressDelivery.matchesFaultCase delivery refund) ∨
      (∃ remedy ∈ remedies, CustomerRedressDelivery.matchesRemedy delivery remedy))
    delivered record

/-- Verify all retained receipts against the assessed refund and its original clocks. -/
def refundPaidFullyOnTime (c : FaultRefundCase) (refund : EarlierFeeRefund) (observed : Moment)
    (history : HoldHistory) (facts : HoldFacts)
    (schedules : PaymentPartRef → PaymentSchedule)
    (followUp : PaymentPartRef → Option Moment)
    (postLiftCutoff : PaymentPartRef → Moment → ClockCutoff) : Prop :=
  let f := c.form
  let parts := (facts.establishedParts f.lesson.id (.lessonRefund f.place.id)).filter
    (fun p ↦ p.ref.obligation == refund.id)
  refund.lesson = f.lesson.id ∧ refund.place = f.place.id ∧ refund.trigger.by observed ∧
  (parts.map PaymentPart.ref).Nodup ∧ sumAmounts parts PaymentPart.amount = refund.amount ∧
  (∀ part ∈ parts,
    part.recipient = .lessonRefund f.place.account ∧ facts.isCanonicalPart part ∧
    HoldFacts.matchesForm facts f part.ref ∧
    (∀ paid ∈ history.payments.posted, paid.instruction.part = part.ref →
      history.payments.recipientReceived part.recipient paid →
      ∃ credit ∈ c.ledger, refund.trigger.before credit.point ∧
        LessonRefundReceiptMatches f.place credit refund.id paid history.payments ∧
        (∀ reversal ∈ c.ledger, reversal.kind = .creditReturned credit.id →
          reversal.account = credit.account → credit.point.before reversal.point →
          ∃ returned ∈ history.payments.returned, returned.paidReceipt = paid.id ∧
            returned.amount = reversal.amount ∧ returned.returnedAt = reversal.point)) ∧
    let schedule := schedules part.ref
    schedule.dueAt = refund.due ∧ schedule.originalExecutionDeadline = refund.executionDeadline ∧
    schedule.legalDeadline = refund.legalDeadline ∧
    postLiftTermMatches f.deadlines.postLiftPay schedule ∧
    (∀ releasedAt, releasedAt.by observed →
      postLiftPromptPaymentDue c.decisions.authorities facts history part schedule releasedAt →
      PostLiftCutoffMatches f.deadlines.postLiftPay history releasedAt (postLiftCutoff part.ref releasedAt) ∧
      history.payments.fullyRetainedBy part (postLiftCutoff part.ref releasedAt)) ∧
    paymentCompletedByApplicableDeadlines c.decisions.authorities facts history part schedule
      (followUp part.ref)) ∧
  FeeRefundCompleted f.place c.ledger observed refund.amount (some refund.id)

def EarlierFeeRefund.fulfilledOnTime (old : EarlierFeeRefund) (c : FaultRefundCase)
    (observed : Moment) (history : HoldHistory) (facts : HoldFacts)
    (schedules : PaymentPartRef → PaymentSchedule)
    (followUp : PaymentPartRef → Option Moment)
    (postLiftCutoff : PaymentPartRef → Moment → ClockCutoff) : Prop :=
  old ∈ c.establishedEarlier ∧ refundPaidFullyOnTime c old observed history facts schedules followUp postLiftCutoff

def WholeRefundCompleteOnTime (assessment : AssessedFaultRefund) (observed : Moment)
    (history : HoldHistory) (facts : HoldFacts)
    (schedules : PaymentPartRef → PaymentSchedule)
    (followUp : PaymentPartRef → Option Moment)
    (postLiftCutoff : PaymentPartRef → Moment → ClockCutoff) : Prop :=
  let c := assessment.faultCase
  c.amountDue observed assessment.trigger assessment.agreedDeadline assessment.deadline
    assessment.legalDeadline assessment.finalFee assessment.refund ∧
  c.newObligationAt assessment.trigger ∧
  ∃ due, PaymentDeadline.fromRefundTrigger c.form.deadlines.refund.due c.refundEvents
    assessment.trigger due ∧
    refundPaidFullyOnTime c
      { id := c.obligation, lesson := c.form.lesson.id, place := c.form.place.id,
        trigger := assessment.trigger, due := due, executionDeadline := assessment.agreedDeadline,
        legalDeadline := assessment.legalDeadline, amount := assessment.refund }
      observed history facts schedules followUp postLiftCutoff

/-- Actual requests remain attributable to the tutor and course coordinator.
    They supply evidence of contact, not authorisation to change a booking. -/
inductive TutorArrangementNeeded where
  | reschedule | cancel | handOver
  deriving DecidableEq, Repr

structure TutorChangeContact where
  lesson : LessonId
  requestedBy : ActorId
  receivedBy : ActorId
  need : TutorArrangementNeeded
  receivedAt : Moment
  reference : EvidenceRef

def TutorChangeContact.matches (contact : TutorChangeContact) (f : PartOne)
    (ev : StartEvidence) (request : TutorArrangementNeeded) (observed : Moment) : Prop :=
  f ∈ ev.effectiveForms ∧ contact.lesson = f.lesson.id ∧
  EffectiveTutorAt f.lesson ev contact.receivedAt contact.requestedBy ∧
  contact.receivedBy = f.lesson.coordinator ∧ contact.need = request ∧ contact.receivedAt.by observed

/-- Scope separate services to their own record and agreed terms. -/
structure IndependentServiceRecord where
  serviceReference : String
  termsReference : String
  separateFromLessons : List LessonId
  recordedAt : Moment

def IndependentServiceRecord.keptSeparate (service : IndependentServiceRecord)
    (lesson : Lesson) (record : LessonSettlement)
    (handledUnderTerms : String → String → Prop) : Prop :=
  service.serviceReference ≠ "" ∧ service.termsReference ≠ "" ∧
  lesson.id ∈ service.separateFromLessons ∧ record.lesson = lesson.id ∧
  handledUnderTerms service.serviceReference service.termsReference

/-- Facts and evidence may still come from a recused handler. This record carries no decision. -/
structure MatterEvidenceSubmission where
  matter : ReviewMatter
  submittedBy : ActorId
  recipient : ActorId
  evidence : EvidenceRef
  receivedAt : Moment

def RecusedEvidenceRecorded (a : ReviewAuthorities) (originalHandler : ActorId)
    (recusal : RecusalRecord) (record : MatterEvidenceSubmission) : Prop :=
  record.submittedBy = originalHandler ∧
  (a.interest record.matter originalHandler record.receivedAt).affected ∧
  recusalConforms a record.matter originalHandler record.receivedAt recusal ∧
  record.recipient = recusal.replacement.handler

/-- The agreed content and service requirements bound a tutor's own method choice. -/
structure TeachingMethodChoice where
  lesson : LessonId
  tutor : ActorId
  method : String
  chosenAt : Moment

def TeachingMethodChoice.permitted (choice : TeachingMethodChoice) (f : PartOne)
    (ev : StartEvidence) (complies : String → String → Prop) : Prop :=
  f ∈ ev.effectiveForms ∧ choice.lesson = f.lesson.id ∧ choice.method ≠ "" ∧
  EffectiveTutorAt f.lesson ev choice.chosenAt choice.tutor ∧
  complies f.serviceTerms choice.method

/-- Apply the retained cancellation or change terms to an allowed event and its fee. -/
structure AgreedChangeAssessment where
  termsReference : String
  finalFee : Amount
  tutorPay : Amount
  verifiedUnderApplicableTerms : Prop

def AgreedChangeSettlementRecorded (f : PartOne) (ev : StartEvidence) (query : Moment)
    (cancellation : Option CancellationRequest) (reschedule : Option AgreedScheduleChange)
    (absence : Option (AbsenceFacts × AbsenceReasonEvidence)) (assessment : AgreedChangeAssessment)
    (settlement : LessonSettlement)
    (handler : Handler) (assignment : SettlementAssignment) (holds : HoldHistory)
    (holdFacts : HoldFacts) : Prop :=
  (∃ roster forms, ev.rosterFormsAt f.lesson query roster forms ∧ f ∈ forms) ∧
  assignment.authorised f handler query ∧
  FeeHoldTermsMatch f holdFacts ∧
  holds.mayCarryOutDecision assignment.authorities holdFacts assignment.matter assignment.decision query ∧
  ¬FeeOnHold holds assignment.authorities holdFacts f.place query ∧
  ((∃ request ∈ cancellation, request.point.by query ∧ CanCancelOneToOne f request ev) ∨
    (∃ change ∈ reschedule, change ∈ ev.changes ∧ change.allowed f.lesson ev ∧
      EffectiveSchedule f.lesson ev change.record.nextSchedule query) ∨
    (∃ entry ∈ absence, oneToOneAbsenceUsesChangeTerms f.lesson f.place entry.1 ∧
      entry.2.applies f entry.1 query ∧
      ∃ schedule start, ev.retainsOneToOneAbsence f schedule start query entry.1)) ∧
  assessment.termsReference = f.cancelChangeTerms ∧ assessment.verifiedUnderApplicableTerms ∧
  settlement.matchesPaymentHistory f.place ev.ledger query ∧
  settlement.feePayable = assessment.finalFee ∧ settlement.tutorPay = assessment.tutorPay ∧
  settlement.creditDueBack = grossLessonCreditRestoration settlement.debited assessment.finalFee

/-- The retained discussion identifies the same failed booking and §6.1 matter. -/
structure BookingDiscussion where
  matter : ReviewMatter
  place : PlaceId
  occurredAt : Moment
  affected : List ActorId
  contacts : List RearrangementContact

def UncoveredBookingDiscussed (f : PartOne) (ev : StartEvidence) (discussion : BookingDiscussion)
    (outsideTerms : Prop) : Prop :=
  f ∈ ev.effectiveForms ∧ outsideTerms ∧ discussion.matter.lesson = f.lesson.id ∧
  discussion.place = f.place.id ∧ f.place.customer ∈ discussion.affected ∧
  (∀ actor ∈ discussion.affected, ∃ contact ∈ discussion.contacts,
    contact.lesson = f.lesson.id ∧ contact.coordinator = f.lesson.coordinator ∧
    contact.recipient = actor ∧ f.confirmedAt.by contact.point ∧ contact.point.by discussion.occurredAt)

def ConcernAfterFailedBookingDiscussion (f : PartOne) (ev : StartEvidence)
    (discussion : BookingDiscussion) (outsideTerms originalCannotGoAhead agreementReached : Prop)
    (terms : ReviewTerms) (facts : ConcernFacts) (publication : ConcernContactPublication)
    (concern : Concern) : Prop :=
  UncoveredBookingDiscussed f ev discussion outsideTerms ∧ originalCannotGoAhead ∧ ¬ agreementReached ∧
  ReviewTerms.matchesForm terms f ∧ discussion.occurredAt.by concern.receivedAt ∧
  concern.matter.sameCase discussion.matter ∧
  (match concern.subject with
    | .customer place _ | .student place _ => place = f.place
    | _ => concern.raisedBy ∈ discussion.affected) ∧
  concernAccepted f.lesson terms facts publication concern

end SourceV14.Operations
