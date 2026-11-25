import SourceV14.Operations

namespace SourceV14.Workflow.Review

open Booking Confirmation Course CreditEvidence Operations SourceV14.Settlement

/-!
Complaint and correction steps for v1.5 §§6.1, 6.3 and 6.6. The confirmation form
supplies the lesson contacts, deadlines, and the separate records of amounts due and
money actually received. The provider can also use applicable published terms for
contributors who did not receive a form.
-/

structure PublishedContacts where
  lesson : LessonId
  publication : ConcernContactPublication
  publishedAt : Moment
  deriving DecidableEq, Repr

structure Intake where
  lesson : Lesson
  terms : ReviewTerms
  form : Option PartOne
  publication : PublishedContacts
  concern : Concern

/-- The original decision can record a particular obligation and its original amount. -/
structure OriginalRecord where
  outcome : RecordedSettlementOutcome
  payment : Option PaymentPart
  deriving DecidableEq, Repr

inductive Correction where
  | nonmonetary (original : OriginalRecord) (finding : ReviewFinding)
      (record : SettlementCorrection)
  | monetary (original : OriginalRecord) (payment : PaymentCorrectionCase)
  deriving DecidableEq, Repr

def Correction.record : Correction → SettlementCorrection
  | .nonmonetary _ _ record => record
  | .monetary _ payment => payment.correction

/-- Filing details for an actual additional receipt under §6.3 and form Part 2. -/
structure CorrectedPayout where
  form : PartOne
  original : OriginalRecord
  correction : PaymentCorrectionCase
  payment : CorrectionPaymentRecord
  recordedAt : Moment
  part : PaymentPart
  applicable : PaymentTerms
  settledAbsence : Option (Moment × AbsenceFacts × AbsenceReasonEvidence)
  reviewedRefund : Option ReviewedRefundAssessment
  reviewedGroupAbsence : Option (LessonSettlement × LessonSettlement × Moment)
  reviewedFee : EvidenceRef → PlaceId → Amount → Prop
  reviewedUnavailable : ReviewFinding → PlaceId → Prop
  earlierGroupRefunds : List EarlierFeeRefund
  reviewedTutorAmounts : Option TutorCorrectionAmounts
  decisions : DecisionRecords
  funds : CurrentLessonFunds
  approval : PaymentApprovalRoute
  schedule : PaymentSchedule
  agreedConditions : PaymentInstruction → Prop
  afterLift : List PostLiftPaymentRecord
  dueTrigger : Option PaymentTrigger
  executionTrigger : Option PaymentTrigger
  onTime : Prop
  completedOnTime : Prop
  adoptedMaterials : Option MaterialsTerms := none

/-- A review-triggered check records the balance available for the remaining refund. -/
structure RefundFundingCheck where
  form : PartOne
  correction : PaymentCorrectionCase
  funds : CurrentLessonFunds
  coversRemaining : Bool

/-- A recorded notice of unpaid money at a verified shortage. -/
structure ShortageFiling where
  form : PartOne
  correction : PaymentCorrectionCase
  funds : CurrentLessonFunds
  notice : CorrectionShortageNotice

/-- An overdue payment notice cites the original form, obligation and payment schedule. -/
structure PaymentEscalation where
  form : PartOne
  matter : ReviewMatter
  part : PaymentPart
  terms : PaymentTerms
  dueTrigger : Option PaymentTrigger
  executionTrigger : Option PaymentTrigger
  schedule : PaymentSchedule
  notice : EscalationNotice
  assignment : EscalationAssignment
  adoptedMaterials : Option MaterialsTerms := none

structure History where
  publications : List PublishedContacts
  intakes : List Intake
  acknowledgments : List (Concern × ConcernAcknowledgment)
  appointmentTriggers : List ConcernAppointmentTrigger
  appointments : List ReviewAppointment
  initialFindings : List InitialFinding
  reviewFindings : List ReviewFinding
  replies : List ConcernHandlingRecord
  escalations : List (Concern × EscalationNotice × EscalationAssignment)
  originals : List OriginalRecord
  corrections : List Correction
  correctedPayouts : List CorrectedPayout
  refundFundingChecks : List RefundFundingCheck := []
  shortageFilings : List ShortageFiling := []
  recoveries : List (PaymentCorrectionCase × RecoveryRecord) := []
  reviewEscalations : List (ReviewMatter × EscalationNotice × EscalationAssignment) := []
  paymentEscalations : List PaymentEscalation := []
  refundAssessments : List (PaymentCorrectionCase × AssessedFaultRefund) := []

def History.empty : History where
  publications := []
  intakes := []
  acknowledgments := []
  appointmentTriggers := []
  appointments := []
  initialFindings := []
  reviewFindings := []
  replies := []
  escalations := []
  originals := []
  corrections := []
  correctedPayouts := []

def History.originalOutcomes (history : History) : List RecordedSettlementOutcome :=
  history.originals.map OriginalRecord.outcome

def History.paymentCorrections (history : History) : List PaymentCorrectionCase :=
  history.corrections.filterMap fun row ↦ match row with
    | .nonmonetary .. => none
    | .monetary _ payment => some payment

private structure PortionVersion where
  outcome : Option EvidenceRef
  effectiveAt : Moment
  trail : CorrectedPortion
  origin : Option OriginalRecord
  deriving DecidableEq

private def principalFor (versions : List PortionVersion) (ref : PaymentPartRef)
    (recipient : PaymentRecipient) : Amount :=
  sumAmountsWhere versions (fun version ↦ version.trail.part.ref.sameObligation ref &&
    version.trail.part.recipient.samePayee recipient) (·.trail.part.amount)

private def adoptPortionRevision (versions : List PortionVersion)
    (revision : PaymentCorrectionCase) : Option (List PortionVersion) := do
  let [old] := versions.filter (fun old ↦ decide
    ((old.outcome = none ∨ old.outcome = some revision.correction.originalOutcome) ∧
      old.effectiveAt.by revision.finding.decidedAt ∧ old.trail.part = revision.originalPart))
    | none
  let corrected := revision.money.corrected
  if !old.trail.part.ref.sameCorrectionClaim corrected.ref ||
      !old.trail.part.matchesMaterialsCreditor || !corrected.matchesMaterialsCreditor ||
      decide (corrected.amount < 0) then none
  else
    let next : PortionVersion := ⟨some revision.finding.outcome, revision.finding.decidedAt,
      ⟨corrected, old.trail.part :: old.trail.prior⟩, old.origin⟩
    some (versions.map fun version ↦ if version = old then next else version)

private def History.retainedPortionsAt (history : History) (ref : PaymentPartRef)
    (query knownAt : Moment)
    (refundPortions : Option (Moment × List PaymentPart)) (capture : Option PaymentCorrectionCase) :
    Option (List PortionVersion × Option (Amount × Amount)) := do
  let revisions := (history.paymentCorrections.filter fun row ↦
    ref.sameCorrectionClaim row.originalPart.ref && decide
      (row.correction.lesson = ref.lesson ∧ row.finding.decidedAt.by row.correction.recordedAt ∧
        row.finding.decidedAt.by query ∧ row.correction.recordedAt.by knownAt)).mergeSort
    (fun first second ↦ decide (first.finding.decidedAt.by second.finding.decidedAt))
  let initial ← match refundPortions with
    | some (recordedAt, parts) =>
      if recordedAt.by query ∧
          parts.all (fun part ↦ ref.sameObligation part.ref && decide (0 ≤ part.amount)) = true
      then some (parts.map fun part ↦ ⟨none, recordedAt, ⟨part, []⟩, none⟩)
      else none
    | none => some (history.originals.filterMap fun row ↦ do
      let part ← row.payment
      if ref.sameCorrectionClaim part.ref && decide (row.outcome.decidedAt.by query) &&
          !revisions.any (fun revision ↦ decide
            (revision.finding.outcome = row.outcome.outcome ∧
              revision.money.corrected = part ∧
              revision.finding.decidedAt.by row.outcome.decidedAt ∧
              revision.finding.matter.lesson = row.outcome.matter.lesson ∧
              revision.finding.matter.id = row.outcome.matter.id))
      then some ⟨some row.outcome.outcome, row.outcome.decidedAt, ⟨part, []⟩, some row⟩
      else none)
  if ¬ (initial.map (·.trail.part.ref)).Nodup then none
  else
    let (versions, reviewed) ← revisions.foldlM
      (fun (versions, reviewed) revision ↦ do
        let next ← adoptPortionRevision versions revision
        let reviewed := if capture = some revision then
          some (principalFor versions revision.originalPart.ref revision.originalPart.recipient,
            principalFor next revision.money.corrected.ref revision.money.corrected.recipient)
          else reviewed
        pure (next, reviewed)) (initial, none)
    if (versions.flatMap (·.trail.refs)).Nodup then some (versions, reviewed) else none

/-- The original portions come from the adopted refund assessment when one exists.
Each dated correction replaces the exact amount and reference adopted for its portion. -/
def History.correctedScopeAt (history : History) (c : PaymentCorrectionCase) (query : Moment)
    (refundPortions : Option (Moment × List PaymentPart) := none) (knownAt : Moment := query) :
    Option CorrectedMonetaryScope := do
  let (versions, reviewed) ← history.retainedPortionsAt c.originalPart.ref query knownAt
    refundPortions (some c)
  let (previousPrincipal, reviewedPrincipal) ← reviewed
  let [selected] := versions.filter (fun version ↦
    version.outcome == some c.finding.outcome && version.trail.part == c.money.corrected)
    | none
  some ⟨selected.trail, versions.map (·.trail), previousPrincipal, reviewedPrincipal⟩

private def History.refundPrincipalFrom (history : History) (ref : PaymentPartRef)
    (recipient : PaymentRecipient) (query : Moment)
    (base : Option (Moment × List PaymentPart)) : Option Amount := do
  let (versions, _) ← history.retainedPortionsAt ref query query base none
  if versions.all (fun version ↦ version.trail.part.recipient.samePayee recipient) then
    some (principalFor versions ref recipient)
  else none

/-- Account filing and corrected payment read the same retained refund portions. -/
def History.refundPrincipalAt (history : History) (ref : PaymentPartRef) (recipient : PaymentRecipient)
    (recordedAt : Moment) (parts : List PaymentPart) (query : Moment) : Option Amount :=
  history.refundPrincipalFrom ref recipient query (some (recordedAt, parts))

/-- Independently retained original refund decisions supply amounts when no assessment represents
those obligations. The decision date establishes presence before the cutoff. -/
def History.priorRefundPrincipalsFromOriginals (history : History) (place : Place)
    (represented : List ObligationId) (cutoff query : Moment) : Option (List (ObligationId × Amount)) :=
  let recipient := PaymentRecipient.lessonRefund place.account
  let purpose := PaymentPurpose.lessonRefund place.id
  let obligations := history.originals.filterMap fun row ↦ do
    let part ← row.payment
    if row.outcome.matter.lesson = place.lesson ∧ row.outcome.decidedAt.before cutoff ∧
        part.ref.lesson = place.lesson ∧ part.ref.purpose = purpose ∧ part.recipient = recipient ∧
        part.ref.obligation ∉ represented then some part.ref.obligation else none
  obligations.eraseDups.mapM fun obligation ↦ do
    let amount ← history.refundPrincipalFrom ⟨place.lesson, obligation, 0, purpose⟩ recipient query none
    pure (obligation, amount)

private def History.priorMaterialsPartsFor (history : History) (original : OriginalRecord)
    (payment : PaymentCorrectionCase) : Option (List PaymentPart) :=
  if payment.money.corrected.ref.purpose.isMaterialsShare then
    let saved : History :=
      { history with corrections := history.corrections ++ [Correction.monetary original payment] }
    (saved.correctedScopeAt payment payment.correction.recordedAt).map (·.selected.prior)
  else some []

private def amountsFor (old : OriginalRecord) (payment : PaymentCorrectionCase)
    (reference : EvidenceRef) : Option PaymentPart :=
  if reference = old.outcome.outcome then old.payment
  else if reference = payment.finding.outcome then some payment.money.corrected
  else none

/-- Amounts are looked up for the particular retained correction and its linked original decision.
    Distinct people or obligations may be addressed by the same reviewed outcome. -/
def History.monetaryOutcome (history : History) (payment : PaymentCorrectionCase)
    (reference : EvidenceRef) : Option PaymentPart :=
  history.corrections.findSome? fun row ↦ match row with
    | .nonmonetary .. => none
    | .monetary original saved =>
      if saved = payment then amountsFor original saved reference else none

/-- Evidence from the parties, the authority register and the agreed or published terms. -/
structure Evidence where
  authority : ReviewAuthorities
  holds : HoldFacts
  concernFacts : ConcernFacts
  publishedTerms : Lesson → ConcernContactPublication → ReviewTerms → Prop
  replyTrigger : Concern → Moment → Option PaymentTrigger
  verifiedReplyTrigger : Concern → PaymentTrigger → Prop
  replyLegalDeadline : Concern → Option Moment
  verifiedFactCheck : ConcernFactCheck → Prop
  originalOutcome : RecordedSettlementOutcome → Prop
  recordedAmount : ReviewMatter → EvidenceRef → PaymentPart → Prop
  recoveryUnderOriginalTerms : PaymentPart → RecoveryDecision → Prop := fun _ _ ↦ False
  mayApproveRecovery : ReviewMatter → ActorId → Moment → Prop := fun _ _ _ ↦ False
  governingReviewForm : ReviewMatter → PartOne → Prop := fun _ _ ↦ False
  reviewLegalDeadline : ReviewMatter → Option Moment := fun _ ↦ none
  establishedPaymentTerms : ReviewMatter → PaymentPartRef → PartOne → PaymentTerms → Prop :=
    fun _ _ _ _ ↦ False
  paymentLegalDeadline : PaymentPartRef → Option Moment := fun _ ↦ none
  verifiedPaymentTrigger : PaymentPartRef → PaymentTrigger → Prop := fun _ _ ↦ False
  refundPortionsAt : PartOne → ObligationId → Moment → Option (Moment × List PaymentPart) :=
    fun _ _ _ ↦ none
  /-- Basis, actual trigger and effective deadline from the retained assessment. -/
  refundOriginAt : PartOne → PaymentPartRef → Moment → Option (RefundBasis × Moment × Moment) :=
    fun _ _ _ ↦ none
  refundPriorPrincipals : PartOne → ObligationId → Moment → Option (List (ObligationId × Amount)) :=
    fun _ _ _ ↦ none
  /-- Verified structured contents of this exact review. The refund consumer rechecks the
  effective fee, original case and refund amount. -/
  reviewedFaultRefund : PaymentCorrectionCase → Option AssessedFaultRefund := fun _ ↦ none

def Evidence.noFaultRefundAt (evidence : Evidence) (form : PartOne) (ref : PaymentPartRef)
    (time : Moment) : Option (Moment × Moment) := do
  let (basis, trigger, due) ← evidence.refundOriginAt form ref time
  if basis = .noFaultCancellation then some (trigger, due) else none

private def Evidence.correctionRefundPortions (evidence : Evidence) (form : PartOne)
    (c : PaymentCorrectionCase) (time : Moment) : Option (Moment × List PaymentPart) :=
  let ref := c.money.corrected.ref
  if ref.purpose = .lessonRefund form.place.id then
    evidence.refundPortionsAt form ref.obligation time
  else none

private def History.correctedScopeForFormAt (history : History) (evidence : Evidence)
    (form : PartOne) (c : PaymentCorrectionCase) (query : Moment) (knownAt : Moment := query) :
    Option CorrectedMonetaryScope :=
  history.correctedScopeAt c query (evidence.correctionRefundPortions form c query) knownAt

/-- An original decision retained by this workflow counts even if the parties later change. -/
def History.authorities (history : History) (authority : ReviewAuthorities) : ReviewAuthorities :=
  { authority with actualOriginalDecisions := authority.actualOriginalDecisions ++
      history.originals.map (fun row ↦
        (row.outcome.matter, row.outcome.decidedBy, row.outcome.decidedAt)) }

def History.concernFacts (history : History) (facts : ConcernFacts) : ConcernFacts :=
  { facts with appointmentTriggers := history.appointmentTriggers }

def History.decisionRecords (history : History) (authority : ReviewAuthorities)
    (facts : DecisionRecords) : DecisionRecords :=
  { facts with
    authorities := history.authorities authority
    appointments := history.appointments
    initialFindings := history.initialFindings
    reviewFindings := history.reviewFindings }

/-- A receipt can supply a prior refund's terms only when it agrees with the
retained assessment where one exists. Receipt filing establishes actual credit. -/
def Evidence.retainedRefundAt (evidence : Evidence) (form : PartOne) (start : StartEvidence)
    (through : Moment) (part : PaymentPartRef) : Option RefundRecord :=
  let origin := evidence.refundOriginAt form part through
  (start.creditRecords.verifiedRefunds.reverse.find? fun file ↦
    decide (file.payment.instruction.part.sameObligation part = true ∧
      file.payment.instruction.atTime.by through) &&
    origin.all (fun (basis, trigger, due) ↦
      file.settlement.basis == basis && file.settlement.trigger == trigger &&
        file.settlement.due == due)).map (·.settlement)

def CorrectedPayout.paymentScope (row : CorrectedPayout) (history : History) (evidence : Evidence) :
    Option CorrectedMonetaryScope :=
  history.correctedScopeForFormAt evidence row.form row.correction
    row.payment.paid.instruction.atTime row.recordedAt

/-- The filing uses the adopted correction, the shared ledger and the actual payment history.
    Money, holds and approvals are recorded through their own steps. -/
def CorrectedPayout.conforms (row : CorrectedPayout) (history : History) (evidence : Evidence)
    (start : StartEvidence) (holds : HoldHistory) : Prop :=
  let c := row.correction
  let holds := holds.withPartRevisionsKnownAt row.recordedAt
  row.original ∈ history.originals ∧ .monetary row.original c ∈ history.corrections ∧
    row.payment.paid.instruction.atTime.by row.recordedAt ∧
    ∃ scope ∈ row.paymentScope history evidence,
      CorrectedPaymentPosted row.form start c row.part row.applicable row.settledAbsence
      row.reviewedRefund row.reviewedGroupAbsence row.reviewedFee row.reviewedUnavailable
      row.earlierGroupRefunds row.reviewedTutorAmounts
      (evidence.retainedRefundAt row.form start c.finding.decidedAt)
      (evidence.noFaultRefundAt row.form c.originalPart.ref c.finding.decidedAt)
      row.payment holds start.ledger (history.decisionRecords evidence.authority row.decisions)
      [row.original.outcome] (history.monetaryOutcome c) evidence.holds
      row.schedule row.afterLift row.dueTrigger row.executionTrigger
      row.onTime row.completedOnTime scope row.adoptedMaterials

def CorrectedPayout.authorised (row : CorrectedPayout) (history : History) (evidence : Evidence)
    (start : StartEvidence) (holds : HoldHistory) : Prop :=
  let priors := match row.part.recipient with
    | .lessonRefund _ => evidence.refundPriorPrincipals row.form row.part.ref.obligation
        row.payment.paid.instruction.atTime
    | .person .. => some []
  row.conforms history evidence start holds ∧
    ∃ scope ∈ row.paymentScope history evidence, ∃ principals ∈ priors,
      CorrectedPaymentAuthorised row.form row.correction row.part row.payment
        (holds.withPartRevisionsKnownAt row.recordedAt) start.ledger
        (history.authorities evidence.authority) row.funds evidence.holds row.approval
        row.schedule row.agreedConditions row.afterLift scope principals

private def formRetainedAt (start : StartEvidence) (form : PartOne)
    (lesson : Lesson) (time : Moment) : Prop :=
  form.lesson = lesson ∧ form.matches ∧ form.confirmedAt.by time ∧
    (form ∈ start.effectiveForms ∨ ∃ booking, (form, booking) ∈ start.bookings)

def Intake.termsApply (entry : Intake) (evidence : Evidence) (start : StartEvidence) : Prop :=
  match entry.form with
  | none => evidence.publishedTerms entry.lesson entry.publication.publication entry.terms
  | some form =>
    formRetainedAt start form entry.lesson entry.concern.receivedAt ∧
    Operations.ReviewTerms.matchesForm entry.terms form ∧
    match entry.concern.subject with
    | .customer place _ | .student place _ => place = form.place
    | _ => True

def Intake.namedReviewer (entry : Intake) : Option ActorId :=
  entry.form.map (·.contacts.reviewer)

private def Intake.replyCutoff (entry : Intake) (evidence : Evidence)
    (start : StartEvidence) (time : Moment) (cutoff : ClockCutoff) : Prop :=
  match entry.form with
  | none => cutoff = entry.terms.finalReplyDeadline
  | some form => ComplaintReplyCutoff form start entry.concern time
      (evidence.replyTrigger entry.concern time) evidence.verifiedReplyTrigger cutoff

def Intake.replyOnTime (entry : Intake) (evidence : Evidence)
    (start : StartEvidence) (reply : ConcernResponse) : Prop :=
  let agreed := entry.replyCutoff evidence start reply.sentAt
  let legal := evidence.replyLegalDeadline entry.concern
  ((∃ cutoff, agreed cutoff) ∨ legal.isSome = true) ∧
    (∀ cutoff, agreed cutoff → cutoff.metBy reply.sentAt) ∧
    ∀ deadline ∈ legal, reply.sentAt.by deadline

private def Intake.ackDeadlineMatches (entry : Intake) (evidence : Evidence)
    (start : StartEvidence) (ack : ConcernAcknowledgment) : Prop :=
  let legal := evidence.replyLegalDeadline entry.concern
  match entry.form with
  | some form => ComplaintAcknowledgmentDeadlineMatches form start entry.concern
      ack.acknowledgmentAt (evidence.replyTrigger entry.concern ack.acknowledgmentAt)
      evidence.verifiedReplyTrigger legal ack.finalReplyDeadline
  | none => ack.finalReplyDeadline =
    match entry.terms.finalReplyDeadline, legal with
    | .exact deadline, _ => .exact (deadlineUnderEarlierLaw deadline legal)
    | .second second, none => .second second
    | .second second, some law =>
      if law.seconds < second ∨ (law.seconds = second ∧ law.order = 0)
      then .exact law else .second second

private def History.matterRetained (history : History) (matter : ReviewMatter)
    (time : Moment) : Prop :=
  (∃ row ∈ history.intakes,
    row.concern.matter.sameCase matter ∧ row.concern.receivedAt.by time) ∨
  (∃ row ∈ history.initialFindings, row.matter.sameCase matter ∧ row.decidedAt.by time) ∨
  ∃ row ∈ history.originals,
    row.outcome.matter.sameCase matter ∧ row.outcome.decidedAt.by time

/-- Verify a takeover using the applicable law, the agreed dates and the common payment history. -/
def PaymentEscalation.conforms (row : PaymentEscalation) (history : History) (evidence : Evidence)
    (start : StartEvidence) (holds : HoldHistory) : Prop :=
  let takenOverAt := row.notice.takenOverAt
  let hasTutorRevision :=
    match row.part.ref.purpose with
    | .tutorPay _ => history.paymentCorrections.any fun revision ↦
      (revision.originalPart.ref == row.part.ref || revision.money.corrected.ref == row.part.ref) &&
        decide (revision.correction.recordedAt.by takenOverAt)
    | _ => false
  -- A revised notice names the current portion. Its original decision supplies the terms.
  let tutorOrigin := if hasTutorRevision then (do
    let (versions, _) ← history.retainedPortionsAt row.part.ref takenOverAt takenOverAt none none
    let [current] := versions.filter (fun version ↦ version.trail.part == row.part)
      | none
    if current.trail.prior.isEmpty ||
        !current.trail.prior.all (fun prior ↦ prior.recipient.samePayee row.part.recipient)
    then none else current.origin)
    else none
  let originalRef := (tutorOrigin.bind fun origin ↦ origin.payment.map (·.ref)).getD row.part.ref
  let tutorSettlements :=
    if hasTutorRevision then tutorOrigin.toList.map (·.outcome) else history.originalOutcomes
  let tutorAmount := fun outcome ↦
    if hasTutorRevision then
      tutorOrigin.bind fun original ↦ if original.outcome.outcome == outcome then some row.part else none
    else
      (history.originals.find? fun original ↦ original.outcome.outcome == outcome &&
        original.payment.any (fun part ↦ part.ref == row.part.ref)).bind (·.payment)
  let verified := fun (term : PaymentDeadline) (supplied : Option PaymentTrigger) ↦
    match term with
    | .after _ _ false => ∀ trigger ∈ supplied,
        evidence.verifiedPaymentTrigger originalRef trigger ∧
        trigger.point.by takenOverAt ∧ trigger.boundaries = start.clockBoundaries
    | _ => True
  formRetainedAt start row.form row.form.lesson takenOverAt ∧
    postLiftTermMatches row.form.deadlines.postLiftPay row.schedule ∧
    verified row.terms.due row.dueTrigger ∧ verified row.terms.latestExecution row.executionTrigger ∧
    LessonPaymentEscalationRecorded row.form start (history.authorities evidence.authority)
      evidence.holds (holds.withPartRevisionsKnownAt takenOverAt) row.matter row.part row.terms
      (fun matter _ ↦ evidence.establishedPaymentTerms matter originalRef)
      row.dueTrigger row.executionTrigger row.schedule (evidence.paymentLegalDeadline originalRef)
      (fun _ ↦ row.schedule.postLiftDeadline.cutoff) row.notice row.assignment
      row.adoptedMaterials tutorSettlements tutorAmount

inductive Event where
  | publishContacts (lesson : Lesson) (terms : ReviewTerms) (record : PublishedContacts)
  | receive (entry : Intake)
  | acknowledge (entry : Intake) (ack : ConcernAcknowledgment)
  | requestAppointment (entry : Intake) (trigger : ConcernAppointmentTrigger)
  | appoint (appointment : ReviewAppointment)
  | decideInitial (form : PartOne) (terms : ReviewTerms) (finding : InitialFinding)
  | retainOriginal (lesson : Lesson) (record : OriginalRecord)
  | decideReview (lesson : Lesson) (form : Option PartOne) (finding : ReviewFinding)
  | reply (entry : Intake) (record : ConcernHandlingRecord)
  | escalateReply (entry : Intake) (notice : EscalationNotice)
      (assignment : EscalationAssignment)
  | escalateHeldReview (form : PartOne) (hold : FormalHold) (notice : EscalationNotice)
      (assignment : EscalationAssignment)
  | escalateRequestedReview (entry : Intake) (requestedAt : Moment) (notice : EscalationNotice)
      (assignment : EscalationAssignment)
  | escalatePayment (row : PaymentEscalation)
  | recordCorrection (lesson : Lesson) (correction : Correction)
  | fileRecovery (lesson : Lesson) (correction : PaymentCorrectionCase) (row : RecoveryRecord)
  | checkRefundFunding (row : RefundFundingCheck) (decisions : DecisionRecords)
  | notifyShortage (row : ShortageFiling) (decisions : DecisionRecords)
  | fileCorrectedPayment (row : CorrectedPayout)

def Event.atTime : Event → Moment
  | .publishContacts _ _ record => record.publishedAt
  | .receive entry => entry.concern.receivedAt
  | .acknowledge _ ack => ack.acknowledgmentAt
  | .requestAppointment _ trigger => trigger.atTime
  | .appoint appointment => appointment.appointedAt
  | .decideInitial _ _ finding => finding.decidedAt
  | .retainOriginal _ record => record.outcome.decidedAt
  | .decideReview _ _ finding => finding.decidedAt
  | .reply _ record => record.response.sentAt
  | .escalateReply _ _ assignment => assignment.assignedAt
  | .escalateHeldReview _ _ _ assignment | .escalateRequestedReview _ _ _ assignment =>
      assignment.assignedAt
  | .escalatePayment row => row.assignment.assignedAt
  | .recordCorrection _ correction => correction.record.recordedAt
  | .fileRecovery _ _ row => row.actualReturn.returnedAt
  | .checkRefundFunding row _ => row.funds.checkedAt
  | .notifyShortage row _ => row.notice.sentAt
  | .fileCorrectedPayment row => row.recordedAt

/-- A reply is recorded with its actual time. Timeliness uses the separate `Intake.replyOnTime`
    check, and escalation records the action taken without changing the original deadline. -/
inductive Step (evidence : Evidence) (start : StartEvidence) (holds : HoldHistory) :
    History → Event → History → Prop where
  | publishContacts {history} (lesson : Lesson) (terms : ReviewTerms) (row : PublishedContacts)
      (sameLesson : row.lesson = lesson.id)
      (published : concernContactsPublished lesson terms row.publication)
      (fresh : row ∉ history.publications) :
      Step evidence start holds history (.publishContacts lesson terms row)
        { history with publications := history.publications ++ [row] }

  | receive {history} (entry : Intake)
      (published : entry.publication ∈ history.publications)
      (publicationMatches : entry.publication.lesson = entry.lesson.id ∧
        entry.publication.publishedAt.by entry.concern.receivedAt)
      (terms : entry.termsApply evidence start)
      (admitted : concernAccepted entry.lesson entry.terms
        (history.concernFacts evidence.concernFacts) entry.publication.publication entry.concern)
      (fresh : ∀ old ∈ history.intakes, ¬old.concern.matter.sameCase entry.concern.matter) :
      Step evidence start holds history (.receive entry)
        { history with intakes := history.intakes ++ [entry] }

  | acknowledge {history entry} (ack : ConcernAcknowledgment)
      (received : entry ∈ history.intakes)
      (correct : concernAcknowledgmentConforms
        { entry.terms with finalReplyDeadline := ack.finalReplyDeadline }
        entry.concern ack.handler ack)
      (afterLog : ack.loggedAt.by ack.acknowledgmentAt)
      (deadline : entry.ackDeadlineMatches evidence start ack)
      (fresh : ∀ old ∈ history.acknowledgments, old.1 ≠ entry.concern) :
      Step evidence start holds history (.acknowledge entry ack)
        { history with acknowledgments := history.acknowledgments ++ [(entry.concern, ack)] }

  | requestAppointment {history entry} (trigger : ConcernAppointmentTrigger)
      (received : entry ∈ history.intakes)
      (applies : trigger.applies entry.concern trigger.atTime)
      (fresh : trigger ∉ history.appointmentTriggers) :
      Step evidence start holds history (.requestAppointment entry trigger)
        { history with appointmentTriggers := history.appointmentTriggers ++ [trigger] }

  | appoint {history} (appointment : ReviewAppointment)
      (authorised : appointment.applies (history.authorities evidence.authority)
        appointment.matter appointment.handler appointment.appointedAt)
      (fresh : appointment ∉ history.appointments) :
      Step evidence start holds history (.appoint appointment)
        { history with appointments := history.appointments ++ [appointment] }

  | decideInitial {history} (form : PartOne) (terms : ReviewTerms) (finding : InitialFinding)
      (formApplies : formRetainedAt start form form.lesson finding.decidedAt ∧
        finding.matter.lesson = form.lesson.id ∧ Operations.ReviewTerms.matchesForm terms form)
      (recordedSetters : holds.temporarySettersRecorded (history.authorities evidence.authority)
        evidence.holds finding.matter finding.decidedAt)
      (authorised : initialFindingRecordedConforms (history.authorities evidence.authority)
        terms form.contacts.substitute history.appointments
        (finding :: history.initialFindings) finding)
      (fresh : finding ∉ history.initialFindings) :
      Step evidence start holds history (.decideInitial form terms finding)
        { history with initialFindings := history.initialFindings ++ [finding] }

  | retainOriginal {history} (lesson : Lesson) (row : OriginalRecord)
      (sameLesson : row.outcome.matter.lesson = lesson.id)
      (original : evidence.originalOutcome row.outcome)
      (amount : ∀ part ∈ row.payment, part.ref.lesson = lesson.id ∧ 0 ≤ part.amount ∧
        evidence.recordedAmount row.outcome.matter row.outcome.outcome part)
      (fresh : row ∉ history.originals) :
      Step evidence start holds history (.retainOriginal lesson row)
        { history with originals := history.originals ++ [row] }

  | decideReview {history} (lesson : Lesson) (form : Option PartOne) (finding : ReviewFinding)
      (sameLesson : finding.matter.lesson = lesson.id)
      (originalMatter : history.matterRetained finding.matter finding.decidedAt)
      (formApplies : ∀ f ∈ form,
        formRetainedAt start f lesson finding.decidedAt ∧
        ∀ entry ∈ history.intakes, entry.concern.matter.sameCase finding.matter →
          ∀ governing ∈ entry.form, f = governing)
      (recordedSetters : holds.temporarySettersRecorded (history.authorities evidence.authority)
        evidence.holds finding.matter finding.decidedAt)
      (authorised : reviewFindingRecordedConforms (history.authorities evidence.authority)
        (form.map (·.contacts.reviewer)) history.appointments history.initialFindings
        (finding :: history.reviewFindings) finding)
      (appointmentForRequest : ∀ entry ∈ history.intakes,
        entry.concern.matter.sameCase finding.matter →
        (∃ trigger ∈ history.appointmentTriggers,
          trigger.applies entry.concern finding.decidedAt) →
        ∃ appointment ∈ history.appointments,
          entry.concern.receivedAt.by appointment.appointedAt ∧
          appointment.applies (history.authorities evidence.authority) finding.matter
            finding.reviewer finding.decidedAt)
      (fresh : finding ∉ history.reviewFindings) :
      Step evidence start holds history (.decideReview lesson form finding)
        { history with reviewFindings := history.reviewFindings ++ [finding] }

  | reply {history entry} (record : ConcernHandlingRecord)
      (received : entry ∈ history.intakes)
      (sameConcern : record.concern = entry.concern)
      (acknowledged : (entry.concern, record.acknowledgment) ∈ history.acknowledgments)
      (afterAcknowledgment : record.acknowledgment.acknowledgmentAt.by record.response.sentAt)
      (handled : record.recorded entry.lesson
        { entry.terms with finalReplyDeadline := record.acknowledgment.finalReplyDeadline }
        (history.concernFacts evidence.concernFacts) entry.publication.publication
        (history.authorities evidence.authority) history.appointments evidence.verifiedFactCheck
        entry.namedReviewer history.initialFindings history.reviewFindings)
      (fresh : ∀ prior ∈ history.replies, prior.concern = entry.concern →
        prior.response ≠ record.response) :
      Step evidence start holds history (.reply entry record)
        { history with replies := history.replies ++ [record] }

  | escalateReply {history entry} (notice : EscalationNotice) (assignment : EscalationAssignment)
      (received : entry ∈ history.intakes)
      (afterReceipt : entry.concern.receivedAt.by notice.takenOverAt)
      (overdue : (∃ cutoff, entry.replyCutoff evidence start notice.takenOverAt cutoff ∧
        cutoff.hasPassed notice.takenOverAt) ∨
        ∃ law ∈ evidence.replyLegalDeadline entry.concern, law.before notice.takenOverAt)
      (unanswered : ¬∃ reply ∈ history.replies, reply.concern = entry.concern ∧
        reply.response.sentAt.by notice.takenOverAt)
      (details : escalationDetailsConform entry.terms entry.concern.matter
        (.reply entry.concern.matter.id) notice)
      (assigned : assignment.matches notice)
      (fresh : (entry.concern, notice, assignment) ∉ history.escalations) :
      Step evidence start holds history (.escalateReply entry notice assignment)
        { history with escalations := history.escalations ++ [(entry.concern, notice, assignment)] }

  | escalateHeldReview {history} (form : PartOne) (hold : FormalHold)
      (notice : EscalationNotice) (assignment : EscalationAssignment)
      (retained : formRetainedAt start form form.lesson hold.decidedAt)
      (sameCaseForm : ∀ entry ∈ history.intakes, entry.concern.matter.sameCase hold.matter →
        entry.concern.receivedAt.by notice.takenOverAt → ∀ governing ∈ entry.form, governing = form)
      (checked : LessonReviewEscalationRecorded form (history.authorities evidence.authority)
        evidence.holds holds hold history.reviewFindings history.appointments history.initialFindings
        evidence.governingReviewForm (evidence.reviewLegalDeadline hold.matter) notice assignment)
      (fresh : (hold.matter, notice, assignment) ∉ history.reviewEscalations) :
      Step evidence start holds history (.escalateHeldReview form hold notice assignment)
        { history with reviewEscalations :=
            history.reviewEscalations ++ [(hold.matter, notice, assignment)] }

  | escalateRequestedReview {history entry} (requestedAt : Moment) (notice : EscalationNotice)
      (assignment : EscalationAssignment)
      (received : entry ∈ history.intakes)
      (requested : ∃ trigger ∈ history.appointmentTriggers, trigger.atTime = requestedAt ∧
        trigger.applies entry.concern notice.takenOverAt ∧
        ∃ party, trigger.cause = .partyRequestedReview party)
      (overdue : escalationConforms entry.terms entry.concern.matter
        (.reviewRequest entry.concern.matter.id)
        (deadlineUnderEarlierLaw entry.terms.finalReviewDeadline
          (evidence.reviewLegalDeadline entry.concern.matter)) none notice)
      (unresolved : ¬∃ finding ∈ history.reviewFindings,
        finding.matter.sameCase entry.concern.matter ∧
        requestedAt.by finding.decidedAt ∧ finding.decidedAt.by notice.takenOverAt)
      (assigned : assignment.matches notice)
      (independent : let matter := entry.concern.matter
        let authority := history.authorities evidence.authority
        independentReviewer authority matter assignment.assignedTo assignment.assignedAt ∧
        didNotMakeOriginalFinding history.initialFindings matter assignment.assignedTo
          assignment.assignedAt ∧
        holds.notTemporarySetter authority evidence.holds matter assignment.assignedTo
          assignment.assignedAt)
      (fresh : (entry.concern.matter, notice, assignment) ∉ history.reviewEscalations) :
      Step evidence start holds history (.escalateRequestedReview entry requestedAt notice assignment)
        { history with reviewEscalations :=
            history.reviewEscalations ++ [(entry.concern.matter, notice, assignment)] }

  | escalatePayment {history} (row : PaymentEscalation)
      (checked : row.conforms history evidence start holds)
      (fresh : ∀ prior ∈ history.paymentEscalations,
        prior.notice ≠ row.notice ∨ prior.assignment ≠ row.assignment) :
      Step evidence start holds history (.escalatePayment row)
        { history with paymentEscalations := history.paymentEscalations ++ [row] }

  | recordNonmonetary {history} (lesson : Lesson) (old : OriginalRecord)
      (finding : ReviewFinding) (correction : SettlementCorrection)
      (original : old ∈ history.originals)
      (reviewed : finding ∈ history.reviewFindings)
      (nonmonetary : ¬∃ part, evidence.recordedAmount finding.matter finding.outcome part)
      (linked : correctionAfterReviewConforms lesson (history.authorities evidence.authority)
        history.appointments [old.outcome] finding correction)
      (fresh : .nonmonetary old finding correction ∉ history.corrections) :
      Step evidence start holds history
        (.recordCorrection lesson (.nonmonetary old finding correction))
        { history with corrections := history.corrections ++ [.nonmonetary old finding correction] }

  | recordMonetary {history} (lesson : Lesson) (old : OriginalRecord)
      (payment : PaymentCorrectionCase)
      (original : old ∈ history.originals)
      (reviewed : payment.finding ∈ history.reviewFindings)
      (correctAmount : evidence.recordedAmount payment.finding.matter payment.finding.outcome
        payment.money.corrected)
      (linked : ∃ prior ∈ history.priorMaterialsPartsFor old payment,
        payment.recorded lesson (history.authorities evidence.authority)
          history.appointments [old.outcome] (amountsFor old payment) holds.payments prior)
      (fresh : payment ∉ history.paymentCorrections) :
      Step evidence start holds history (.recordCorrection lesson (.monetary old payment))
        { history with
          corrections := history.corrections ++ [.monetary old payment]
          refundAssessments := history.refundAssessments ++
            ((evidence.reviewedFaultRefund payment).toList.map (payment, ·)) }

  | fileRecovery {history} (lesson : Lesson) (correction : PaymentCorrectionCase)
      (row : RecoveryRecord)
      (adopted : correction ∈ history.paymentCorrections)
      (sameLesson : correction.correction.lesson = lesson.id)
      (recovered : recoveryConforms holds.payments correction evidence.recoveryUnderOriginalTerms
        evidence.mayApproveRecovery row)
      (fresh : ∀ prior ∈ history.recoveries,
        prior.2.actualReturn.id ≠ row.actualReturn.id ∧ prior.2.decision ≠ row.decision) :
      Step evidence start holds history (.fileRecovery lesson correction row)
        { history with recoveries := history.recoveries ++ [(correction, row)] }

  | checkRefundFunding {history} (row : RefundFundingCheck) (decisions : DecisionRecords)
      (adopted : row.correction ∈ history.paymentCorrections)
      (form : formRetainedAt start row.form row.form.lesson row.funds.checkedAt)
      (checked : ∃ scope ∈ history.correctedScopeForFormAt evidence row.form row.correction
          row.funds.checkedAt,
        ReviewedRefundFundingChecked row.form row.correction
          (history.decisionRecords evidence.authority decisions) history.originalOutcomes
          (history.monetaryOutcome row.correction) holds.payments start.ledger row.funds
          (row.coversRemaining = true) scope) :
    Step evidence start holds history (.checkRefundFunding row decisions)
      { history with refundFundingChecks := history.refundFundingChecks ++ [row] }

  | notifyShortage {history} (row : ShortageFiling) (decisions : DecisionRecords)
      (adopted : row.correction ∈ history.paymentCorrections)
      (form : formRetainedAt start row.form row.form.lesson row.funds.checkedAt)
      (sent : ∃ scope ∈ history.correctedScopeForFormAt evidence row.form row.correction
          row.funds.checkedAt,
        CorrectionShortfallRecorded row.form row.correction row.funds
          (history.decisionRecords evidence.authority decisions) history.originalOutcomes
          (history.monetaryOutcome row.correction) holds.payments start.ledger row.notice
          (fun place person ↦ start.creditRecords.ownsAccount person place.account) scope) :
    Step evidence start holds history (.notifyShortage row decisions)
      { history with shortageFilings := history.shortageFilings ++ [row] }

  | fileCorrectedPayment {history} (row : CorrectedPayout)
      (filed : row.conforms history evidence start holds)
      (fresh : ∀ prior ∈ history.correctedPayouts,
        prior.payment.paid.id ≠ row.payment.paid.id) :
      Step evidence start holds history (.fileCorrectedPayment row)
        { history with correctedPayouts := history.correctedPayouts ++ [row] }

end SourceV14.Workflow.Review
