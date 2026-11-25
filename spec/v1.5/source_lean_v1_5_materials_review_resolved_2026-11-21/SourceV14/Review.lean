import SourceV14.Settlement

/-!
Direct translation of the locked v1.5 English rules §§6.1–6.6 and the review and
post-lift records on the companion confirmation form.
-/

namespace SourceV14

abbrev ConcernId := Nat
abbrev ObligationId := Nat
abbrev HoldId := Nat
abbrev PaymentId := Nat
abbrev ApprovalId := Nat
abbrev EvidenceRef := Nat

/-- What a payment or settlement portion concerns. -/
inductive PaymentPurpose where
  | customerFee (place : PlaceId)
  | lessonRefund (place : PlaceId)
  | tutorPay (tutor : ActorId)
  | materialsShare (material : Nat) (holder : ActorId)
  | materialsShortfall (material : Nat) (holder : ActorId) (claim : String)
  | other
  deriving DecidableEq, Repr

/-- A distinct portion of an obligation, so a hold on one portion does not block others. -/
structure PaymentPartRef where
  lesson : LessonId
  obligation : ObligationId
  portion : Nat
  purpose : PaymentPurpose := .other
  deriving DecidableEq, Repr

def PaymentPartRef.sameObligation (a b : PaymentPartRef) : Bool :=
  a.lesson == b.lesson && a.obligation == b.obligation && a.purpose == b.purpose

def PaymentPurpose.isMaterialsShare : PaymentPurpose → Bool
  | .materialsShare .. | .materialsShortfall .. => true
  | _ => false

/-- Candidate references for the same claim. A creditor change still needs the exact
retained original and reviewed parts. Ordinary payment references keep the holder. -/
def PaymentPartRef.sameCorrectionClaim (a b : PaymentPartRef) : Bool :=
  a.lesson == b.lesson && a.obligation == b.obligation &&
    match a.purpose, b.purpose with
    | .materialsShare material _, .materialsShare other _ => material == other
    | .materialsShortfall material _ claim, .materialsShortfall other _ otherClaim =>
      material == other && claim == otherClaim
    | purpose, otherPurpose => purpose == otherPurpose

structure ReviewMatter where
  id : ConcernId
  lesson : LessonId
  parties : List ActorId
  deriving DecidableEq, Repr

def ReviewMatter.sameCase (a b : ReviewMatter) : Prop :=
  a.lesson = b.lesson ∧ a.id = b.id

/-- Dates and periods are compared against the actual triggering event. -/
inductive DeadlineTerm where
  | date (deadline : Moment)
  | period (seconds : Nat) (expiry : ClockCutoff)
  deriving DecidableEq, Repr

def DeadlineTerm.cutoff : DeadlineTerm → ClockCutoff
  | .date deadline => .exact deadline
  | .period _ expiry => expiry

/-- Section 6.1 and confirmation form Part 1. -/
structure ReviewTerms where
  coordinator : ActorId
  alternativeContact : ActorId
  leadAcademicTutor : ActorId
  finalReplyDeadline : ClockCutoff
  finalReviewDeadline : Moment
  temporaryHoldExpiry : Moment
  handoffDeadline : Moment
  escalationContact : ActorId
  deriving DecidableEq, Repr

/-- Authorisations and interests in the particular decision at the stated time. -/
structure ReviewAuthorities where
  corePartner : ActorId → Moment → Prop
  initialFinding : ReviewMatter → ActorId → Moment → Prop
  reviewer : ReviewMatter → ActorId → Moment → Prop
  approvesPayment : PaymentPartRef → ActorId → Moment → Prop
  interest : ReviewMatter → ActorId → Moment → DirectInterest
  originalDecisionMaker : ReviewMatter → Option ActorId
  actualOriginalDecisions : List (ReviewMatter × ActorId × Moment) := []
  actualTemporaryHoldSetters : List (ReviewMatter × ActorId × Moment) := []
  originalSettlementProposers : ReviewMatter → List ActorId
  originalSettlementApprovers : ReviewMatter → List ActorId

def ReviewAuthorities.disinterested (a : ReviewAuthorities) (m : ReviewMatter)
    (actor : ActorId) (atTime : Moment) : Prop :=
  ¬(a.interest m actor atTime).affected

/-- The alternative contact can record a concern and set aside money for that case. -/
def ReviewAuthorities.mayDecideDispute (a : ReviewAuthorities) (m : ReviewMatter)
    (actor : ActorId) (atTime : Moment) : Prop :=
  ∀ (caseMatter : ReviewMatter) (contact : ActorId) (effectiveAt : Moment),
    (caseMatter, contact, effectiveAt) ∈ a.actualTemporaryHoldSetters →
    caseMatter.sameCase m → effectiveAt.by atTime → actor ≠ contact

structure ReviewAppointment where
  matter : ReviewMatter
  corePartner : ActorId
  handler : ActorId
  appointedAt : Moment
  deriving DecidableEq, Repr

def ReviewAppointment.applies (a : ReviewAuthorities) (m : ReviewMatter)
    (handler : ActorId) (time : Moment) (p : ReviewAppointment) : Prop :=
  p.matter = m ∧ p.handler = handler ∧ p.appointedAt.by time ∧
    a.corePartner p.corePartner p.appointedAt ∧ a.disinterested m handler time

structure RecusalRecord where
  disclosedTo : List ActorId
  tookDecision : Bool
  replacement : ReviewAppointment
  deriving DecidableEq, Repr

/-- Sections 1.2 and 6.1 require disclosure, recusal and a disinterested appointment. -/
def recusalConforms (a : ReviewAuthorities) (m : ReviewMatter) (handler : ActorId)
    (time : Moment) (record : RecusalRecord) : Prop :=
  (a.interest m handler time).affected →
    (∀ party ∈ m.parties, party ∈ record.disclosedTo) ∧ record.tookDecision = false ∧
    record.replacement.handler ≠ handler ∧
    record.replacement.applies a m record.replacement.handler time

inductive CustomerConcern where | fee | refund | compensation
  deriving DecidableEq, Repr

inductive StudentConcern where | attendance | service | remedy | paymentOwed
  deriving DecidableEq, Repr

inductive ConcernSubject where
  | customer (place : Place) (issue : CustomerConcern)
  | student (place : Place) (issue : StudentConcern)
  | tutor
  | share
  | materialOmission (materials : List Nat) (basis : String)
  deriving DecidableEq, Repr

structure Concern where
  matter : ReviewMatter
  raisedBy : ActorId
  subject : ConcernSubject
  receiver : ActorId
  receivedAt : Moment
  deriving DecidableEq, Repr

inductive ConcernAppointmentCause where
  | decisionNeeded
  | partyRequestedReview (party : ActorId)
  deriving DecidableEq, Repr

structure ConcernAppointmentTrigger where
  matter : ReviewMatter
  cause : ConcernAppointmentCause
  atTime : Moment
  evidence : EvidenceRef
  deriving DecidableEq, Repr

def ConcernAppointmentTrigger.applies (trigger : ConcernAppointmentTrigger) (concern : Concern)
    (through : Moment) : Prop :=
  trigger.matter.sameCase concern.matter ∧ concern.receivedAt.by trigger.atTime ∧
    trigger.atTime.by through ∧
    match trigger.cause with
    | .decisionNeeded => True
    | .partyRequestedReview party => party = concern.raisedBy ∨ party ∈ concern.matter.parties

/-- Open facts relevant to standing and access to the two complaint channels. -/
structure ConcernFacts where
  effectivePlace : Place → Moment → Prop
  tutorAffected : ReviewMatter → ActorId → Prop
  relevantShareClaimantAffected : ReviewMatter → ActorId → Prop
  believesUseOmitted : ReviewMatter → ActorId → Prop
  relevantContributor : ReviewMatter → ActorId → Prop
  coordinatorUnreachable : ReviewMatter → Moment → Prop
  coordinatorPersonallyInterested : ReviewMatter → Moment → Prop
  complaintAboutCoordinator : ReviewMatter → Prop
  appointmentTriggers : List ConcernAppointmentTrigger := []

def concernStanding (facts : ConcernFacts) (c : Concern) : Prop :=
  match c.subject with
  | .customer place _ =>
      place.lesson = c.matter.lesson ∧ facts.effectivePlace place c.receivedAt ∧
        (c.raisedBy = place.customer ∨ c.raisedBy = place.payer)
  | .student place _ => place.lesson = c.matter.lesson ∧
      facts.effectivePlace place c.receivedAt ∧ c.raisedBy = place.student
  | .tutor => facts.tutorAffected c.matter c.raisedBy
  | .share => facts.relevantShareClaimantAffected c.matter c.raisedBy
  | .materialOmission materials basis =>
      materials ≠ [] ∧ basis ≠ "" ∧ facts.believesUseOmitted c.matter c.raisedBy

def concernChannel (terms : ReviewTerms) (facts : ConcernFacts) (c : Concern) : Prop :=
  c.receiver = terms.coordinator ∨
    (c.receiver = terms.alternativeContact ∧
      (facts.coordinatorUnreachable c.matter c.receivedAt ∨
        facts.coordinatorPersonallyInterested c.matter c.receivedAt ∨
        facts.complaintAboutCoordinator c.matter ∨
        facts.relevantContributor c.matter c.raisedBy))

inductive ContactPublicationSource where | policy | materialsTerms
  deriving DecidableEq, Repr

structure ConcernContactPublication where
  source : ContactPublicationSource
  publishedBy : ActorId
  coordinator : ActorId
  usualContact : String
  alternativeContact : ActorId
  alternativeDetails : String
  deriving DecidableEq, Repr

def concernContactsPublished (l : Lesson) (terms : ReviewTerms)
    (publication : ConcernContactPublication) : Prop :=
  publication.publishedBy = l.provider ∧ publication.coordinator = terms.coordinator ∧
    terms.coordinator = l.coordinator ∧
    publication.alternativeContact = terms.alternativeContact ∧
    publication.usualContact ≠ "" ∧ publication.alternativeDetails ≠ ""

/-- An intake under the published contacts does not require the contributor to hold the form. -/
def concernAccepted (l : Lesson) (terms : ReviewTerms) (facts : ConcernFacts)
    (publication : ConcernContactPublication) (c : Concern) : Prop :=
  c.matter.lesson = l.id ∧ concernContactsPublished l terms publication ∧
    concernStanding facts c ∧ concernChannel terms facts c

structure ConcernAcknowledgment where
  concern : ConcernId
  loggedBy : ActorId
  acknowledgedBy : ActorId
  acknowledgedTo : ActorId
  loggedAt : Moment
  acknowledgmentAt : Moment
  handler : ActorId
  finalReplyDeadline : ClockCutoff
  escalationContact : ActorId
  deriving DecidableEq, Repr

def concernAcknowledgmentConforms (terms : ReviewTerms) (c : Concern) (handler : ActorId)
    (ack : ConcernAcknowledgment) : Prop :=
  ack.concern = c.matter.id ∧ ack.loggedBy = c.receiver ∧ ack.acknowledgedBy = c.receiver ∧
    ack.acknowledgedTo = c.raisedBy ∧ c.receivedAt.by ack.loggedAt ∧
    c.receivedAt.by ack.acknowledgmentAt ∧ ack.handler = handler ∧
    ack.finalReplyDeadline = terms.finalReplyDeadline ∧
    ack.escalationContact = terms.escalationContact

structure ConcernResponse where
  concern : ConcernId
  handler : ActorId
  checkedFacts : Bool
  outcome : String
  reasons : String
  sentAt : Moment
  sentTo : List ActorId
  deriving DecidableEq, Repr

def concernResponseRecorded (c : Concern) (handler : ActorId)
    (r : ConcernResponse) : Prop :=
  r.concern = c.matter.id ∧ r.handler = handler ∧ r.checkedFacts = true ∧
    r.outcome ≠ "" ∧ r.reasons ≠ "" ∧ c.receivedAt.by r.sentAt ∧
    (∀ party ∈ c.matter.parties, party ∈ r.sentTo)

def concernResponseConforms (terms : ReviewTerms) (c : Concern) (handler : ActorId)
    (r : ConcernResponse) : Prop :=
  concernResponseRecorded c handler r ∧ terms.finalReplyDeadline.metBy r.sentAt

structure ConcernHandlingNeeds where
  disputedDecision : Bool
  originalHandlerMustStepAside : Bool
  partyRequestsReview : Bool
  deriving DecidableEq, Repr

def concernAppointmentRequired (needs : ConcernHandlingNeeds) : Prop :=
  needs.disputedDecision = true ∨ needs.originalHandlerMustStepAside = true ∨
    needs.partyRequestsReview = true

def concernAppointmentRequiredFor (facts : ConcernFacts) (concern : Concern) (through : Moment)
    (needs : ConcernHandlingNeeds) : Prop :=
  concernAppointmentRequired needs ∨
    ∃ trigger ∈ facts.appointmentTriggers, trigger.applies concern through

def concernAppointmentConforms (a : ReviewAuthorities) (m : ReviewMatter)
    (needs : ConcernHandlingNeeds) (handler : ActorId) (time : Moment)
    (appointment : ReviewAppointment) : Prop :=
  concernAppointmentRequired needs → appointment.applies a m handler time

structure ConcernFactCheck where
  matter : ReviewMatter
  checkedBy : ActorId
  checkedAt : Moment
  evidence : EvidenceRef
  outcome : String
  reasons : String
  reviewOutcome : Option EvidenceRef := none
  deriving DecidableEq, Repr

structure ConcernHandlingRecord where
  concern : Concern
  initiallyAssigned : ActorId
  needs : ConcernHandlingNeeds
  acknowledgment : ConcernAcknowledgment
  check : ConcernFactCheck
  response : ConcernResponse

inductive DisputedFinding where | absenceReason | fault | otherDisputedFact
  deriving DecidableEq, Repr

inductive DecisionSupportTask where | checkEvidence | calculateAmounts | proposeOutcome
  deriving DecidableEq, Repr

structure DecisionSupportContribution where
  matter : ReviewMatter
  requestedBy : ActorId
  requestedAt : Moment
  agent : ActorId
  task : DecisionSupportTask
  evidence : EvidenceRef
  deliveredAt : Moment
  deriving DecidableEq, Repr

structure InitialFinding where
  matter : ReviewMatter
  issue : DisputedFinding
  decider : ActorId
  decidedAt : Moment
  recordedReasons : String
  decisionSupport : List DecisionSupportContribution := []
  deriving DecidableEq, Repr

/-- Optional evidence or advice used by the authorised decision-maker. -/
def decisionSupportConforms (finding : InitialFinding)
    (contribution : DecisionSupportContribution) : Prop :=
  contribution.matter.sameCase finding.matter ∧ contribution.requestedBy = finding.decider ∧
    contribution.agent ≠ finding.decider ∧ contribution.requestedAt.by contribution.deliveredAt ∧
    contribution.deliveredAt.by finding.decidedAt

def initialFindingConformsWithContacts (a : ReviewAuthorities) (terms : ReviewTerms)
    (namedSubstitute : Option ActorId) (appointments : List ReviewAppointment)
    (finding : InitialFinding) : Prop :=
  a.initialFinding finding.matter finding.decider finding.decidedAt ∧
    a.disinterested finding.matter finding.decider finding.decidedAt ∧
    finding.recordedReasons ≠ "" ∧
    (finding.decider = terms.leadAcademicTutor ∨
      ((a.interest finding.matter terms.leadAcademicTutor finding.decidedAt).affected ∧
        (namedSubstitute = some finding.decider ∨
          ∃ p ∈ appointments, p.applies a finding.matter finding.decider finding.decidedAt))) ∧
    a.mayDecideDispute finding.matter finding.decider finding.decidedAt ∧
    ∀ support ∈ finding.decisionSupport, decisionSupportConforms finding support

def initialFindingConforms (a : ReviewAuthorities) (terms : ReviewTerms)
    (appointments : List ReviewAppointment) (finding : InitialFinding) : Prop :=
  initialFindingConformsWithContacts a terms none appointments finding

def initialFindingRecordedConforms (a : ReviewAuthorities) (terms : ReviewTerms)
    (namedSubstitute : Option ActorId) (appointments : List ReviewAppointment)
    (actualFindings : List InitialFinding) (finding : InitialFinding) : Prop :=
  finding ∈ actualFindings ∧
    initialFindingConformsWithContacts a terms namedSubstitute appointments finding ∧
    (finding.decider ≠ terms.leadAcademicTutor →
      ∃ appointment ∈ appointments,
        appointment.applies a finding.matter finding.decider finding.decidedAt)

def independentReviewer (a : ReviewAuthorities) (m : ReviewMatter) (actor : ActorId)
    (time : Moment) : Prop :=
  a.reviewer m actor time ∧ a.disinterested m actor time ∧
    a.originalDecisionMaker m ≠ some actor ∧
    ∀ (oldMatter : ReviewMatter) (oldActor : ActorId) (oldTime : Moment),
      (oldMatter, oldActor, oldTime) ∈ a.actualOriginalDecisions →
      oldMatter.sameCase m → oldTime.by time → oldActor ≠ actor

structure ReviewFinding where
  matter : ReviewMatter
  reviewer : ActorId
  decidedAt : Moment
  reasons : String
  outcome : EvidenceRef
  correctionNeeded : Bool
  deriving DecidableEq, Repr

def reviewFindingConformsWithContacts (a : ReviewAuthorities) (namedReviewer : Option ActorId)
    (appointments : List ReviewAppointment) (r : ReviewFinding) : Prop :=
  independentReviewer a r.matter r.reviewer r.decidedAt ∧ r.reasons ≠ "" ∧
    (namedReviewer = some r.reviewer ∨
      ∃ appointed ∈ appointments, appointed.applies a r.matter r.reviewer r.decidedAt) ∧
    a.mayDecideDispute r.matter r.reviewer r.decidedAt

def reviewFindingConforms (a : ReviewAuthorities) (appointments : List ReviewAppointment)
    (r : ReviewFinding) : Prop :=
  reviewFindingConformsWithContacts a none appointments r

/-- Use the original actor for the stable case even if its parties have changed. -/
def didNotMakeOriginalFinding (initialFindings : List InitialFinding) (matter : ReviewMatter)
    (actor : ActorId) (atTime : Moment) : Prop :=
  ∀ original ∈ initialFindings, original.matter.sameCase matter →
    original.decidedAt.by atTime → original.decider ≠ actor

/-- A change in the case's listed parties does not change the identity of its original decider. -/
def reviewFindingRecordedConforms (a : ReviewAuthorities) (namedReviewer : Option ActorId)
    (appointments : List ReviewAppointment) (initialFindings : List InitialFinding)
    (reviewFindings : List ReviewFinding) (r : ReviewFinding) : Prop :=
  r ∈ reviewFindings ∧ reviewFindingConformsWithContacts a namedReviewer appointments r ∧
    didNotMakeOriginalFinding initialFindings r.matter r.reviewer r.decidedAt

/-- A factual reply can precede review. Reporting a review outcome uses its independent finding. -/
def ConcernHandlingRecord.reviewOutcomeConforms (record : ConcernHandlingRecord)
    (authority : ReviewAuthorities) (appointments : List ReviewAppointment)
    (namedReviewer : Option ActorId) (initialFindings : List InitialFinding)
    (reviewFindings : List ReviewFinding) : Prop :=
  match record.check.reviewOutcome with
  | none => True
  | some outcome =>
    ∃ finding, reviewFindingRecordedConforms authority namedReviewer appointments
      initialFindings reviewFindings finding ∧ finding.matter.sameCase record.concern.matter ∧
      finding.outcome = outcome ∧ finding.reviewer = record.check.checkedBy ∧
      record.check.checkedAt.by finding.decidedAt ∧ finding.decidedAt.by record.response.sentAt ∧
      finding.reasons = record.check.reasons

def ConcernHandlingRecord.recorded (record : ConcernHandlingRecord) (l : Lesson)
    (terms : ReviewTerms) (facts : ConcernFacts) (publication : ConcernContactPublication)
    (authority : ReviewAuthorities) (appointments : List ReviewAppointment)
    (verifiedCheck : ConcernFactCheck → Prop) (namedReviewer : Option ActorId)
    (initialFindings : List InitialFinding) (reviewFindings : List ReviewFinding) : Prop :=
  let c := record.concern
  let check := record.check
  let r := record.response
  concernAccepted l terms facts publication c ∧
    concernAcknowledgmentConforms terms c record.initiallyAssigned record.acknowledgment ∧
    record.acknowledgment.loggedAt.by record.acknowledgment.acknowledgmentAt ∧
    check.matter = c.matter ∧ check.checkedBy = r.handler ∧ c.receivedAt.by check.checkedAt ∧
    check.checkedAt.by r.sentAt ∧ verifiedCheck check ∧ r.outcome = check.outcome ∧
    r.reasons = check.reasons ∧ concernResponseRecorded c check.checkedBy r ∧
    ((check.checkedBy = record.initiallyAssigned ∧
      authority.disinterested c.matter check.checkedBy check.checkedAt ∧
      ¬concernAppointmentRequiredFor facts c r.sentAt record.needs) ∨
      ∃ p ∈ appointments, c.receivedAt.by p.appointedAt ∧
        p.applies authority c.matter check.checkedBy check.checkedAt) ∧
    record.reviewOutcomeConforms authority appointments namedReviewer initialFindings reviewFindings

def ConcernHandlingRecord.conforms (record : ConcernHandlingRecord) (l : Lesson)
    (terms : ReviewTerms) (facts : ConcernFacts) (publication : ConcernContactPublication)
    (authority : ReviewAuthorities) (appointments : List ReviewAppointment)
    (verifiedCheck : ConcernFactCheck → Prop) (namedReviewer : Option ActorId)
    (initialFindings : List InitialFinding) (reviewFindings : List ReviewFinding) : Prop :=
  record.recorded l terms facts publication authority appointments verifiedCheck
    namedReviewer initialFindings reviewFindings ∧ terms.finalReplyDeadline.metBy record.response.sentAt

inductive FaultEvidence where
  | noReply | refusalToConfirm | concernRaised
  | substantive (evidence : EvidenceRef)
  deriving DecidableEq, Repr

/-- Fault needs substantive evidence beyond the procedural events. -/
def sufficientKindOfEvidenceForFault (items : List FaultEvidence) : Prop :=
  ∃ evidence, FaultEvidence.substantive evidence ∈ items

/-- Someone who may receive an amount and the separately identified lesson refund account. -/
inductive PaymentRecipient where
  | person (person : ActorId) (agreedRecipient : Option ActorId)
  | lessonRefund (debitedAccount : AccountId)
  deriving DecidableEq, Repr

def PaymentRecipient.samePayee : PaymentRecipient → PaymentRecipient → Bool
  | .person a _, .person b _ => a == b
  | .lessonRefund a, .lessonRefund b => a == b
  | _, _ => false

inductive PaymentDestination where
  | person (person : ActorId)
  | account (account : AccountId)
  deriving DecidableEq, Repr

def PaymentRecipient.accepts : PaymentRecipient → PaymentDestination → Prop
  | PaymentRecipient.person owner agreed, PaymentDestination.person paid =>
      owner = paid ∨ agreed = some paid
  | PaymentRecipient.lessonRefund debited, PaymentDestination.account paid => debited = paid
  | _, _ => False

instance (r : PaymentRecipient) (d : PaymentDestination) : Decidable (r.accepts d) := by
  cases r <;> cases d <;> unfold PaymentRecipient.accepts <;> infer_instance

structure PaymentPart where
  ref : PaymentPartRef
  recipient : PaymentRecipient
  amount : Amount
  deriving DecidableEq, Repr

def PaymentPart.matchesMaterialsCreditor (part : PaymentPart) : Bool :=
  match part.ref.purpose with
  | .materialsShare _ holder | .materialsShortfall _ holder _ =>
    match part.recipient with
    | .person payee _ => payee == holder
    | .lessonRefund _ => false
  | _ => true

/-- The terms of the attempted or executed payment, shared by permissions and receipts. -/
structure PaymentInstruction where
  part : PaymentPartRef
  destination : PaymentDestination
  executor : ActorId
  amount : Amount
  atTime : Moment
  deriving DecidableEq, Repr

/-- An actual receipt in the ledger. Retention of its evidence is separately checkable. -/
structure PostedPayment where
  id : PaymentId
  instruction : PaymentInstruction
  evidence : Option EvidenceRef
  deriving DecidableEq, Repr

structure ReturnedPayment where
  id : Nat
  paidReceipt : PaymentId
  amount : Amount
  returnedAt : Moment
  evidence : EvidenceRef
  deriving DecidableEq, Repr

/-- The designee in force when this exact receipt was made. -/
structure AgreedRecipientReceipt where
  paid : PostedPayment
  payee : ActorId
  designee : ActorId
  agreedAt : Moment
  ceasedAt : Option Moment
  agreement : EvidenceRef
  deriving DecidableEq, Repr

structure PaymentHistory where
  posted : List PostedPayment
  returned : List ReturnedPayment
  agreedRecipientReceipts : List AgreedRecipientReceipt := []
  deriving DecidableEq, Repr

/-- A changed designee neither invalidates an earlier correct receipt nor cures a misdirection. -/
def PaymentHistory.recipientReceived (h : PaymentHistory) (recipient : PaymentRecipient)
    (paid : PostedPayment) : Prop :=
  match recipient with
  | .person payee _ => paid.instruction.destination = .person payee ∨
    h.agreedRecipientReceipts.any (fun row ↦ decide (row.paid = paid ∧ row.payee = payee ∧
      paid.instruction.destination = .person row.designee ∧ row.agreedAt.by paid.instruction.atTime ∧
      row.ceasedAt.all (fun limit ↦ decide (paid.instruction.atTime.before limit)) = true))
      = true
  | .lessonRefund account => paid.instruction.destination = .account account

instance (h : PaymentHistory) (recipient : PaymentRecipient) (paid : PostedPayment) :
    Decidable (h.recipientReceived recipient paid) := by
  cases recipient <;> unfold PaymentHistory.recipientReceived <;> infer_instance

/-- Each receipt and each actual return contributes once to the obligation. -/
def PaymentHistory.distinctReceipts (h : PaymentHistory) : Prop :=
  (h.posted.map PostedPayment.id).Nodup ∧ (h.returned.map ReturnedPayment.id).Nodup

def PaymentHistory.validReturns (h : PaymentHistory) : Prop :=
  (∀ r ∈ h.returned, 0 < r.amount ∧ ∃ paid ∈ h.posted,
    paid.id = r.paidReceipt ∧ paid.instruction.atTime.before r.returnedAt) ∧
  ∀ paid ∈ h.posted, sumAmounts (h.returned.filter (fun r ↦ r.paidReceipt == paid.id))
    ReturnedPayment.amount ≤ paid.instruction.amount

def PostedPayment.retainedAmountBefore (p : PostedPayment) (returned : List ReturnedPayment)
    (time : Moment) : Amount :=
  let returnedAmount := sumAmountsWhere returned (fun r ↦
    decide (r.paidReceipt = p.id ∧ p.instruction.atTime.before r.returnedAt ∧
      r.returnedAt.before time ∧ 0 < r.amount)) ReturnedPayment.amount
  max 0 (p.instruction.amount - returnedAmount)

def PaymentHistory.receivedForPartBefore (h : PaymentHistory) (part : PaymentPartRef)
    (recipient : PaymentRecipient) (time : Moment) : Amount :=
  sumAmountsWhere h.posted (fun p ↦ decide (p.instruction.part = part ∧
    h.recipientReceived recipient p ∧ p.instruction.atTime.before time))
    (fun p ↦ p.retainedAmountBefore h.returned time)

def PaymentHistory.receivedForObligationBefore (h : PaymentHistory) (lesson : LessonId)
    (obligation : ObligationId) (recipient : PaymentRecipient) (time : Moment)
    (purpose : Option PaymentPurpose := none) : Amount :=
  sumAmountsWhere h.posted (fun p ↦ decide (p.instruction.part.lesson = lesson ∧
    p.instruction.part.obligation = obligation ∧
    (purpose.isNone = true ∨ purpose = some p.instruction.part.purpose) ∧
    h.recipientReceived recipient p ∧
    p.instruction.atTime.before time))
    (fun p ↦ p.retainedAmountBefore h.returned time)

/-- Actual retained receipts for an established payment purpose, across its portions. -/
def PaymentHistory.receivedForPurposeBefore (history : PaymentHistory) (lesson : LessonId)
    (purpose : PaymentPurpose) (recipient : PaymentRecipient)
    (time : Moment) : Amount :=
  sumAmountsWhere history.posted (fun p ↦ decide
    (p.instruction.part.lesson = lesson ∧ p.instruction.part.purpose = purpose ∧
      history.recipientReceived recipient p ∧ p.instruction.atTime.before time))
    (fun p ↦ p.retainedAmountBefore history.returned time)

def PaymentHistory.remainingPurposeBefore (history : PaymentHistory) (lesson : LessonId)
    (purpose : PaymentPurpose) (recipient : PaymentRecipient) (amount : Amount)
    (time : Moment) : Amount :=
  max 0 (amount - history.receivedForPurposeBefore lesson purpose recipient time)

def PaymentHistory.remainingBefore (h : PaymentHistory) (part : PaymentPart) (time : Moment) :
    Amount :=
  max 0 (part.amount - h.receivedForPartBefore part.ref part.recipient time)

/-- Credit belongs to the cutoff, including its exact observed order within the clock tick. -/
def PaymentHistory.fullyRetainedBy (h : PaymentHistory) (part : PaymentPart)
    (cutoff : ClockCutoff) : Prop :=
  h.distinctReceipts ∧ h.validReturns ∧
    cutoff.forEveryOrder (fun deadline ↦
      h.remainingBefore part { deadline with order := deadline.order + 1 } = 0)

/-- Section 6.3 calculates the unpaid amount separately for the payee and the obligation. -/
def PaymentHistory.remainingObligationBefore (h : PaymentHistory) (lesson : LessonId)
    (obligation : ObligationId) (recipient : PaymentRecipient) (correctAmount : Amount)
    (time : Moment) (purpose : Option PaymentPurpose := none) : Amount :=
  max 0 (correctAmount - h.receivedForObligationBefore lesson obligation recipient time purpose)

def PaymentHistory.validOutstandingPayment (h : PaymentHistory) (part : PaymentPart)
    (p : PaymentInstruction) : Prop :=
  p.part = part.ref ∧ part.recipient.accepts p.destination ∧
    0 < p.amount ∧ p.amount ≤ h.remainingBefore part p.atTime ∧
    h.distinctReceipts ∧ h.validReturns

def PaymentHistory.actualPaymentWithEvidence (h : PaymentHistory) (p : PostedPayment) : Prop :=
  p ∈ h.posted ∧ p.evidence.isSome = true

structure SettlementCorrection where
  lesson : LessonId
  originalOutcome : EvidenceRef
  correction : EvidenceRef
  recordedBy : ActorId
  recordedAt : Moment
  notified : List ActorId
  deriving DecidableEq, Repr

structure RecordedSettlementOutcome where
  matter : ReviewMatter
  outcome : EvidenceRef
  decidedBy : ActorId
  decidedAt : Moment
  deriving DecidableEq, Repr

def correctionRecordConforms (l : Lesson) (original : RecordedSettlementOutcome)
    (finding : ReviewFinding)
    (correction : SettlementCorrection) : Prop :=
  correction.lesson = l.id ∧ correction.lesson = finding.matter.lesson ∧
    original.matter.sameCase finding.matter ∧ original.decidedAt.before finding.decidedAt ∧
    finding.reviewer ≠ original.decidedBy ∧
    correction.originalOutcome = original.outcome ∧ correction.recordedBy = l.coordinator ∧
    finding.decidedAt.by correction.recordedAt ∧ correction.correction = finding.outcome ∧
    correction.correction ≠ correction.originalOutcome ∧
    (∀ party ∈ original.matter.parties ++ finding.matter.parties, party ∈ correction.notified)

def correctionAfterReviewConforms (l : Lesson) (a : ReviewAuthorities)
    (appointments : List ReviewAppointment) (originalOutcomes : List RecordedSettlementOutcome)
    (finding : ReviewFinding)
    (correction : SettlementCorrection) : Prop :=
  reviewFindingConforms a appointments finding ∧ finding.correctionNeeded = true ∧
    ∃ original ∈ originalOutcomes, correctionRecordConforms l original finding correction

structure MonetaryCorrection where
  corrected : PaymentPart
  reviewedAt : Moment
  actualReceipts : List PostedPayment
  deriving DecidableEq, Repr

def MonetaryCorrection.matchesReceipt (c : MonetaryCorrection) (p : PostedPayment)
    (prior : List PaymentPartRef := []) : Prop :=
  p.instruction.part.lesson = c.corrected.ref.lesson ∧
    p.instruction.part.obligation = c.corrected.ref.obligation ∧
    (if prior.contains p.instruction.part then True
      else p.instruction.part.purpose = c.corrected.ref.purpose) ∧
    p.instruction.atTime.by c.reviewedAt

/-- The receipts recorded with the correction are still present in the payment ledger. -/
def correctionActualPaymentsRetained (h : PaymentHistory) (c : MonetaryCorrection)
    (prior : List PaymentPartRef := []) : Prop :=
  h.distinctReceipts ∧ h.validReturns ∧ (c.actualReceipts.map PostedPayment.id).Nodup ∧
    ∀ p ∈ c.actualReceipts, p ∈ h.posted ∧ c.matchesReceipt p prior

def correctionActualPaymentsRecorded (h : PaymentHistory) (c : MonetaryCorrection)
    (prior : List PaymentPartRef := []) : Prop :=
  correctionActualPaymentsRetained h c prior ∧
    ∀ p ∈ h.posted, c.matchesReceipt p prior → p ∈ c.actualReceipts

/-- The reviewed amount belongs to the original liability and to the adopted outcome. -/
structure PaymentCorrectionCase where
  originalPart : PaymentPart
  finding : ReviewFinding
  correction : SettlementCorrection
  money : MonetaryCorrection
  deriving DecidableEq, Repr

def PaymentCorrectionCase.changesMaterialsCreditor (c : PaymentCorrectionCase) : Bool :=
  c.originalPart.ref.purpose.isMaterialsShare &&
    c.originalPart.ref.purpose != c.money.corrected.ref.purpose

def PaymentCorrectionCase.priorMaterialsRefs (c : PaymentCorrectionCase)
    (prior : List PaymentPart) : List PaymentPartRef :=
  if c.money.corrected.ref.purpose.isMaterialsShare then (c.originalPart :: prior).map (·.ref)
  else []

def PaymentCorrectionCase.outcomeConforms (c : PaymentCorrectionCase) (l : Lesson)
    (a : ReviewAuthorities) (appointments : List ReviewAppointment)
    (outcomes : List RecordedSettlementOutcome) (monetaryOutcome : EvidenceRef → Option PaymentPart) :
    Prop :=
  correctionAfterReviewConforms l a appointments outcomes c.finding c.correction ∧
    monetaryOutcome c.correction.originalOutcome = some c.originalPart ∧
    monetaryOutcome c.finding.outcome = some c.money.corrected ∧
    c.money.reviewedAt = c.finding.decidedAt ∧ c.money.corrected.ref.lesson = l.id ∧
    c.originalPart.ref.sameCorrectionClaim c.money.corrected.ref = true ∧
    c.originalPart.matchesMaterialsCreditor = true ∧
    c.money.corrected.matchesMaterialsCreditor = true ∧
    0 ≤ c.money.corrected.amount

def PaymentCorrectionCase.recorded (c : PaymentCorrectionCase) (l : Lesson)
    (a : ReviewAuthorities) (appointments : List ReviewAppointment)
    (outcomes : List RecordedSettlementOutcome) (monetaryOutcome : EvidenceRef → Option PaymentPart)
    (history : PaymentHistory) (prior : List PaymentPart := []) : Prop :=
  c.outcomeConforms l a appointments outcomes monetaryOutcome ∧
    correctionActualPaymentsRecorded history c.money (c.priorMaterialsRefs prior)

/-- Reuse an adopted correction as later ledger entries become available. -/
def PaymentCorrectionCase.retained (c : PaymentCorrectionCase) (l : Lesson)
    (a : ReviewAuthorities) (appointments : List ReviewAppointment)
    (outcomes : List RecordedSettlementOutcome) (monetaryOutcome : EvidenceRef → Option PaymentPart)
    (history : PaymentHistory) (prior : List PaymentPart := []) : Prop :=
  c.outcomeConforms l a appointments outcomes monetaryOutcome ∧
    correctionActualPaymentsRetained history c.money (c.priorMaterialsRefs prior)

def MonetaryCorrection.misdirectedReceipts (c : MonetaryCorrection) (h : PaymentHistory) :
    List PostedPayment :=
  c.actualReceipts.filter (fun paid ↦ decide (¬h.recipientReceived c.corrected.recipient paid))

structure CorrectedPortion where
  part : PaymentPart
  prior : List PaymentPart
  deriving DecidableEq, Repr

def CorrectedPortion.refs (portion : CorrectedPortion) : List PaymentPartRef :=
  (portion.part.ref :: portion.prior.map (·.ref)).eraseDups

structure CorrectedMonetaryScope where
  selected : CorrectedPortion
  portions : List CorrectedPortion
  previousPrincipal : Amount
  reviewedPrincipal : Amount
  deriving DecidableEq, Repr

def CorrectedMonetaryScope.principal (scope : CorrectedMonetaryScope) : Amount :=
  sumAmountsWhere scope.portions (fun portion ↦
    portion.part.ref.sameObligation scope.selected.part.ref &&
      portion.part.recipient.samePayee scope.selected.part.recipient) (·.part.amount)

/-- A materials receipt follows its own revised portion if there is a retained allocation.
For an unallocated reference, only the unchanged obligation and creditor can match. -/
def CorrectedMonetaryScope.matchesMaterialsReceipt (scope : CorrectedMonetaryScope)
    (ref : PaymentPartRef) : Bool :=
  let part := scope.selected.part
  match scope.portions.find? (fun portion ↦ portion.refs.contains ref) with
  | some portion =>
    portion.part.ref.sameObligation part.ref && portion.part.recipient.samePayee part.recipient
  | none => part.ref.sameObligation ref

/-- The refund balance uses credit actually restored to the original debit account. -/
def MonetaryCorrection.outstandingBefore (c : MonetaryCorrection) (history : PaymentHistory)
    (credits : List Booking.CreditPosting) (refundPlace : Option Place)
    (time : Moment) (outstanding : Amount) (scope : CorrectedMonetaryScope) : Prop :=
  let part := c.corrected
  let principal := scope.principal
  match part.recipient with
  | .person _ _ =>
    if part.ref.purpose.isMaterialsShare then
      let received := sumAmountsWhere history.posted (fun paid ↦
        scope.matchesMaterialsReceipt paid.instruction.part &&
          decide (history.recipientReceived part.recipient paid ∧ paid.instruction.atTime.before time))
        (fun paid ↦ paid.retainedAmountBefore history.returned time)
      outstanding = max 0 (principal - received)
    else outstanding = history.remainingObligationBefore part.ref.lesson
      part.ref.obligation part.recipient principal time (some part.ref.purpose)
  | .lessonRefund account =>
      ∃ p ∈ refundPlace, part.ref.lesson = p.lesson ∧ part.ref.purpose = .lessonRefund p.id ∧
        p.account = account ∧ outstanding = Settlement.refundBalanceDue p
          (credits.filter (fun entry ↦ decide (entry.point.before time))) time
          principal (some part.ref.obligation)

/-- Only an evidenced receipt with a reference in this portion's lineage can discharge it.
The obligation balance separately counts all receipts to its payee. -/
def CorrectedPortion.outstandingBefore (portion : CorrectedPortion) (history : PaymentHistory)
    (credits : List Booking.CreditPosting) (refundPlace : Option Place) (time : Moment) :
    Amount :=
  let part := portion.part
  let refs := portion.refs
  match part.recipient, refundPlace with
  | .person _ _, _ =>
    max 0 (part.amount - sumAmounts refs (fun ref ↦
      history.receivedForPartBefore ref part.recipient time))
  | .lessonRefund account, some place =>
    let relevant := credits.filter fun credit ↦
      decide (credit.point.before time) &&
        match credit.kind with
        | .lessonRefund .. => history.posted.any fun receipt ↦
          refs.contains receipt.instruction.part && decide
            (receipt.id = credit.id ∧ receipt.instruction.destination = .account account ∧
              credit.account = account ∧ receipt.instruction.atTime = credit.point ∧
              receipt.instruction.amount = credit.amount ∧ receipt.evidence.isSome = true)
        | _ => true
    Settlement.refundBalanceDue place relevant time part.amount (some part.ref.obligation)
  | .lessonRefund _, none => 0

structure CorrectionPaymentRecord where
  correction : EvidenceRef
  paid : PostedPayment
  refundCredit : Option Booking.CreditPosting
  deriving DecidableEq, Repr

/-- A separate actual payment discharges only the remaining corrected liability. -/
def PaymentCorrectionCase.additionalPaymentPosted (c : PaymentCorrectionCase) (l : Lesson)
    (history : PaymentHistory) (credits : List Booking.CreditPosting) (refundPlace : Option Place)
    (record : CorrectionPaymentRecord) (scope : CorrectedMonetaryScope)
    (otherPrincipals : List (ObligationId × Amount) := []) : Prop :=
  let paid := record.paid.instruction
  let corrected := c.money.corrected
  record.correction = c.correction.correction ∧ c.finding.decidedAt.by paid.atTime ∧
    paid.part.lesson = l.id ∧ paid.part = corrected.ref ∧
    corrected.recipient.accepts paid.destination ∧
    0 < paid.amount ∧ history.actualPaymentWithEvidence record.paid ∧
    history.recipientReceived corrected.recipient record.paid ∧
    (∃ outstanding, c.money.outstandingBefore history credits refundPlace paid.atTime
      outstanding scope ∧
      paid.amount ≤ outstanding) ∧
    paid.amount ≤ scope.selected.outstandingBefore history credits refundPlace paid.atTime ∧
    match corrected.recipient with
    | .person _ _ => record.refundCredit = none
    | .lessonRefund _ =>
      ∃ p ∈ refundPlace, ∃ credit ∈ record.refundCredit,
        credit.id = record.paid.id ∧ credit.point = paid.atTime ∧ credit.amount = paid.amount ∧
        Settlement.ValidLessonRefund p credits credit corrected.ref.obligation scope.principal false
          otherPrincipals

/-- Record the actual credit received for this corrected refund on its original account. -/
def PaymentCorrectionCase.observedRefundPosted (c : PaymentCorrectionCase) (p : Place)
    (history : PaymentHistory) (credits : List Booking.CreditPosting)
    (record : CorrectionPaymentRecord) : Prop :=
  let paid := record.paid.instruction
  let corrected := c.money.corrected
  record.correction = c.correction.correction ∧ c.finding.decidedAt.by paid.atTime ∧
  paid.part = corrected.ref ∧ paid.part.lesson = p.lesson ∧ paid.part.purpose = .lessonRefund p.id ∧
  corrected.recipient = .lessonRefund p.account ∧ paid.destination = .account p.account ∧
  history.actualPaymentWithEvidence record.paid ∧ history.distinctReceipts ∧ history.validReturns ∧
  ∃ credit ∈ record.refundCredit,
    Settlement.LessonRefundPostingMatches p credits credit corrected.ref.obligation ∧
    credit.id = record.paid.id ∧ credit.point = paid.atTime ∧ credit.amount = paid.amount

structure RecoveryDecision where
  matter : ReviewMatter
  payment : PaymentId
  amount : Amount
  approvedBy : ActorId
  approvedAt : Moment
  deriving DecidableEq, Repr

structure RecoveryRecord where
  correction : EvidenceRef
  decision : RecoveryDecision
  actualReturn : ReturnedPayment
  deriving DecidableEq, Repr

def recoveryConforms (history : PaymentHistory) (c : PaymentCorrectionCase)
    (underOriginalTerms : PaymentPart → RecoveryDecision → Prop)
    (authorised : ReviewMatter → ActorId → Moment → Prop)
    (r : RecoveryRecord) : Prop :=
  r.correction = c.correction.correction ∧ r.decision.matter = c.finding.matter ∧
    ∃ paid, c.money.matchesReceipt paid (c.priorMaterialsRefs []) ∧
      paid.id = r.decision.payment ∧
      history.actualPaymentWithEvidence paid ∧
      paid.instruction.atTime.before r.decision.approvedAt ∧
      c.finding.decidedAt.by r.decision.approvedAt ∧
      r.decision.approvedAt.by r.actualReturn.returnedAt ∧
      underOriginalTerms c.originalPart r.decision ∧
      authorised r.decision.matter r.decision.approvedBy r.decision.approvedAt ∧
      r.actualReturn.paidReceipt = paid.id ∧ r.actualReturn.amount = r.decision.amount ∧
      r.actualReturn ∈ history.returned ∧ history.distinctReceipts ∧ history.validReturns

structure CorrectionShortageNotice where
  correction : EvidenceRef
  payee : PaymentRecipient
  sentTo : ActorId
  sentAt : Moment
  outstanding : Amount
  progress : String
  deriving DecidableEq, Repr

def correctionShortageNoticeConforms (c : PaymentCorrectionCase) (l : Lesson)
    (history : PaymentHistory) (credits : List Booking.CreditPosting) (refundPlace : Option Place)
    (checkedAt : Moment) (refundOwedTo : Place → ActorId → Prop)
    (notice : CorrectionShortageNotice) (scope : CorrectedMonetaryScope) : Prop :=
  c.money.corrected.ref.lesson = l.id ∧ c.correction.recordedAt.by checkedAt ∧
    checkedAt.by notice.sentAt ∧
    notice.correction = c.correction.correction ∧ notice.payee = c.money.corrected.recipient ∧
    c.money.outstandingBefore history credits refundPlace checkedAt notice.outstanding scope ∧
    notice.progress ≠ "" ∧
    match notice.payee with
    | .person person _ => notice.sentTo = person
    | .lessonRefund account => ∃ p ∈ refundPlace, p.lesson = l.id ∧ p.account = account ∧
        c.money.corrected.ref.purpose = .lessonRefund p.id ∧ refundOwedTo p notice.sentTo


/-- Section 6.2 distinguishes a named payment, a pending decision and whole-group settlement. -/
inductive FormalHoldSubject where
  | payment
  | decision (decision : Nat)
  | groupSettlement
  deriving DecidableEq, Repr

structure FormalHold where
  id : HoldId
  matter : ReviewMatter
  subject : FormalHoldSubject
  portions : List PaymentPart
  imposedBy : ActorId
  decidedAt : Moment
  effectiveAt : Moment
  reasons : String
  reviewAt : Moment
  deriving DecidableEq, Repr

/-- A lift can expressly remove the hold from only some of its covered amounts. -/
inductive LiftScope where
  | all
  | paymentParts (parts : List PaymentPartRef)
  deriving DecidableEq, Repr

structure FormalLift where
  hold : HoldId
  scope : LiftScope
  decidedBy : ActorId
  decidedAt : Moment
  effectiveAt : Moment
  deriving DecidableEq, Repr

structure TemporaryHold where
  matter : ReviewMatter
  contact : ActorId
  part : PaymentPart
  complaintNamesPayment : PaymentPartRef
  allegedFacts : String
  authorisedAt : Moment
  effectiveAt : Moment
  deriving DecidableEq, Repr

/-- The exact prior and adopted amounts from a retained monetary correction. -/
structure HoldPartRevision where
  prior : PaymentPart
  corrected : PaymentPart
  priorOutcome : EvidenceRef
  correctedOutcome : EvidenceRef
  priorAt : Moment
  adoptedAt : Moment
  recordedAt : Moment := adoptedAt
  deriving DecidableEq, Repr

/-- Fact inputs for a hold concern the complaint and the payment or decision in question. -/
structure HoldFacts where
  terms : ReviewMatter → ReviewTerms
  termsApply : ReviewMatter → Prop
  acceptedPaymentConcern : ReviewMatter → PaymentPart → String → Moment → Prop
  reviewerCannotActInTime : ReviewMatter → Moment → Prop
  temporaryAuthority : ReviewMatter → ActorId → PaymentPartRef → Moment → Prop
  allegedFactsWouldChangePayment : ReviewMatter → PaymentPartRef → String → Prop
  separatelyIdentifiable : PaymentPartRef → Moment → Prop
  establishedParts : LessonId → PaymentPurpose → List PaymentPart
  paymentAffected : ReviewMatter → PaymentPartRef → Prop
  decisionPending : ReviewMatter → Nat → Moment → Prop
  partFallsUnderDecision : ReviewMatter → Nat → PaymentPartRef → Prop
  decisionConcernsWholeGroup : ReviewMatter → Nat → Prop
  isGroupLesson : LessonId → Prop
  affectsWholeSettlement : ReviewMatter → Prop
  groupSettlementParts : LessonId → List PaymentPartRef

/-- The amount, recipient and reference belong to the same established portion. -/
def HoldFacts.isCanonicalPart (facts : HoldFacts) (part : PaymentPart) : Prop :=
  let portions := facts.establishedParts part.ref.lesson part.ref.purpose
  part ∈ portions ∧ (portions.map PaymentPart.ref).Nodup ∧
    ∀ p ∈ portions, p.ref.lesson = part.ref.lesson ∧
      p.ref.purpose = part.ref.purpose ∧ 0 < p.amount

/-- The group scope includes established fees for the effective seats of this lesson. -/
def HoldFacts.groupSettlementScopeMatches (facts : HoldFacts) (lesson : Lesson)
    (places : List Place) : Prop :=
  (facts.isGroupLesson lesson.id ↔ lesson.kind = .group) ∧
    (lesson.kind = .group →
      let scope := facts.groupSettlementParts lesson.id
      scope.Nodup ∧ (∀ place ∈ places, place.matches lesson) ∧
      (∀ ref ∈ scope, ref.lesson = lesson.id ∧
        (∃ part, part.ref = ref ∧ facts.isCanonicalPart part) ∧
        match ref.purpose with
        | .customerFee seat | .lessonRefund seat => ∃ place ∈ places, place.id = seat
        | _ => True) ∧
      ∀ place ∈ places, ∀ part ∈ facts.establishedParts lesson.id (.customerFee place.id),
        part.ref ∈ scope)

/-- Compare the recorded parts against the independently established total for this payee. -/
def HoldFacts.coversPurpose (facts : HoldFacts) (lesson : LessonId) (purpose : PaymentPurpose)
    (recipient : PaymentRecipient) (total : Amount) : Prop :=
  let portions := facts.establishedParts lesson purpose
  (∀ p ∈ portions, p.ref.lesson = lesson ∧ p.ref.purpose = purpose ∧
    p.recipient = recipient ∧ 0 < p.amount) ∧
  (portions.map PaymentPart.ref).Nodup ∧ sumAmounts portions PaymentPart.amount = total

def HoldFacts.coversObligation (facts : HoldFacts) (ref : PaymentPartRef)
    (recipient : PaymentRecipient) (total : Amount) : Prop :=
  let portions := (facts.establishedParts ref.lesson ref.purpose).filter
    (fun part ↦ part.ref.obligation == ref.obligation)
  (∀ p ∈ portions, p.ref.lesson = ref.lesson ∧ p.ref.purpose = ref.purpose ∧
    p.recipient = recipient ∧ 0 < p.amount) ∧
  (portions.map PaymentPart.ref).Nodup ∧ sumAmounts portions PaymentPart.amount = total

/-- Actual approval scope, including any later end to coverage of a portion. -/
structure ApprovalScopeEntry where
  part : PaymentPartRef
  destination : PaymentDestination
  amount : Amount
  ceasesCoveringAt : Option Moment
  deriving DecidableEq, Repr

structure PaymentApproval where
  id : ApprovalId
  approver : ActorId
  executor : ActorId
  grantedAt : Moment
  validThrough : Option Moment
  invalidatedAt : Option Moment
  scope : List ApprovalScopeEntry
  deriving DecidableEq, Repr

structure NewApprovalArrangement where
  part : PaymentPartRef
  releasedAt : Moment
  original : ApprovalId
  replacement : ApprovalId
  arrangedBy : ActorId
  arrangedAt : Moment
  deriving DecidableEq, Repr

structure OriginalSettlementApproval where
  approver : ActorId
  approvedAt : Moment
  evidence : EvidenceRef
  deriving DecidableEq, Repr

/-- The original proposal and its approvals can exist before any payment scope is available. -/
structure RecordedOriginalSettlement where
  matter : ReviewMatter
  decision : Nat
  wholeGroup : Bool
  portions : List PaymentPartRef
  proposedBy : ActorId
  proposedAt : Moment
  proposalEvidence : EvidenceRef
  approvals : List OriginalSettlementApproval
  deriving DecidableEq, Repr

structure HoldHistory where
  payments : PaymentHistory
  temporary : List TemporaryHold
  formal : List FormalHold
  lifts : List FormalLift
  approvals : List PaymentApproval := []
  approvalArrangements : List NewApprovalArrangement := []
  originalSettlements : List RecordedOriginalSettlement := []
  clockBoundaries : List ClockBoundary := []
  partRevisions : List HoldPartRevision := []
  deriving DecidableEq, Repr

/-- Keep the prior version after the coordinator records an adopted monetary correction. -/
def HoldHistory.withPartRevision (history : HoldHistory) (original : RecordedSettlementOutcome)
    (correction : PaymentCorrectionCase) : HoldHistory :=
  { history with partRevisions := history.partRevisions ++
      [⟨correction.originalPart, correction.money.corrected, original.outcome,
        correction.finding.outcome, original.decidedAt, correction.finding.decidedAt,
        correction.correction.recordedAt⟩] }

def HoldHistory.withPartRevisionsKnownAt (history : HoldHistory) (knownAt : Moment) : HoldHistory :=
  { history with partRevisions := history.partRevisions.filter (fun row ↦
      decide (row.recordedAt.by knownAt)) }

private def HoldPartRevision.precedes (prior next : HoldPartRevision) : Bool :=
  prior.corrected == next.prior && prior.correctedOutcome == next.priorOutcome &&
    decide (prior.adoptedAt.before next.adoptedAt)

private def HoldPartRevision.touches (row : HoldPartRevision) (ref : PaymentPartRef) : Bool :=
  row.prior.ref == ref || row.corrected.ref == ref

private def HoldPartRevision.withinPriorScope (revision : HoldPartRevision) : Bool :=
  revision.prior.recipient.samePayee revision.corrected.recipient &&
    decide (revision.corrected.amount ≤ revision.prior.amount)

private def HoldPartRevision.insertByAdoption (row : HoldPartRevision) :
    List HoldPartRevision → List HoldPartRevision
  | [] => [row]
  | first :: rest =>
    if row.adoptedAt.by first.adoptedAt then row :: first :: rest
    else first :: row.insertByAdoption rest

private def HoldHistory.revisionsByAdoption (history : HoldHistory) : List HoldPartRevision :=
  history.partRevisions.foldr HoldPartRevision.insertByAdoption []

private def HoldHistory.portionPath (history : HoldHistory) (prior : PaymentPart)
    (since through : Moment) : List HoldPartRevision :=
  history.revisionsByAdoption.foldl (fun trail row ↦
    if decide (since.before row.adoptedAt ∧ row.adoptedAt.by through) &&
      (match trail with
      | [] => prior == row.prior
      | previous :: _ => previous.precedes row)
    then row :: trail else trail) []

@[simp] private theorem HoldHistory.portionPath_of_noPartRevisions (history : HoldHistory)
    (empty : history.partRevisions = []) (prior : PaymentPart) (since through : Moment) :
    history.portionPath prior since through = [] := by
  simp [HoldHistory.portionPath, HoldHistory.revisionsByAdoption, empty]

@[simp] private abbrev HoldHistory.scopeThrough (history : HoldHistory) (held : PaymentPart)
    (since : Moment)
    (part : PaymentPartRef) (through : Moment) (unresolved : Bool) : Prop :=
  let trail := history.portionPath held since through
  (trail.head?.map (·.corrected.ref)).getD held.ref = part ∧
    trail.all HoldPartRevision.withinPriorScope = !unresolved

private def HoldHistory.predecessors (history : HoldHistory) (part : PaymentPart)
    (through : Moment) : List HoldPartRevision :=
  history.revisionsByAdoption.reverse.foldl (fun trail row ↦
    if decide (row.adoptedAt.by through) &&
      (match trail with
      | [] => row.corrected == part
      | next :: _ => row.precedes next)
    then row :: trail else trail) []

@[simp] private theorem HoldHistory.predecessors_of_noPartRevisions (history : HoldHistory)
    (empty : history.partRevisions = []) (part : PaymentPart) (through : Moment) :
    history.predecessors part through = [] := by
  simp [HoldHistory.predecessors, HoldHistory.revisionsByAdoption, empty]

/-- Only an unambiguous retained version determines a revised portion at this time. -/
def HoldHistory.establishedPartsAt (history : HoldHistory) (facts : HoldFacts) (lesson : LessonId)
    (purpose : PaymentPurpose) (time : Moment) : List PaymentPart :=
  let revisions := history.partRevisions
  let unrelated := (facts.establishedParts lesson purpose).filter fun part ↦
    !(revisions.any (·.touches part.ref))
  let prior := revisions.filterMap fun row ↦
    if decide (row.priorAt.by time ∧ time.before row.adoptedAt) &&
      !(revisions.any (·.precedes row)) then some row.prior else none
  let corrected := revisions.filterMap fun row ↦
    if decide (row.adoptedAt.by time) &&
      !(revisions.any fun next ↦ row.precedes next && decide (next.adoptedAt.by time)) &&
      (history.predecessors row.corrected time).all (fun choice ↦
        !(revisions.any fun alternate ↦ choice != alternate &&
          choice.prior == alternate.prior && choice.priorOutcome == alternate.priorOutcome &&
          decide (alternate.adoptedAt.by time)))
    then some row.corrected else none
  unrelated ++ ((prior.eraseDups ++ corrected).filter fun part ↦
    part.ref.lesson == lesson && part.ref.purpose == purpose && decide (0 < part.amount))

def HoldHistory.factsAt (history : HoldHistory) (facts : HoldFacts) (time : Moment) : HoldFacts :=
  { facts with establishedParts := fun lesson purpose ↦
      history.establishedPartsAt facts lesson purpose time }

@[simp] theorem HoldHistory.factsAt_of_noPartRevisions (history : HoldHistory)
    (empty : history.partRevisions = []) (facts : HoldFacts) (time : Moment) :
    history.factsAt facts time = facts := by
  have parts : (fun lesson purpose ↦ history.establishedPartsAt facts lesson purpose time) =
      facts.establishedParts := by
    funext lesson purpose
    simp [HoldHistory.establishedPartsAt, empty, List.filter_eq_self]
  unfold HoldHistory.factsAt
  rw [parts]

private def HoldHistory.versionAt (history : HoldHistory) (part : PaymentPart)
    (time through : Moment) : PaymentPart :=
  ((history.predecessors part through).find? (fun row ↦
    decide (time.before row.adoptedAt))).map (·.prior) |>.getD part

/-- Payee-specific receipts under an exact predecessor reference survive a correction. -/
def HoldHistory.remainingPortionBefore (history : HoldHistory) (part : PaymentPart)
    (time : Moment) (through : Moment := time) : Amount :=
  match history.predecessors part through with
  | [] => history.payments.remainingBefore part time
  | trail =>
    let historical := history.versionAt part time through
    let earlierRefs := (trail.filter fun row ↦ decide (row.adoptedAt.by time)).map (·.prior.ref)
    let refs := (historical.ref :: earlierRefs).eraseDups
    max 0 (historical.amount - sumAmounts refs (fun ref ↦
      history.payments.receivedForPartBefore ref historical.recipient time))

/-- Measure completion of the adopted amount using receipts to its own payee. -/
def HoldHistory.fullyRetainedPortionBy (history : HoldHistory) (part : PaymentPart)
    (cutoff : ClockCutoff) (through : Moment) : Prop :=
  match history.predecessors part through with
  | [] => history.payments.fullyRetainedBy part cutoff
  | trail =>
    let refs := (part.ref :: trail.map (·.prior.ref)).eraseDups
    history.payments.distinctReceipts ∧ history.payments.validReturns ∧
      cutoff.forEveryOrder fun deadline ↦
        part.amount ≤ sumAmounts refs (fun ref ↦
          history.payments.receivedForPartBefore ref part.recipient
            { deadline with order := deadline.order + 1 })

def HoldHistory.distinctFormalDecisions (history : HoldHistory) : Prop :=
  (history.formal.map FormalHold.id).Nodup

def HoldHistory.approvalRecorded (history : HoldHistory) (approval : PaymentApproval) : Prop :=
  approval ∈ history.approvals ∧ (history.approvals.map PaymentApproval.id).Nodup

def ReviewAuthorities.mayImposeOrLift (a : ReviewAuthorities) (m : ReviewMatter)
    (actor : ActorId) (time : Moment) : Prop :=
  a.reviewer m actor time ∧ a.disinterested m actor time ∧
    actor ∉ a.originalSettlementProposers m ∧ actor ∉ a.originalSettlementApprovers m

def TemporaryHold.maySetAside (t : TemporaryHold) (a : ReviewAuthorities) (facts : HoldFacts)
    (payments : PaymentHistory)
    (outstanding : Amount := payments.remainingBefore t.part t.effectiveAt) : Prop :=
  let terms := facts.terms t.matter
  facts.termsApply t.matter ∧ t.contact = terms.alternativeContact ∧
    facts.isCanonicalPart t.part ∧ t.part.ref.lesson = t.matter.lesson ∧
    t.part.ref = t.complaintNamesPayment ∧ t.allegedFacts ≠ "" ∧
    facts.acceptedPaymentConcern t.matter t.part t.allegedFacts t.effectiveAt ∧
    facts.allegedFactsWouldChangePayment t.matter t.part.ref t.allegedFacts ∧
    a.disinterested t.matter t.contact t.effectiveAt ∧
    facts.reviewerCannotActInTime t.matter t.effectiveAt ∧
    t.authorisedAt.before t.effectiveAt ∧
    facts.temporaryAuthority t.matter t.contact t.part.ref t.authorisedAt ∧
    facts.separatelyIdentifiable t.part.ref t.effectiveAt ∧
    (facts.isGroupLesson t.matter.lesson →
      ¬(t.part.ref ∈ facts.groupSettlementParts t.matter.lesson ∧
        ∀ ref ∈ facts.groupSettlementParts t.matter.lesson, ref = t.part.ref)) ∧
    t.effectiveAt.before terms.temporaryHoldExpiry ∧
    0 < outstanding

private def HoldHistory.temporaryMaySetAside (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (t : TemporaryHold) : Prop :=
  t.maySetAside a (history.factsAt facts t.effectiveAt) history.payments
    (history.remainingPortionBefore t.part t.effectiveAt)

/-- The authority check for a finding uses the lawful setters in its own recorded case. -/
def HoldHistory.temporarySettersRecorded (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (matter : ReviewMatter) (through : Moment) : Prop :=
  ∀ (caseMatter : ReviewMatter) (actor : ActorId) (effectiveAt : Moment),
    caseMatter.sameCase matter → effectiveAt.by through →
    ((caseMatter, actor, effectiveAt) ∈ a.actualTemporaryHoldSetters ↔
      ∃ temp ∈ history.temporary, temp.matter = caseMatter ∧ temp.contact = actor ∧
        temp.effectiveAt = effectiveAt ∧ history.temporaryMaySetAside a facts temp)

def HoldHistory.notTemporarySetter (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (matter : ReviewMatter) (actor : ActorId) (atTime : Moment) : Prop :=
  ∀ temp ∈ history.temporary, temp.matter.sameCase matter →
    history.temporaryMaySetAside a facts temp →
    temp.effectiveAt.by atTime → actor ≠ temp.contact

structure TemporaryHoldNotice where
  matter : ReviewMatter
  part : PaymentPartRef
  concernLoggedBy : ActorId
  sentBy : ActorId
  sentAt : Moment
  sentTo : List ActorId
  immediateNotice : Bool
  deriving DecidableEq, Repr

def temporaryHoldNoticeConforms (a : ReviewAuthorities) (t : TemporaryHold)
    (n : TemporaryHoldNotice) : Prop :=
  n.matter = t.matter ∧ n.part = t.part.ref ∧ n.concernLoggedBy = t.contact ∧
    n.sentBy = t.contact ∧ t.effectiveAt.by n.sentAt ∧ n.immediateNotice = true ∧
    (∀ party ∈ t.matter.parties, party ∈ n.sentTo) ∧
    (∀ partner, a.corePartner partner t.effectiveAt → partner ∈ n.sentTo)

def temporaryHoldDispositionConforms (a : ReviewAuthorities) (facts : HoldFacts)
    (t : TemporaryHold) (appointment : ReviewAppointment)
    (decider : ActorId) (decidedAt : Moment) : Prop :=
  let terms := facts.terms t.matter
  appointment.applies a t.matter decider decidedAt ∧ independentReviewer a t.matter decider decidedAt ∧
    decider ≠ t.contact ∧
    t.effectiveAt.by appointment.appointedAt ∧
    appointment.appointedAt.by terms.handoffDeadline ∧ decidedAt.by terms.temporaryHoldExpiry

def FormalHold.covers (hold : FormalHold) (part : PaymentPartRef) : Prop :=
  ∃ p ∈ hold.portions, p.ref = part

def FormalHold.concernsWholeGroup (hold : FormalHold) (facts : HoldFacts) : Prop :=
  hold.subject = .groupSettlement ∨
    (∃ decision, hold.subject = .decision decision ∧
      facts.decisionConcernsWholeGroup hold.matter decision) ∨
    (let group := facts.groupSettlementParts hold.matter.lesson
     group ≠ [] ∧ ∀ part ∈ group, hold.covers part)

def FormalHold.mayImpose (hold : FormalHold) (a : ReviewAuthorities) (facts : HoldFacts)
    (payments : PaymentHistory)
    (outstanding : PaymentPart → Amount := fun part ↦ payments.remainingBefore part hold.effectiveAt) :
    Prop :=
  a.mayImposeOrLift hold.matter hold.imposedBy hold.decidedAt ∧
    hold.decidedAt.by hold.effectiveAt ∧
    (hold.portions.map PaymentPart.ref).Nodup ∧
    (∀ p ∈ hold.portions, p.ref.lesson = hold.matter.lesson ∧
      facts.isCanonicalPart p ∧ 0 < outstanding p) ∧
    (facts.isGroupLesson hold.matter.lesson → hold.concernsWholeGroup facts →
      facts.affectsWholeSettlement hold.matter) ∧
    match hold.subject with
    | .payment =>
        hold.portions ≠ [] ∧ ∀ p ∈ hold.portions, facts.paymentAffected hold.matter p.ref
    | .decision decision =>
        facts.decisionPending hold.matter decision hold.effectiveAt ∧
          ∀ p ∈ hold.portions, facts.partFallsUnderDecision hold.matter decision p.ref
    | .groupSettlement =>
        facts.isGroupLesson hold.matter.lesson ∧ hold.portions ≠ [] ∧
          (∀ p ∈ hold.portions, p.ref ∈ facts.groupSettlementParts hold.matter.lesson ∧
            facts.paymentAffected hold.matter p.ref)

structure FormalHoldNotice where
  hold : HoldId
  sentBy : ActorId
  sentAt : Moment
  sentTo : List ActorId
  subject : FormalHoldSubject
  portions : List PaymentPart
  reasons : String
  reviewAt : Moment
  deriving DecidableEq, Repr

def formalHoldNoticeConforms (hold : FormalHold) (n : FormalHoldNotice) : Prop :=
  n.hold = hold.id ∧ n.sentBy = hold.imposedBy ∧ hold.decidedAt.by n.sentAt ∧ n.sentAt.by hold.reviewAt ∧
    n.subject = hold.subject ∧
    n.portions = hold.portions ∧ n.reasons = hold.reasons ∧ n.reasons ≠ "" ∧
    n.reviewAt = hold.reviewAt ∧ (∀ party ∈ hold.matter.parties, party ∈ n.sentTo)

def FormalLift.covers (lift : FormalLift) (part : PaymentPartRef) : Prop :=
  match lift.scope with
  | .all => True
  | .paymentParts parts => part ∈ parts

def FormalLift.mayLift (lift : FormalLift) (a : ReviewAuthorities) (hold : FormalHold) : Prop :=
  lift.hold = hold.id ∧ a.mayImposeOrLift hold.matter lift.decidedBy lift.decidedAt ∧
    hold.effectiveAt.by lift.decidedAt ∧ lift.decidedAt.by lift.effectiveAt ∧
    hold.effectiveAt.before lift.effectiveAt ∧
    match lift.scope with
    | .all => True
    | .paymentParts parts => parts ≠ [] ∧ ∀ part ∈ parts, hold.covers part

/-- The original approval is the first recorded approval of this same settlement portion. -/
def HoldHistory.originallyApprovedBy (history : HoldHistory) (a : ReviewAuthorities)
    (ref : PaymentPartRef) (actor : ActorId) (query : Moment) : Prop :=
  let validScope := fun approval : PaymentApproval ↦
    ∃ entry ∈ approval.scope, entry.part = ref ∧ 0 < entry.amount ∧
      a.approvesPayment entry.part approval.approver approval.grantedAt
  ∃ approval ∈ history.approvals, approval.approver = actor ∧ approval.grantedAt.by query ∧
    validScope approval ∧ ∀ prior ∈ history.approvals, validScope prior →
      approval.grantedAt.by prior.grantedAt

def RecordedOriginalSettlement.appliesTo (original : RecordedOriginalSettlement)
    (hold : FormalHold) : Prop :=
  original.matter.lesson = hold.matter.lesson ∧
    ((original.matter.sameCase hold.matter ∧ hold.subject = .decision original.decision) ∨
      (hold.subject = .groupSettlement ∧ original.wholeGroup = true) ∨
      ∃ ref ∈ original.portions, hold.covers ref)

def HoldHistory.originalSettlementActor (history : HoldHistory) (hold : FormalHold)
    (actor : ActorId) (query : Moment) : Prop :=
  ∃ original ∈ history.originalSettlements, original.appliesTo hold ∧
    original.proposedAt.by query ∧
    (original.proposedBy = actor ∨ ∃ approved ∈ original.approvals,
      approved.approver = actor ∧ original.proposedAt.by approved.approvedAt ∧
      approved.approvedAt.by query)

def HoldHistory.validFormalHold (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (hold : FormalHold) : Prop :=
  hold ∈ history.formal ∧
    hold.mayImpose a (history.factsAt facts hold.effectiveAt) history.payments
      (fun part ↦ history.remainingPortionBefore part hold.effectiveAt) ∧
    (∀ part ∈ hold.portions,
      ¬history.originallyApprovedBy a part.ref hold.imposedBy hold.decidedAt) ∧
    history.notTemporarySetter a facts hold.matter hold.imposedBy hold.decidedAt ∧
    ¬history.originalSettlementActor hold hold.imposedBy hold.decidedAt

def HoldHistory.validLift (history : HoldHistory) (a : ReviewAuthorities) (facts : HoldFacts)
    (hold : FormalHold) (lift : FormalLift) : Prop :=
  lift.mayLift a hold ∧
    (∀ part ∈ hold.portions, lift.covers part.ref →
      ¬history.originallyApprovedBy a part.ref lift.decidedBy lift.decidedAt) ∧
    ¬history.originalSettlementActor hold lift.decidedBy lift.decidedAt ∧
    history.notTemporarySetter a facts hold.matter lift.decidedBy lift.decidedAt

@[simp] private def HoldHistory.formalScopeThrough (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (hold : FormalHold) (part : PaymentPartRef) (time through : Moment)
    (unresolved : Bool) : Prop :=
  history.validFormalHold a facts hold ∧ hold.effectiveAt.by time ∧
    ∃ source ∈ hold.portions,
      history.scopeThrough source hold.effectiveAt part through unresolved ∧
      ¬∃ lift ∈ history.lifts,
        history.validLift a facts hold lift ∧ lift.covers source.ref ∧ lift.effectiveAt.by time

def HoldHistory.formalInForce (history : HoldHistory) (a : ReviewAuthorities) (facts : HoldFacts)
    (hold : FormalHold) (part : PaymentPartRef) (time : Moment)
    (through : Moment := time) : Prop :=
  history.formalScopeThrough a facts hold part time through false

@[simp] private def HoldHistory.temporaryScopeThrough (history : HoldHistory)
    (a : ReviewAuthorities) (facts : HoldFacts) (t : TemporaryHold) (part : PaymentPartRef)
    (time through : Moment) (unresolved : Bool) : Prop :=
  t ∈ history.temporary ∧ history.temporaryMaySetAside a facts t ∧
    history.scopeThrough t.part t.effectiveAt part through unresolved ∧
    t.effectiveAt.by time ∧ time.before (facts.terms t.matter).temporaryHoldExpiry ∧
    ¬∃ hold, hold.matter.sameCase t.matter ∧
      history.validFormalHold a facts hold ∧ t.effectiveAt.by hold.effectiveAt ∧
      hold.effectiveAt.by time ∧ ∃ source ∈ hold.portions,
        history.scopeThrough t.part t.effectiveAt source.ref hold.effectiveAt false

def HoldHistory.temporaryInForce (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (t : TemporaryHold) (part : PaymentPartRef) (time : Moment)
    (through : Moment := time) : Prop :=
  history.temporaryScopeThrough a facts t part time through false

def HoldHistory.paymentOnHold (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (part : PaymentPartRef) (time : Moment)
    (through : Moment := time) : Prop :=
  (∃ hold, history.formalInForce a facts hold part time through) ∨
    (∃ temp, history.temporaryInForce a facts temp part time through)

/-- A plausible scope change needs evidence before a new payment is authorised. -/
def HoldHistory.paymentHoldScopeUnresolved (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (part : PaymentPartRef) (time : Moment)
    (through : Moment := time) : Prop :=
  (∃ hold, history.formalScopeThrough a facts hold part time through true) ∨
    (∃ temp, history.temporaryScopeThrough a facts temp part time through true)

@[simp] theorem HoldHistory.noUnresolvedScopeWithoutRevisions (history : HoldHistory)
    (empty : history.partRevisions = []) (a : ReviewAuthorities) (facts : HoldFacts)
    (part : PaymentPartRef) (time through : Moment) :
    ¬history.paymentHoldScopeUnresolved a facts part time through := by
  simp [HoldHistory.paymentHoldScopeUnresolved, empty]

def HoldHistory.decisionOnFormalHold (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (m : ReviewMatter) (decision : Nat) (time : Moment) : Prop :=
  ∃ hold, history.validFormalHold a facts hold ∧ hold.effectiveAt.by time ∧
    let wholeDecision :=
      (hold.matter.sameCase m ∧ hold.subject = .decision decision) ∨
      (hold.matter.lesson = m.lesson ∧ hold.subject = .groupSettlement ∧
        facts.decisionConcernsWholeGroup m decision)
    (wholeDecision ∧ ¬∃ lift ∈ history.lifts,
      history.validLift a facts hold lift ∧ lift.scope = .all ∧ lift.effectiveAt.by time) ∨
    (hold.matter.lesson = m.lesson ∧ hold.subject = .groupSettlement ∧
      ∃ portion ∈ hold.portions, facts.partFallsUnderDecision m decision portion.ref ∧
        history.formalInForce a facts hold portion.ref time)

/-- Test an identified decision again when it is to be carried out. -/
def HoldHistory.mayCarryOutDecision (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (matter : ReviewMatter) (decision : Nat) (time : Moment) : Prop :=
  history.distinctFormalDecisions ∧ ¬history.decisionOnFormalHold a facts matter decision time

inductive TemporaryHoldDecision where
  | finding (result : ReviewFinding)
  | formal (hold : FormalHold)
  deriving DecidableEq, Repr

/-- Recording and handing off an effective temporary hold are separate duties. -/
def HoldHistory.temporaryHoldHandled (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (temp : TemporaryHold) (notice : TemporaryHoldNotice)
    (appointment : ReviewAppointment) (decision : TemporaryHoldDecision) : Prop :=
  temp ∈ history.temporary ∧ history.temporaryMaySetAside a facts temp ∧
    temporaryHoldNoticeConforms a temp notice ∧
    match decision with
    | .finding f => f.matter = temp.matter ∧ reviewFindingConforms a [appointment] f ∧
      temporaryHoldDispositionConforms a facts temp appointment f.reviewer f.decidedAt
    | .formal hold => hold.matter = temp.matter ∧ history.validFormalHold a facts hold ∧
      hold.covers temp.part.ref ∧
      temporaryHoldDispositionConforms a facts temp appointment hold.imposedBy hold.decidedAt

def HoldHistory.formalHoldNotified (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (hold : FormalHold) (notice : FormalHoldNotice) : Prop :=
  history.validFormalHold a facts hold ∧ formalHoldNoticeConforms hold notice

structure ReviewDelayNotice where
  hold : HoldId
  reviewDate : Moment
  cause : String
  sentAt : Moment
  nextActionDate : Moment
  sentTo : List ActorId
  deriving DecidableEq, Repr

def reviewDelayNoticeRequired (reviewDate : Moment) (decisionAt : Option Moment) : Prop :=
  ¬∃ time ∈ decisionAt, time.by reviewDate

def reviewDelayNoticeConforms (hold : FormalHold) (reviewDate : Moment)
    (notice : ReviewDelayNotice) : Prop :=
  notice.hold = hold.id ∧ notice.reviewDate = reviewDate ∧ notice.cause ≠ "" ∧
    reviewDate.by notice.sentAt ∧ notice.sentAt.before notice.nextActionDate ∧
    (∀ party ∈ hold.matter.parties, party ∈ notice.sentTo)

inductive ReassessmentOutcome where
  | continues (reasons : String) (nextReviewAt : Moment)
  | lifts (lift : FormalLift)
  deriving DecidableEq, Repr

structure FormalReassessment where
  hold : HoldId
  reviewer : ActorId
  reviewedAt : Moment
  groundsRemain : Bool
  outcome : ReassessmentOutcome
  notified : List ActorId
  deriving DecidableEq, Repr

def formalReassessmentConforms (a : ReviewAuthorities) (hold : FormalHold)
    (r : FormalReassessment) : Prop :=
  r.hold = hold.id ∧ independentReviewer a hold.matter r.reviewer r.reviewedAt ∧
    hold.effectiveAt.by r.reviewedAt ∧
    match r.outcome with
    | .continues reasons next =>
        r.groundsRemain = true ∧ reasons ≠ "" ∧ r.reviewedAt.before next ∧
          (∀ party ∈ hold.matter.parties, party ∈ r.notified)
    | .lifts lift =>
        r.groundsRemain = false ∧ lift.mayLift a hold ∧ lift.decidedBy = r.reviewer ∧
          lift.decidedAt = r.reviewedAt ∧ lift.scope = .all

def HoldHistory.reassessmentRecorded (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (hold : FormalHold) (r : FormalReassessment) : Prop :=
  history.validFormalHold a facts hold ∧
    formalReassessmentConforms a hold r ∧
    history.notTemporarySetter a facts hold.matter r.reviewer r.reviewedAt ∧
    match r.outcome with
    | .continues _ _ =>
      ¬∃ lift ∈ history.lifts, history.validLift a facts hold lift ∧ lift.scope = .all ∧
        lift.effectiveAt.by r.reviewedAt
    | .lifts lift => lift ∈ history.lifts ∧ history.validLift a facts hold lift

/-- A delay notice cites the current review date set by the hold or an actual reassessment. -/
def HoldHistory.reviewDelayNotified (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (hold : FormalHold) (reassessments : List FormalReassessment)
    (decisions : List ReviewFinding) (appointments : List ReviewAppointment)
    (notice : ReviewDelayNotice) : Prop :=
  let continued := fun r : FormalReassessment ↦
    r ∈ reassessments ∧ history.reassessmentRecorded a facts hold r ∧
      r.reviewedAt.by notice.reviewDate
  history.validFormalHold a facts hold ∧
    ((notice.reviewDate = hold.reviewAt ∧ ¬∃ r, continued r) ∨
      ∃ r, continued r ∧ (∃ reasons, r.outcome = .continues reasons notice.reviewDate) ∧
        ¬∃ later, continued later ∧ r.reviewedAt.before later.reviewedAt) ∧
    (¬∃ decision ∈ decisions, decision.matter.sameCase hold.matter ∧
      reviewFindingConforms a appointments decision ∧ hold.effectiveAt.by decision.decidedAt ∧
      decision.decidedAt.by notice.reviewDate) ∧
    reviewDelayNoticeConforms hold notice.reviewDate notice

/-- Section 6.4 requires publication of the date and scope of policy changes. -/
inductive RuleChangeSubject where
  | fees | pay | revenueShares | decisionAuthority
  deriving DecidableEq, Repr

structure PolicyPublication where
  issuedBy : ActorId
  issuedAt : Moment
  rules : EvidenceRef
  supportingTerms : EvidenceRef
  deriving DecidableEq, Repr

def policyPublicationConforms (a : ReviewAuthorities) (p : PolicyPublication) : Prop :=
  a.corePartner p.issuedBy p.issuedAt

structure RuleChangePublication where
  version : Nat
  publishedBy : ActorId
  publishedAt : Moment
  effectiveAt : Moment
  changes : List RuleChangeSubject
  statedScope : String
  deriving DecidableEq, Repr

def ruleChangePublicationConforms (a : ReviewAuthorities) (p : RuleChangePublication) : Prop :=
  a.corePartner p.publishedBy p.publishedAt ∧ p.changes ≠ [] ∧ p.statedScope ≠ ""

structure ArrangementConsent where
  person : ActorId
  arrangement : EvidenceRef
  changeVersion : Nat
  consentedAt : Moment
  deriving DecidableEq, Repr

structure ExistingArrangement where
  ref : EvidenceRef
  originalVersion : Nat
  affected : List ActorId
  deriving DecidableEq, Repr

def arrangementChangeAgreed (p : RuleChangePublication) (arrangement : ExistingArrangement)
    (consents : List ArrangementConsent) (arrangementChangedAt : Moment) : Prop :=
  ∀ person ∈ arrangement.affected, ∃ c ∈ consents,
    c.person = person ∧ c.arrangement = arrangement.ref ∧ c.changeVersion = p.version ∧
    c.consentedAt.by arrangementChangedAt

/-- Existing commitments keep their original terms unless everyone affected agrees to a change. -/
def versionAppliesToExisting (a : ReviewAuthorities) (arrangement : ExistingArrangement)
    (change : RuleChangePublication) (coversArrangement : RuleChangePublication → EvidenceRef → Prop)
    (consents : List ArrangementConsent)
    (arrangementChangedAt time : Moment)
    (version : Nat) : Prop :=
  let agreedChangeInEffect := ruleChangePublicationConforms a change ∧
    coversArrangement change arrangement.ref ∧ change.publishedAt.by time ∧
    change.effectiveAt.by time ∧ arrangementChangedAt.by time ∧ arrangement.affected ≠ [] ∧
    arrangementChangeAgreed change arrangement consents arrangementChangedAt
  (agreedChangeInEffect ∧ version = change.version) ∨
    (¬agreedChangeInEffect ∧ version = arrangement.originalVersion)

/-- A retained term in an existing private arrangement. -/
structure PrivateArrangement (Scope Terms : Type) where
  scope : Scope
  reference : EvidenceRef
  terms : Terms
  effectiveAt : Moment

structure PrivateAmendment (Scope Terms : Type) where
  prior : PrivateArrangement Scope Terms
  replacement : PrivateArrangement Scope Terms
  adoptedAt : Moment

structure PrivateAmendmentAssent where
  amendment : EvidenceRef
  person : ActorId
  consentedAt : Moment
  evidence : EvidenceRef

/-- Assent is verified against the exact recorded replacement, including its terms and scope. -/
def PrivateAmendment.allAffectedAssented {Scope Terms : Type}
    (change : PrivateAmendment Scope Terms) (affected : PrivateAmendment Scope Terms → ActorId → Prop)
    (verifiedAssent : PrivateAmendment Scope Terms → PrivateAmendmentAssent → Prop)
    (assents : List PrivateAmendmentAssent) : Prop :=
  (∃ person, affected change person) ∧
    ∀ person, affected change person → ∃ assent ∈ assents,
      assent.amendment = change.replacement.reference ∧ assent.person = person ∧
      assent.consentedAt.by change.adoptedAt ∧ verifiedAssent change assent

def PrivateAmendment.effectiveFor {Scope Terms : Type} (change : PrivateAmendment Scope Terms)
    (incumbent : PrivateArrangement Scope Terms) (affected : PrivateAmendment Scope Terms → ActorId → Prop)
    (verifiedAssent : PrivateAmendment Scope Terms → PrivateAmendmentAssent → Prop)
    (assents : List PrivateAmendmentAssent) (query : Moment) : Prop :=
  change.prior = incumbent ∧ change.replacement.scope = incumbent.scope ∧
    change.replacement.reference ≠ incumbent.reference ∧
    incumbent.effectiveAt.by change.adoptedAt ∧
    incumbent.effectiveAt.before change.replacement.effectiveAt ∧
    change.adoptedAt.by change.replacement.effectiveAt ∧ change.replacement.effectiveAt.by query ∧
    change.allAffectedAssented affected verifiedAssent assents

/-- Read the retained amendments in their effective order, starting from the confirmed term. -/
def privateArrangementAt {Scope Terms : Type}
    (affected : PrivateAmendment Scope Terms → ActorId → Prop)
    (verifiedAssent : PrivateAmendment Scope Terms → PrivateAmendmentAssent → Prop)
    (assents : List PrivateAmendmentAssent) (query : Moment)
    (incumbent : PrivateArrangement Scope Terms) :
    List (PrivateAmendment Scope Terms) → PrivateArrangement Scope Terms → Prop
  | [], operative => operative = incumbent
  | change :: rest, operative =>
    let effective := change.effectiveFor incumbent affected verifiedAssent assents query
    (effective ∧ privateArrangementAt affected verifiedAssent assents query change.replacement rest operative) ∨
      (¬effective ∧ privateArrangementAt affected verifiedAssent assents query incumbent rest operative)

/-- A confirmed loss is recorded separately from fees due to the tutor under §§3.2 and 3.4. -/
structure TutorBreachLoss where
  lesson : Lesson
  agreement : String
  breach : EvidenceRef
  loss : EvidenceRef
  incurredAt : Moment
  actualLoss : Amount
  tutorResponsibility : Amount
  deriving DecidableEq, Repr

structure TutorLossFinding where
  loss : Nat
  lesson : LessonId
  tutor : ActorId
  provider : ActorId
  agreement : String
  breach : EvidenceRef
  verifiedActualLoss : Amount
  verifiedTutorResponsibility : Amount
  causeVerified : Bool
  underAgreementAndApplicableRequirements : Bool
  verifier : ActorId
  verifiedAt : Moment
  deriving DecidableEq, Repr

structure TutorDebtRecovery where
  id : Nat
  loss : Nat
  debtor : ActorId
  creditor : ActorId
  amount : Amount
  madeAt : Moment
  evidence : EvidenceRef
  deriving DecidableEq, Repr

structure TutorDebtRecord where
  loss : Nat
  debtor : ActorId
  creditor : ActorId
  confirmedAmount : Amount
  recordedAt : Moment
  deriving DecidableEq, Repr

def tutorDebtConforms (l : Lesson) (agreement : String) (loss : TutorBreachLoss)
    (authorised : LessonId → String → ActorId → Moment → Prop)
    (f : TutorLossFinding) (debt : TutorDebtRecord) : Prop :=
  loss.lesson = l ∧ loss.agreement = agreement ∧ f.agreement = loss.agreement ∧
    f.lesson = l.id ∧ f.tutor = l.tutor ∧ f.provider = l.provider ∧
    f.breach = loss.breach ∧ f.loss = loss.loss ∧ loss.incurredAt.by f.verifiedAt ∧
    f.verifiedActualLoss = loss.actualLoss ∧ f.verifiedTutorResponsibility = loss.tutorResponsibility ∧
    f.causeVerified = true ∧ f.underAgreementAndApplicableRequirements = true ∧
    authorised l.id agreement f.verifier f.verifiedAt ∧
    0 < f.verifiedActualLoss ∧ 0 ≤ f.verifiedTutorResponsibility ∧
    f.verifiedTutorResponsibility ≤ f.verifiedActualLoss ∧
    debt.loss = f.loss ∧ debt.debtor = f.tutor ∧ debt.creditor = f.provider ∧
    debt.confirmedAmount = f.verifiedTutorResponsibility ∧ f.verifiedAt.by debt.recordedAt

def tutorLossesRecordedOnce (debts : List TutorDebtRecord) : Prop :=
  (debts.map TutorDebtRecord.loss).Nodup

def tutorDebtRemainingBefore (debt : TutorDebtRecord) (recoveries : List TutorDebtRecovery)
    (time : Moment) : Amount :=
  let previous := recoveries.filter (fun r ↦ decide (r.loss = debt.loss ∧
    r.debtor = debt.debtor ∧ r.creditor = debt.creditor ∧ debt.recordedAt.by r.madeAt ∧
    r.madeAt.before time ∧ 0 < r.amount))
  max 0 (debt.confirmedAmount - sumAmounts previous TutorDebtRecovery.amount)

structure CustomerRedressDelivery where
  lesson : LessonId
  provider : ActorId
  place : PlaceId
  obligation : ObligationId
  fulfilledAt : Moment
  evidence : EvidenceRef
  deriving DecidableEq, Repr

/-- Check actual recorded delivery of each redress obligation for the same lesson and provider. -/
def customerRedressFulfilledBefore (l : Lesson) (required : LessonId → PlaceId → ObligationId → Prop)
    (verifiedDelivery : CustomerRedressDelivery → Prop) (deliveries : List CustomerRedressDelivery)
    (time : Moment) : Prop :=
  ∀ place obligation, required l.id place obligation → ∃ d ∈ deliveries,
    d.lesson = l.id ∧ d.provider = l.provider ∧ d.place = place ∧ d.obligation = obligation ∧
    d.fulfilledAt.before time ∧ verifiedDelivery d

/-- Recovery follows the provider's own fulfilment of customer redress. -/
def tutorDebtRecoveryConforms (l : Lesson) (agreement : String) (loss : TutorBreachLoss)
    (authorised : LessonId → String → ActorId → Moment → Prop) (finding : TutorLossFinding)
    (debts : List TutorDebtRecord) (debt : TutorDebtRecord) (recoveries : List TutorDebtRecovery)
    (redressRequired : LessonId → PlaceId → ObligationId → Prop)
    (verifiedDelivery : CustomerRedressDelivery → Prop) (deliveries : List CustomerRedressDelivery)
    (r : TutorDebtRecovery) : Prop :=
  debt ∈ debts ∧ tutorLossesRecordedOnce debts ∧ tutorDebtConforms l agreement loss authorised finding debt ∧
    r ∈ recoveries ∧ (recoveries.map TutorDebtRecovery.id).Nodup ∧
  ((recoveries.filter (fun receipt ↦ receipt.loss == debt.loss)).map (·.madeAt)).Nodup ∧
  debt.recordedAt.by r.madeAt ∧
    customerRedressFulfilledBefore l redressRequired verifiedDelivery deliveries r.madeAt ∧
    r.loss = debt.loss ∧ r.debtor = debt.debtor ∧ r.creditor = debt.creditor ∧
    0 < r.amount ∧ r.amount ≤ tutorDebtRemainingBefore debt recoveries r.madeAt

def PaymentApproval.authorisedAtGrant (approval : PaymentApproval) (a : ReviewAuthorities) :
    Prop :=
  approval.scope ≠ [] ∧
    ∀ entry ∈ approval.scope, a.approvesPayment entry.part approval.approver approval.grantedAt

def PaymentApproval.validAt (approval : PaymentApproval) (atTime : Moment) : Prop :=
  approval.grantedAt.by atTime ∧
    (∀ limit ∈ approval.validThrough, atTime.by limit) ∧
    (∀ ended ∈ approval.invalidatedAt, atTime.before ended)

def ApprovalScopeEntry.remainingBefore (entry : ApprovalScopeEntry) (history : PaymentHistory)
    (part : PaymentPart) (time : Moment) : Amount :=
  max 0 (entry.amount - history.receivedForPartBefore part.ref part.recipient time)

def ApprovalScopeEntry.covers (entry : ApprovalScopeEntry) (history : PaymentHistory)
    (part : PaymentPart) (instruction : PaymentInstruction) : Prop :=
  entry.part = instruction.part ∧ entry.destination = instruction.destination ∧
    (∀ endTime ∈ entry.ceasesCoveringAt, instruction.atTime.before endTime) ∧
    instruction.amount ≤ entry.remainingBefore history part instruction.atTime

def PaymentApproval.covers (approval : PaymentApproval) (history : PaymentHistory)
    (part : PaymentPart) (instruction : PaymentInstruction) : Prop :=
  ∃ entry ∈ approval.scope, entry.covers history part instruction

private def HoldHistory.samePayeeAtGrant (history : HoldHistory) (approval : PaymentApproval)
    (part : PaymentPart) (atTime : Moment) : Bool :=
  (history.versionAt part approval.grantedAt atTime).recipient.samePayee part.recipient

/-- A retained approval covers the same payee even if the destination was shared. -/
def HoldHistory.approvalCovers (history : HoldHistory) (approval : PaymentApproval)
    (part : PaymentPart) (instruction : PaymentInstruction) : Prop :=
  if history.samePayeeAtGrant approval part instruction.atTime then
    approval.covers history.payments part instruction
  else False

@[simp] theorem HoldHistory.approvalCovers_of_noPartRevisions (history : HoldHistory)
    (empty : history.partRevisions = []) (approval : PaymentApproval) (part : PaymentPart)
    (instruction : PaymentInstruction) :
    history.approvalCovers approval part instruction ↔
      approval.covers history.payments part instruction := by
  cases recipient : part.recipient <;>
    simp [HoldHistory.approvalCovers, HoldHistory.samePayeeAtGrant, HoldHistory.versionAt,
      empty, recipient, PaymentRecipient.samePayee]

def PaymentApproval.originallyCovered (approval : PaymentApproval) (part : PaymentPart) : Prop :=
  ∃ entry ∈ approval.scope, entry.part = part.ref ∧ part.recipient.accepts entry.destination ∧
    0 < entry.amount ∧ ∀ stopped ∈ entry.ceasesCoveringAt, approval.grantedAt.before stopped

/-- Due date, execution deadline and the earlier deadline under law remain distinct. -/
structure PaymentSchedule where
  dueAt : Moment
  originalExecutionDeadline : Moment
  legalDeadline : Option Moment
  postLiftDeadline : DeadlineTerm
  deriving DecidableEq, Repr

/-- A post-lift elapsed period uses the certified cutoff for this actual lift. -/
def HoldHistory.resolvesDeadline (history : HoldHistory) (term : DeadlineTerm) (start : Moment) : Prop :=
  match term with
  | .date _ => True
  | .period duration cutoff => cutoff = ClockBoundary.after history.clockBoundaries start duration

def HoldHistory.metDeadline (history : HoldHistory) (term : DeadlineTerm) (start point : Moment) : Prop :=
  history.resolvesDeadline term start ∧ term.cutoff.metBy point

def PaymentSchedule.meetsLegalDeadline (terms : PaymentSchedule) (atTime : Moment) : Prop :=
  ∀ deadline ∈ terms.legalDeadline, atTime.by deadline

/-- Section 6.4 lets the named executor carry out the surviving original approval. -/
def originalExecutorMayPay (a : ReviewAuthorities) (facts : HoldFacts)
    (history : HoldHistory) (approval : PaymentApproval) (part : PaymentPart)
    (schedule : PaymentSchedule) (originalPaymentConditions : PaymentInstruction → Prop)
    (instruction : PaymentInstruction) : Prop :=
  (history.factsAt facts instruction.atTime).isCanonicalPart part ∧
    history.approvalRecorded approval ∧
    approval.authorisedAtGrant a ∧ approval.validAt instruction.atTime ∧
    history.approvalCovers approval part instruction ∧
    instruction.executor = approval.executor ∧
    history.payments.validOutstandingPayment part instruction ∧
    originalPaymentConditions instruction ∧
    instruction.atTime.by schedule.originalExecutionDeadline ∧
    history.distinctFormalDecisions ∧
    ¬history.paymentOnHold a facts part.ref instruction.atTime ∧
    ¬history.paymentHoldScopeUnresolved a facts part.ref instruction.atTime ∧
    instruction.amount ≤ history.remainingPortionBefore part instruction.atTime

/-- A later duplicate lift cannot give another window for a portion already released. -/
def HoldHistory.releasesPart (history : HoldHistory) (a : ReviewAuthorities)
    (facts : HoldFacts) (hold : FormalHold) (lift : FormalLift) (part : PaymentPartRef)
    (through : Moment := lift.effectiveAt) : Prop :=
  history.validFormalHold a facts hold ∧ lift ∈ history.lifts ∧
    history.validLift a facts hold lift ∧ history.distinctFormalDecisions ∧
    ∃ source ∈ hold.portions,
      history.scopeThrough source hold.effectiveAt part through false ∧
      lift.covers source.ref ∧
      ¬∃ earlier ∈ history.lifts, history.validLift a facts hold earlier ∧
        earlier.covers source.ref ∧ earlier.effectiveAt.before lift.effectiveAt

/-- The same payment part is continuously held up to its first unheld moment. -/
def HoldHistory.firstUnheldFrom (history : HoldHistory) (a : ReviewAuthorities) (facts : HoldFacts)
    (part : PaymentPartRef) (start releasedAt : Moment) (through : Moment := releasedAt) : Prop :=
  start.by releasedAt ∧ ¬history.paymentOnHold a facts part releasedAt through ∧
    ¬history.paymentHoldScopeUnresolved a facts part releasedAt through ∧
    ∀ time, start.by time → time.before releasedAt → history.paymentOnHold a facts part time through

/-- The complete release follows a recorded formal lift. Another hold may end later. -/
def HoldHistory.paymentReleasedAt (history : HoldHistory) (a : ReviewAuthorities) (facts : HoldFacts)
    (part : PaymentPartRef) (releasedAt : Moment) (through : Moment := releasedAt) : Prop :=
  ∃ hold lift, history.releasesPart a facts hold lift part through ∧
    history.firstUnheldFrom a facts part lift.effectiveAt releasedAt through

/-- A release after the original deadline must trace back to it if the unpaid
    part was formally held then. A release before that deadline has its own history. -/
def postLiftReleaseMatches (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (part : PaymentPart) (schedule : PaymentSchedule) (releasedAt : Moment)
    (through : Moment := releasedAt) : Prop :=
  let original := schedule.originalExecutionDeadline
  history.paymentReleasedAt a facts part.ref releasedAt through ∧
    (original.before releasedAt →
      (∃ hold, history.formalInForce a facts hold part.ref original through) →
      0 < history.remainingPortionBefore part original through →
      history.firstUnheldFrom a facts part.ref original releasedAt through)

/-- The prompt payment duty concerns an established due and unpaid amount. -/
def postLiftPromptPaymentDue (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (part : PaymentPart) (schedule : PaymentSchedule) (releasedAt : Moment)
    (through : Moment := releasedAt) : Prop :=
  (history.factsAt facts through).isCanonicalPart part ∧
    postLiftReleaseMatches a facts history part schedule releasedAt through ∧
    schedule.dueAt.before releasedAt ∧ 0 < history.remainingPortionBefore part releasedAt through

/-- Failure to complete prompt payment is observable even if ordinary execution remained open. -/
def postLiftPromptPaymentComplies (a : ReviewAuthorities) (facts : HoldFacts)
    (history : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (releasedAt observedAt : Moment) : Prop :=
  let cutoff := schedule.postLiftDeadline.cutoff
  postLiftPromptPaymentDue a facts history part schedule releasedAt observedAt →
    history.resolvesDeadline schedule.postLiftDeadline releasedAt ∧
    (cutoff.mayHavePassed observedAt → history.fullyRetainedPortionBy part cutoff observedAt)

/-- The execution window opens at the first release from a hold continuous from the deadline. -/
def postLiftWindowOpened (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (part : PaymentPart) (schedule : PaymentSchedule) (releasedAt : Moment)
    (through : Moment := releasedAt) : Prop :=
  let original := schedule.originalExecutionDeadline
  (history.factsAt facts through).isCanonicalPart part ∧
    history.paymentReleasedAt a facts part.ref releasedAt through ∧
    (∃ hold, history.formalInForce a facts hold part.ref original through) ∧
    0 < history.remainingPortionBefore part original through ∧ original.before releasedAt ∧
    history.firstUnheldFrom a facts part.ref original releasedAt through ∧
    history.resolvesDeadline schedule.postLiftDeadline releasedAt

/-- Permission to use the form's window requires an effective hold at the original deadline. -/
def postLiftWindowApplies (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (part : PaymentPart) (schedule : PaymentSchedule) (releasedAt atTime : Moment) : Prop :=
  postLiftWindowOpened a facts history part schedule releasedAt atTime ∧
    releasedAt.by atTime ∧ schedule.postLiftDeadline.cutoff.metBy atTime ∧
    0 < history.remainingPortionBefore part atTime

/-- Check the selected payment again at actual execution, including every other effective hold. -/
def postLiftPaymentConditions (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (part : PaymentPart) (schedule : PaymentSchedule) (releasedAt : Moment)
    (instruction : PaymentInstruction) : Prop :=
  postLiftWindowApplies a facts history part schedule releasedAt instruction.atTime ∧
    history.payments.validOutstandingPayment part instruction ∧
    ¬history.paymentOnHold a facts part.ref instruction.atTime ∧
    ¬history.paymentHoldScopeUnresolved a facts part.ref instruction.atTime ∧
    instruction.amount ≤ history.remainingPortionBefore part instruction.atTime

def originalApprovalAfterLift (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (original : PaymentApproval) (part : PaymentPart) (schedule : PaymentSchedule)
    (releasedAt : Moment)
    (originalPaymentConditions : PaymentInstruction → Prop) (p : PaymentInstruction) : Prop :=
  postLiftPaymentConditions a facts history part schedule releasedAt p ∧
    history.approvalRecorded original ∧ original.authorisedAtGrant a ∧
    original.originallyCovered (history.versionAt part original.grantedAt p.atTime) ∧
    original.grantedAt.by schedule.originalExecutionDeadline ∧
    original.validAt p.atTime ∧ history.approvalCovers original part p ∧
    p.executor = original.executor ∧ originalPaymentConditions p

def newApprovalRequiredAfterLift (history : HoldHistory) (original : PaymentApproval)
    (part : PaymentPart) (p : PaymentInstruction) : Prop :=
  ¬original.validAt p.atTime ∨ ¬history.approvalCovers original part p

/-- A new approval for a payment still owed comes from the authority current at its grant. -/
def newApprovalAfterLift (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (original replacement : PaymentApproval) (part : PaymentPart) (schedule : PaymentSchedule)
    (releasedAt : Moment)
    (currentPaymentConditions : PaymentInstruction → Prop) (p : PaymentInstruction) : Prop :=
  postLiftPaymentConditions a facts history part schedule releasedAt p ∧
    history.approvalRecorded original ∧ history.approvalRecorded replacement ∧
    original.authorisedAtGrant a ∧
    original.originallyCovered (history.versionAt part original.grantedAt p.atTime) ∧
    original.grantedAt.by schedule.originalExecutionDeadline ∧
    newApprovalRequiredAfterLift history original part p ∧
    replacement.id ≠ original.id ∧ original.grantedAt.before replacement.grantedAt ∧
    replacement.authorisedAtGrant a ∧ replacement.validAt p.atTime ∧
    history.approvalCovers replacement part p ∧ p.executor = replacement.executor ∧
    currentPaymentConditions p

def HoldHistory.noEarlierApprovalFor (history : HoldHistory) (a : ReviewAuthorities) (part : PaymentPart)
    (first : PaymentApproval) (through : Moment := first.grantedAt) : Prop :=
  ∀ old ∈ history.approvals, old ≠ first → old.grantedAt.by first.grantedAt →
    old.authorisedAtGrant a → ¬old.originallyCovered (history.versionAt part old.grantedAt through)

/-- A hold can stop an unpaid portion before the first approval is granted. -/
def firstApprovalAfterLift (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (first : PaymentApproval) (part : PaymentPart) (schedule : PaymentSchedule)
    (releasedAt : Moment)
    (originalPaymentConditions : PaymentInstruction → Prop) (p : PaymentInstruction) : Prop :=
  postLiftPaymentConditions a facts history part schedule releasedAt p ∧
    history.approvalRecorded first ∧ history.noEarlierApprovalFor a part first p.atTime ∧
    schedule.originalExecutionDeadline.before first.grantedAt ∧
    first.authorisedAtGrant a ∧ first.validAt p.atTime ∧
    history.approvalCovers first part p ∧ p.executor = first.executor ∧ originalPaymentConditions p

/-- Record the current authority's approval arrangement within the form's completion period. -/
def approvalArrangementConforms (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (old replacement : PaymentApproval) (part : PaymentPart) (schedule : PaymentSchedule)
    (releasedAt : Moment) (record : NewApprovalArrangement) (p : PaymentInstruction) : Prop :=
  record ∈ history.approvalArrangements ∧
    history.paymentReleasedAt a facts part.ref releasedAt p.atTime ∧
    p.part = part.ref ∧ record.part = part.ref ∧
    record.releasedAt = releasedAt ∧ record.original = old.id ∧
    record.replacement = replacement.id ∧ replacement.id ≠ old.id ∧
    history.approvalRecorded old ∧ old.authorisedAtGrant a ∧
    old.originallyCovered (history.versionAt part old.grantedAt p.atTime) ∧
    history.approvalRecorded replacement ∧ replacement.authorisedAtGrant a ∧
    old.grantedAt.before replacement.grantedAt ∧ replacement.validAt p.atTime ∧
    history.approvalCovers replacement part p ∧ p.executor = replacement.executor ∧
    newApprovalRequiredAfterLift history old part p ∧
    a.approvesPayment part.ref record.arrangedBy record.arrangedAt ∧
    record.arrangedAt.by replacement.grantedAt ∧ replacement.grantedAt.by p.atTime ∧
    history.metDeadline schedule.postLiftDeadline releasedAt record.arrangedAt

structure PostLiftPaymentRecord where
  releasedAt : Moment
  schedule : PaymentSchedule
  originalApproval : Option PaymentApproval
  replacementApproval : Option PaymentApproval
  namedExecutor : ActorId
  approvedOutstandingAtPayment : Amount
  otherHoldsAtPayment : List HoldId
  otherTemporaryAmountsAtPayment : List PaymentPartRef
  paid : PostedPayment
  deriving DecidableEq, Repr

def PostLiftPaymentRecord.usedApproval (record : PostLiftPaymentRecord) : Option PaymentApproval :=
  record.replacementApproval.or record.originalApproval

/-- The actual arrangement for replacing a formerly covering approval is a separate duty. -/
def PostLiftPaymentRecord.approvalArrangementRecorded (row : PostLiftPaymentRecord)
    (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory) (part : PaymentPart) : Prop :=
  ∀ old ∈ row.originalApproval, ∀ replacement ∈ row.replacementApproval,
    ∃ arrangement, approvalArrangementConforms a facts history old replacement part row.schedule
      row.releasedAt arrangement row.paid.instruction

/-- Part 2 of the form records the actual approved amount and payment, with the hold and lift. -/
def postLiftPaymentRecordConforms (a : ReviewAuthorities) (facts : HoldFacts)
    (history : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (record : PostLiftPaymentRecord) : Prop :=
  let p := record.paid.instruction
  (history.factsAt facts p.atTime).isCanonicalPart part ∧ record.schedule = schedule ∧
    history.payments.actualPaymentWithEvidence record.paid ∧
    history.payments.recipientReceived part.recipient record.paid ∧
    history.payments.validOutstandingPayment part p ∧
    postLiftReleaseMatches a facts history part schedule record.releasedAt p.atTime ∧
    record.releasedAt.by p.atTime ∧
    history.resolvesDeadline schedule.postLiftDeadline record.releasedAt ∧
    ¬history.paymentOnHold a facts part.ref p.atTime ∧
    ¬history.paymentHoldScopeUnresolved a facts part.ref p.atTime ∧
    p.amount ≤ history.remainingPortionBefore part p.atTime ∧
    (match record.originalApproval with
    | none => ∃ first ∈ record.replacementApproval, history.noEarlierApprovalFor a part first p.atTime
    | some original => history.approvalRecorded original ∧ original.authorisedAtGrant a ∧
        original.originallyCovered (history.versionAt part original.grantedAt p.atTime) ∧
        original.grantedAt.by schedule.originalExecutionDeadline ∧
        original.grantedAt.before record.releasedAt ∧
        ∀ replacement ∈ record.replacementApproval, replacement.id ≠ original.id ∧
          original.grantedAt.before replacement.grantedAt ∧
          newApprovalRequiredAfterLift history original part p) ∧
    (∃ usedApproval ∈ record.usedApproval, history.approvalRecorded usedApproval ∧
      record.namedExecutor = usedApproval.executor ∧ record.namedExecutor = p.executor ∧
      usedApproval.authorisedAtGrant a ∧ usedApproval.validAt p.atTime ∧
      history.samePayeeAtGrant usedApproval part p.atTime = true ∧
      ∃ entry ∈ usedApproval.scope, entry.covers history.payments part p ∧
        record.approvedOutstandingAtPayment =
          min (history.remainingPortionBefore part p.atTime)
            (entry.remainingBefore history.payments part p.atTime)) ∧
    (∀ id, id ∈ record.otherHoldsAtPayment ↔
      ∃ hold, hold.id = id ∧
        ∃ ref, ref.lesson = part.ref.lesson ∧ ref.obligation = part.ref.obligation ∧ ref.purpose = part.ref.purpose ∧
          history.formalInForce a facts hold ref p.atTime) ∧
    (∀ ref, ref ∈ record.otherTemporaryAmountsAtPayment ↔
      ref.lesson = part.ref.lesson ∧ ref.obligation = part.ref.obligation ∧ ref.purpose = part.ref.purpose ∧
        ∃ temp, history.temporaryInForce a facts temp ref p.atTime)

/-- A payment can still be recorded after an earlier legal or prompt-payment cutoff. -/
def paymentMeetsApplicableDeadlines (a : ReviewAuthorities) (facts : HoldFacts)
    (history : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (release : Option Moment) (payment : PostedPayment) : Prop :=
  let atTime := payment.instruction.atTime
  payment.instruction.part = part.ref ∧ history.payments.actualPaymentWithEvidence payment ∧
    schedule.meetsLegalDeadline atTime ∧
    match release with
    | none => atTime.by schedule.originalExecutionDeadline
    | some releasedAt =>
      history.paymentReleasedAt a facts part.ref releasedAt atTime ∧ releasedAt.by atTime ∧
        (atTime.by schedule.originalExecutionDeadline ∨
          postLiftWindowApplies a facts history part schedule releasedAt atTime) ∧
        (postLiftPromptPaymentDue a facts history part schedule releasedAt atTime →
          history.metDeadline schedule.postLiftDeadline releasedAt atTime)

/-- Timely completion measures the whole retained amount at each applicable cutoff. -/
def paymentCompletedByApplicableDeadlines (a : ReviewAuthorities) (facts : HoldFacts)
    (history : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (release : Option Moment) (through : Moment := release.getD schedule.originalExecutionDeadline) :
    Prop :=
  let complete := fun cutoff ↦ history.fullyRetainedPortionBy part cutoff through
  (history.factsAt facts through).isCanonicalPart part ∧
    (∀ statutory ∈ schedule.legalDeadline, complete statutory) ∧
    match release with
    | none => complete schedule.originalExecutionDeadline
    | some releasedAt =>
      history.paymentReleasedAt a facts part.ref releasedAt through ∧
        (complete schedule.originalExecutionDeadline ∨
          (postLiftWindowOpened a facts history part schedule releasedAt through ∧
            schedule.postLiftDeadline.cutoff.metBy releasedAt ∧
            complete schedule.postLiftDeadline.cutoff)) ∧
        (postLiftPromptPaymentDue a facts history part schedule releasedAt through →
          history.resolvesDeadline schedule.postLiftDeadline releasedAt ∧
          complete schedule.postLiftDeadline.cutoff)

inductive EscalationMatter where
  | reply (concern : ConcernId)
  | review (hold : HoldId)
  | reviewRequest (concern : ConcernId)
  | payment (part : PaymentPartRef)
  deriving DecidableEq, Repr

def deadlineMissed (deadline : Moment) (completedAt : Option Moment) (observedAt : Moment) :
    Prop :=
  deadline.before observedAt ∧ ¬∃ time ∈ completedAt, time.by deadline

structure EscalationNotice where
  caseRef : EscalationMatter
  takenOverBy : ActorId
  takenOverAt : Moment
  responsiblePerson : ActorId
  progress : String
  newActionDate : Moment
  sentTo : List ActorId
  deriving DecidableEq, Repr

structure EscalationAssignment where
  caseRef : EscalationMatter
  assignedBy : ActorId
  assignedTo : ActorId
  assignedAt : Moment
  deriving DecidableEq, Repr

def EscalationAssignment.matches (assignment : EscalationAssignment) (notice : EscalationNotice) : Prop :=
  assignment.caseRef = notice.caseRef ∧ assignment.assignedBy = notice.takenOverBy ∧
    assignment.assignedTo = notice.responsiblePerson ∧
    notice.takenOverAt.by assignment.assignedAt ∧ assignment.assignedAt.by notice.newActionDate

def escalationDetailsConform (terms : ReviewTerms) (m : ReviewMatter)
    (caseRef : EscalationMatter) (notice : EscalationNotice) : Prop :=
  notice.caseRef = caseRef ∧ notice.takenOverBy = terms.escalationContact ∧ notice.progress ≠ "" ∧
  notice.takenOverAt.by notice.newActionDate ∧ (∀ party ∈ m.parties, party ∈ notice.sentTo)

def escalationConforms (terms : ReviewTerms) (m : ReviewMatter)
    (caseRef : EscalationMatter) (deadline : Moment) (completedAt : Option Moment)
    (notice : EscalationNotice) : Prop :=
  deadlineMissed deadline completedAt notice.takenOverAt ∧
  escalationDetailsConform terms m caseRef notice

/-- The agreed date remains on record when an applicable earlier legal limit governs. -/
def deadlineUnderEarlierLaw (agreed : Moment) (legal : Option Moment) : Moment :=
  match legal with
  | none => agreed
  | some limit => if limit.before agreed then limit else agreed

def replyEscalationConforms (l : Lesson) (terms : ReviewTerms) (concern : Concern)
    (facts : ConcernFacts) (publication : ConcernContactPublication) (a : ReviewAuthorities)
    (appointments : List ReviewAppointment) (verifiedCheck : ConcernFactCheck → Prop)
    (namedReviewer : Option ActorId) (initialFindings : List InitialFinding)
    (reviewFindings : List ReviewFinding)
    (actualReplies : List ConcernHandlingRecord) (legalDeadline : Option Moment)
    (notice : EscalationNotice) (assignment : EscalationAssignment) : Prop :=
  concernAccepted l terms facts publication concern ∧
    (terms.finalReplyDeadline.hasPassed notice.takenOverAt ∨
      ∃ law ∈ legalDeadline, law.before notice.takenOverAt) ∧
    escalationDetailsConform terms concern.matter (.reply concern.matter.id) notice ∧
    assignment.matches notice ∧ concern.receivedAt.by notice.takenOverAt ∧
    ¬∃ reply ∈ actualReplies, reply.concern = concern ∧
      reply.recorded l terms facts publication a appointments verifiedCheck
        namedReviewer initialFindings reviewFindings ∧
      reply.response.sentAt.by notice.takenOverAt

def reviewEscalationConforms (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (hold : FormalHold) (decisions : List ReviewFinding) (appointments : List ReviewAppointment)
    (namedReviewer : Option ActorId) (initialFindings : List InitialFinding)
    (legalDeadline : Option Moment) (notice : EscalationNotice) (assignment : EscalationAssignment) : Prop :=
  let terms := facts.terms hold.matter
  history.validFormalHold a facts hold ∧ hold.effectiveAt.by notice.takenOverAt ∧
  facts.termsApply hold.matter ∧
  escalationConforms terms hold.matter (.review hold.id)
    (deadlineUnderEarlierLaw terms.finalReviewDeadline legalDeadline) none notice ∧
  assignment.matches notice ∧
  independentReviewer a hold.matter assignment.assignedTo assignment.assignedAt ∧
  didNotMakeOriginalFinding initialFindings hold.matter assignment.assignedTo assignment.assignedAt ∧
  history.notTemporarySetter a facts hold.matter assignment.assignedTo assignment.assignedAt ∧
  (¬∃ lift ∈ history.lifts, history.validLift a facts hold lift ∧ lift.scope = .all ∧
    lift.effectiveAt.by notice.takenOverAt) ∧
  ¬∃ decision, decision.matter.sameCase hold.matter ∧
    reviewFindingRecordedConforms a namedReviewer appointments initialFindings decisions decision ∧
    history.notTemporarySetter a facts decision.matter decision.reviewer decision.decidedAt ∧
    hold.effectiveAt.by decision.decidedAt ∧ decision.decidedAt.by notice.takenOverAt

def paymentEscalationConforms (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory)
    (matter : ReviewMatter) (part : PaymentPart) (schedule : PaymentSchedule)
    (postLiftCutoff : Moment → Prop × ClockCutoff) (notice : EscalationNotice)
    (assignment : EscalationAssignment) : Prop :=
  let through := notice.takenOverAt
  facts.termsApply matter ∧ part.ref.lesson = matter.lesson ∧
  (history.factsAt facts through).isCanonicalPart part ∧
  assignment.matches notice ∧ 0 < history.remainingPortionBefore part through ∧
  let original := schedule.originalExecutionDeadline
  let heldAtOriginal := fun hold : FormalHold ↦
    history.formalInForce a facts hold part.ref original through
  ∃ deadline : ClockCutoff,
    ((∃ law ∈ schedule.legalDeadline, deadline = .exact law) ∨
      (deadline = .exact original ∧ (¬∃ hold, heldAtOriginal hold) ∧
        ¬history.paymentHoldScopeUnresolved a facts part.ref original through) ∨
      ∃ releasedAt, releasedAt.by notice.takenOverAt ∧
        (postLiftCutoff releasedAt).1 ∧ deadline = (postLiftCutoff releasedAt).2 ∧
        (((¬∃ hold, heldAtOriginal hold) ∧
            ¬history.paymentHoldScopeUnresolved a facts part.ref original through ∧
            postLiftPromptPaymentDue a facts history part schedule releasedAt through) ∨
          postLiftWindowOpened a facts history part schedule releasedAt through)) ∧
    deadline.hasPassed notice.takenOverAt ∧
    escalationDetailsConform (facts.terms matter) matter (.payment part.ref) notice ∧
    deadline.forEveryOrder (fun cutoff ↦
      0 < history.remainingPortionBefore part { cutoff with order := cutoff.order + 1 } through)

end SourceV14
