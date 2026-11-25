import SourceV14.Common

namespace SourceV14.Booking

/-- §§1.1–1.4. The actors operate in the lesson to which their agreement applies. -/
def InScope (arrangedBySpark independentService : Bool) : Prop :=
  arrangedBySpark = true ∧ independentService = false

def MayDecide (appointed : Bool) (interest : DirectInterest) : Prop :=
  appointed = true ∧ ¬ interest.affected

structure Handler where
  actor : ActorId
  substituteAppointed : Bool
  interest : DirectInterest
  deriving Repr

def Handler.maySettle (h : Handler) (l : Lesson) : Prop :=
  (h.actor = l.coordinator ∨ h.substituteAppointed = true) ∧ ¬ h.interest.affected

def RecusalPerformed (interest : DirectInterest)
    (disclosed steppedAside substituteAppointed : Bool) : Prop :=
  interest.affected →
    disclosed = true ∧ steppedAside = true ∧ substituteAppointed = true

/-- §1.3. Method remains the tutor's choice within the agreed service. -/
def MethodPermitted (meetsAgreedContent meetsAgreedService : Bool) : Prop :=
  meetsAgreedContent = true ∧ meetsAgreedService = true

def TutorArrangementNotice (mustReschedule mustCancel mustHandover contacted : Bool) : Prop :=
  (mustReschedule = true ∨ mustCancel = true ∨ mustHandover = true) → contacted = true

inductive ConfirmationTarget where
  | schedule (lesson : LessonId) (start finish : Moment) (timeZone : String)
  | replacementTutor (lesson : LessonId) (tutor : ActorId)
  deriving DecidableEq, Repr

structure Confirmation where
  target : ConfirmationTarget
  place : PlaceId
  actor : ActorId
  point : Moment
  deriving DecidableEq, Repr

/-- §1.4. Paying on behalf of a place does not name its designated payer. -/
def DesignatedConfirmation (p : Place) (c : Confirmation) : Prop :=
  c.place = p.id ∧ c.actor = p.payer

structure ScheduleApproval where
  target : ConfirmationTarget
  actor : ActorId
  point : Moment
  deriving DecidableEq, Repr

def ScheduleApproval.forActor (c : ScheduleApproval) (actor : ActorId)
    (target : ConfirmationTarget) (agreedAt : Moment) : Prop :=
  c.actor = actor ∧ c.target = target ∧ c.point.by agreedAt

structure Notice where
  target : ConfirmationTarget
  sender : ActorId
  recipient : ActorId
  channel : String
  point : Moment
  deriving DecidableEq, Repr

def NoticePerformed (n : Notice) (target : ConfirmationTarget) (recipient : ActorId)
    (agreedChannel : String) : Prop :=
  n.target = target ∧ n.recipient = recipient ∧ n.channel = agreedChannel

/-- §2.1. Part 1 and the terms it refers to are provided before commitment. -/
def TermsProvidedInTime (formAt termsAt : Moment) (commitments : List Moment)
    (payment : Option Moment) : Prop :=
  (∀ t ∈ commitments, formAt.before t ∧ termsAt.before t) ∧
  (∀ t, payment = some t → formAt.before t ∧ termsAt.before t)

-- §2.3. All lesson charges and returns use the specified credit account.
inductive CreditKind where
  | topUp (receipt : Nat)
  | compensation (original : LessonId) (place : PlaceId)
  | lessonDebit (lesson : LessonId) (place : PlaceId)
  | lessonRefund (lesson : LessonId) (place : PlaceId) (refund : Nat)
  | creditReturned (receipt : Nat)
  | topUpReturn (receipt : Nat)
  deriving DecidableEq, Repr

/-- A posting actually made to an account, at the point it affects available credit. -/
structure CreditPosting where
  id : Nat
  account : AccountId
  kind : CreditKind
  amount : Amount
  point : Moment
  deriving DecidableEq, Repr

def CreditPosting.change (e : CreditPosting) : Amount :=
  match e.kind with
  | .topUp _ | .compensation _ _ | .lessonRefund _ _ _ => e.amount
  | .lessonDebit _ _ | .creditReturned _ | .topUpReturn _ => -e.amount

def balanceBefore (opening : AccountId → Amount) (ledger : List CreditPosting)
    (account : AccountId) (point : Moment) : Amount :=
  opening account + sumAmountsWhere ledger
    (fun e ↦ decide (e.account = account ∧ e.point.before point)) CreditPosting.change

/-- A credit entry alone does not prove that funds were received. -/
structure TopUpReceipt where
  id : Nat
  customer : ActorId
  provider : ActorId
  account : AccountId
  received : Amount
  receivedAt : Moment
  deriving DecidableEq, Repr

def TopUpPerformed (r : TopUpReceipt) (ledger : List CreditPosting) : Prop :=
  ∃ e ∈ ledger, e.kind = .topUp r.id ∧ e.account = r.account ∧
    e.amount = r.received ∧ r.receivedAt.by e.point

/-- The permitted amount in a top-up return comes from its own applicable terms. -/
def TopUpReturnBasis (receipt : TopUpReceipt) (permittedByTerms amount : Amount) : Prop :=
  0 < amount ∧ amount ≤ permittedByTerms ∧ permittedByTerms ≤ receipt.received

/-- A fully discounted place satisfies payment without a debit. -/
structure DiscountRecord where
  lesson : LessonId
  place : PlaceId
  basis : String
  coveredFee : Amount
  point : Moment
  deriving DecidableEq, Repr

def DiscountRecord.covers (d : DiscountRecord) (p : Place) (point : Moment) : Prop :=
  d.lesson = p.lesson ∧ d.place = p.id ∧ d.coveredFee = p.normalFee ∧
    d.point.by point ∧ d.basis ≠ ""

instance (d : DiscountRecord) (p : Place) (point : Moment) : Decidable (d.covers p point) := by
  unfold DiscountRecord.covers
  infer_instance

def hasLessonDebit (p : Place) (ledger : List CreditPosting) (point : Moment) : Bool :=
  ledger.any fun e ↦ decide (e.kind = .lessonDebit p.lesson p.id ∧ e.point.by point)

def DiscountCoversFullFee (p : Place) (ledger : List CreditPosting)
    (discounts : List DiscountRecord) (point : Moment) : Prop :=
  p.feePayable = 0 ∧ hasLessonDebit p ledger point = false ∧ ∃ d ∈ discounts, d.covers p point

def debitEntries (p : Place) (ledger : List CreditPosting) (point : Moment) :
    List CreditPosting :=
  ledger.filter fun e ↦ decide
    (e.kind = .lessonDebit p.lesson p.id ∧ e.account = p.account ∧ e.point.by point)

def paidInFull (p : Place) (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (point : Moment) : Bool :=
  decide (0 < p.normalFee ∧ 0 ≤ p.feePayable ∧ p.feePayable ≤ p.normalFee) &&
    ((decide (p.feePayable = 0) && !hasLessonDebit p ledger point &&
      discounts.any (fun d ↦ decide (d.covers p point))) ||
      decide (0 < p.feePayable ∧
        sumAmounts (debitEntries p ledger point) (·.amount) = p.feePayable))

def PaidInFull (p : Place) (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (point : Moment) : Prop :=
  paidInFull p ledger discounts point = true


def DebitAtConfirmation (p : Place) (opening : AccountId → Amount)
    (prior : List CreditPosting) (e : CreditPosting) (confirmedAt : Moment) : Prop :=
  p.validFees ∧ 0 < p.feePayable ∧
  e.kind = .lessonDebit p.lesson p.id ∧ e.account = p.account ∧
  e.amount = p.feePayable ∧ e.point = confirmedAt ∧
  e.amount ≤ balanceBefore opening prior p.account confirmedAt

-- §§2.2 and 2.5. Agreed date, what actually happens, and reporting are distinct.
structure Schedule where
  lesson : LessonId
  start : Moment
  finish : Moment
  timeZone : String
  agreedAt : Moment
  effectiveAt : Moment
  deriving DecidableEq, Repr

def Schedule.confirmationTarget (s : Schedule) : ConfirmationTarget :=
  .schedule s.lesson s.start s.finish s.timeZone

def Schedule.valid (s : Schedule) : Prop :=
  s.agreedAt.by s.effectiveAt ∧ s.effectiveAt.by s.start ∧
  s.start.before s.finish ∧ s.timeZone ≠ ""

def Schedule.effectiveAtQuery (s : Schedule) (history : List Schedule) (query : Moment) :
    Prop :=
  s ∈ history ∧ s.valid ∧ s.effectiveAt.by query ∧
  ∀ other ∈ history, other.lesson = s.lesson → other.valid →
    other.effectiveAt.by query → other.effectiveAt.by s.effectiveAt

def CancelOneToOne (l : Lesson) (p : Place) (actor : ActorId)
    (request cutoff : Moment) (actualTeachingBegan : Option Moment) : Prop :=
  p.matches l ∧ l.kind = .oneToOne ∧ actor = p.customer ∧ request.by cutoff ∧
  ∀ began, actualTeachingBegan = some began → request.before began

/-- A late proposal or an unagreed date does not change the time. -/
def GroupReschedule (l : Lesson) (roster : List Place) (consents : List Confirmation)
    (next : Schedule) (approvals : List ScheduleApproval) (actualTeachingBegan : Option Moment)
    (tutor : ActorId := l.tutor) : Prop :=
  l.kind = .group ∧ roster ≠ [] ∧ next.lesson = l.id ∧ next.valid ∧
  (∀ actor ∈ [tutor, l.provider], ∃ c ∈ approvals,
    c.forActor actor next.confirmationTarget next.agreedAt) ∧
  (∀ began, actualTeachingBegan = some began → next.agreedAt.before began) ∧
  (∀ p ∈ roster, p.matches l ∧ ∃ c ∈ consents,
    DesignatedConfirmation p c ∧ c.target = next.confirmationTarget ∧
      c.point.by next.agreedAt)

/-- A student who is still taking a confirmed group lesson keeps it on its agreed schedule. -/
def GroupGoesAhead (kind : LessonKind) (confirmed validArrangement : Bool)
    (studentsTakingIt : List ActorId) : Prop :=
  kind = .group ∧ confirmed = true ∧ validArrangement = true ∧ studentsTakingIt ≠ []

def NoFaultCancellation (cannotProceedAsAgreed anyPartyAtFault : Bool)
    (acceptanceDeadline cancellation : Moment) (newAcceptance : Option Moment) : Prop :=
  cannotProceedAsAgreed = true ∧ anyPartyAtFault = false ∧
  acceptanceDeadline.before cancellation ∧
  (∀ t, newAcceptance = some t → acceptanceDeadline.before t)

def noFaultRefund (feeDebited undeliveredAgreedValue : Amount)
    (noneTaught : Bool) : Amount :=
  if noneTaught then feeDebited else min feeDebited undeliveredAgreedValue

structure DeliveryReport where
  lesson : LessonId
  place : PlaceId
  student : ActorId
  coordinator : ActorId
  point : Moment
  servicesReceived : List Nat
  servicesNotReceived : List Nat
  deriving DecidableEq, Repr

structure StudentCompletionReport where
  lesson : LessonId
  place : PlaceId
  student : ActorId
  coordinator : ActorId
  point : Moment
  deriving DecidableEq, Repr

structure AttendanceReport where
  lesson : LessonId
  place : PlaceId
  student : ActorId
  coordinator : ActorId
  point : Moment
  attended : Bool
  deriving DecidableEq, Repr

structure TutorDeliveryReport where
  lesson : LessonId
  tutor : ActorId
  coordinator : ActorId
  point : Moment
  completed : Bool
  details : String
  deriving DecidableEq, Repr

structure StudentFollowUp where
  lesson : LessonId
  place : PlaceId
  coordinator : ActorId
  student : ActorId
  point : Moment
  channel : String
  deriving DecidableEq, Repr

def FollowUpPerformed (followUp : StudentFollowUp) (l : Lesson) (p : Place)
    (after query : Moment) : Prop :=
  p.matches l ∧ followUp.lesson = l.id ∧ followUp.place = p.id ∧
  followUp.coordinator = l.coordinator ∧ followUp.student = p.student ∧
  followUp.channel ≠ "" ∧ after.by followUp.point ∧ followUp.point.by query

/-- §2.5. Both notices and actual payment conditions matter. -/
def StartRequirements (l : Lesson) (roster : List Place)
    (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (start : Moment) : Prop :=
  let prior := ledger.filter (fun e ↦ decide (e.point.before start))
  let available := discounts.filter (fun d ↦ decide (d.point.before start))
  ∀ p ∈ roster, p.matches l ∧ PaidInFull p prior available start

def UnauthorisedStartResponsibility (providerWentAhead startConditionsMet : Bool)
    (verifiedTeachingSettledUnderTerms : Bool) : Prop :=
  providerWentAhead = true ∧ startConditionsMet = false →
    verifiedTeachingSettledUnderTerms = true

inductive PeriodStartEvidence where
  | unknown
  | verifiedNotStarted
  | verifiedStart (began : Moment)
  deriving DecidableEq, Repr

/-- Only periods verified as not yet started use the new time. -/
def LessonPeriodBase (previous next change : Moment) (evidence : PeriodStartEvidence)
    (selected : Moment) : Prop :=
  match evidence with
  | .unknown => False
  | .verifiedNotStarted => selected = next
  | .verifiedStart began =>
    (began.by change ∧ selected = previous) ∨ (change.before began ∧ selected = next)

end SourceV14.Booking
