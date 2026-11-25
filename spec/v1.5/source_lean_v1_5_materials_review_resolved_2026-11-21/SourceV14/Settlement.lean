import SourceV14.Booking

namespace SourceV14.Settlement

open Booking

/-- §4.1 usual settlement needs student, tutor and coordinator confirmation. -/
def OneToOneUsual (l : Lesson) (startRequirementsMet : Prop)
    (studentConfirmed tutorConfirmed coordinatorConfirmed : Bool) : Prop :=
  l.kind = .oneToOne ∧ startRequirementsMet ∧ studentConfirmed = true ∧
    tutorConfirmed = true ∧ coordinatorConfirmed = true

/-- The expiry is a verified point, including its order within its recorded second. -/
def fallbackMature (start expiry query : Moment) : Prop :=
  expiry.seconds = start.seconds + thirtyDays ∧ expiry.by query

def OneToOneVerified (l : Lesson) (start expiry query : Moment)
    (studentConfirmed tutorConfirmed coordinatorConfirmed factsVerified : Bool) : Prop :=
  l.kind = .oneToOne ∧
  (studentConfirmed = false ∨ tutorConfirmed = false ∨ coordinatorConfirmed = false) ∧
  fallbackMature start expiry query ∧ factsVerified = true

/-- §4.2 locks the effective register, including absent students who retain places. -/
structure Roster where
  lesson : LessonId
  reference : Nat
  places : List Place
  lockedAt : Moment
  deriving Repr

def Roster.valid (r : Roster) (l : Lesson) (start : Moment) : Prop :=
  r.lesson = l.id ∧ r.lockedAt.by start ∧
  (∀ p ∈ r.places, p.matches l) ∧
  (r.places.map (·.id)).Nodup ∧ (r.places.map (·.student)).Nodup

def groupCount (r : Roster) (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (attendanceConfirmed faultFound : List PlaceId) (query : Moment) : Nat :=
  (r.places.filter fun place ↦ paidInFull place ledger discounts query &&
    attendanceConfirmed.contains place.id && !faultFound.contains place.id).length

def GroupUsual (l : Lesson) (r : Roster) (start query : Moment)
    (startRequirementsMet : Prop) (tutorReportedCompletion : Bool)
    (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (attendanceConfirmed faultFound : List PlaceId) : Prop :=
  l.kind = .group ∧ r.valid l start ∧ start.by query ∧ startRequirementsMet ∧
  tutorReportedCompletion = true ∧
  r.places.length < 2 * groupCount r ledger discounts attendanceConfirmed faultFound query

def GroupVerified (l : Lesson) (r : Roster) (usual : Prop) (start expiry query : Moment)
    (factsVerified : Bool) : Prop :=
  l.kind = .group ∧ r.valid l start ∧ ¬ usual ∧
    fallbackMature start expiry query ∧ factsVerified = true

/-- For the remaining places after cancellation, absence and fault have been handled. -/
def GroupOrdinaryPlaceFee (p : Place) (l : Lesson) (r : Roster)
    (usualOrVerified paymentInFull : Prop)
    (otherTreatmentApplies paymentOnHold wentAheadAsAgreed serviceAvailable : Bool)
    (fee : Amount) : Prop :=
  l.kind = .group ∧ p.matches l ∧ p ∈ r.places ∧ usualOrVerified ∧ paymentInFull ∧
  otherTreatmentApplies = false ∧ paymentOnHold = false ∧
  wentAheadAsAgreed = true ∧ serviceAvailable = true ∧ fee = p.feePayable

/-- A validly posted reversal subtracts only from its own receipt on this account. -/
def returnedFrom (ledger : List CreditPosting) (receipt : CreditPosting)
    (query : Moment) : Amount :=
  sumAmountsWhere ledger
    (fun e ↦ decide (e.kind = .creditReturned receipt.id ∧ e.account = receipt.account ∧
      receipt.point.before e.point ∧ e.point.by query)) (·.amount)

def debitTotal (p : Place) (ledger : List CreditPosting) (query : Moment) : Amount :=
  sumAmounts (debitEntries p ledger query) (·.amount)

/-- §4.3. Restorations to other accounts do not reduce the refund due. -/
private def matchesRefund (p : Place) (refund : Option Nat) (kind : CreditKind) : Bool :=
  match kind with
  | .lessonRefund lesson place obligation =>
    lesson == p.lesson && place == p.id && (refund.isNone || refund == some obligation)
  | _ => false

def creditsRestoredFor (p : Place) (ledger : List CreditPosting) (query : Moment)
    (refund : Option Nat := none) : Amount :=
  sumAmountsWhere ledger
    (fun e ↦ matchesRefund p refund e.kind && decide (e.account = p.account ∧ e.point.by query))
    (fun receipt ↦ receipt.amount - returnedFrom ledger receipt query)

def refundBalanceDue (p : Place) (ledger : List CreditPosting) (query : Moment)
    (refundTotal : Amount) (refund : Option Nat := none) : Amount :=
  max 0 (refundTotal - creditsRestoredFor p ledger query refund)

/-- Actual credit retained above the assessed amount of this refund. -/
def refundExcessRetained (p : Place) (ledger : List CreditPosting) (query : Moment)
    (refundTotal : Amount) (refund : Nat) : Amount :=
  max 0 (creditsRestoredFor p ledger query (some refund) - refundTotal)

/-- Sum the credit applied to liabilities, excluding excess on each known refund. -/
def creditsAppliedToLessonRefunds (p : Place) (ledger : List CreditPosting) (query : Moment)
    (principals : List (Nat × Amount)) : Amount :=
  creditsRestoredFor p ledger query - sumAmounts principals (fun (refund, principal) ↦
    refundExcessRetained p ledger query principal refund)

def FeeRefundCompleted (p : Place) (ledger : List CreditPosting) (query : Moment)
    (refundTotal : Amount) (refund : Option Nat := none) : Prop :=
  0 ≤ refundTotal ∧ refundBalanceDue p ledger query refundTotal refund = 0

/-- Each represented liability has its own complete restoration to the original account. -/
def RefundPrincipalsRestored (p : Place) (ledger : List CreditPosting) (query : Moment)
    (principals : List (Nat × Amount)) : Prop :=
  (principals.map Prod.fst).Nodup ∧
  ∀ row ∈ principals, FeeRefundCompleted p ledger query row.2 (some row.1)

/-- The ledger contains the actual positive credit for this refund on its original account. -/
def LessonRefundPostingMatches (p : Place) (ledger : List CreditPosting) (receipt : CreditPosting)
    (refund : Nat) : Prop :=
  receipt ∈ ledger ∧ receipt.kind = .lessonRefund p.lesson p.id refund ∧
    receipt.account = p.account ∧ 0 < receipt.amount

/-- A receipt must address the original account and remain within both refund and fee balances. -/
def ValidLessonRefund (p : Place) (ledger : List CreditPosting) (receipt : CreditPosting)
    (refund : Nat) (refundTotal : Amount) (cumulativeLessonFee : Bool)
    (otherPrincipals : List (Nat × Amount) := []) : Prop :=
  let prior := ledger.filter (fun e ↦ decide (e.point.before receipt.point))
  let scope := if cumulativeLessonFee then none else some refund
  LessonRefundPostingMatches p ledger receipt refund ∧
  receipt.amount ≤ refundBalanceDue p prior receipt.point refundTotal scope ∧
  receipt.amount ≤ debitTotal p prior receipt.point -
    creditsAppliedToLessonRefunds p prior receipt.point otherPrincipals

structure LessonSettlement where
  lesson : LessonId
  place : PlaceId
  feePayable : Amount
  debited : Amount
  creditDueBack : Amount
  restored : Amount
  tutorPay : Amount
  materialShare : Amount
  deriving DecidableEq, Repr

def LessonSettlement.matchesPaymentHistory (r : LessonSettlement) (p : Place)
    (ledger : List CreditPosting) (query : Moment) : Prop :=
  r.lesson = p.lesson ∧ r.place = p.id ∧
  r.debited = debitTotal p ledger query ∧ r.restored = creditsRestoredFor p ledger query

/-- The thirty-day tutor-pay condition is distinct from the fallback settlement condition. -/
def TutorPayTime (start expiry query : Moment) (settled agreedPaymentConditions : Prop)
    (earlierLawRequiresPayment : Bool) : Prop :=
  settled ∧ agreedPaymentConditions ∧
  (fallbackMature start expiry query ∨ earlierLawRequiresPayment = true)

def payableTutorTotal (placeFees : List Amount) (applicableDeduction : Amount) : Amount :=
  max 0 (sumAmounts placeFees id - applicableDeduction)

end SourceV14.Settlement
