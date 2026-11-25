import SourceV14.Review

/-! A lossless grouping of the direct payment and hold evidence, plus separate
proof-carrying observations for one payment part. -/

namespace RecognisedV15

open SourceV14

structure PaymentRestrictions where
  temporary : List TemporaryHold
  formal : List FormalHold
  lifts : List FormalLift
  partRevisions : List HoldPartRevision := []
  deriving DecidableEq, Repr

structure ScopedApprovals where
  approvals : List PaymentApproval
  arrangements : List NewApprovalArrangement
  deriving DecidableEq, Repr

structure SettlementAndClock where
  originalSettlements : List RecordedOriginalSettlement
  clockBoundaries : List ClockBoundary
  deriving DecidableEq, Repr

/-- This groups existing records; it creates no new payment or approval. -/
structure PaymentEvidence where
  payments : PaymentHistory
  restrictions : PaymentRestrictions
  scopedApprovals : ScopedApprovals
  settlementAndClock : SettlementAndClock
  deriving DecidableEq, Repr

namespace PaymentEvidence

def fromDirect (h : HoldHistory) : PaymentEvidence :=
  ⟨h.payments, ⟨h.temporary, h.formal, h.lifts, h.partRevisions⟩,
    ⟨h.approvals, h.approvalArrangements⟩, ⟨h.originalSettlements, h.clockBoundaries⟩⟩

def toDirect (e : PaymentEvidence) : HoldHistory :=
  ⟨e.payments, e.restrictions.temporary, e.restrictions.formal, e.restrictions.lifts,
    e.scopedApprovals.approvals, e.scopedApprovals.arrangements,
    e.settlementAndClock.originalSettlements, e.settlementAndClock.clockBoundaries,
    e.restrictions.partRevisions⟩

@[simp] theorem toDirect_fromDirect (h : HoldHistory) : (fromDirect h).toDirect = h := by
  cases h
  rfl

@[simp] theorem fromDirect_toDirect (e : PaymentEvidence) : fromDirect e.toDirect = e := by
  cases e with
  | mk p r a s => cases r; cases a; cases s; rfl

end PaymentEvidence

/-- Availability under the direct source's original-approval route, for one instruction. -/
structure AvailableOriginalInstruction (e : PaymentEvidence) (a : ReviewAuthorities)
    (facts : HoldFacts) (part : PaymentPart) (schedule : PaymentSchedule)
    (conditions : PaymentInstruction → Prop) where
  approval : PaymentApproval
  instruction : PaymentInstruction
  permitted : originalExecutorMayPay a facts e.toDirect approval part schedule conditions instruction

/-- An evidenced posted execution, including one that was misdirected. -/
structure ExecutedPayment (e : PaymentEvidence) (part : PaymentPart) where
  receipt : PostedPayment
  recorded : e.payments.actualPaymentWithEvidence receipt
  samePart : receipt.instruction.part = part.ref

/-- Credit for this part additionally requires the source's recipient test. -/
structure QualifiedReceipt (e : PaymentEvidence) (part : PaymentPart) extends
    ExecutedPayment e part where
  recipientReceived : e.payments.recipientReceived part.recipient receipt

end RecognisedV15
