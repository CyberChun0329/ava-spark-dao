import SourceV14.Review

namespace SourceV14.Workflow.Payment

/-!
Occurrence records for v1.5 §§4.3 and 6.2–6.6 and the confirmation form's payment rows.
The rules for authority, effective holds, due dates and proper recipients still apply to these
records. An observed transfer remains available to §6.3 even when it fails those rules.
-/

/-- A payment-side occurrence, with the record used by the corresponding source check. -/
inductive Event where
  | proposeSettlement (proposal : RecordedOriginalSettlement)
  | approveSettlement (proposal : RecordedOriginalSettlement)
      (approval : OriginalSettlementApproval)
  | grantApproval (approval : PaymentApproval)
  | arrangeApproval (arrangement : NewApprovalArrangement)
  | temporaryHold (hold : TemporaryHold)
  | temporaryNotice (hold : TemporaryHold) (notice : TemporaryHoldNotice)
  | temporaryHandoff (hold : TemporaryHold) (appointment : ReviewAppointment)
  | formalHold (hold : FormalHold)
  | formalNotice (notice : FormalHoldNotice)
  | formalLift (lift : FormalLift)
  | reviewDelay (notice : ReviewDelayNotice)
  | reassess (record : FormalReassessment)
  | reviewEscalation (hold : HoldId) (notice : EscalationNotice) (assignment : EscalationAssignment)
  | post (paid : PostedPayment)
  | agreedRecipient (receipt : AgreedRecipientReceipt)
  | postLiftRecord (record : PostLiftPaymentRecord)
  | returnPayment (returned : ReturnedPayment)
  | escalate (part : PaymentPartRef) (notice : EscalationNotice) (assignment : EscalationAssignment)
  deriving DecidableEq, Repr

/-- Hold decisions occur at their decision time; their effects use their recorded effective time. -/
def Event.atTime : Event → Moment
  | .proposeSettlement proposal => proposal.proposedAt
  | .approveSettlement _ approval => approval.approvedAt
  | .grantApproval approval => approval.grantedAt
  | .arrangeApproval arrangement => arrangement.arrangedAt
  | .temporaryHold hold => hold.effectiveAt
  | .temporaryNotice _ notice => notice.sentAt
  | .temporaryHandoff _ appointment => appointment.appointedAt
  | .formalHold hold => hold.decidedAt
  | .formalNotice notice => notice.sentAt
  | .formalLift lift => lift.decidedAt
  | .reviewDelay notice => notice.sentAt
  | .reassess record => record.reviewedAt
  | .reviewEscalation _ _ assignment => assignment.assignedAt
  | .post paid => paid.instruction.atTime
  | .agreedRecipient receipt => receipt.paid.instruction.atTime
  | .postLiftRecord record => record.paid.instruction.atTime
  | .returnPayment returned => returned.returnedAt
  | .escalate _ _ assignment => assignment.assignedAt

/-- §§4.3, 6.3 and form Part 2. Match both records of this actual account credit.
    The original debit account and filing evidence are checked when applying the refund rules. -/
def refundCreditMatches (paid : PostedPayment) (credit : Booking.CreditPosting) : Prop :=
  let instruction := paid.instruction
  paid.id = credit.id ∧ instruction.atTime = credit.point ∧
    instruction.amount = credit.amount ∧ instruction.destination = .account credit.account ∧
    ∃ place, instruction.part.purpose = .lessonRefund place ∧
      credit.kind = .lessonRefund instruction.part.lesson place instruction.part.obligation

/-- §§4.3 and 6.3. Reverse the very receipt used for the credit, on its actual account. -/
def returnCreditMatches (paid : PostedPayment) (returned : ReturnedPayment)
    (credit : Booking.CreditPosting) : Prop :=
  paid.id = returned.paidReceipt ∧ returned.id = credit.id ∧
    returned.returnedAt = credit.point ∧ returned.amount = credit.amount ∧
    paid.instruction.destination = .account credit.account ∧
    credit.kind = .creditReturned paid.id ∧
    ∃ place, paid.instruction.part.purpose = .lessonRefund place

private def formalHoldDecidedBy (history : HoldHistory) (id : HoldId) (atTime : Moment) : Prop :=
  ∃ hold ∈ history.formal, hold.id = id ∧ hold.decidedAt.by atTime

/-- The steps retain specified occurrences and relate them to the existing records they concern.
    Notices, handoffs and escalation assignments are retained in the labels. -/
inductive Step : HoldHistory → Event → HoldHistory → Prop where
  -- §§6.2 and 6.4. Preserve who actually proposed or approved the original settlement.
  | proposeSettlement {history} (proposal : RecordedOriginalSettlement)
      (proposed : proposal.approvals = [])
      (fresh : ∀ existing ∈ history.originalSettlements,
        existing.matter.sameCase proposal.matter → existing.decision ≠ proposal.decision) :
      Step history (.proposeSettlement proposal)
        { history with originalSettlements := history.originalSettlements ++ [proposal] }

  | approveSettlement {history proposal} (approval : OriginalSettlementApproval)
      (recorded : proposal ∈ history.originalSettlements)
      (afterProposal : proposal.proposedAt.by approval.approvedAt)
      (fresh : approval ∉ proposal.approvals) :
      Step history (.approveSettlement proposal approval)
        { history with
          originalSettlements := history.originalSettlements.map (fun row ↦
            if row = proposal then
              { row with approvals := row.approvals ++ [approval] }
            else row) }

  -- §§6.4 and 6.6 and form Part 2. An arrangement may precede the new grant.
  | grantApproval {history} (approval : PaymentApproval)
      (fresh : approval.id ∉ history.approvals.map PaymentApproval.id) :
      Step history (.grantApproval approval)
        { history with approvals := history.approvals ++ [approval] }

  | arrangeApproval {history} (arrangement : NewApprovalArrangement)
      (original : ∃ approval ∈ history.approvals,
        approval.id = arrangement.original ∧ approval.grantedAt.by arrangement.arrangedAt)
      (fresh : arrangement ∉ history.approvalArrangements) :
      Step history (.arrangeApproval arrangement)
        { history with approvalArrangements := history.approvalArrangements ++ [arrangement] }

  -- §6.2 and form Part 1. Existence of a hold record and its legal effect are separate.
  | temporaryHold {history} (hold : TemporaryHold)
      (fresh : hold ∉ history.temporary) :
      Step history (.temporaryHold hold)
        { history with temporary := history.temporary ++ [hold] }

  | temporaryNotice {history hold} (notice : TemporaryHoldNotice)
      (recorded : hold ∈ history.temporary)
      (sameMatter : notice.matter = hold.matter) (samePart : notice.part = hold.part.ref)
      (afterHold : hold.effectiveAt.by notice.sentAt) :
      Step history (.temporaryNotice hold notice) history

  | temporaryHandoff {history hold} (appointment : ReviewAppointment)
      (recorded : hold ∈ history.temporary) (sameMatter : appointment.matter = hold.matter)
      (afterHold : hold.effectiveAt.by appointment.appointedAt) :
      Step history (.temporaryHandoff hold appointment) history

  | formalHold {history} (hold : FormalHold)
      (fresh : hold.id ∉ history.formal.map FormalHold.id) :
      Step history (.formalHold hold) { history with formal := history.formal ++ [hold] }

  | formalNotice {history} (notice : FormalHoldNotice)
      (recorded : formalHoldDecidedBy history notice.hold notice.sentAt) :
      Step history (.formalNotice notice) history

  | formalLift {history} (lift : FormalLift)
      (recorded : formalHoldDecidedBy history lift.hold lift.decidedAt)
      (fresh : lift ∉ history.lifts) :
      Step history (.formalLift lift) { history with lifts := history.lifts ++ [lift] }

  | reviewDelay {history} (notice : ReviewDelayNotice)
      (recorded : formalHoldDecidedBy history notice.hold notice.sentAt) :
      Step history (.reviewDelay notice) history

  | reassess {history} (record : FormalReassessment)
      (recorded : formalHoldDecidedBy history record.hold record.reviewedAt)
      (sameLift : match record.outcome with
        | .continues _ _ => True
        | .lifts lift => lift ∈ history.lifts ∧
            lift.hold = record.hold ∧ lift.decidedAt = record.reviewedAt) :
      Step history (.reassess record) history

  | reviewEscalation {history id} (notice : EscalationNotice) (assignment : EscalationAssignment)
      (recorded : formalHoldDecidedBy history id notice.takenOverAt)
      (sameNotice : notice.caseRef = .review id)
      (sameAssignment : assignment.caseRef = .review id)
      (afterTakeover : notice.takenOverAt.by assignment.assignedAt) :
      Step history (.reviewEscalation id notice assignment) history

  -- §§4.3, 6.3 and 6.6. Record the amounts actually transferred, with their exact receipt IDs.
  | post {history} (paid : PostedPayment)
      (positive : 0 < paid.instruction.amount)
      (fresh : paid.id ∉ history.payments.posted.map PostedPayment.id) :
      Step history (.post paid)
        { history with payments := { history.payments with
            posted := history.payments.posted ++ [paid] } }

  | agreedRecipient {history} (receipt : AgreedRecipientReceipt)
      (recorded : receipt.paid ∈ history.payments.posted)
      (destination : receipt.paid.instruction.destination = .person receipt.designee)
      (fresh : receipt ∉ history.payments.agreedRecipientReceipts) :
      Step history (.agreedRecipient receipt)
        { history with payments := { history.payments with
            agreedRecipientReceipts := history.payments.agreedRecipientReceipts ++ [receipt] } }

  -- The form row cites the actual receipt. Its payment and release checks use the source rules.
  | postLiftRecord {history} (record : PostLiftPaymentRecord)
      (recorded : record.paid ∈ history.payments.posted) :
      Step history (.postLiftRecord record) history

  | returnPayment {history paid} (returned : ReturnedPayment)
      (recorded : paid ∈ history.payments.posted) (sameReceipt : returned.paidReceipt = paid.id)
      (afterReceipt : paid.instruction.atTime.before returned.returnedAt)
      (positive : 0 < returned.amount)
      (withinReceipt :
        sumAmounts (history.payments.returned.filter (fun row ↦ row.paidReceipt == paid.id))
          ReturnedPayment.amount + returned.amount ≤ paid.instruction.amount)
      (fresh : returned.id ∉ history.payments.returned.map ReturnedPayment.id) :
      Step history (.returnPayment returned)
        { history with payments := { history.payments with
            returned := history.payments.returned ++ [returned] } }

  -- §6.6. Taking over a payment does not change any schedule or obligation.
  | escalate {history part} (notice : EscalationNotice) (assignment : EscalationAssignment)
      (sameNotice : notice.caseRef = .payment part)
      (sameAssignment : assignment.caseRef = .payment part)
      (afterTakeover : notice.takenOverAt.by assignment.assignedAt) :
      Step history (.escalate part notice assignment) history

end SourceV14.Workflow.Payment
