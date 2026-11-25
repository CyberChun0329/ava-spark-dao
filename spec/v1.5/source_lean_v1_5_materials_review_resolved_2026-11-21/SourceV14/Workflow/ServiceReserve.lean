import SourceV14.Workflow.LessonAccounts
import SourceV14.Workflow.Reserves
import SourceV14.Workflow.TutorFaultHistory

namespace SourceV14.Workflow.ServiceReserve

open Booking Confirmation Course Operations Redress SourceV14.Settlement

/-- The bookkeeper identifies the lesson funds, all payment obligations still
applicable at the transfer, and the issued compensation credit still spendable.
The accounting evidence verifies a current balance net of the earlier reserve
transfers, and supplies the treatment of credit spent from a mixed balance. -/
structure Account where
  funds : CurrentLessonFunds
  obligations : List PaymentPart
  availableCourseCredit : Amount
  priorTransfers : List ServiceReserveTransfer := []

structure Filing where
  form : PartOne
  account : Account
  transfer : ServiceReserveTransfer

def AssessedRefund.concernsFault (assessment : Redress.AssessedRefund) : Bool :=
  match assessment.evidence with
  | .originalCompensation .. | .faultRefund .. => true
  | _ => false

def AssessedRefund.completedAt (assessment : Redress.AssessedRefund)
    (review : Review.History) (ev : StartEvidence) (query : Moment) : Prop :=
  let a := assessment.amount
  a.recordedAt.by query ∧
    ((∃ principal, LessonAccounts.refundPrincipalAt review a query = some principal ∧
      FeeRefundCompleted a.form.place ev.ledger query principal (some a.obligation)) ∨
      fullRefundClosedBy a.form.place ev.creditRecords.closed query)

def AssessedRefund.coversChoice (assessment : Redress.AssessedRefund)
    (request : DirectRefundRequest) (query : Moment) : Prop :=
  request.validFor assessment.amount.form.place ∧
  match assessment.evidence with
  | .faultRefund _ (.direct elected _) _ =>
    elected = request ∧ elected.receivedAt.by query
  | _ => False

/-- Use the known redress of this lesson. Recording an approved remedy or
an assessed refund alone does not discharge it. -/
def dealtWithAt (history : Redress.History) (review : Review.History) (ev : StartEvidence)
    (lesson : LessonId) (query : Moment) : Prop :=
  let remedyApplies := fun row : AcceptedRemedy ↦
    row.agreement.lesson = lesson ∧ row.agreement.acceptedAt.by query
  let refundApplies := fun row : Redress.AssessedRefund ↦
    row.amount.form.lesson.id = lesson ∧ row.amount.recordedAt.by query ∧
      AssessedRefund.concernsFault row = true
  ((∃ row ∈ history.remedies, remedyApplies row) ∨
    ∃ row ∈ history.assessments, refundApplies row ∧
      match row.evidence with
      | .faultRefund .. => True
      | _ => False) ∧
  (∀ row ∈ history.remedies, remedyApplies row →
    (∃ delivered ∈ history.deliveries, delivered.remedy = row.id ∧ delivered.atTime.by query) ∨
      fullRefundClosedBy row.facts.form.place ev.creditRecords.closed query ∨
      ∃ refund ∈ history.assessments, refund.amount.form.place = row.facts.form.place ∧
        AssessedRefund.completedAt refund review ev query ∧
        match refund.evidence with
        | .faultRefund _ (.direct request _) _ =>
          ∀ service ∈ row.agreement.scope,
            remedyRefundSwitch row.facts.form.place row.agreement request service
        | _ => False) ∧
  (∀ row ∈ history.assessments, refundApplies row → AssessedRefund.completedAt row review ev query) ∧
  ∀ request ∈ history.requests, request.lesson = lesson → request.receivedAt.by query →
    ∃ assessment ∈ history.assessments, AssessedRefund.coversChoice assessment request query ∧
      AssessedRefund.completedAt assessment review ev query

private def concernsTutorFinding (facts : FaultFacts) (form : PartOne)
    (finding : TutorFaultFinding) : Prop :=
  facts.form.place = form.place ∧
  match facts.fault with
  | .tutor applied _ => applied = finding
  | .provider _ => False

/-- Redress for a verified tutor fault cannot vanish merely because no refund
assessment has been opened yet. Check each known eligible affected place. -/
def TutorFaultHistory.History.redressRecordedForReserve
    (faults : TutorFaultHistory.History) (history : Redress.History) (review : Review.History)
    (ev : StartEvidence) (lesson : LessonId) (forms : List PartOne) (query : Moment) : Prop :=
  ∀ entry, faults.operativeAt entry query → entry.fault.originalLesson.id = lesson →
    ∀ form ∈ forms, entry.fault.finding.scope.affects form.place.id →
      (∃ attendedAt, entry.evidence.records.originalAttendanceTime lesson form.place.id attendedAt ∧
        attendedAt.by query ∧ ev.paidInFull form attendedAt) →
      fullRefundClosedBy form.place ev.creditRecords.closed query ∨
        (∃ remedy ∈ history.remedies, remedy.agreement.acceptedAt.by query ∧
          concernsTutorFinding remedy.facts form entry.fault.finding) ∨
        ∃ refund ∈ history.assessments, AssessedRefund.completedAt refund review ev query ∧
          match refund.evidence with
          | .faultRefund facts .. => concernsTutorFinding facts form entry.fault.finding
          | _ => False

/-- The fee balance is the verified balance after actual refunds and
disbursements. Deduct only remaining obligations and still-available credits. -/
def Account.transferable (account : Account) (holds : HoldHistory) (point : Moment) :
    Amount :=
  let known := holds.withPartRevisionsKnownAt point
  max 0 (account.funds.amountFrom .lessonFees FundingEntry.available -
    sumAmounts account.obligations (fun part ↦ known.remainingPortionBefore part point) -
    account.availableCourseCredit)

def Filing.conforms (filing : Filing) (verify : Account → ServiceReserveTransfer → Prop)
    (ev : StartEvidence) (redress : Redress.History) (review : Review.History)
    (faults : TutorFaultHistory.History) (holds : HoldHistory) : Prop :=
  let row := filing.transfer
  let account := filing.account
  let f := filing.form
  row.lesson = f.lesson.id ∧ row.provider = f.lesson.provider ∧
  (∃ roster forms, ev.rosterFormsAt f.lesson row.point roster forms ∧ f ∈ forms ∧
    TutorFaultHistory.History.redressRecordedForReserve faults redress review ev
      row.lesson forms row.point) ∧
  verify account row ∧ account.funds.validFor f.lesson ∧ account.funds.checkedAt = row.point ∧
  (account.obligations.map PaymentPart.ref).Nodup ∧
  (∀ part ∈ account.obligations, part.ref.lesson = row.lesson ∧ 0 ≤ part.amount) ∧
  0 ≤ account.availableCourseCredit ∧
  dealtWithAt redress review ev row.lesson row.point ∧
  row.postedAmount = account.transferable holds row.point

end SourceV14.Workflow.ServiceReserve
