import SourceV14.Workflow.Redress

namespace SourceV14.Workflow.Debt

open Course Confirmation Operations

/-- The verified loss, teaching agreement, and actual decision under §6.5. -/
structure AssessedLoss where
  form : PartOne
  breachedAt : Moment
  loss : TutorBreachLoss
  authorised : LessonId → String → ActorId → Moment → Prop
  finding : TutorLossFinding
  debt : TutorDebtRecord

def AssessedLoss.conforms (row : AssessedLoss) (ev : StartEvidence) : Prop :=
  row.form.matches ∧ row.breachedAt.by row.loss.incurredAt ∧
  row.loss.lesson = { row.form.lesson with
    tutor := row.loss.lesson.tutor, normalTutorFee := row.loss.lesson.normalTutorFee } ∧
  (∃ terms, EffectiveTutorAgreementAt row.form ev row.breachedAt row.loss.lesson.tutor
    row.loss.agreement row.loss.lesson.normalTutorFee terms) ∧
  tutorDebtConforms row.loss.lesson row.loss.agreement row.loss row.authorised row.finding row.debt

structure History where
  losses : List AssessedLoss := []
  collected : List TutorDebtRecovery := []

def History.confirmed (h : History) : List TutorDebtRecord := h.losses.map AssessedLoss.debt

structure RecoveryEvidence where
  refunds : List AssessedFaultRefund
  remedies : List AssessedRemedy
  establishedRedress : LessonId → PlaceId → ObligationId → Prop
  delivered : List CustomerRedressDelivery

/-- The records supporting recovery use the current verified customer ledger and
the retained assessment and delivery for the same lesson and place. The set of
separate agreed redress obligations is supplied as in the direct rule. -/
def RecoveryEvidence.usesHistory (facts : RecoveryEvidence) (history : Redress.History)
    (ev : StartEvidence) : Prop :=
  (∀ refund ∈ facts.refunds,
    refund.faultCase.ledger = ev.ledger ∧
    ∃ earlier ∈ history.assessments,
      earlier.amount.form = refund.faultCase.form ∧ earlier.amount.obligation = refund.faultCase.obligation ∧
      earlier.amount.trigger = refund.trigger ∧ earlier.amount.principal = refund.refund) ∧
  (∀ remedy ∈ facts.remedies,
    remedy.faultCase.ledger = ev.ledger ∧ remedy.faultCase.closed = ev.creditRecords.closed ∧
    ∃ entry ∈ history.remedies, entry.facts.form = remedy.faultCase.form ∧
      history.progress ev entry = remedy.progress)

def AssessedLoss.sameTutorFault (loss : AssessedLoss) (facts : Redress.FaultFacts) : Prop :=
  facts.form.lesson.id = loss.form.lesson.id ∧
  facts.form.lesson.provider = loss.form.lesson.provider ∧
  match facts.fault with
  | .tutor finding _ => finding.tutor = loss.loss.lesson.tutor
  | .provider _ => False

def AssessedLoss.refundConcernsBreach (loss : AssessedLoss) (entry : Redress.AssessedRefund) : Prop :=
  match entry.evidence with
  | .originalCompensation facts _ | .faultRefund facts .. => loss.sameTutorFault facts
  | _ => False

/-- The externally supplied list can include other obligations. It cannot
omit recorded refunds or active remedies for this original teaching fault. -/
def RecoveryEvidence.coversRetained (facts : RecoveryEvidence) (history : Redress.History)
    (ev : StartEvidence) (loss : AssessedLoss) (madeAt : Moment) : Prop :=
  (∀ entry ∈ history.assessments, loss.refundConcernsBreach entry → entry.amount.recordedAt.by madeAt →
    facts.establishedRedress entry.amount.form.lesson.id entry.amount.form.place.id
      entry.amount.obligation) ∧
  (∀ entry ∈ history.remedies, loss.sameTutorFault entry.facts → entry.agreement.acceptedAt.by madeAt →
    ¬ fullRefundClosedBy entry.facts.form.place ev.creditRecords.closed madeAt →
    ∃ assessment ∈ facts.remedies,
      assessment.faultCase.form = entry.facts.form ∧ assessment.progress = history.progress ev entry ∧
      facts.establishedRedress entry.facts.form.lesson.id entry.facts.form.place.id assessment.obligation)

inductive Event where
  | confirm (loss : AssessedLoss)
  | collect (loss : AssessedLoss) (redress : RecoveryEvidence) (receipt : TutorDebtRecovery)

def Event.form : Event → PartOne
  | .confirm loss | .collect loss .. => loss.form

inductive Step (ev : StartEvidence) (redress : Redress.History) : History → Event → History → Prop where
  | confirm {before : History} {loss : AssessedLoss}
      (confirmed : loss.conforms ev)
      (fresh : loss.debt.loss ∉ before.confirmed.map TutorDebtRecord.loss) :
    Step ev redress before (.confirm loss) { before with losses := before.losses ++ [loss] }
  | collect {before : History} {loss : AssessedLoss} {facts : RecoveryEvidence}
      {receipt : TutorDebtRecovery}
      (confirmed : loss ∈ before.losses) (sameRedress : facts.usesHistory redress ev)
      (complete : facts.coversRetained redress ev loss receipt.madeAt)
      (posted : TutorDebtRecoveryPosted loss.form ev loss.loss loss.breachedAt
        loss.authorised loss.finding before.confirmed loss.debt (before.collected ++ [receipt])
        facts.refunds facts.remedies facts.establishedRedress facts.delivered receipt) :
    Step ev redress before (.collect loss facts receipt)
      { before with collected := before.collected ++ [receipt] }

end SourceV14.Workflow.Debt
