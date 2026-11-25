import SourceV14.Workflow.Materials
import SourceV14.Workflow.Redress
import SourceV14.Workflow.Review

namespace SourceV14.Workflow.LessonAccounts

open Booking Confirmation Course Operations

private def agreedValue {α : Type} [DecidableEq α] : List α → Option α
  | [] => none
  | value :: others =>
    if others.all (fun other ↦ decide (other = value)) then some value else none

private structure AmountDecision where
  reference : Option EvidenceRef
  atTime : Moment
  amount : Amount
  part : Option (PaymentPartRef × PaymentRecipient)

private def revises (row : PaymentCorrectionCase)
    (old : AmountDecision) : Bool :=
  decide ((old.reference.isNone ∨ old.reference = some row.correction.originalOutcome) ∧
    (old.part.isNone ∨ old.part = some (row.originalPart.ref, row.originalPart.recipient)) ∧
    old.atTime.by row.finding.decidedAt ∧ old.amount = row.originalPart.amount)

/-- A correction replaces its linked result. Two conflicting, unlinked replacements
leave the amount unresolved. The workflow retains all of their underlying records. -/
private def revisedDecisions (initial : AmountDecision) (revisions : List PaymentCorrectionCase) :
    List AmountDecision × List AmountDecision :=
  revisions.foldl (fun (retained, operative) row ↦
    if retained.any (revises row) then
      let next : AmountDecision :=
        ⟨some row.finding.outcome, row.finding.decidedAt, row.money.corrected.amount,
          some (row.money.corrected.ref, row.money.corrected.recipient)⟩
      (next :: retained, next :: operative.filter (fun old ↦ !revises row old))
    else (retained, operative)) ([initial], [initial])

private def retainedCorrections (review : Review.History) (form : PartOne) (atTime : Moment)
    (purpose : PaymentPurpose) : List PaymentCorrectionCase :=
  (review.paymentCorrections.filter fun row ↦ decide
    (row.correction.lesson = form.lesson.id ∧ row.money.corrected.ref.lesson = form.lesson.id ∧
      row.originalPart.ref.lesson = form.lesson.id ∧ row.originalPart.ref.purpose = purpose ∧
      row.money.corrected.ref.purpose = purpose ∧
      row.finding.decidedAt.by row.correction.recordedAt ∧ row.correction.recordedAt.by atTime)).mergeSort
    (fun earlier later ↦ decide (earlier.finding.decidedAt.by later.finding.decidedAt))

private def retainedRefunds (redress : Redress.History) (form : PartOne) (atTime : Moment) :
    List Redress.AssessedRefund :=
  redress.assessments.filter fun row ↦ decide
    (row.amount.form.lesson.id = form.lesson.id ∧ row.amount.form.place = form.place ∧
      row.amount.recordedAt.by atTime)

/-- Read the amount authorised for this assessment's obligation at the filing cutoff.
    A revision follows its exact original portion. A replacement may change the portion reference;
    the effective portions must remain distinct and owed back to the original account. -/
def refundPrincipalAt (review : Review.History) (refund : Redress.RefundAssessment)
    (query : Moment) : Option Amount :=
  refund.principalAt review query

private def providerReceives (form : PartOne) : PaymentRecipient → Bool
  | .person provider _ => provider == form.lesson.provider
  | .lessonRefund _ => false

private def feeAfterReview (review : Review.History) (form : PartOne)
    (base : Settlement.AdoptedFee) (corrections : List PaymentCorrectionCase) : Option Amount :=
  let originalAmount := base.decision.amounts.feePayable
  let originals := (review.originals.filterMap fun old ↦ old.payment.filter fun part ↦
    decide (old.outcome.outcome = base.reference ∧ old.outcome.matter.lesson = form.lesson.id ∧
      old.outcome.decidedBy = base.decision.handler.actor ∧
      old.outcome.decidedAt = base.decision.decidedAt ∧ part.ref.lesson = form.lesson.id ∧
      part.ref.purpose = .customerFee form.place.id ∧ part.amount = originalAmount) &&
    providerReceives form part.recipient).eraseDups
  match originals with
  | [part] =>
    let initial : AmountDecision :=
      ⟨some base.reference, base.decision.decidedAt, originalAmount,
        some (part.ref, part.recipient)⟩
    let related := corrections.filter fun row ↦
      row.originalPart.ref.obligation == part.ref.obligation &&
        row.money.corrected.ref.obligation == part.ref.obligation
    let effective := (revisedDecisions initial related).2
    if effective.all
        (fun row ↦ row.part.any (fun (_, recipient) ↦ providerReceives form recipient)) then
      agreedValue (effective.map (·.amount))
    else none
  | _ =>
    if corrections.any (fun row ↦ row.correction.originalOutcome == base.reference &&
        row.originalPart.amount == originalAmount &&
        providerReceives form row.originalPart.recipient) then
      none
    else some originalAmount

private def latestRefunds (refunds : List Redress.AssessedRefund) : List Redress.AssessedRefund :=
  refunds.filter fun row ↦
    !refunds.any (fun other ↦ decide (row.amount.trigger.before other.amount.trigger))

private def amountForFeeBasis (basis : Settlement.FeeBasis)
    (fromPlaceDecision fromOrdinaryFee : Option Amount) : Option Amount :=
  match basis with
  | .absence .. | .agreedChange .. | .providerStartedEarly .. => fromPlaceDecision
  | .ordinaryOneToOne .. | .ordinaryGroup .. => fromOrdinaryFee

private def baseTutorPay (base : Settlement.AdoptedFee) : Option Amount :=
  amountForFeeBasis base.decision.basis (some base.decision.amounts.tutorPay) none

private def tutorPay (settlement : Settlement.History) (review : Review.History) (form : PartOne)
    (atTime : Moment) (base : Option Settlement.AdoptedFee) : Option Amount :=
  let tutorDecisions := settlement.tutors.filter fun row ↦ decide
    (row.form.lesson.id = form.lesson.id ∧ form.place ∈ row.forms.map (·.place) ∧
      row.settledAt.by atTime)
  let payoutPart := fun due : Settlement.TutorDue ↦ fun part : PaymentPart ↦
    settlement.tutorPayments.any fun payout ↦ decide
      (payout.settlement.form.lesson.id = due.form.lesson.id ∧
        payout.settlement.form.place = due.form.place ∧
        payout.settlement.agreement.tutor = due.agreement.tutor ∧
        payout.settlement.settledAt = due.settledAt ∧
        payout.receipt.instruction.atTime.by atTime ∧ payout.part.ref = part.ref ∧
        payout.part.recipient = part.recipient)
  let payForPlace := tutorDecisions.map fun due ↦
    let originalOutcome := fun row : PaymentCorrectionCase ↦ review.originals.any fun original ↦
      decide (original.payment = some row.originalPart ∧
        original.outcome.outcome = row.correction.originalOutcome ∧
        original.outcome.matter.lesson = due.assignment.matter.lesson ∧
        original.outcome.matter.id = due.assignment.matter.id ∧
        original.outcome.decidedBy = due.handler.actor ∧ original.outcome.decidedAt = due.settledAt ∧
        row.originalPart.amount = due.net) &&
      row.originalPart.recipient.samePayee (.person due.agreement.tutor none)
    let revisions := retainedCorrections review form atTime (.tutorPay due.agreement.tutor)
    let payableRevisions := revisions.foldl (fun retained row ↦
      let directlyLinked := (due.separatePart == some row.originalPart) ||
        payoutPart due row.originalPart || originalOutcome row
      let successor := retained.any fun earlier ↦ decide
        (earlier.money.corrected = row.originalPart ∧
          earlier.finding.outcome = row.correction.originalOutcome ∧
          earlier.finding.decidedAt.by row.finding.decidedAt)
      if row.originalPart.ref.obligation == row.money.corrected.ref.obligation &&
          (directlyLinked || successor) then
        retained ++ [row]
      else retained) []
    if form.lesson.kind = .oneToOne then
      let initial : AmountDecision := ⟨none, due.settledAt, due.net, none⟩
      let effective := (revisedDecisions initial payableRevisions).2
      agreedValue (effective.map (·.amount))
    else if due.net = due.agreedFee ∧
        (payableRevisions.all (fun row ↦ row.originalPart.amount == row.money.corrected.amount))
        then
      ((due.basis.paymentsByPlace.find? (fun row ↦ row.place == form.place.id)).map (·.tutorPay))
    else none
  if tutorDecisions.isEmpty then base.bind baseTutorPay
  else (payForPlace.mapM id).bind agreedValue

private def originalRefundDue (base : Settlement.AdoptedFee) (file : FiledLessonAccount)
    (fee : Option Amount) : Option Amount :=
  let original := base.decision.amounts
  if fee = some original.feePayable then
    amountForFeeBasis base.decision.basis (some original.creditDueBack)
      (if file.debited ≤ original.feePayable then some 0 else none)
  else none

/-- The materials charges already attributed to this place under §5.3. -/
def materialsChargeAt (form : PartOne) (materials : Materials.History)
    (atTime : Moment) (principal : MaterialsPrincipalContext := {}) : Amount :=
  sumAmountsWhere (materials.recognisedChargesAt form.lesson.id atTime principal)
    (fun row ↦ row.1.place == form.place.id) (fun row ↦ row.1.amount)

def materialsUnresolved (form : PartOne) (materials : Materials.History)
    (atTime : Moment) : Prop :=
  let verified := fun check : Materials.UseCheck ↦ check.use.lesson.id = form.lesson.id ∧
    form.place ∈ check.use.places ∧ check.checkedAt.by atTime
  let accounted := fun (observed basis : Materials.UseCheck) (material : MaterialId)
      (charges : List MaterialsCharge) ↦
    basis.use.lesson.id = form.lesson.id ∧ form.place ∈ basis.use.places ∧
      basis.terms = observed.terms ∧
      (∀ m ∈ observed.use.materialsAt form.place.id, m ∈ basis.use.materialsAt form.place.id) ∧
      ∃ charge ∈ charges, charge.place = form.place.id ∧ charge.material = material
  (form.materialsTermsRef.isSome = true ∧ ¬∃ check ∈ materials.useChecks, verified check) ∨
  (∃ row ∈ materials.provisions, row.form.place = form.place ∧
    row.pending.checkedAt.by atTime ∧
    ¬∃ entitlement ∈ materials.entitlements,
      entitlement.verifiedAt.by atTime ∧ row.pending.resolvedBy entitlement.original.record
        entitlement.verifiedAt) ∨
  (∃ check ∈ materials.useChecks, verified check ∧
    ∃ material ∈ check.use.materialsAt form.place.id,
      ¬(∃ row ∈ materials.originals, row.record.material = material ∧
        row.record.settledAt.by atTime ∧ accounted check row.check material row.record.charges) ∧
      ¬∃ row ∈ materials.shortfalls, row.record.material = material ∧
        row.record.identifiedAt.by atTime ∧
        accounted check row.check material row.additionalCharges)

/-- An amount-changing review of a consolidated materials obligation cannot be
distributed to a place without an established attribution. -/
def reviewedMaterialsPending (form : PartOne) (materials : Materials.History)
    (review : Review.History) (atTime : Moment) (gross : MaterialsGrossEvidence := {}) : Prop :=
  (materials.recognisedChargesAt form.lesson.id atTime ⟨review.paymentCorrections, gross⟩).any
    (fun row ↦ row.1.place == form.place.id && row.2) = true

/-- Part 2 reads the adopted decisions, scoped refund liabilities and verified materials charges
at filing. The ledger check and append belong to the local settlement step. -/
def uses (settlement : Settlement.History) (redress : Redress.History)
    (review : Review.History) (materials : Materials.History) (course : StartEvidence) :
    Settlement.Event → (gross : MaterialsGrossEvidence := {}) → Prop
  | .fileAccount form file, gross =>
    let baseEvidence := fun entry : Settlement.AdoptedFee ↦
      entry.decision.form = form ∧ entry.decision.decidedAt.by file.filedAt ∧
      entry.decision.respectsRecordedGroupAbsence settlement.fees file.filedAt
    ∃ base : Option Settlement.AdoptedFee,
      file.settlementEvidence = base.map (·.reference) ∧
      (∀ entry ∈ base, entry ∈ settlement.fees ∧ baseEvidence entry) ∧
      (base = none → ¬∃ entry ∈ settlement.fees, baseEvidence entry) ∧
      let refundRows := retainedRefunds redress form file.filedAt
      let feeCorrections := retainedCorrections review form file.filedAt
        (.customerFee form.place.id)
      let refunds := refundRows.map fun row ↦
        (row.amount.obligation, refundPrincipalAt review row.amount file.filedAt)
      let feeRows := latestRefunds refundRows
      let fees : Option (List Amount) := feeRows.mapM fun row ↦ row.feeAt review file.filedAt
      let refundFee := fees.bind agreedValue
      let finalFeeFor := fun row : Settlement.AdoptedFee ↦
        let baseFee := feeAfterReview review form row feeCorrections
        if refundRows.isEmpty then baseFee
        else if baseFee = some row.decision.amounts.feePayable then refundFee
        else baseFee.bind fun revised ↦ agreedValue (revised :: refundFee.toList)
      let expectedFee := (base.map finalFeeFor).getD refundFee
      file.refunds = refunds ∧
      (∀ amount, file.feePayable = some amount ↔ expectedFee = some amount ∧
        (∀ other ∈ settlement.fees, baseEvidence other → finalFeeFor other = some amount) ∧
        ∀ row ∈ feeRows, row.feeEvidenceAt redress course review file.filedAt) ∧
      file.creditDueBack = (if refundRows.isEmpty then
        base.bind (fun row ↦ originalRefundDue row file file.feePayable)
        else (refunds.mapM Prod.snd).map fun amounts ↦ sumAmounts amounts id) ∧
      file.tutorPay = tutorPay settlement review form file.filedAt base ∧
      file.materialShare = materialsChargeAt form materials file.filedAt
        ⟨review.paymentCorrections, gross⟩ ∧
      (file.materialsPending = true ↔ materialsUnresolved form materials file.filedAt ∨
        reviewedMaterialsPending form materials review file.filedAt gross)
  | _, _ => True

end SourceV14.Workflow.LessonAccounts
