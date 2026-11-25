import SourceV14.Workflow.MaterialsCombination

/-!
Source workflow for §5 and the materials entries on the v1.5 lesson confirmation.
The direct readers supply the checks on use, allocation, reserves and payment.
-/

namespace SourceV14.Workflow.Materials

open Confirmation Course Operations

/-- The coordinator's verified use for this lesson, distinct from the tutor's list and report. -/
structure UseCheck where
  use : VerifiedMaterialsUse
  terms : MaterialsTerms
  advanceCheck : Option NonstandardMaterialsCheck
  checkedAt : Moment

def UseCheck.matchesCourse (row : UseCheck) (ev : StartEvidence) : Prop :=
  ∃ lesson roster forms, ev.rosterFormsAt lesson row.checkedAt roster forms ∧
    row.use.lesson = { lesson with tutor := row.use.lesson.tutor } ∧
    EffectiveTutorAt lesson ev row.use.startedAt row.use.lesson.tutor ∧
    ev.teachingBegan = some row.use.startedAt ∧ ev.teachingEnded = some row.use.endedAt ∧
    (∀ feedback ∈ row.use.deliveryReports, feedback ∈ ev.afterLesson.serviceFeedback) ∧
    ∀ place ∈ row.use.places, row.use.materialsAt place.id ≠ [] →
      ∃ form ∈ forms, form.place = place ∧
        form.materialsOrBundle = some row.terms.materialsOrBundle ∧
        form.materialsTermsRef = some row.terms.agreementReference ∧
        form.materialsPayer = some row.terms.accountingAndPaymentParty

/-- The original charge and the exact use and terms on which it was established. -/
structure Settlement where
  record : MaterialsSettlementRecord
  check : UseCheck

def Settlement.conforms (row : Settlement) : Prop :=
  let original := row.record
  original.lesson = row.check.use.lesson.id ∧
    original.termsReference = row.check.terms.agreementReference ∧ original.reference ≠ "" ∧
    row.check.use.endedAt.before original.settledAt ∧ row.check.checkedAt.by original.settledAt ∧
    original.places.Nodup ∧
    original.charges = row.check.use.chargesFor row.check.terms original.material ∧
    ∀ charge ∈ original.charges, charge.place ∈ original.places

/-- An authenticated transfer document, retained with its own observation time. -/
structure Transfer where
  material : MaterialId
  record : MaterialsTransferRecord material
  sparkDao : ActorId
  recordedAt : Moment

def Transfer.forMaterial (material : MaterialId) (row : Transfer) :
    Option (MaterialsTransferRecord material) :=
  if same : row.material = material then some (same ▸ row.record) else none

/-- A later check supports a separate shortfall record against the retained original. -/
structure Shortfall where
  original : Settlement
  record : MaterialsShortfall
  check : UseCheck

def Shortfall.conforms (row : Shortfall) (shortfalls : List MaterialsShortfall)
    (principal : MaterialsPrincipalContext := {}) : Prop :=
  let original := row.original.record
  row.record.lesson = original.lesson ∧ row.record.material = original.material ∧
    row.record.termsReference = original.termsReference ∧
    row.record.originalSettlementReference = original.reference ∧ row.record.reference ≠ "" ∧
    row.check.use.lesson.id = original.lesson ∧ row.check.terms = row.original.check.terms ∧
    original.settledAt.before row.record.identifiedAt ∧
    row.check.checkedAt.by row.record.identifiedAt ∧
    row.record.charges = row.record.newCharges original shortfalls
      (row.check.use.chargesFor row.check.terms original.material) principal row.check.use.findings ∧
    ∀ charge ∈ row.check.use.chargesFor row.check.terms original.material,
      charge.place ∈ original.places

/-- Add only the shortfall beyond the original charge for each place. -/
def Shortfall.additionalCharges (row : Shortfall) : List MaterialsCharge :=
  row.record.charges

/-- One holder's recognised amount under the applicable shares for the use or shortfall. -/
structure Entitlement where
  original : Settlement
  shortfall : Option Shortfall
  holder : ActorId
  amount : Amount
  verifiedAt : Moment
  sparkDao : ActorId
  shareHistory : MaterialsShareHistory original.record.material

def Entitlement.check (row : Entitlement) : UseCheck :=
  (row.shortfall.map Shortfall.check).getD row.original.check

def Entitlement.obligation (row : Entitlement) : ObligationId :=
  (row.shortfall.map (·.record.obligation)).getD row.original.record.obligation

def Entitlement.purposeFor (row : Entitlement) (holder : ActorId) : PaymentPurpose :=
  match row.shortfall with
  | none => .materialsShare row.original.record.material holder
  | some entry => .materialsShortfall row.original.record.material holder entry.record.reference

/-- A live provision backed by money already excluded from this funding snapshot. -/
structure ProvisionFundingExclusion where
  key : MaterialsFundingKey
  entry : Nat
  amount : Amount
  evidence : EvidenceRef

/-- Receipt allocation when an aggregate payment or a rights change leaves the scope unclear. -/
structure ProvisionPaymentOverlap where
  originalReference : String
  shortfallReference : Option String
  obligation : ObligationId
  material : MaterialId
  termsReference : String
  amount : Amount
  evidence : EvidenceRef
  deriving DecidableEq

private def ProvisionPaymentOverlap.scope (row : ProvisionPaymentOverlap) :=
  (row.originalReference, row.shortfallReference, row.obligation, row.material, row.termsReference)

/-- The paid instruction, its applicable approval and dates, and funds checked at posting. -/
structure Receipt where
  entitlement : Entitlement
  form : PartOne
  agreedRecipient : Option ActorId
  recipientReceipt : Option AgreedRecipientReceipt
  part : PaymentPart
  paid : PostedPayment
  authority : ReviewAuthorities
  facts : HoldFacts
  approval : PaymentApprovalRoute
  schedule : PaymentSchedule
  dueTrigger : Option PaymentTrigger
  executionTrigger : Option PaymentTrigger
  conditions : PaymentInstruction → Prop
  afterLift : List PostLiftPaymentRecord
  funds : CurrentLessonFunds
  excludedProvisionFunds : List ProvisionFundingExclusion := []
  /-- Verify an exclusion for the still-protected part after the proposed payment. -/
  verifiesProvisionExclusion : CurrentLessonFunds → PostedPayment → ProvisionFundingExclusion →
    Prop := fun _ _ _ ↦ False
  provisionPaymentOverlaps : List ProvisionPaymentOverlap := []
  /-- Verify allocation and actual retained credit for the stated charge and provision keys. -/
  verifiesProvisionOverlap : PaymentHistory → PostedPayment → List PendingMaterialsShare →
    ProvisionPaymentOverlap → Prop := fun _ _ _ _ ↦ False

/-- The time of material verification controls reuse. The administrative filing time
    records a separate action. -/
structure ReceiptRecord where
  paid : PostedPayment
  funds : CurrentLessonFunds
  verifiedAt : Moment
  filedAt : Option Moment

structure History where
  terms : List MaterialsTerms := []
  reports : List TutorMaterialsReport := []
  useChecks : List UseCheck := []
  provisions : List PendingMaterialsFundingRecord := []
  originals : List Settlement := []
  transfers : List Transfer := []
  shortfalls : List Shortfall := []
  entitlements : List Entitlement := []
  receipts : List ReceiptRecord := []
  combinationChecks : List CombinationCheck := []
  /-- Independent evidence that this exact payment and entitlement were associated at this time. -/
  verifiesReceiptAt : PostedPayment → Entitlement → Moment → EvidenceRef → Prop :=
    fun _ _ _ _ ↦ False

def History.canFileReceipt (history : History) (paid : PostedPayment) (filedAt : Moment) : Prop :=
  history.receipts.countP (fun entry ↦ entry.paid.id == paid.id) = 1 ∧
    ∃ entry ∈ history.receipts,
      entry.paid = paid ∧ entry.filedAt = none ∧ entry.verifiedAt.by filedAt

def History.fileReceipt (history : History) (paid : PostedPayment) (filedAt : Moment) : History :=
  { history with receipts := history.receipts.map (fun entry ↦
      if entry.paid == paid then { entry with filedAt := some filedAt } else entry) }

def History.hasVerifiedReceiptAt (history : History) (paid : PostedPayment) (point : Moment) :
    Bool :=
  history.receipts.any (fun entry ↦ entry.paid == paid && decide (entry.verifiedAt.by point))

def History.usesKnownAt (history : History) (lesson : LessonId) (atTime : Moment) :
    List UseCheck :=
  history.useChecks.filter (fun row ↦
    row.use.lesson.id == lesson && decide (row.checkedAt.by atTime))

def UseCheck.coveredThrough (row : UseCheck) (parts : List CombinationPart)
    (atTime : Moment) : Prop :=
  ∀ finding ∈ row.use.findings, finding.usedAt.by atTime →
    ∀ place ∈ row.use.places, place.id = finding.place →
      ∃ part ∈ parts, part.coversUse row.terms place finding.material

def UseCheck.matchesPricing (row : UseCheck) (parts : List CombinationPart) : Prop :=
  ∀ used ∈ row.use.combination, used.materials ≠ [] →
    ∃ part ∈ parts, part.terms = row.terms ∧
      ∃ priced ∈ part.places, priced.place = used.place ∧ priced.materials = used.materials

/-- Each occurrence underlying this charge uses a check covering the known
combination reached at that time. The exact pricing basis for the final
combination was checked before a first use within that combination. -/
def History.checkedNonstandardPricing (history : History) (row : UseCheck)
    (atTime : Moment) : Prop :=
  let known := history.usesKnownAt row.use.lesson.id atTime
  let checked := fun check : CombinationCheck ↦ check.lesson.id = row.use.lesson.id ∧
    check.recordedAt.by atTime
  (∀ finding ∈ row.use.findings,
    ∃ check ∈ history.combinationChecks, checked check ∧ check.checkedAt.before finding.usedAt ∧
      ∃ parts ∈ check.options,
        ∀ actual ∈ known, actual.coveredThrough parts finding.usedAt) ∧
  ∃ check ∈ history.combinationChecks, checked check ∧
    (∃ observed ∈ known, ∃ finding ∈ observed.use.findings,
      check.checkedAt.before finding.usedAt ∧
      ∀ prior ∈ known, prior.terms = observed.terms →
        ∀ used ∈ prior.use.findings, used.place = finding.place →
          used.material = finding.material → finding.usedAt.by used.usedAt) ∧
    ∃ parts ∈ check.options, row.matchesPricing parts ∧
      (∀ actual ∈ known, actual.coveredThrough parts atTime) ∧
      ∀ part ∈ parts, ∀ priced ∈ part.places, ∀ material ∈ priced.materials,
        ∃ actual ∈ known, actual.terms = part.terms ∧ priced.place ∈ actual.use.places ∧
          material ∈ actual.use.materialsAt priced.place.id

def History.pricingAvailable (history : History) (row : UseCheck) (atTime : Moment) : Prop :=
  match row.terms.pricing with
  | .standardBundle _ => row.terms.calculatesVerifiedUse row.use row.advanceCheck atTime
  | .otherCombination .. =>
    row.terms.covers row.use.combination ∧
      (∀ finding ∈ row.use.findings, row.terms.agreedAt.before finding.usedAt) ∧
      history.checkedNonstandardPricing row atTime

private def History.chargeScopes (history : History) (lesson : LessonId) :
    List (MaterialsChargeScope × List MaterialsCharge) :=
  ((history.originals.filter (fun row ↦ row.record.lesson == lesson)).map
    (fun row ↦ (row.record.chargeScope, row.record.grossChargeInputs))) ++
  ((history.shortfalls.filter (fun row ↦ row.record.lesson == lesson)).map
    (fun row ↦ (row.record.chargeScope, row.record.grossChargeInputs row.original.record)))

def History.recognisedChargesAt (history : History) (lesson : LessonId) (atTime : Moment)
    (principal : MaterialsPrincipalContext := {})
    (includeScope : MaterialsChargeScope → Bool := fun _ ↦ true) :
    List (MaterialsCharge × Bool) :=
  (history.chargeScopes lesson).flatMap fun (scope, charges) ↦
    if includeScope scope && decide (scope.establishedAt.by atTime) then
      charges.map (fun charge ↦ principal.chargeAt scope charge atTime)
    else []

@[simp] theorem History.recognisedChargesAt_empty (lesson : LessonId) (atTime : Moment)
    (principal : MaterialsPrincipalContext) (includeScope : MaterialsChargeScope → Bool) :
    ({} : History).recognisedChargesAt lesson atTime principal includeScope = [] := rfl

/-- §5.3 limits the combined charges for this lesson, counting each place's normal fee once. -/
def History.combinedCapAllows (history : History) (lesson : LessonId)
    (additional : List MaterialsCharge) (atTime : Moment)
    (principal : MaterialsPrincipalContext := {}) : Prop :=
  let bounds := (history.chargeScopes lesson).mapM fun (scope, charges) ↦
    principal.grossUpperBoundAt scope charges atTime
  let uses := (history.usesKnownAt lesson atTime).flatMap (·.use.combination)
  bounds.any (fun established ↦ decide
    (sumAmounts established id + sumAmounts additional MaterialsCharge.amount ≤
      materialsCapRate * materialsCapBase uses)) = true

private def budgetKey (pending : PendingMaterialsShare) : MaterialsFundingKey :=
  ⟨pending.lesson, pending.place, pending.material, pending.termsReference⟩

private def budgetMatchesOriginal (key : MaterialsFundingKey)
    (original : MaterialsSettlementRecord) : Bool :=
  key.lesson == original.lesson && key.material == original.material &&
    key.termsReference == original.termsReference &&
    original.charges.any (·.place == key.place)

private def History.materialChargeFor (history : History) (key : MaterialsFundingKey)
    (checkedAt : Moment) (principal : MaterialsPrincipalContext) : Amount × Bool :=
  let charges := history.recognisedChargesAt key.lesson checkedAt principal
    (fun scope ↦ key.material == scope.material && key.termsReference == scope.termsReference)
  let here := charges.filter (fun row ↦ row.1.place == key.place)
  (sumAmounts here (fun row ↦ row.1.amount), here.any Prod.snd)

/-- A provision can cease to count after all shares of the retained original charge
    are accounted for and actually received. Where a known transfer or shortfall
    complicates that reconciliation, retain the provision until re-estimated. -/
noncomputable def History.paidOriginalCharge (history : History) (payments : PaymentHistory)
    (estimate : PendingMaterialsShare) (checkedAt : Moment)
    (principal : MaterialsPrincipalContext := {}) : Bool :=
  let key := budgetKey estimate
  let verifiedPayments := payments.posted.filter (fun paid ↦
    paid.evidence.isSome && decide (estimate.checkedAt.before paid.instruction.atTime) &&
      history.hasVerifiedReceiptAt paid checkedAt)
  history.originals.any (fun row ↦
    let original := row.record
    let governingTransfers := history.transfers.filter (fun transfer ↦
      transfer.material == key.material && decide (transfer.recordedAt.by checkedAt) &&
      decide (transfer.record.transfer.effectiveAt.by checkedAt) &&
      original.charges.any (fun charge ↦ @decide
        (transfer.record.governs original.lesson original.reference charge.place)
        (Classical.propDecidable _)))
    -- A governing transfer changes uncollected shares; a verified receipt from before
    -- its effective time still counts. Reconcile any later receipts separately.
    let recordedPayments := { payments with posted := verifiedPayments.filter (fun paid ↦
      governingTransfers.all (fun transfer ↦
        decide (paid.instruction.atTime.before transfer.record.transfer.effectiveAt))) }
    let shares := history.entitlements.filter (fun entitlement ↦
      let basis := entitlement.original.record
      entitlement.shortfall.isNone && decide (entitlement.verifiedAt.by checkedAt) &&
        basis.lesson == original.lesson && basis.material == original.material &&
        basis.termsReference == original.termsReference && basis.reference == original.reference &&
        basis.obligation == original.obligation)
    budgetMatchesOriginal key original && decide (original.settledAt.by checkedAt) &&
      -- The original payee totals alone cannot reconcile a revised portion.
      !(principal.reviewsFor original.chargeScope checkedAt |>.any (fun review ↦
        review.originalPart != review.money.corrected)) &&
      !(history.shortfalls.any (fun shortfall ↦
        shortfall.record.lesson == original.lesson &&
          shortfall.record.material == original.material &&
          shortfall.record.termsReference == original.termsReference &&
          shortfall.record.originalSettlementReference == original.reference &&
          decide (shortfall.record.identifiedAt.by checkedAt) &&
          shortfall.additionalCharges.any
            (fun charge ↦ charge.place == key.place && decide (0 < charge.amount)))) &&
      !shares.isEmpty && decide ((shares.map Entitlement.holder).Nodup) &&
      sumAmounts shares Entitlement.amount == sumAmounts original.charges MaterialsCharge.amount &&
      shares.all (fun entitlement ↦ entitlement.shareHistory.amendments.isEmpty &&
        recordedPayments.remainingObligationBefore original.lesson original.obligation
          (.person entitlement.holder none) entitlement.amount checkedAt
          (some (entitlement.purposeFor entitlement.holder)) == 0))

private noncomputable def History.operativeProvisionsAt (history : History)
    (payments : PaymentHistory) (lesson : LessonId) (checkedAt : Moment)
    (principal : MaterialsPrincipalContext) :
    List PendingMaterialsShare :=
  let estimates := (history.provisions.map (·.pending)).filter (fun row ↦
    row.lesson == lesson && decide (row.checkedAt.by checkedAt))
  let operative := estimates.filter (fun row ↦ !estimates.any (fun later ↦
    budgetKey later == budgetKey row && decide (row.checkedAt.before later.checkedAt)))
  operative.filter (fun row ↦ !history.paidOriginalCharge payments row checkedAt principal)

/-- Keep the operative estimates for this lesson at the check, including any
    established charge still protected by an estimate. -/
noncomputable def History.liveMaterialBudgetsAt (history : History) (payments : PaymentHistory)
    (lesson : LessonId) (checkedAt : Moment) (principal : MaterialsPrincipalContext := {}) :
    List (MaterialsFundingKey × Amount) :=
  (history.operativeProvisionsAt payments lesson checkedAt principal).map
    (fun row ↦
      let key := budgetKey row
      (key, max row.budget (history.materialChargeFor key checkedAt principal).1))

/-- Check both independent pending amounts and their interaction with each joint booking
    case. Current receipts reduce an outstanding booked expense for its own obligation. -/
def History.provisionBudgetAllows (history : History) (ev : StartEvidence)
    (payments : PaymentHistory) (row : PendingMaterialsFundingRecord)
    (principal : MaterialsPrincipalContext := {}) : Prop :=
  let checkedAt := row.funds.checkedAt
  let budgets := history.liveMaterialBudgetsAt payments row.pending.lesson checkedAt principal
  let teachingHasBegun := ∃ began ∈ ev.teachingBegan, began.by checkedAt
  row.funds.secures (sumAmounts budgets Prod.snd) ∧
  ∀ (f : PartOne) (booking : BookingEvidence), (f, booking) ∈ ev.bookings →
    f.lesson = row.form.lesson → f.confirmedAt.by checkedAt →
    ∀ roster, ev.readsBookedRoster f ev.groupRoster checkedAt roster →
      let places := (roster.map (·.places)).getD [f.place]
      let recheck : FundingCheck := ⟨{ booking.funding.terms with payments }, row.funds⟩
      recheck.casesSecuredWithMaterials f.lesson places budgets teachingHasBegun

/-- A check filed out of order also changes the known budgets at any later retained check.
    Use that check's own funds and time. -/
def History.provisionsStillCovered (history : History) (ev : StartEvidence)
    (payments : PaymentHistory) (row : PendingMaterialsFundingRecord)
    (principal : MaterialsPrincipalContext := {}) : Prop :=
  let updated := { history with provisions := row :: history.provisions }
  ∀ later ∈ history.provisions, later.pending.lesson = row.pending.lesson →
    row.pending.checkedAt.before later.pending.checkedAt →
    updated.provisionBudgetAllows ev payments later principal

/-- Recording controls evidence availability. The share reader applies the transfer's own terms
    and effective time to the payment in question. -/
def History.shareEvidence (history : History) (row : Entitlement) (knownAt : Moment) :
    MaterialsShareEvidence row.original.record.material where
  originalSettlementReference := row.original.record.reference
  originalSettlementAt := row.original.record.settledAt
  entitlementVerifiedAt := row.verifiedAt
  advanceCheck := row.check.advanceCheck
  sparkDao := row.sparkDao
  transfers := (history.transfers.filter (fun transfer ↦ decide
    (transfer.recordedAt.by knownAt))).filterMap
      (Transfer.forMaterial row.original.record.material)
  shortfall := row.shortfall.map Shortfall.record
  shareHistory := row.shareHistory

def Entitlement.retainedBasis (row : Entitlement) (history : History) : Prop :=
  row.original ∈ history.originals ∧
    ∀ shortfall ∈ row.shortfall, shortfall ∈ history.shortfalls ∧ shortfall.original = row.original

def History.pendingProvisionRecorded (history : History) (ev : StartEvidence)
    (row : Entitlement) : Prop :=
  ∀ prior ∈ history.provisions.map PendingMaterialsFundingRecord.pending,
    prior.resolvedBy row.original.record row.verifiedAt → prior.status.provisionRequired →
    ∃ funding ∈ history.provisions, funding.pending = prior ∧
      (∃ roster forms, ev.rosterFormsAt funding.form.lesson funding.funds.checkedAt roster forms ∧
        funding.form ∈ forms) ∧
      PendingMaterialsProvision funding.form row.check.terms funding.pending
        funding.otherAmountsOwed funding.funds funding.verifiedEstimate

/-- Earlier designated recipients are resolved from the receipt-specific shared ledger entries. -/
def Entitlement.collectionsMatch (row : Entitlement) (history : History)
    (payments : PaymentHistory) : Prop :=
  (history.shareEvidence row row.verifiedAt).collectionsMatch
    row.check.use row.check.terms row.verifiedAt
    (fun holder point ↦ payments.receivedForObligationBefore row.original.record.lesson
      row.obligation (.person holder none) point (some (row.purposeFor holder)))

/-- The same single receipt used by the local payment reader is appended to the shared ledger. -/
def withReceipt (history : HoldHistory) (paid : PostedPayment) : HoldHistory :=
  { history with payments := { history.payments with posted := history.payments.posted ++ [paid] } }

def Receipt.postingHistory (row : Receipt) (holds : HoldHistory) : HoldHistory :=
  let next := withReceipt holds row.paid
  match row.recipientReceipt with
  | none => next
  | some recipient =>
    { next with payments := { next.payments with
        agreedRecipientReceipts := next.payments.agreedRecipientReceipts ++ [recipient] } }

def Receipt.recipientMatches (row : Receipt) (holds : HoldHistory) : Prop :=
  ∀ recipient ∈ row.recipientReceipt,
    recipient ∈ holds.payments.agreedRecipientReceipts ∧ recipient.paid = row.paid ∧
    recipient.payee = row.entitlement.holder ∧ row.agreedRecipient = some recipient.designee ∧
    row.paid.instruction.destination = .person recipient.designee ∧
    recipient.agreedAt.by row.paid.instruction.atTime ∧
    ∀ ceased ∈ recipient.ceasedAt, row.paid.instruction.atTime.before ceased

def Receipt.provisionFundsOutsideAvailable (row : Receipt) (entry : Nat) : Amount :=
  sumAmountsWhere row.excludedProvisionFunds (·.entry == entry) (·.amount)

private structure ProvisionCharge where
  scope : MaterialsChargeScope
  originalObligation : ObligationId
  charges : List MaterialsCharge
  pending : Bool
  use : VerifiedMaterialsUse

private def History.provisionChargesAt (history : History) (lesson : LessonId)
    (atTime : Moment) (principal : MaterialsPrincipalContext) : List ProvisionCharge :=
  let charge := fun scope original charges use ↦
    let gross := charges.map (fun row ↦ principal.chargeAt scope row atTime)
    (⟨scope, original, gross.map Prod.fst, gross.any Prod.snd, use⟩ : ProvisionCharge)
  ((history.originals.filter (fun row ↦ row.record.lesson == lesson &&
    decide (row.record.settledAt.by atTime))).map (fun row ↦
      charge row.record.chargeScope row.record.obligation row.record.grossChargeInputs
        row.check.use)) ++
    (history.shortfalls.filter (fun row ↦ row.record.lesson == lesson &&
      decide (row.record.identifiedAt.by atTime))).map (fun row ↦
        charge row.record.chargeScope row.original.record.obligation
          (row.record.grossChargeInputs row.original.record) row.check.use)

private def ProvisionCharge.keyFor (scope : ProvisionCharge) (place : PlaceId) :
    MaterialsFundingKey :=
  ⟨scope.scope.lesson, place, scope.scope.material, scope.scope.termsReference⟩

private def ProvisionCharge.payee (scope : ProvisionCharge) (paid : PostedPayment) :
    Option ActorId :=
  let part := paid.instruction.part
  if scope.scope.matchesPart part then
    match part.purpose with
    | .materialsShare _ holder | .materialsShortfall _ holder _ => some holder
    | _ => none
  else none

private def ProvisionCharge.matchesEntitlement (scope : ProvisionCharge) (row : Entitlement) :
    Bool :=
  let entScope := (row.shortfall.map (·.record.chargeScope)).getD row.original.record.chargeScope
  scope.scope == entScope && scope.originalObligation == row.original.record.obligation

private def ProvisionCharge.priorPayments (scope : ProvisionCharge) (history : History)
    (payments : PaymentHistory) (atTime : Moment) : List PostedPayment :=
  payments.posted.filter fun paid ↦
    paid.evidence.isSome && decide (paid.instruction.atTime.before atTime) &&
      history.hasVerifiedReceiptAt paid atTime &&
      (scope.payee paid).any (fun holder ↦
        decide (payments.recipientReceived (.person holder none) paid))

private def ProvisionCharge.retainedPriorAmount (scope : ProvisionCharge) (history : History)
    (payments : PaymentHistory) (atTime : Moment) (includePayment : PostedPayment → Bool) : Amount :=
  sumAmounts ((scope.priorPayments history payments atTime).filter includePayment)
    (fun paid ↦ paid.retainedAmountBefore payments.returned atTime)

/-- A late-recorded rights change can affect which earlier cash discharges this expense. -/
private noncomputable def ProvisionCharge.needsReceiptAllocation (scope : ProvisionCharge)
    (history : History) (paid : PostedPayment) (atTime : Moment)
    (principal : MaterialsPrincipalContext) : Bool :=
  (principal.reviewsFor scope.scope atTime).any (fun review ↦
    review.originalPart != review.money.corrected &&
      (review.originalPart.ref == paid.instruction.part ||
        review.money.corrected.ref == paid.instruction.part)) ||
  history.transfers.any (fun transfer ↦ transfer.material == scope.scope.material &&
    decide (transfer.recordedAt.by atTime) &&
    decide (transfer.record.transfer.effectiveAt.by paid.instruction.atTime) &&
    scope.charges.any (fun charge ↦
      scope.use.findings.any (fun finding ↦
        finding.place == charge.place && finding.material == scope.scope.material &&
        decide (finding.usedAt.before transfer.record.transfer.effectiveAt)) &&
      @decide (transfer.record.governs scope.scope.lesson scope.scope.originalReference charge.place)
        (Classical.propDecidable _))) ||
  history.entitlements.any (fun row ↦ scope.matchesEntitlement row &&
    decide (row.verifiedAt.by atTime) &&
    row.shareHistory.amendments.any (fun change ↦
      decide (change.replacement.effectiveAt.by paid.instruction.atTime) &&
      scope.charges.any (fun charge ↦
        change.replacement.scope == (scope.scope.lesson, charge.place))))

private def ProvisionCharge.matchesOverlap (scope : ProvisionCharge)
    (overlap : ProvisionPaymentOverlap) : Bool :=
  overlap.scope == (scope.scope.originalReference, scope.scope.shortfallReference,
    scope.scope.obligation, scope.scope.material, scope.scope.termsReference)

private def ProvisionCharge.thisPayment (scope : ProvisionCharge) (row : Receipt) : Amount :=
  if scope.matchesEntitlement row.entitlement && scope.payee row.paid == some row.entitlement.holder
  then row.paid.instruction.amount else 0

private def ProvisionCharge.includes (scope : ProvisionCharge) (estimate : PendingMaterialsShare) :
    Bool :=
  scope.charges.any (fun charge ↦
    scope.keyFor charge.place == budgetKey estimate && decide (0 < charge.amount))

private def History.provisionAmount (history : History) (estimate : PendingMaterialsShare)
    (atTime : Moment) (principal : MaterialsPrincipalContext) : Amount :=
  let key := budgetKey estimate
  let (known, pending) := history.materialChargeFor key atTime principal
  if !pending && history.originals.any (fun row ↦ budgetMatchesOriginal key row.record &&
    decide (estimate.checkedAt.by row.record.settledAt ∧ row.record.settledAt.by atTime)) then known
  else max estimate.budget known

private def ProvisionCharge.chargeWithin (scope : ProvisionCharge)
    (estimates : List PendingMaterialsShare) : Amount :=
  sumAmountsWhere scope.charges (fun charge ↦
    estimates.any (fun estimate ↦ scope.keyFor charge.place == budgetKey estimate)) (·.amount)

private noncomputable def ProvisionCharge.knownOverlap (scope : ProvisionCharge)
    (history : History) (payments : PaymentHistory) (row : Receipt)
    (estimates : List PendingMaterialsShare) (principal : MaterialsPrincipalContext) : Amount :=
  let atTime := row.paid.instruction.atTime
  let covered := estimates.filter scope.includes
  let received := scope.retainedPriorAmount history payments atTime (fun paid ↦
    covered.all (fun estimate ↦ decide (estimate.checkedAt.before paid.instruction.atTime)) &&
      !scope.needsReceiptAllocation history paid atTime principal)
  let inside := scope.chargeWithin covered
  let outside := sumAmounts scope.charges (·.amount) - inside
  if scope.pending then 0
  else min inside (max 0 (received + scope.thisPayment row - outside))

private def ProvisionCharge.verifiedOverlap (scope : ProvisionCharge) (row : Receipt) : Amount :=
  sumAmountsWhere row.provisionPaymentOverlaps scope.matchesOverlap (·.amount)

/-- Protect the balance of each live provision after crediting cash for the same charge.
    A grouped receipt establishes at least the excess over charges outside those provisions. -/
def Receipt.protectsProvisions (row : Receipt) (history : History) (payments : PaymentHistory)
    (principal : MaterialsPrincipalContext := {}) : Prop :=
  let atTime := row.paid.instruction.atTime
  let lesson := row.form.lesson.id
  let estimates := history.operativeProvisionsAt payments lesson atTime principal
  let scopes := (history.provisionChargesAt lesson atTime principal).filter
    (fun scope ↦ estimates.any scope.includes)
  let known := fun (scope : ProvisionCharge) ↦
    scope.knownOverlap history payments row estimates principal
  let remaining := sumAmounts estimates (fun estimate ↦
    history.provisionAmount estimate atTime principal) -
    sumAmounts scopes (fun scope ↦ max (known scope) (scope.verifiedOverlap row))
  let excluded := sumAmounts row.excludedProvisionFunds (·.amount)
  (row.provisionPaymentOverlaps.map ProvisionPaymentOverlap.scope).Nodup ∧
  (∀ overlap ∈ row.provisionPaymentOverlaps,
    0 < overlap.amount ∧ row.verifiesProvisionOverlap payments row.paid estimates overlap ∧
      ∃ scope ∈ scopes, scope.matchesOverlap overlap = true ∧
        let matching := estimates.filter scope.includes
        let received := scope.retainedPriorAmount history payments atTime (fun paid ↦
          matching.any (fun estimate ↦ decide (estimate.checkedAt.before paid.instruction.atTime)))
        overlap.amount ≤ min (scope.chargeWithin matching) (received + scope.thisPayment row)) ∧
  (row.excludedProvisionFunds.map (fun entry ↦ (entry.entry, entry.key))).Nodup ∧
  (∀ entry ∈ row.excludedProvisionFunds,
    0 < entry.amount ∧ row.verifiesProvisionExclusion row.funds row.paid entry ∧
      (∃ estimate ∈ estimates, budgetKey estimate = entry.key ∧
        sumAmountsWhere row.excludedProvisionFunds (·.key == entry.key) (·.amount) ≤
          history.provisionAmount estimate atTime principal - sumAmounts scopes (fun scope ↦
            scope.knownOverlap history payments row [estimate] principal)) ∧
      ∃ funds ∈ row.funds.entries, funds.id = entry.entry ∧ funds.availability = .spendable ∧
        row.provisionFundsOutsideAvailable funds.id ≤ funds.committedElsewhere) ∧
  excluded ≤ remaining ∧
  row.funds.covers (row.paid.instruction.amount + (remaining - excluded))

/-- Verify the share as of actual payment using transfer evidence available at `knownAt`. -/
def Receipt.conformsAt (row : Receipt) (history : History) (ev : StartEvidence)
    (holds : HoldHistory) (knownAt : Moment) (observed : Bool := false)
    (principal : MaterialsPrincipalContext := {}) : Prop :=
  let entitlement := row.entitlement
  let check := entitlement.check
  row.part.ref.purpose = entitlement.purposeFor entitlement.holder ∧
    row.paid.id ∉ history.receipts.map (·.paid.id) ∧
    row.recipientMatches holds ∧
    MaterialsPaymentPosted row.form ev check.use check.terms entitlement.original.record.material
      entitlement.holder (history.shareEvidence entitlement knownAt) entitlement.original.record
      (history.originals.map Settlement.record) (history.shortfalls.map Shortfall.record)
      (history.provisions.map PendingMaterialsFundingRecord.pending) history.provisions
      (history.pendingProvisionRecorded ev entitlement) entitlement.amount row.agreedRecipient
      (fun _ _ ↦ none) row.part row.paid holds row.authority row.facts row.approval row.schedule
      row.dueTrigger row.executionTrigger row.conditions row.afterLift
      (FiledPaymentOnTime row.form row.authority row.facts holds row.part row.schedule
        row.paid row.afterLift)
      (FiledPaymentCompletedOnTime row.form row.authority row.facts holds row.part row.schedule
        row.afterLift)
      row.funds knownAt observed (entitlement.retainedBasis history) principal

def Receipt.conforms (row : Receipt) (history : History) (ev : StartEvidence)
    (holds : HoldHistory) (principal : MaterialsPrincipalContext := {}) : Prop :=
  row.entitlement ∈ history.entitlements ∧
    row.conformsAt history ev holds row.paid.instruction.atTime (principal := principal) ∧
    row.protectsProvisions history holds.payments principal

/-- Substantive verification of an existing ledger receipt, using evidence available by
    `verifiedAt` and testing the entitlement as of the actual payment. -/
def Receipt.observedAt (row : Receipt) (history : History) (ev : StartEvidence)
    (holds : HoldHistory) (verifiedAt : Moment)
    (principal : MaterialsPrincipalContext := {}) : Prop :=
  row.paid ∈ holds.payments.posted ∧
    row.paid.instruction.atTime.by verifiedAt ∧
    row.entitlement.retainedBasis history ∧
    history.pendingProvisionRecorded ev row.entitlement ∧
    row.conformsAt history ev holds verifiedAt true principal

/-- Each event names the single record added by the corresponding local transition. -/
inductive Event where
  | adopt (lesson : Lesson) (terms : MaterialsTerms)
  | report (lesson : Lesson) (report : TutorMaterialsReport)
  | checkCombination (row : CombinationCheck)
  | verify (row : UseCheck)
  | provision (terms : MaterialsTerms) (row : PendingMaterialsFundingRecord)
  | settle (row : Settlement)
  | transfer (row : Transfer)
  | identifyShortfall (row : Shortfall)
  | establish (row : Entitlement)
  | post (row : Receipt)
  | verifyReceipt (row : Receipt) (verifiedAt : Moment) (reference : EvidenceRef)
  | file (paid : PostedPayment) (filedAt : Moment)

def Event.atTime : Event → Moment
  | .adopt _ terms => terms.agreedAt
  | .report _ row => row.reportedAt
  | .checkCombination row => row.recordedAt
  | .verify row => row.checkedAt
  | .provision _ row => row.pending.checkedAt
  | .settle row => row.record.settledAt
  | .transfer row => row.recordedAt
  | .identifyShortfall row => row.record.identifiedAt
  | .establish row => row.verifiedAt
  | .post row => row.paid.instruction.atTime
  | .verifyReceipt _ verifiedAt _ => verifiedAt
  | .file _ filedAt => filedAt

def Event.receipt : Event → Option PostedPayment
  | .post row | .verifyReceipt row _ _ => some row.paid
  | .file paid _ => some paid
  | _ => none

def Event.recipientReceipt : Event → Option AgreedRecipientReceipt
  | .post row | .verifyReceipt row _ _ => row.recipientReceipt
  | _ => none

/-- §5 uses recorded course evidence and the shared payment and hold ledger. -/
inductive Step (ev : StartEvidence) (holds : HoldHistory) :
    History → Event → History → (principal : MaterialsPrincipalContext := {}) → Prop where
  | adopt {history lesson terms principal}
      (adopted : terms.adoptedFor lesson)
      (fresh : ∀ prior ∈ history.terms,
        prior.lesson = terms.lesson → prior.agreementReference ≠ terms.agreementReference) :
      Step ev holds history (.adopt lesson terms)
        { history with terms := terms :: history.terms } principal
  | report {history lesson row began ended principal}
      (actual : ev.teachingBegan = some began ∧ ev.teachingEnded = some ended)
      (effectiveTutor : EffectiveTutorAt lesson ev began row.tutor)
      (timely : row.timely { lesson with tutor := row.tutor } began ended) :
      Step ev holds history (.report lesson row)
        { history with reports := row :: history.reports } principal
  | checkCombination {history row principal}
      (verified : row.conforms ev history.terms)
      (fresh : ∀ prior ∈ history.combinationChecks, prior.lesson.id = row.lesson.id →
        prior.reference ≠ row.reference) :
      Step ev holds history (.checkCombination row)
        { history with combinationChecks := row :: history.combinationChecks } principal
  | verify {history row principal}
      (adopted : row.terms ∈ history.terms)
      (reported : ∀ report ∈ row.use.tutorReport, report ∈ history.reports)
      (course : row.matchesCourse ev)
      (confirmed : row.terms.adoptedFor row.use.lesson ∧ row.use.verifiedBy row.checkedAt) :
      Step ev holds history (.verify row) { history with useChecks := row :: history.useChecks }
        principal
  | provision {history terms row principal}
      (adopted : terms ∈ history.terms)
      (form : ∃ roster forms, ev.rosterFormsAt row.form.lesson row.funds.checkedAt roster forms ∧
        row.form ∈ forms)
      (pending : ¬ row.pending.status.holdMustFollowSection62)
      (provided : PendingMaterialsProvision row.form terms row.pending row.otherAmountsOwed
        row.funds row.verifiedEstimate)
      (dated : ∀ prior ∈ history.provisions, budgetKey prior.pending = budgetKey row.pending →
        prior.pending.checkedAt ≠ row.pending.checkedAt)
      (joint : ({ history with provisions := row :: history.provisions }
        ).provisionBudgetAllows ev holds.payments row principal)
      (preserved : history.provisionsStillCovered ev holds.payments row principal) :
      Step ev holds history (.provision terms row)
        { history with provisions := row :: history.provisions } principal
  | settle {history row principal}
      (verified : row.check ∈ history.useChecks)
      (computed : row.conforms)
      (pricing : history.pricingAvailable row.check row.record.settledAt)
      (cap : history.combinedCapAllows row.record.lesson row.record.charges row.record.settledAt
        principal)
      (fresh : ∀ prior ∈ history.originals, prior.record.lesson = row.record.lesson →
        prior.record.material = row.record.material →
        ¬ (prior.record.obligation = row.record.obligation ∨
          (prior.record.termsReference = row.record.termsReference ∧
            (prior.record.reference = row.record.reference ∨
              ∃ place ∈ row.record.places, place ∈ prior.record.places)))) :
      Step ev holds history (.settle row) { history with originals := row :: history.originals }
        principal
  | transfer {history row principal}
      (authenticated : row.record.reference ≠ "" ∧
        row.record.verifiedTerms row.record.reference row.record.transfer ∧
        row.record.transfer.allowed row.sparkDao row.record.voluntary
          row.record.publishedTermsSatisfied)
      (fresh : ∀ prior ∈ history.transfers, prior.material = row.material →
        prior.record.reference ≠ row.record.reference) :
      Step ev holds history (.transfer row) { history with transfers := row :: history.transfers }
        principal
  | identifyShortfall {history row principal}
      (retained : row.original ∈ history.originals)
      (verified : row.check ∈ history.useChecks)
      (computed : row.conforms (history.shortfalls.map Shortfall.record) principal)
      (additional : ∃ charge ∈ row.additionalCharges, 0 < charge.amount)
      (ordered : ∀ prior ∈ history.shortfalls, prior.record.belongsTo row.original.record = true →
        row.record.addsToPlaceCoveredBy prior.record →
        prior.record.identifiedAt.before row.record.identifiedAt)
      (pricing : history.pricingAvailable row.check row.record.identifiedAt)
      (cap : history.combinedCapAllows row.record.lesson row.additionalCharges
        row.record.identifiedAt principal)
      (fresh : ∀ prior ∈ history.shortfalls, prior.record.lesson = row.record.lesson →
        prior.record.material = row.record.material →
        prior.record.reference ≠ row.record.reference) :
      Step ev holds history (.identifyShortfall row)
        { history with shortfalls := row :: history.shortfalls } principal
  | establish {history row principal}
      (computed : (history.shareEvidence row row.verifiedAt).eligibleAt row.check.use
        row.check.terms row.original.record row.holder row.amount row.verifiedAt
        (useBasisVerified := row.retainedBasis history)
        (shortfalls := history.shortfalls.map Shortfall.record) (principal := principal))
      (received : row.collectionsMatch history holds.payments)
      (provided : history.pendingProvisionRecorded ev row) :
      Step ev holds history (.establish row)
        { history with entitlements := row :: history.entitlements } principal
  | post {history row principal}
      (fresh : row.paid.id ∉ holds.payments.posted.map PostedPayment.id)
      (freshRecipient : ∀ recipient ∈ row.recipientReceipt,
        recipient ∉ holds.payments.agreedRecipientReceipts)
      (payment : row.conforms history ev (row.postingHistory holds) principal) :
      Step ev holds history (.post row)
        { history with
          receipts := ⟨row.paid, row.funds, row.paid.instruction.atTime,
            some row.paid.instruction.atTime⟩ :: history.receipts } principal
  | verifyReceipt {history row verifiedAt reference principal}
      (evidence : history.verifiesReceiptAt row.paid row.entitlement verifiedAt reference)
      (observed : row.observedAt history ev holds verifiedAt principal) :
      Step ev holds history (.verifyReceipt row verifiedAt reference)
        { history with receipts := ⟨row.paid, row.funds, verifiedAt, none⟩ :: history.receipts } principal
  | file {history paid filedAt principal}
      (fileable : history.canFileReceipt paid filedAt) :
      Step ev holds history (.file paid filedAt) (history.fileReceipt paid filedAt) principal

end SourceV14.Workflow.Materials
