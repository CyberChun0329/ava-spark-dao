import SourceV14.Confirmation
import SourceV14.Fault
import SourceV14.Review

namespace SourceV14

/-! Clause 4.4. Contingent expenses and funds that can be used at the time of the check. -/

/-- A verified funding entry is identified across both sources of funds. -/
inductive FundingSource where
  | lessonFees
  | providerFunds
  deriving DecidableEq, Repr

inductive FundingAvailability where
  | spendable
  | paidOutUnrecovered
  | compensationNotReceived
  deriving DecidableEq, Repr

structure FundingEntry where
  id : Nat
  source : FundingSource
  availability : FundingAvailability
  balance : Amount
  committedElsewhere : Amount
  securedForLesson : Amount
  deriving DecidableEq, Repr

def FundingEntry.available (entry : FundingEntry) : Amount :=
  match entry.availability with
  | .spendable => entry.balance - entry.committedElsewhere
  | .paidOutUnrecovered | .compensationNotReceived => 0

def FundingEntry.valid (entry : FundingEntry) : Prop :=
  0 ≤ entry.committedElsewhere ∧ entry.committedElsewhere ≤ entry.balance ∧
    0 ≤ entry.securedForLesson ∧ entry.securedForLesson ≤ entry.available

/-- Verified balances for one lesson and its provider at the check time. Entry identifiers
    refer to distinct funds. Each entry records commitments elsewhere and the amount
    secured for this lesson. -/
structure CurrentLessonFunds where
  lesson : LessonId
  provider : ActorId
  checkedAt : Moment
  entries : List FundingEntry
  deriving Repr

def CurrentLessonFunds.validFor (funds : CurrentLessonFunds) (lesson : Lesson) : Prop :=
  funds.lesson = lesson.id ∧ funds.provider = lesson.provider ∧
    (funds.entries.map FundingEntry.id).Nodup ∧ ∀ entry ∈ funds.entries, entry.valid

def CurrentLessonFunds.amountFrom (funds : CurrentLessonFunds) (source : FundingSource)
    (amount : FundingEntry → Amount) : Amount :=
  sumAmountsWhere funds.entries (fun entry ↦ entry.source == source) amount

def CurrentLessonFunds.coversWith (funds : CurrentLessonFunds) (expense : Amount)
    (amount : FundingEntry → Amount) : Prop :=
  max 0 (expense - funds.amountFrom .lessonFees amount) ≤ funds.amountFrom .providerFunds amount

def CurrentLessonFunds.covers (funds : CurrentLessonFunds) (expense : Amount) : Prop :=
  funds.coversWith expense FundingEntry.available

def CurrentLessonFunds.secures (funds : CurrentLessonFunds) (expense : Amount) : Prop :=
  funds.coversWith expense FundingEntry.securedForLesson

/-- Shared facts are identified by their subject. An additional condition comes from
    a question under the recorded lesson terms, shared between places where applicable. -/
inductive FundingFact where
  | teachingBegan
  | couldProceedAsAgreed
  | partyAtFaultForDisruption
  | agreedCase (termsReference question : String)
  deriving DecidableEq, Repr

structure FundingCondition where
  subject : FundingFact
  value : Bool
  deriving DecidableEq, Repr

def FundingCondition.valid (condition : FundingCondition) : Prop :=
  match condition.subject with
  | .agreedCase reference question => reference ≠ "" ∧ question ≠ ""
  | _ => True

def FundingCondition.holds (condition : FundingCondition) (facts : FundingFact → Bool) : Bool :=
  facts condition.subject == condition.value

inductive FundingOutcomeKind where
  | standardCompensation (receivedTeaching : Bool) (unappliedReliefOwed : Amount)
  | fullRefund
  | noFaultCancellation (someTeaching : Bool) (undeliveredAgreedValue : Amount)
  | otherAgreedRemedy (agreementReference : String) (finalFee : Amount)
  | ordinarySettlement (finalFee : Amount)
  deriving DecidableEq, Repr

/-- The agreed or otherwise verified inputs for a possible outcome at a place. -/
structure PlaceFundingOutcome where
  place : PlaceId
  kind : FundingOutcomeKind
  caseReference : String
  conditions : List FundingCondition
  deriving DecidableEq, Repr

def PlaceFundingOutcome.validFor (outcome : PlaceFundingOutcome) (place : Place) : Prop :=
  outcome.place = place.id ∧ outcome.caseReference ≠ "" ∧
    (∀ condition ∈ outcome.conditions, condition.valid) ∧
    match outcome.kind with
    | .standardCompensation true unapplied =>
        0 ≤ unapplied ∧ unapplied ≤ unappliedHalfPriceBenefit place place.feePayable
    | .standardCompensation false unapplied => unapplied = 0
    | .fullRefund => True
    | .noFaultCancellation false value => value = 0
    | .noFaultCancellation true value => 0 ≤ value
    | .otherAgreedRemedy reference finalFee =>
        reference ≠ "" ∧ 0 ≤ finalFee ∧ finalFee ≤ place.feePayable
    | .ordinarySettlement finalFee => 0 ≤ finalFee ∧ finalFee ≤ place.feePayable

def PlaceFundingOutcome.matchesFacts (outcome : PlaceFundingOutcome)
    (facts : FundingFact → Bool) : Prop :=
  (∀ condition ∈ outcome.conditions, condition.holds facts = true) ∧
    match outcome.kind with
    | .standardCompensation true _ => facts .teachingBegan = true
    | .noFaultCancellation someTeaching _ =>
        facts .teachingBegan = someTeaching ∧ facts .couldProceedAsAgreed = false ∧
          facts .partyAtFaultForDisruption = false
    | _ => True

/-- In a check before debiting, the original debit is the agreed payable fee, including zero
    for a fully discounted place. The refund realises the original-lesson discount. -/
def PlaceFundingOutcome.refund (outcome : PlaceFundingOutcome) (place : Place) : Amount :=
  match outcome.kind with
  | .standardCompensation received _ =>
      grossLessonCreditRestoration place.feePayable
        (feeAfterOriginalCompensation place (if received then .some else .none))
  | .fullRefund => place.feePayable
  | .noFaultCancellation someTeaching value =>
      Booking.noFaultRefund place.feePayable value (!someTeaching)
  | .otherAgreedRemedy _ fee | .ordinarySettlement fee =>
      grossLessonCreditRestoration place.feePayable fee

/-- The fixed benefit is available against a later booking after no teaching.
    If applied to the original lesson, only separately owed unapplied relief adds to its refund. -/
def PlaceFundingOutcome.customerCost (outcome : PlaceFundingOutcome) (place : Place) : Amount :=
  outcome.refund place +
    match outcome.kind with
    | .standardCompensation true unapplied => compensationCourseCredit place + unapplied
    | .standardCompensation false _ => compensationCourseCredit place + halfPriceBenefit place
    | _ => 0

def PlaceFundingOutcome.isPartialNoFault (outcome : PlaceFundingOutcome) : Bool :=
  match outcome.kind with
  | .noFaultCancellation true _ => true
  | _ => false

def PlaceFundingOutcome.restoresFullDebit (outcome : PlaceFundingOutcome) (place : Place) : Bool :=
  match outcome.kind with
  | .fullRefund | .standardCompensation false _ | .noFaultCancellation false _ => true
  | _ => decide (0 < place.feePayable) && outcome.refund place == place.feePayable

inductive FundingExpenseKind where
  | tutorPay (tutor : ActorId)
  | materialsShare (material : Nat) (holder : ActorId)
  | handlingCost (recipient : ActorId)
  | otherAgreedRemedy (recipient : ActorId)
  deriving DecidableEq, Repr

def FundingExpenseKind.payee : FundingExpenseKind → ActorId
  | .tutorPay payee | .materialsShare _ payee | .handlingCost payee | .otherAgreedRemedy payee =>
      payee

def FundingExpenseKind.purpose : FundingExpenseKind → PaymentPurpose
  | .tutorPay tutor => .tutorPay tutor
  | .materialsShare material holder => .materialsShare material holder
  | _ => .other

structure MaterialsFundingKey where
  lesson : LessonId
  place : PlaceId
  material : Nat
  termsReference : String
  deriving DecidableEq, Repr

/-- The part of a booked materials expense allocated to a specific place. -/
structure FundingMaterialPortion where
  place : PlaceId
  amount : Amount
  deriving DecidableEq, Repr

/-- One row per applicable underlying cost. The scope is empty for common expenses and
    otherwise names the outcomes that cause the cost. Several outcomes can name one shared cost. -/
structure FundingExpense where
  obligation : ObligationId
  lesson : LessonId
  kind : FundingExpenseKind
  agreementReference : String
  component : String
  amount : Amount
  agreedRecipient : Option ActorId
  outcomes : List (PlaceId × String)
  conditions : List FundingCondition
  materialsPortions : List FundingMaterialPortion := []
  deriving DecidableEq, Repr

def FundingExpense.key (expense : FundingExpense) : FundingExpenseKind × String × String :=
  (expense.kind, expense.agreementReference, expense.component)

def FundingExpense.owedAt (expense : FundingExpense) (payments : PaymentHistory)
    (checkedAt : Moment) : Amount :=
  payments.remainingObligationBefore expense.lesson expense.obligation
    (.person expense.kind.payee expense.agreedRecipient) expense.amount checkedAt
    (some expense.kind.purpose)

/-- The part of an expense still reserved for this exact estimate. A receipt against a
    multi-place expense could have drawn upon this portion. -/
def FundingExpense.materialsCoverage (expense : FundingExpense) (key : MaterialsFundingKey)
    (payments : PaymentHistory) (checkedAt : Moment) : Amount :=
  match expense.kind with
  | .materialsShare material _ =>
      if key.lesson = expense.lesson ∧ key.material = material ∧
          key.termsReference = expense.agreementReference then
        let portion := sumAmountsWhere expense.materialsPortions (·.place == key.place) (·.amount)
        max 0 (portion - (expense.amount - expense.owedAt payments checkedAt))
      else 0
  | _ => 0

/-- The agreed form references on which the funding inventory is based. -/
structure FundingFormTerms where
  place : PlaceId
  references : List String
  noFaultReference : String
  materialsReference : Option String := none
  deriving DecidableEq, Repr

def FundingFormTerms.fromForm (form : Confirmation.PartOne) : FundingFormTerms :=
  ⟨form.place.id, [form.serviceTerms, form.cancelChangeTerms, form.noFaultTerms,
    form.applicableStartTerms, form.tutorAgreementRef] ++ form.materialsTermsRef.toList ++
    form.discountBasis.toList, form.noFaultTerms, form.materialsTermsRef⟩

def FundingExpense.validMaterialsPortions (expense : FundingExpense)
    (forms : List FundingFormTerms) : Prop :=
  match expense.kind with
  | .materialsShare .. =>
      (expense.materialsPortions.map FundingMaterialPortion.place).Nodup ∧
      sumAmounts expense.materialsPortions FundingMaterialPortion.amount ≤ expense.amount ∧
      ∀ portion ∈ expense.materialsPortions, 0 ≤ portion.amount ∧
        ∃ form ∈ forms, form.place = portion.place ∧
          form.materialsReference = some expense.agreementReference
  | _ => expense.materialsPortions = []

inductive PartialNoFaultScope where
  | infeasible (basis : String)
  | possible (cases : List PlaceFundingOutcome)

/-- Applicability and any valuation of undelivered teaching are read from the retained
    terms for the place. Each feasible alternative is itself a scenario input. -/
structure PartialNoFaultRecord where
  place : PlaceId
  reference : String
  evidence : EvidenceRef
  scope : PartialNoFaultScope

def PartialNoFaultRecord.cases (record : PartialNoFaultRecord) : List PlaceFundingOutcome :=
  match record.scope with
  | .infeasible _ => []
  | .possible cases => cases

def PartialNoFaultRecord.matchesForm (record : PartialNoFaultRecord)
    (form : FundingFormTerms) : Prop :=
  record.place = form.place ∧ record.reference = form.noFaultReference ∧
    record.reference ∈ form.references ∧
    match record.scope with
    | .infeasible basis => basis ≠ ""
    | .possible cases => cases ≠ [] ∧
        ∀ outcome ∈ cases, outcome.place = form.place ∧ outcome.isPartialNoFault = true

inductive FundingConditionUse where
  | outcome (place : PlaceId) (caseReference : String)
  | expense (obligation : ObligationId)
  deriving DecidableEq, Repr

/-- A condition read from a specific retained term, for the particular outcome or cost. -/
structure FundingConditionRecord where
  use : FundingConditionUse
  reference : String
  condition : FundingCondition
  evidence : EvidenceRef
  deriving DecidableEq, Repr

/-- The provider's verified inventory, retained with its basis in the applicable terms.
    Its outcome and cost rows are the input to the check, including any agreed remedy
    and any ordinary payment owed with a possible case. -/
structure VerifiedFundingInventory where
  lesson : LessonId
  provider : ActorId
  recordedAt : Moment
  evidence : EvidenceRef
  forms : List FundingFormTerms
  outcomes : List PlaceFundingOutcome
  expenses : List FundingExpense
  conditionRecords : List FundingConditionRecord
  partialNoFault : List PartialNoFaultRecord

def VerifiedFundingInventory.allOutcomes (inventory : VerifiedFundingInventory) :
    List PlaceFundingOutcome :=
  inventory.outcomes ++ inventory.partialNoFault.flatMap PartialNoFaultRecord.cases

def VerifiedFundingInventory.coversPartialNoFault (inventory : VerifiedFundingInventory) : Prop :=
  (inventory.partialNoFault.map PartialNoFaultRecord.place).Perm
      (inventory.forms.map FundingFormTerms.place) ∧
    (∀ record ∈ inventory.partialNoFault, ∃ form ∈ inventory.forms, record.matchesForm form) ∧
    ∀ outcome ∈ inventory.outcomes, outcome.isPartialNoFault = false

def VerifiedFundingInventory.conditionsFor (inventory : VerifiedFundingInventory)
    (use : FundingConditionUse) : List FundingCondition :=
  (inventory.conditionRecords.filter (fun record ↦ record.use == use)).map (·.condition)

def FundingConditionRecord.matchesInventory (record : FundingConditionRecord)
    (inventory : VerifiedFundingInventory) : Prop :=
  record.condition.valid ∧
    (match record.condition.subject with
     | .agreedCase reference _ => reference = record.reference
     | _ => True) ∧
    match record.use with
    | .outcome place caseReference =>
        (∃ form ∈ inventory.forms, form.place = place ∧ record.reference ∈ form.references) ∧
        ∃ outcome ∈ inventory.allOutcomes,
          outcome.place = place ∧ outcome.caseReference = caseReference
    | .expense obligation =>
        (∃ form ∈ inventory.forms, record.reference ∈ form.references) ∧
        ∃ expense ∈ inventory.expenses, expense.obligation = obligation

structure FundingTerms where
  inventory : VerifiedFundingInventory
  payments : PaymentHistory

def FundingTerms.outcomes (terms : FundingTerms) : List PlaceFundingOutcome :=
  terms.inventory.allOutcomes

def FundingTerms.expenses (terms : FundingTerms) : List FundingExpense :=
  terms.inventory.expenses

def FundingTerms.validFor (terms : FundingTerms) (lesson : Lesson) (places : List Place)
    (checkedAt : Moment) : Prop :=
  let outcomeKeys := terms.outcomes.map (fun outcome ↦ (outcome.place, outcome.caseReference))
  let inventory := terms.inventory
  inventory.lesson = lesson.id ∧ inventory.provider = lesson.provider ∧
    inventory.recordedAt.by checkedAt ∧
    (inventory.forms.map FundingFormTerms.place).Perm (places.map Place.id) ∧
    (∀ form ∈ inventory.forms, ∀ reference ∈ form.references, reference ≠ "") ∧
    (∀ record ∈ inventory.conditionRecords, record.matchesInventory inventory) ∧
    outcomeKeys.Nodup ∧
    (∀ outcome ∈ terms.outcomes,
      (∃ place ∈ places, outcome.validFor place) ∧
      outcome.conditions.Perm
        (inventory.conditionsFor (.outcome outcome.place outcome.caseReference)) ∧
      ∃ facts, outcome.matchesFacts facts) ∧
    (∀ place ∈ places,
      (∀ received, ∃ outcome ∈ terms.outcomes, outcome.place = place.id ∧
        ∃ unapplied, outcome.kind = .standardCompensation received unapplied) ∧
      (∃ outcome ∈ terms.outcomes, outcome.place = place.id ∧ outcome.kind = .fullRefund) ∧
      ∃ outcome ∈ terms.outcomes, outcome.place = place.id ∧
        outcome.kind = .noFaultCancellation false 0) ∧
    terms.payments.distinctReceipts ∧ terms.payments.validReturns ∧
    (∀ receipt ∈ terms.payments.posted, receipt.instruction.part.lesson = lesson.id →
      receipt.instruction.atTime.before checkedAt →
        receipt.evidence.isSome = true ∧ 0 < receipt.instruction.amount) ∧
    (∀ expense ∈ terms.expenses, expense.lesson = lesson.id ∧
      expense.agreementReference ≠ "" ∧ expense.component ≠ "" ∧ 0 ≤ expense.amount ∧
      expense.validMaterialsPortions inventory.forms ∧
      (∀ key ∈ expense.outcomes, key ∈ outcomeKeys) ∧
      expense.conditions.Perm (inventory.conditionsFor (.expense expense.obligation)) ∧
      ∀ receipt ∈ terms.payments.posted, receipt.instruction.atTime.before checkedAt →
        receipt.instruction.part.lesson = expense.lesson →
        receipt.instruction.part.obligation = expense.obligation →
        receipt.instruction.part.purpose = expense.kind.purpose) ∧
    inventory.coversPartialNoFault

def FundingTerms.paidTeachingBefore (terms : FundingTerms) (checkedAt : Moment) : Amount :=
  let teaching := terms.payments.posted.filter (fun receipt ↦
    receipt.instruction.part.lesson == terms.inventory.lesson &&
      decide (receipt.instruction.atTime.before checkedAt) &&
      match receipt.instruction.part.purpose with
      | .tutorPay _ => true
      | _ => false)
  sumAmounts teaching (fun receipt ↦
    receipt.retainedAmountBefore terms.payments.returned checkedAt)

/-- One outcome or a joint selection from different places under one assignment of case facts.
    Conditions on independent facts impose no restriction on combining them. -/
structure FundingCase where
  selections : List (Place × PlaceFundingOutcome)
  facts : FundingFact → Bool

def FundingCase.possible (scenario : FundingCase) (terms : FundingTerms) (lesson : Lesson)
    (places : List Place) : Prop :=
  scenario.selections ≠ [] ∧
    (scenario.selections.length = 1 ∨ lesson.kind = .group) ∧
    (scenario.selections.map (fun pair ↦ pair.1.id)).Nodup ∧
    ∀ (place : Place) (outcome : PlaceFundingOutcome),
      (place, outcome) ∈ scenario.selections →
        place ∈ places ∧ outcome ∈ terms.outcomes ∧ outcome.place = place.id ∧
          outcome.matchesFacts scenario.facts

def FundingCase.expenses (scenario : FundingCase) (terms : FundingTerms) : List FundingExpense :=
  terms.expenses.filter (fun expense ↦
    (expense.outcomes.isEmpty || scenario.selections.any (fun (_, outcome) ↦
      expense.outcomes.contains (outcome.place, outcome.caseReference))) &&
    expense.conditions.all (fun condition ↦ condition.holds scenario.facts))

def FundingCase.includesFullRefund (scenario : FundingCase) : Bool :=
  scenario.selections.any (fun (place, outcome) ↦ outcome.restoresFullDebit place)

def FundingCase.paidTeaching (scenario : FundingCase) (terms : FundingTerms)
    (checkedAt : Moment) : Amount :=
  if scenario.includesFullRefund then terms.paidTeachingBefore checkedAt else 0

def FundingCase.remainingCost (scenario : FundingCase) (terms : FundingTerms)
    (checkedAt : Moment) : Amount :=
  sumAmounts scenario.selections (fun (place, outcome) ↦ outcome.customerCost place) +
    sumAmounts (scenario.expenses terms) (fun expense ↦ expense.owedAt terms.payments checkedAt)

/-- Only the part of a live materials estimate absent from this booking case is added
    to its cost. Use in this lesson can generate a share only in a teaching case. -/
def FundingCase.remainingCostWithMaterials (scenario : FundingCase) (terms : FundingTerms)
    (checkedAt : Moment) (budgets : List (MaterialsFundingKey × Amount)) : Amount :=
  let booked := scenario.expenses terms
  let additional := if scenario.facts .teachingBegan then
    sumAmounts budgets (fun (key, amount) ↦
      let covered := sumAmounts booked (fun expense ↦
        expense.materialsCoverage key terms.payments checkedAt)
      max 0 (amount - covered))
    else 0
  scenario.remainingCost terms checkedAt + additional

def FundingCase.accountedCost (scenario : FundingCase) (terms : FundingTerms)
    (checkedAt : Moment) : Amount :=
  scenario.remainingCost terms checkedAt + scenario.paidTeaching terms checkedAt

def FundingCase.checked (scenario : FundingCase) (terms : FundingTerms)
    (funds : CurrentLessonFunds) : Prop :=
  let expenses := scenario.expenses terms
  (expenses.map FundingExpense.key).Nodup ∧ (expenses.map FundingExpense.obligation).Nodup ∧
    funds.secures (scenario.accountedCost terms funds.checkedAt -
      scenario.paidTeaching terms funds.checkedAt)

structure FundingCheck where
  terms : FundingTerms
  funds : CurrentLessonFunds

def FundingCheck.checkedAt (check : FundingCheck) : Moment := check.funds.checkedAt

/-- This confirmation uses the terms that were used for the funding check. -/
def FundingCheck.readsForm (check : FundingCheck) (form : Confirmation.PartOne) : Prop :=
  FundingFormTerms.fromForm form ∈ check.terms.inventory.forms

/-- Recheck compatible booking cases with the materials budgets known at the check. -/
def FundingCheck.casesSecuredWithMaterials (check : FundingCheck) (lesson : Lesson)
    (places : List Place) (budgets : List (MaterialsFundingKey × Amount))
    (teachingHasBegun : Prop) : Prop :=
  ∀ scenario : FundingCase, scenario.possible check.terms lesson places →
    (teachingHasBegun → scenario.facts .teachingBegan = true) →
    check.funds.secures (scenario.remainingCostWithMaterials check.terms check.checkedAt budgets)

/-- The balances cover each possible individual or joint result. Genuinely incompatible
    outcomes never occur in one selection and can rely on the same secured funds. -/
def FundingCheck.securedFor (check : FundingCheck) (lesson : Lesson) (places : List Place) : Prop :=
  check.funds.validFor lesson ∧
    places ≠ [] ∧ (places.map Place.id).Nodup ∧
    (∀ place ∈ places, place.matches lesson ∧ place.validFees) ∧
    check.terms.validFor lesson places check.checkedAt ∧
    ∀ (scenario : FundingCase), scenario.possible check.terms lesson places →
      scenario.checked check.terms check.funds

/-- The funding check precedes the relevant commitment, confirmation or debit. -/
def FundingCheck.securedBefore (check : FundingCheck) (lesson : Lesson) (places : List Place)
    (eventAt : Moment) : Prop :=
  check.securedFor lesson places ∧ check.checkedAt.before eventAt

/-- A review rechecks current funds against the established outstanding refund. The lesson
    refund remains due under its own terms even if the check shows insufficient funds. -/
def reviewRefundFunding (lesson : Lesson) (checkedAt : Moment) (funds : CurrentLessonFunds)
    (refundStillOwed : Amount) : Prop :=
  funds.validFor lesson ∧ funds.checkedAt = checkedAt ∧ 0 ≤ refundStillOwed ∧
    funds.covers refundStillOwed

/-- Clause 4.4 requires consent from those affected before changing agreed arrangements.
    The parties and received consents come from the case records. -/
def fundingArrangementChangeAllowed (affected consented : ActorId → Prop) : Prop :=
  ∀ party, affected party → consented party

/-- Verified lesson balances at fault-case closure. The fee balance already accounts for
    non-refund disbursements made from it. The remaining amounts due are distinct from
    the refunds and still-available course credit recorded separately. -/
structure FaultCaseBalance where
  lessonFeesBeforeRefunds : Amount
  refunds : Amount
  otherAmountsDue : Amount
  issuedCourseCreditStillAvailable : Amount
  deriving Repr

def FaultCaseBalance.serviceReserveAmount (balance : FaultCaseBalance) : Amount :=
  max 0 (balance.lessonFeesBeforeRefunds - balance.refunds - balance.otherAmountsDue -
    balance.issuedCourseCreditStillAvailable)

/-- Only the balance remaining after the closed fault case is transferred to the reserve. -/
def FaultCaseBalance.transfersToServiceReserve (balance : FaultCaseBalance)
    (faultCaseDealtWith : Prop) (transferred : Amount) : Prop :=
  faultCaseDealtWith ∧ 0 ≤ balance.lessonFeesBeforeRefunds ∧ 0 ≤ balance.refunds ∧
    0 ≤ balance.otherAmountsDue ∧ 0 ≤ balance.issuedCourseCreditStillAvailable ∧
    transferred = balance.serviceReserveAmount

end SourceV14
