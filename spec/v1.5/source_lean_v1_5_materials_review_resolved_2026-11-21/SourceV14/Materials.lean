import SourceV14.Booking
import SourceV14.Review

namespace SourceV14

abbrev MaterialId := Nat

/-- The agreed fraction of a place's normal fee for one material in a standard bundle. -/
structure MaterialRate where
  material : MaterialId
  rate : Rat
  deriving DecidableEq, Repr

inductive MaterialsPricing where
  | standardBundle (rates : List MaterialRate)
  | otherCombination (covered : List MaterialId)
      (charge : PlaceId → Amount → List MaterialId → MaterialId → Amount)

def materialsCapRate : Rat := 1 / 10

def MaterialsPricing.materials : MaterialsPricing → List MaterialId
  | .standardBundle rates => rates.map MaterialRate.material
  | .otherCombination covered _ => covered

def MaterialsPricing.covers (pricing : MaterialsPricing) (material : MaterialId) : Prop :=
  material ∈ pricing.materials

/-- Clause 5.3 standard bundle check assuming that every material in the bundle is used. -/
def StandardMaterialsBundle (rates : List MaterialRate) : Prop :=
  (rates.map MaterialRate.material).Nodup ∧
    (∀ rate ∈ rates, 0 ≤ rate.rate) ∧ sumAmounts rates MaterialRate.rate ≤ materialsCapRate

/-- An agreed division of a material's charge among its rights holders at each place. -/
structure MaterialsAllocation (material : MaterialId) where
  agreementReference : String
  holders : List ActorId
  payment : ActorId → PlaceId → Amount → Amount

structure MaterialsConsent where
  material : MaterialId
  actor : ActorId
  termsReference : String
  point : Moment

/-- Clause 5.1 terms adopted for a lesson, including the party responsible for shortfalls. -/
structure MaterialsTerms where
  lesson : LessonId
  adoptedBy : ActorId
  agreedAt : Moment
  agreementReference : String
  accountingAndPaymentParty : ActorId
  materialsOrBundle : String
  contact : String
  licensedUse : MaterialId → Prop
  sharesAndAdjustmentsReference : String
  sharesInForce :
    (material : MaterialId) → Moment → Option (MaterialsAllocation material)
  contributors : MaterialId → List ActorId
  consents : List MaterialsConsent
  ordinaryShareTime :
    (material : MaterialId) → (place : PlaceId) → (firstUse settledAt : Moment) → Moment
  paymentDue : Moment
  paymentDeadline : Moment
  pricing : MaterialsPricing

inductive MaterialUseEvidence where
  | lessonRecord (reference : String)
  | studentFeedback (reference : String)
  | otherVerifiableEvidence (reference : String)
  deriving DecidableEq, Repr

def MaterialUseEvidence.reference : MaterialUseEvidence → String
  | .lessonRecord reference | .studentFeedback reference | .otherVerifiableEvidence reference =>
    reference

/-- Clause 5.2 records expected materials and the tutor's later report separately. -/
structure TutorMaterialsReport where
  lesson : LessonId
  tutor : ActorId
  coordinator : ActorId
  listedAt : Moment
  listedMaterials : List MaterialId
  reportedAt : Moment
  reportedMaterials : List MaterialId

def TutorMaterialsReport.timely (report : TutorMaterialsReport) (lesson : Lesson)
    (lessonStarted lessonEnded : Moment) : Prop :=
  report.lesson = lesson.id ∧ report.tutor = lesson.tutor ∧
    report.coordinator = lesson.coordinator ∧
    report.listedAt.before lessonStarted ∧ lessonEnded.before report.reportedAt

/-- One finding that a student actually received teaching using this material. -/
structure ConfirmedMaterialUse where
  lesson : LessonId
  place : PlaceId
  material : MaterialId
  service : Nat
  usedAt : Moment
  checkedBy : ActorId
  checkedAt : Moment
  evidence : MaterialUseEvidence

/-- The lesson's coordinator, or the uninterested handler appointed under clause 1.2. -/
structure MaterialsUseAuthority where
  authorities : ReviewAuthorities
  /-- The verified decision scope and affected parties for this use finding. -/
  matterFor : ConfirmedMaterialUse → ReviewMatter
  recusalFor : ConfirmedMaterialUse → Option RecusalRecord

def MaterialsUseAuthority.mayCheck
    (authority : MaterialsUseAuthority) (lesson : Lesson) (finding : ConfirmedMaterialUse) : Prop :=
  let matter := authority.matterFor finding
  let a := authority.authorities
  matter.lesson = lesson.id ∧
    ((finding.checkedBy = lesson.coordinator ∧
      a.disinterested matter finding.checkedBy finding.checkedAt) ∨
      ((a.interest matter lesson.coordinator finding.checkedAt).affected ∧
        ∃ recusal ∈ authority.recusalFor finding,
          recusal.replacement.handler = finding.checkedBy ∧
          recusalConforms a matter lesson.coordinator finding.checkedAt recusal))

/-- Authenticated findings for one lesson, keyed to the agreed places and valid handler. -/
structure VerifiedMaterialsUse where
  lesson : Lesson
  startedAt : Moment
  endedAt : Moment
  /-- The tutor's report when this check cites it. Actual use can be independently verified. -/
  tutorReport : Option TutorMaterialsReport
  authority : MaterialsUseAuthority
  places : List Place
  deliveryReports : List Booking.DeliveryReport
  findings : List ConfirmedMaterialUse
  /-- The currently verified source evidence confirms receipt of this service and material use. -/
  verifiesEvidence : ConfirmedMaterialUse → Prop
  /-- A verified finding resolves an omission from the tutor's report. -/
  verifiedReportOmission : ConfirmedMaterialUse → Prop
  uniquePlaces : (places.map Place.id).Nodup
  placeInLesson : ∀ place ∈ places, place.matches lesson
  findingInLesson : ∀ finding ∈ findings, finding.lesson = lesson.id
  findingAtPlace : ∀ finding ∈ findings, finding.place ∈ places.map Place.id

def VerifiedMaterialsUse.verifiedBy (use : VerifiedMaterialsUse) (atTime : Moment) : Prop :=
  use.startedAt.before use.endedAt ∧
  (match use.tutorReport with
  | none => use.endedAt.by atTime
  | some report => report.timely use.lesson use.startedAt use.endedAt ∧
      report.reportedAt.by atTime) ∧
  ∀ finding ∈ use.findings,
    use.authority.mayCheck use.lesson finding ∧
    use.startedAt.by finding.usedAt ∧ finding.usedAt.by use.endedAt ∧
    (match use.tutorReport with
    | none => finding.usedAt.by finding.checkedAt
    | some report => (finding.material ∈ report.reportedMaterials ∨
        use.verifiedReportOmission finding) ∧ report.reportedAt.by finding.checkedAt) ∧
    finding.checkedAt.by atTime ∧
    finding.evidence.reference ≠ "" ∧
    ∃ place ∈ use.places, place.id = finding.place ∧
      match finding.evidence with
      | .lessonRecord _ | .otherVerifiableEvidence _ => use.verifiesEvidence finding
      | .studentFeedback _ =>
        use.verifiesEvidence finding ∧
        ∃ report ∈ use.deliveryReports,
          report.lesson = finding.lesson ∧ report.place = finding.place ∧
          report.student = place.student ∧ report.coordinator = use.lesson.coordinator ∧
          finding.usedAt.by report.point ∧ report.point.by finding.checkedAt ∧
          finding.service ∈ report.servicesReceived ∧
          finding.service ∉ report.servicesNotReceived

/-- Repeated use of a material at a place counts once for that place. -/
def VerifiedMaterialsUse.materialsAt (use : VerifiedMaterialsUse) (place : PlaceId) :
    List MaterialId :=
  ((use.findings.filter (fun finding ↦ finding.place == place)).map
    ConfirmedMaterialUse.material).eraseDups

/-- A material's earliest use among the confirmed findings for this lesson. -/
def VerifiedMaterialsUse.firstConfirmedUse (use : VerifiedMaterialsUse)
    (material : MaterialId) : Option Moment :=
  (use.findings.filter (fun finding ↦ finding.material == material)).foldl
    (fun earliest finding ↦
      match earliest with
      | none => some finding.usedAt
      | some time => some (if finding.usedAt.before time then finding.usedAt else time)) none

/-- The materials used or proposed for a single place. -/
structure PlaceMaterials where
  place : Place
  materials : List MaterialId

def VerifiedMaterialsUse.combination (use : VerifiedMaterialsUse) : List PlaceMaterials :=
  use.places.map (fun place ↦ ⟨place, use.materialsAt place.id⟩)

/-- Clause 5.3 counts each applicable place's normal fee once in the cap base. -/
def materialsCapBase (places : List PlaceMaterials) : Amount :=
  let applicable := places.filter (fun row ↦ !row.materials.isEmpty)
  sumAmounts (applicable.eraseDupsBy (fun a b ↦ a.place.id == b.place.id))
    (fun row ↦ row.place.normalFee)

/-- The material portion is priced against this lesson's normal fee for the place. -/
structure MaterialsCharge where
  place : PlaceId
  material : MaterialId
  amount : Amount
  deriving DecidableEq, Repr

def MaterialsPricing.chargesAt (pricing : MaterialsPricing) (row : PlaceMaterials) :
    List MaterialsCharge :=
  match pricing with
  | .standardBundle rates =>
      (rates.filter (fun rate ↦ row.materials.contains rate.material)).map
        (fun rate ↦ ⟨row.place.id, rate.material, row.place.normalFee * rate.rate⟩)
  | .otherCombination _ charge =>
      row.materials.map (fun material ↦
        ⟨row.place.id, material, charge row.place.id row.place.normalFee row.materials material⟩)

def MaterialsPricing.charges (pricing : MaterialsPricing) (places : List PlaceMaterials) :
    List MaterialsCharge :=
  places.flatMap pricing.chargesAt

def MaterialsTerms.covers (terms : MaterialsTerms) (places : List PlaceMaterials) : Prop :=
  ∀ row ∈ places, row.place.lesson = terms.lesson ∧
    ∀ material ∈ row.materials, terms.pricing.covers material ∧ terms.licensedUse material

def MaterialsTerms.agreedBy (terms : MaterialsTerms) (material : MaterialId) (actor : ActorId) :
    Prop :=
  ∃ consent ∈ terms.consents, consent.material = material ∧ consent.actor = actor ∧
    consent.termsReference = terms.agreementReference ∧ consent.point.by terms.agreedAt

def MaterialsTerms.adoptedFor (terms : MaterialsTerms) (lesson : Lesson) : Prop :=
  terms.lesson = lesson.id ∧ terms.adoptedBy = lesson.provider ∧
  terms.agreementReference ≠ "" ∧ terms.sharesAndAdjustmentsReference ≠ "" ∧
  terms.materialsOrBundle ≠ "" ∧
  terms.contact ≠ "" ∧
  ∀ material ∈ terms.pricing.materials, ∀ contributor ∈ terms.contributors material,
    terms.agreedBy material contributor

def materialsCombinationWithinCap (pricing : MaterialsPricing) (places : List PlaceMaterials) :
    Prop :=
  let charges := pricing.charges places
  (∀ charge ∈ charges, 0 ≤ charge.amount) ∧
    sumAmounts charges MaterialsCharge.amount ≤ materialsCapRate * materialsCapBase places

structure MaterialsAdjustment where
  material : MaterialId
  holder : ActorId
  shareTime : Moment

structure NonstandardMaterialsCheck where
  lesson : LessonId
  termsReference : String
  checkedAt : Moment
  checkedCombinations : List (List PlaceMaterials)
  needsAdjustment : Bool
  affectedRightsHolders : List MaterialsAdjustment

/-- Check the intended nonstandard combination and any required adjustment before use. -/
def MaterialsTerms.nonstandardUseAllowed (terms : MaterialsTerms)
    (check : NonstandardMaterialsCheck) (actual : List PlaceMaterials) : Prop :=
  match terms.pricing with
  | .standardBundle _ => False
  | .otherCombination _ _ =>
      check.lesson = terms.lesson ∧ check.termsReference = terms.agreementReference ∧
      actual ∈ check.checkedCombinations ∧
      (∀ proposed ∈ check.checkedCombinations,
        (proposed.map (fun row ↦ row.place.id)).Nodup ∧
        (∀ row ∈ proposed, row.materials.Nodup) ∧ terms.covers proposed ∧
        materialsCombinationWithinCap terms.pricing proposed) ∧
      (check.needsAdjustment = true →
        check.affectedRightsHolders ≠ [] ∧
        ∀ affected ∈ check.affectedRightsHolders,
          terms.pricing.covers affected.material ∧
          terms.agreedBy affected.material affected.holder ∧ affected.shareTime.by terms.agreedAt ∧
          ∃ allocation, terms.sharesInForce affected.material affected.shareTime =
            some allocation ∧ affected.holder ∈ allocation.holders)

/-- Verify the actual-use computation under the lesson's terms and combined cap. -/
def MaterialsTerms.calculatesVerifiedUse (terms : MaterialsTerms)
    (use : VerifiedMaterialsUse) (advanceCheck : Option NonstandardMaterialsCheck)
    (verifiedAt : Moment) : Prop :=
  terms.adoptedFor use.lesson ∧ use.verifiedBy verifiedAt ∧
    (∀ finding ∈ use.findings, terms.agreedAt.before finding.usedAt) ∧
    terms.covers use.combination ∧
    (match terms.pricing with
    | .standardBundle rates =>
        StandardMaterialsBundle rates ∧
        ∀ rate ∈ rates, ∃ allocation, terms.sharesInForce rate.material terms.agreedAt =
          some allocation ∧ ∀ holder ∈ allocation.holders, terms.agreedBy rate.material holder
    | .otherCombination _ _ =>
        ∃ check, advanceCheck = some check ∧
          terms.nonstandardUseAllowed check
            (use.combination.filter (fun row ↦ !row.materials.isEmpty)) ∧
          ∀ finding ∈ use.findings, check.checkedAt.before finding.usedAt) ∧
    materialsCombinationWithinCap terms.pricing use.combination

def VerifiedMaterialsUse.charges (use : VerifiedMaterialsUse) (terms : MaterialsTerms) :
    List MaterialsCharge :=
  terms.pricing.charges use.combination

def VerifiedMaterialsUse.chargesFor (use : VerifiedMaterialsUse) (terms : MaterialsTerms)
    (material : MaterialId) : List MaterialsCharge :=
  (use.charges terms).filter (fun charge ↦ charge.material == material)

def VerifiedMaterialsUse.totalShare (use : VerifiedMaterialsUse) (terms : MaterialsTerms) :
    Amount :=
  sumAmounts (use.charges terms) MaterialsCharge.amount

/-- The agreed holder portions account for the charge included in the combined cap. -/
def MaterialsAllocation.distributesCharge {material : MaterialId}
    (allocation : MaterialsAllocation material) (place : PlaceId) (amount : Amount) : Prop :=
  allocation.holders.Nodup ∧
    (∀ holder ∈ allocation.holders, 0 ≤ allocation.payment holder place amount) ∧
    sumAmounts allocation.holders (fun holder ↦ allocation.payment holder place amount) = amount

def MaterialsAllocation.portion {material : MaterialId}
    (allocation : MaterialsAllocation material) (holder : ActorId) (place : PlaceId)
    (amount : Amount) : Amount :=
  if holder ∈ allocation.holders then allocation.payment holder place amount else 0

/-- Clause 5.3 distinguishes an amount awaiting verification from an established amount. -/
structure MaterialsShareStatus where
  actualUseVerified : Bool
  entitlementVerified : Bool
  determinedPayable : Bool
  approvedForPayment : Bool

def MaterialsShareStatus.provisionRequired (status : MaterialsShareStatus) : Prop :=
  status.actualUseVerified = false ∨ status.entitlementVerified = false

def MaterialsShareStatus.canSettleAfterVerification (status : MaterialsShareStatus)
    (fundingSecuredUnder44 : Prop) : Prop :=
  status.actualUseVerified = true ∧ status.entitlementVerified = true ∧ fundingSecuredUnder44

def MaterialsShareStatus.holdMustFollowSection62 (status : MaterialsShareStatus) : Prop :=
  status.determinedPayable = true ∨ status.approvedForPayment = true

inductive PriorMaterialsUseAllocation (material : MaterialId) where
  | sharesAtFirstUse
  | otherwiseAgreed (allocation : MaterialsAllocation material)

inductive MaterialsTransferKind where
  | voluntaryTransfer
  | buyback
  deriving DecidableEq, Repr

/-- Clause 5.4 requires a disposition for each of the three classes of receipts. -/
structure MaterialsTransfer (material : MaterialId) where
  transferor : ActorId
  transferee : ActorId
  kind : MaterialsTransferKind
  effectiveAt : Moment
  priorUseUnsettled : PriorMaterialsUseAllocation material
  settledUncollected : MaterialsAllocation material
  laterShortfall : MaterialsAllocation material

/-- Clause 5.1 permits voluntary transfers and Spark DAO buybacks on their published terms. -/
def MaterialsTransfer.allowed {material : MaterialId}
    (transfer : MaterialsTransfer material) (sparkDao : ActorId)
    (voluntary : Prop) (publishedTermsSatisfied : Prop) : Prop :=
  publishedTermsSatisfied ∧
    match transfer.kind with
    | .voluntaryTransfer => voluntary
    | .buyback => transfer.transferee = sparkDao

/-- For unsettled pre-transfer use, apply the shares at first actual use unless agreed otherwise. -/
def MaterialsTransfer.priorUnsettledAllocation {material : MaterialId}
    (transfer : MaterialsTransfer material) (firstActualUse : Moment)
    (sharesAt : Moment → MaterialsAllocation material → Prop)
    (allocation : MaterialsAllocation material) : Prop :=
  match transfer.priorUseUnsettled with
  | .sharesAtFirstUse => sharesAt firstActualUse allocation
  | .otherwiseAgreed agreed => allocation = agreed

/-- Original payments collected before a transfer, for the covered place and material. -/
structure MaterialsCollection where
  holder : ActorId
  amount : Amount
  collectedAt : Moment

/-- Applicable authority, ownership and collection evidence for recorded transfer terms. -/
structure MaterialsTransferRecord (material : MaterialId) where
  transfer : MaterialsTransfer material
  reference : String
  verifiedTerms : String → MaterialsTransfer material → Prop
  transferorShareTime : Moment
  applicableOwnershipTime : Moment → Prop
  voluntary : Prop
  publishedTermsSatisfied : Prop
  /-- The applicable terms assign this specific settlement and place to this disposition. -/
  governs : LessonId → String → PlaceId → Prop
  originalCollections : LessonId → String → PlaceId → List MaterialsCollection
  /-- Collections for the identified shortfall of this original settlement and place. -/
  shortfallCollections : LessonId → (originalReference shortfallReference : String) →
    PlaceId → List MaterialsCollection

def MaterialsTransferRecord.authorised {material : MaterialId}
    (record : MaterialsTransferRecord material) (sparkDao : ActorId)
    (sharesAt : Moment → MaterialsAllocation material → Prop) : Prop :=
  record.reference ≠ "" ∧ record.verifiedTerms record.reference record.transfer ∧
  record.transfer.allowed sparkDao record.voluntary record.publishedTermsSatisfied ∧
  record.transferorShareTime.before record.transfer.effectiveAt ∧
  record.applicableOwnershipTime record.transferorShareTime ∧
  ∃ held, sharesAt record.transferorShareTime held ∧
    record.transfer.transferor ∈ held.holders

/-- Verified prior charge and the identified later shortfall under the applicable terms. -/
structure MaterialsShortfall where
  lesson : LessonId
  material : MaterialId
  termsReference : String
  originalSettlementReference : String
  reference : String
  obligation : ObligationId
  identifiedAt : Moment
  /-- The newly established amount for each affected place. -/
  charges : List MaterialsCharge

/-- The retained original charge for this material under the adopted lesson terms. -/
structure MaterialsSettlementRecord where
  lesson : LessonId
  material : MaterialId
  termsReference : String
  reference : String
  obligation : ObligationId
  settledAt : Moment
  places : List PlaceId
  charges : List MaterialsCharge

/-- The obligation whose gross charge was recognised for this lesson and agreement. -/
structure MaterialsChargeScope where
  lesson : LessonId
  material : MaterialId
  termsReference : String
  originalReference : String
  shortfallReference : Option String
  obligation : ObligationId
  establishedAt : Moment
  deriving DecidableEq

def MaterialsSettlementRecord.chargeScope (row : MaterialsSettlementRecord) :
    MaterialsChargeScope :=
  ⟨row.lesson, row.material, row.termsReference, row.reference, none, row.obligation, row.settledAt⟩

/-- A place within the original settlement can have had no charge before review. -/
private def includeUnchargedPlaces (charges : List MaterialsCharge)
    (places : List PlaceId) (material : MaterialId) : List MaterialsCharge :=
  charges ++ ((places.filter fun place ↦ !charges.any (·.place == place)).map
    fun place ↦ ⟨place, material, 0⟩)

def MaterialsSettlementRecord.grossChargeInputs (row : MaterialsSettlementRecord) :
    List MaterialsCharge :=
  includeUnchargedPlaces row.charges row.places row.material

def MaterialsShortfall.grossChargeInputs (row : MaterialsShortfall)
    (original : MaterialsSettlementRecord) : List MaterialsCharge :=
  includeUnchargedPlaces row.charges original.places row.material

def MaterialsShortfall.chargeScope (row : MaterialsShortfall) : MaterialsChargeScope :=
  ⟨row.lesson, row.material, row.termsReference, row.originalSettlementReference,
    some row.reference, row.obligation, row.identifiedAt⟩

def MaterialsChargeScope.matchesPart (scope : MaterialsChargeScope) (part : PaymentPartRef) :
    Bool :=
  part.lesson == scope.lesson && part.obligation == scope.obligation &&
    match part.purpose, scope.shortfallReference with
    | .materialsShare material _, none => material == scope.material
    | .materialsShortfall material _ claim, some reference =>
      material == scope.material && claim == reference
    | _, _ => false

/-- Verified replacement of this place's gross charge, with the date the evidence was available. -/
structure MaterialsGrossAttribution where
  verifiedAt : Moment
  previous : Amount
  revised : Amount

/-- Gross-charge evidence for the exact adopted review and scope. An aggregate upper bound can
    establish cap headroom without assigning the gross charge among places. -/
structure MaterialsGrossEvidence where
  atPlace : MaterialsChargeScope → PaymentCorrectionCase → PlaceId →
    Option MaterialsGrossAttribution := fun _ _ _ ↦ none
  upperBound : MaterialsChargeScope → List PaymentCorrectionCase → Option (Moment × Amount) :=
    fun _ _ ↦ none
  /-- A new factual check supports further use at this place after the reviewed reduction. -/
  supportsLaterUse : MaterialsChargeScope → PaymentCorrectionCase → ConfirmedMaterialUse → Bool :=
    fun _ _ _ ↦ false

structure MaterialsPrincipalContext where
  corrections : List PaymentCorrectionCase := []
  gross : MaterialsGrossEvidence := {}

def MaterialsPrincipalContext.reviewsFor (principal : MaterialsPrincipalContext)
    (scope : MaterialsChargeScope) (atTime : Moment) : List PaymentCorrectionCase :=
  (principal.corrections.filter fun row ↦
    row.correction.lesson == scope.lesson && scope.matchesPart row.originalPart.ref &&
    row.originalPart.ref.sameCorrectionClaim row.money.corrected.ref && decide
      (scope.establishedAt.by row.finding.decidedAt ∧
        row.finding.decidedAt.by row.correction.recordedAt ∧
        row.correction.recordedAt.by atTime)).mergeSort
    (fun first second ↦ decide (first.finding.decidedAt.by second.finding.decidedAt))

/-- The last verified gross amount and whether a later gross change awaits attribution.
    A zero historical row does not establish which places a later amount correction affects. -/
def MaterialsPrincipalContext.chargeAt (principal : MaterialsPrincipalContext)
    (scope : MaterialsChargeScope) (charge : MaterialsCharge) (atTime : Moment)
    (laterUse : Option (List ConfirmedMaterialUse) := none) :
    MaterialsCharge × Bool :=
  (principal.reviewsFor scope atTime).foldl (fun (previous, pending) review ↦
    if pending then (previous, true)
    else
      let missing := review.originalPart.amount != review.money.corrected.amount
      match principal.gross.atPlace scope review charge.place with
      | some fact =>
        if review.finding.decidedAt.by fact.verifiedAt ∧ fact.verifiedAt.by atTime ∧
            fact.previous = previous.amount ∧ 0 ≤ fact.revised then
          let needsNewUse := laterUse.any fun findings ↦
            decide (fact.revised < previous.amount) && !findings.any (fun finding ↦
              finding.lesson == scope.lesson && finding.place == charge.place &&
              decide (review.correction.recordedAt.by finding.checkedAt ∧
                finding.checkedAt.by atTime) &&
              principal.gross.supportsLaterUse scope review finding)
          ({ previous with amount := fact.revised }, needsNewUse)
        else (previous, missing)
      | none => (previous, missing)) (charge, false)

def MaterialsPrincipalContext.grossUpperBoundAt (principal : MaterialsPrincipalContext)
    (scope : MaterialsChargeScope) (charges : List MaterialsCharge) (atTime : Moment) :
    Option Amount := do
  let effective := charges.map fun charge ↦ principal.chargeAt scope charge atTime
  if effective.any Prod.snd then
    let revisions := principal.reviewsFor scope atTime
    let (verifiedAt, bound) ← principal.gross.upperBound scope revisions
    if verifiedAt.by atTime ∧
        revisions.all (fun row ↦ decide (row.finding.decidedAt.by verifiedAt)) = true ∧
        sumAmountsWhere effective (fun row ↦ !row.2) (fun row ↦ row.1.amount) ≤ bound then
      some bound
    else none
  else some (sumAmounts effective (fun row ↦ row.1.amount))

def MaterialsShortfall.belongsTo (shortfall : MaterialsShortfall)
    (original : MaterialsSettlementRecord) : Bool :=
  shortfall.lesson == original.lesson && shortfall.material == original.material &&
    shortfall.termsReference == original.termsReference &&
    shortfall.originalSettlementReference == original.reference

def MaterialsShortfall.addsToPlaceCoveredBy (shortfall other : MaterialsShortfall) : Prop :=
  ∃ charge ∈ shortfall.charges, 0 < charge.amount ∧
    ∃ earlier ∈ other.charges, earlier.place = charge.place ∧ 0 < earlier.amount

/-- Compare the verified total for each place with amounts already established. -/
def MaterialsShortfall.newCharges (shortfall : MaterialsShortfall)
    (original : MaterialsSettlementRecord) (history : List MaterialsShortfall)
    (verified : List MaterialsCharge) (principal : MaterialsPrincipalContext := {})
    (findings : List ConfirmedMaterialUse := []) :
    List MaterialsCharge :=
  let prior := history.filter (fun row ↦ row.belongsTo original &&
    decide (row.identifiedAt.before shortfall.identifiedAt))
  let read := fun scope charge ↦ principal.chargeAt scope charge shortfall.identifiedAt
    (some findings)
  let established := original.grossChargeInputs.map (read original.chargeScope) ++
    prior.flatMap (fun row ↦ (row.grossChargeInputs original).map (read row.chargeScope))
  verified.map fun charge ↦
    let here := established.filter (fun row ↦ row.1.place == charge.place)
    let earlier := sumAmounts here (fun row ↦ row.1.amount)
    { charge with amount := if here.any Prod.snd then 0 else max 0 (charge.amount - earlier) }

/-- The originally agreed share schedule and later private amendments for one material. -/
structure MaterialsShareHistory (material : MaterialId) where
  originalReference : EvidenceRef
  agreedSharesAt : Moment → Option (MaterialsAllocation material)
  /-- Verify the exact schedule and share-time rule in the adopted agreement. -/
  verifiedOriginal : MaterialsTerms → EvidenceRef →
    (Moment → Option (MaterialsAllocation material)) → Prop
  amendments : List (PrivateAmendment (LessonId × PlaceId) (MaterialsAllocation material)) := []
  assents : List PrivateAmendmentAssent := []
  furtherAffected : PrivateAmendment (LessonId × PlaceId) (MaterialsAllocation material) →
    ActorId → Prop := fun _ _ ↦ False
  verifiedAssent : PrivateAmendment (LessonId × PlaceId) (MaterialsAllocation material) →
    PrivateAmendmentAssent → Prop := fun _ _ ↦ False

/-- Original settlement and later evidence governing a material's payment in this lesson. -/
structure MaterialsShareEvidence (material : MaterialId) where
  originalSettlementReference : String
  originalSettlementAt : Moment
  entitlementVerifiedAt : Moment
  advanceCheck : Option NonstandardMaterialsCheck
  sparkDao : ActorId
  transfers : List (MaterialsTransferRecord material)
  shortfall : Option MaterialsShortfall
  shareHistory : MaterialsShareHistory material

def MaterialsShareEvidence.allocationAt {material : MaterialId}
    (evidence : MaterialsShareEvidence material) (terms : MaterialsTerms) (place : PlaceId)
    (shareTime query : Moment) (allocation : MaterialsAllocation material) : Prop :=
  let shares := evidence.shareHistory
  let scope := (terms.lesson, place)
  shareTime.by evidence.entitlementVerifiedAt ∧
  shares.verifiedOriginal terms shares.originalReference shares.agreedSharesAt ∧
  ∃ original, shares.agreedSharesAt shareTime = some original ∧
    ∃ operative,
      privateArrangementAt
        (fun change person ↦
          ¬(person ∈ change.prior.terms.holders ↔ person ∈ change.replacement.terms.holders) ∨
          (∃ base : Amount, 0 ≤ base ∧ change.prior.terms.portion person place base ≠
            change.replacement.terms.portion person place base) ∨
          shares.furtherAffected change person)
        shares.verifiedAssent shares.assents query
        ⟨scope, shares.originalReference, original, terms.agreedAt⟩
        ((shares.amendments.filter (fun change ↦ change.replacement.scope == scope)).mergeSort
          (fun first second ↦
            decide (first.replacement.effectiveAt.by second.replacement.effectiveAt)))
        operative ∧
      operative.effectiveAt.by evidence.entitlementVerifiedAt ∧ allocation = operative.terms

def MaterialsShareEvidence.transferApplies {material : MaterialId}
    (evidence : MaterialsShareEvidence material) (use : VerifiedMaterialsUse) (place : PlaceId)
    (postingAt : Moment) (record : MaterialsTransferRecord material) : Prop :=
  record.governs use.lesson.id evidence.originalSettlementReference place ∧
  record.transfer.effectiveAt.by postingAt ∧
  ∃ priorUse ∈ use.findings, priorUse.place = place ∧ priorUse.material = material ∧
    priorUse.usedAt.before record.transfer.effectiveAt

def MaterialsShareEvidence.chargeEstablishedAt {material : MaterialId}
    (evidence : MaterialsShareEvidence material) : Moment :=
  (evidence.shortfall.map MaterialsShortfall.identifiedAt).getD evidence.originalSettlementAt

def MaterialsShareEvidence.collectionsAtTransfer {material : MaterialId}
    (evidence : MaterialsShareEvidence material) (record : MaterialsTransferRecord material)
    (lesson : LessonId) (place : PlaceId) : List MaterialsCollection :=
  match evidence.shortfall with
  | none => record.originalCollections lesson evidence.originalSettlementReference place
  | some shortfall =>
    record.shortfallCollections lesson evidence.originalSettlementReference shortfall.reference place

def MaterialsShareEvidence.collectionsMatch {material : MaterialId}
    (evidence : MaterialsShareEvidence material) (use : VerifiedMaterialsUse)
    (terms : MaterialsTerms) (postingAt : Moment)
    (receivedBefore : ActorId → Moment → Amount) : Prop :=
  let charges := use.chargesFor terms material
  ∀ record ∈ evidence.transfers,
    (evidence.shortfall.isSome = true ∨
      evidence.chargeEstablishedAt.before record.transfer.effectiveAt) →
    (∃ charge ∈ charges, evidence.transferApplies use charge.place postingAt record) →
    let collections := charges.flatMap (fun charge ↦
      evidence.collectionsAtTransfer record use.lesson.id charge.place)
    (∀ receipt ∈ collections, 0 ≤ receipt.amount ∧
      evidence.originalSettlementAt.by receipt.collectedAt ∧
      receipt.collectedAt.before record.transfer.effectiveAt) ∧
    ∀ holder, sumAmounts (collections.filter (fun receipt ↦ receipt.holder == holder))
      MaterialsCollection.amount = receivedBefore holder record.transfer.effectiveAt

/-- Read the share basis for the affected income, including agreed changes in force at transfer. -/
def MaterialsShareEvidence.transferBasisAt {material : MaterialId}
    (evidence : MaterialsShareEvidence material) (terms : MaterialsTerms) (charge : MaterialsCharge)
    (firstActualUse : Moment) (record : MaterialsTransferRecord material)
    (allocation : MaterialsAllocation material) : Prop :=
  let effectiveAt := record.transfer.effectiveAt
  let shareTime := if evidence.shortfall.isNone ∧ ¬ evidence.chargeEstablishedAt.before effectiveAt
    then firstActualUse
    else terms.ordinaryShareTime material charge.place firstActualUse evidence.originalSettlementAt
  evidence.allocationAt terms charge.place shareTime effectiveAt allocation

/-- Gross portions under this transfer, including each holder's own earlier collections. -/
def MaterialsShareEvidence.transferPortionsAt {material : MaterialId}
    (evidence : MaterialsShareEvidence material) (terms : MaterialsTerms) (use : VerifiedMaterialsUse)
    (charge : MaterialsCharge) (firstActualUse : Moment) (shareBase : Amount)
    (record : MaterialsTransferRecord material) (gross : ActorId → Amount) : Prop :=
  let historicalShares := fun point ↦ evidence.allocationAt terms charge.place point point
  let alreadySettled := evidence.chargeEstablishedAt.before record.transfer.effectiveAt
  let collected := if evidence.shortfall.isSome = true ∨ alreadySettled then
    evidence.collectionsAtTransfer record use.lesson.id charge.place else []
  let totalCollected := sumAmounts collected MaterialsCollection.amount
  let divides := fun allocation : MaterialsAllocation material ↦ fun base ↦
    allocation.agreementReference ≠ "" ∧ allocation.distributesCharge charge.place base ∧
    ∀ holder, gross holder =
      sumAmountsWhere collected (fun receipt ↦ receipt.holder == holder) MaterialsCollection.amount +
        allocation.portion holder charge.place base
  record.authorised evidence.sparkDao historicalShares ∧
  record.transfer.effectiveAt.by evidence.entitlementVerifiedAt ∧
  (∀ receipt ∈ collected, 0 ≤ receipt.amount ∧
    evidence.originalSettlementAt.by receipt.collectedAt ∧
    receipt.collectedAt.before record.transfer.effectiveAt) ∧
  totalCollected ≤ shareBase ∧
  match evidence.shortfall with
  | some _ => divides record.transfer.laterShortfall (shareBase - totalCollected)
  | none =>
    if alreadySettled then
      divides record.transfer.settledUncollected (shareBase - totalCollected)
    else
      ∃ allocation,
        record.transfer.priorUnsettledAllocation firstActualUse
          (fun point ↦ evidence.allocationAt terms charge.place point record.transfer.effectiveAt)
          allocation ∧
        divides allocation shareBase

/-- This transfer can move the covered amount only within its named pair and towards its recipient. -/
def MaterialsTransfer.reallocates {material : MaterialId} (transfer : MaterialsTransfer material)
    (prior next : ActorId → Amount) : Prop :=
  let source := transfer.transferor
  let destination := transfer.transferee
  source ≠ destination ∧
  (∀ holder, ¬(holder = source ∨ holder = destination) → next holder = prior holder) ∧
  next source ≤ prior source ∧ next source + next destination = prior source + prior destination

def MaterialsTransfer.applyPair {material : MaterialId} (transfer : MaterialsTransfer material)
    (prior next : ActorId → Amount) (holder : ActorId) : Amount :=
  if holder = transfer.transferor ∨ holder = transfer.transferee then next holder else prior holder

/-- Read a sequence of signed allocations, checking each against the preceding gross amounts. -/
def MaterialsShareEvidence.transferredInOrder {material : MaterialId}
    (evidence : MaterialsShareEvidence material) (terms : MaterialsTerms) (use : VerifiedMaterialsUse)
    (charge : MaterialsCharge) (firstActualUse : Moment) (shareBase : Amount) (holder : ActorId) :
    List (MaterialsTransferRecord material) → Option (Moment × (ActorId → Amount)) →
      (ActorId → Amount) → Amount → Prop
  | [], _, prior, portion => portion = prior holder
  | record :: rest, group, prior, portion =>
    let effectiveAt := record.transfer.effectiveAt
    -- Disjoint transfers at the same effective time use one opening allocation.
    let opening := match group with
      | some (time, gross) => if time = effectiveAt then gross else prior
      | none => prior
    ∃ next, evidence.transferPortionsAt terms use charge firstActualUse shareBase record next ∧
      record.transfer.reallocates opening next ∧
      evidence.transferredInOrder terms use charge firstActualUse shareBase holder rest
        (some (effectiveAt, opening)) (record.transfer.applyPair prior next) portion

/-- Apply disjoint transfers against the original basis or strictly ordered transfers whose
    signed amounts agree with each preceding allocation outside the named pair. -/
def MaterialsShareEvidence.composedPortionAt {material : MaterialId}
    (evidence : MaterialsShareEvidence material) (terms : MaterialsTerms) (use : VerifiedMaterialsUse)
    (charge : MaterialsCharge) (firstActualUse postingAt : Moment) (shareBase : Amount)
    (original : ActorId → Amount) (holder : ActorId) (portion : Amount) : Prop :=
  let applicable := evidence.transferApplies use charge.place postingAt
  let party := fun (record : MaterialsTransferRecord material) (actor : ActorId) ↦
    actor = record.transfer.transferor ∨ actor = record.transfer.transferee
  let independent :=
    ∃ gross : MaterialsTransferRecord material → ActorId → Amount,
      (∀ record ∈ evidence.transfers, applicable record →
        (∀ other ∈ evidence.transfers, applicable other →
          (∃ actor, party record actor ∧ party other actor) → other = record) ∧
        evidence.transferPortionsAt terms use charge firstActualUse shareBase record (gross record) ∧
        record.transfer.reallocates original (gross record)) ∧
      (((∀ record ∈ evidence.transfers, applicable record → ¬ party record holder) ∧
          portion = original holder) ∨
        ∃ record ∈ evidence.transfers, applicable record ∧ party record holder ∧
          portion = gross record holder)
  let sequential :=
    ∃ ordered : List (MaterialsTransferRecord material),
      (∀ record, record ∈ ordered ↔ record ∈ evidence.transfers ∧ applicable record) ∧
      ordered.Pairwise (fun earlier later ↦
        earlier.transfer.effectiveAt.before later.transfer.effectiveAt ∨
        (earlier.transfer.effectiveAt = later.transfer.effectiveAt ∧
          ¬ ∃ actor, party earlier actor ∧ party later actor)) ∧
      evidence.transferredInOrder terms use charge firstActualUse shareBase holder
        ordered none original portion
  ∃ first ∈ evidence.transfers, applicable first ∧
    ∃ second ∈ evidence.transfers, applicable second ∧ second ≠ first ∧
      (independent ∨ sequential)

def MaterialsShareEvidence.portionAt {material : MaterialId}
    (evidence : MaterialsShareEvidence material) (terms : MaterialsTerms) (use : VerifiedMaterialsUse)
    (charge : MaterialsCharge) (firstActualUse postingAt : Moment) (holder : ActorId)
    (portion : Amount) : Prop :=
  let shareBase : Amount := match evidence.shortfall with
    | none => charge.amount
    | some shortfall =>
      sumAmountsWhere shortfall.charges (·.place == charge.place) (·.amount)
  let shareTime := terms.ordinaryShareTime material charge.place firstActualUse
    evidence.originalSettlementAt
  let originalBasis := evidence.allocationAt terms charge.place shareTime postingAt
  let applicable := evidence.transferApplies use charge.place postingAt
  (match evidence.shortfall with
    | none => True
    | some _ => 0 ≤ shareBase) ∧
  (((∀ record ∈ evidence.transfers, ¬ applicable record) ∧
    ∃ allocation, originalBasis allocation ∧ allocation.agreementReference ≠ "" ∧
      allocation.distributesCharge charge.place shareBase ∧
      portion = allocation.portion holder charge.place shareBase) ∨
  (∃ record ∈ evidence.transfers, applicable record ∧
    (∀ other ∈ evidence.transfers, applicable other → other = record) ∧
    ∃ allocation, evidence.transferBasisAt terms charge firstActualUse record allocation ∧
      allocation.agreementReference ≠ "" ∧ allocation.distributesCharge charge.place shareBase ∧
    ∃ gross, evidence.transferPortionsAt terms use charge firstActualUse shareBase record gross ∧
      record.transfer.reallocates (fun actor ↦ allocation.portion actor charge.place shareBase) gross ∧
      portion = gross holder) ∨
  (∃ allocation, originalBasis allocation ∧ allocation.agreementReference ≠ "" ∧
    allocation.distributesCharge charge.place shareBase ∧
    evidence.composedPortionAt terms use charge firstActualUse postingAt shareBase
      (fun actor ↦ allocation.portion actor charge.place shareBase) holder portion))

/-- Calculate the holder's payable share from verified use and the applicable historical terms. -/
def MaterialsShareEvidence.eligibleAt {material : MaterialId}
    (evidence : MaterialsShareEvidence material) (use : VerifiedMaterialsUse)
    (terms : MaterialsTerms) (original : MaterialsSettlementRecord)
    (holder : ActorId) (amount : Amount) (postingAt : Moment)
    (knownAt : Moment := postingAt)
    (useBasisVerified : Prop := terms.calculatesVerifiedUse use evidence.advanceCheck
      ((evidence.shortfall.map MaterialsShortfall.identifiedAt).getD
        evidence.originalSettlementAt))
    (shortfalls : List MaterialsShortfall := []) (principal : MaterialsPrincipalContext := {}) :
    Prop :=
  let charges := use.chargesFor terms material
  original.lesson = use.lesson.id ∧ original.material = material ∧
  original.termsReference = terms.agreementReference ∧
  original.reference = evidence.originalSettlementReference ∧
  original.settledAt = evidence.originalSettlementAt ∧
  original.reference ≠ "" ∧
  original.places.Nodup ∧ (original.charges.map MaterialsCharge.place).Nodup ∧
  (∀ row ∈ original.charges, row.place ∈ original.places ∧ row.material = material ∧ 0 ≤ row.amount) ∧
  (∀ row ∈ charges, row.place ∈ original.places) ∧
  use.endedAt.before evidence.originalSettlementAt ∧
  evidence.originalSettlementAt.by evidence.entitlementVerifiedAt ∧
  evidence.chargeEstablishedAt.by postingAt ∧
  postingAt.by knownAt ∧ evidence.entitlementVerifiedAt.by knownAt ∧
  (match evidence.shortfall with
    | none => original.charges = charges
    | some shortfall =>
      shortfall ∈ shortfalls ∧
      shortfall.charges = shortfall.newCharges original shortfalls charges principal use.findings ∧
      (∀ other ∈ shortfalls, other.belongsTo original = true →
        other.identifiedAt = shortfall.identifiedAt →
        shortfall.addsToPlaceCoveredBy other → other = shortfall) ∧
      shortfall.lesson = use.lesson.id ∧ shortfall.material = material ∧
      shortfall.termsReference = terms.agreementReference ∧
      shortfall.originalSettlementReference = evidence.originalSettlementReference ∧
      shortfall.reference ≠ "" ∧
      evidence.originalSettlementAt.before shortfall.identifiedAt ∧
      shortfall.identifiedAt.by evidence.entitlementVerifiedAt) ∧
  useBasisVerified ∧
  ∃ firstActualUse, use.firstConfirmedUse material = some firstActualUse ∧
    ∃ portions : PlaceId → Amount,
      (∀ charge ∈ charges, evidence.portionAt terms use charge firstActualUse
        postingAt holder (portions charge.place)) ∧
      amount = sumAmounts charges (fun charge ↦ portions charge.place) ∧ 0 < amount

/-- Leaving daily work does not cut off a still-valid share under the original terms. -/
def continuingMaterialsEntitlement {material : MaterialId} (contributor : ActorId)
    (allocation : MaterialsAllocation material)
    (shareRemainsValid materialsActuallyUsed : Prop) : Prop :=
  contributor ∈ allocation.holders ∧ shareRemainsValid ∧ materialsActuallyUsed

end SourceV14
