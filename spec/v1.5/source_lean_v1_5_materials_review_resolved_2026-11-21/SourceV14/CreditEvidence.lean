import SourceV14.Confirmation
import SourceV14.Fault
import SourceV14.Review

namespace SourceV14.CreditEvidence

open Booking Confirmation Settlement

/-! Clauses 2.3 and 3.5. Evidence for increases in usable credit and returns of top-up funds. -/

/-- A retained applicable review changes the earlier fault finding of this place. -/
structure FaultFindingReplacement where
  place : PlaceId
  earlierAt : Moment
  review : ReviewFinding

inductive FaultDecision where
  | initial (finding : InitialFinding)
  | review (finding : ReviewFinding)

def FaultDecision.decidedAt : FaultDecision → Moment
  | .initial finding => finding.decidedAt
  | .review finding => finding.decidedAt

inductive FindingDisposition where
  | fault (basis : FaultBasis)
  | other

/-- The recorded outcome accompanying this particular decision, rather than another review. -/
structure FaultDecisionRecord where
  decision : FaultDecision
  place : PlaceId
  disposition : FindingDisposition

/-- Authorisation and actual verified facts are deliberately separate. -/
structure DecisionRecords where
  authorities : ReviewAuthorities
  terms : ReviewTerms
  appointments : List ReviewAppointment
  initialFindings : List InitialFinding := []
  reviewFindings : List ReviewFinding := []
  faultOutcomes : List FaultDecisionRecord
  faultReplacements : List FaultFindingReplacement := []
  /-- Verified scope of the matter, including the places covered by a class finding. -/
  faultMatterCovers : ReviewMatter → PlaceId → Prop
  /-- Verified tutor assignment for the affected lesson in the fault finding. -/
  wasResponsibleTutor : Lesson → TutorFaultFinding → Prop
  /-- When the affected student attended or was ready to attend the original lesson. -/
  originalAttendanceTime : LessonId → PlaceId → Moment → Prop

def FaultDecision.effectiveFor (d : FaultDecision) (records : DecisionRecords)
    (lesson : LessonId) (place : PlaceId) (query : Moment) : Prop :=
  match d with
  | .initial finding => finding.matter.lesson = lesson ∧ finding.issue = .fault ∧
      finding.decidedAt.by query ∧ records.faultMatterCovers finding.matter place ∧
      initialFindingConforms records.authorities records.terms records.appointments finding
  | .review finding => finding.matter.lesson = lesson ∧ finding.decidedAt.by query ∧
      records.faultMatterCovers finding.matter place ∧
      reviewFindingConforms records.authorities records.appointments finding

def DecisionRecords.faultStillApplies (records : DecisionRecords) (f : PartOne)
    (matter : ReviewMatter) (oldAt query : Moment) : Prop :=
  ¬∃ replacement ∈ records.faultReplacements, replacement.place = f.place.id ∧
    replacement.earlierAt = oldAt ∧ replacement.review.matter.sameCase matter ∧
    oldAt.before replacement.review.decidedAt ∧ replacement.review.decidedAt.by query ∧
    records.faultMatterCovers replacement.review.matter f.place.id ∧
    reviewFindingRecordedConforms records.authorities (some f.contacts.reviewer)
      records.appointments records.initialFindings records.reviewFindings replacement.review

/-- The finding uses the staff and timing terms applicable to the actual original form. -/
def FaultDecision.effectiveForForm (d : FaultDecision) (records : DecisionRecords)
    (f : PartOne) (query : Moment) : Prop :=
  records.terms.coordinator = f.lesson.coordinator ∧
  records.terms.leadAcademicTutor = f.contacts.leadAcademicTutor ∧
  match d with
  | .initial finding =>
    finding.matter.lesson = f.lesson.id ∧ finding.issue = .fault ∧
    finding.decidedAt.by query ∧ records.faultMatterCovers finding.matter f.place.id ∧
    records.faultStillApplies f finding.matter finding.decidedAt query ∧
    initialFindingRecordedConforms records.authorities records.terms f.contacts.substitute
      records.appointments records.initialFindings finding
  | .review finding =>
    finding.matter.lesson = f.lesson.id ∧ finding.decidedAt.by query ∧
    records.faultMatterCovers finding.matter f.place.id ∧
    records.faultStillApplies f finding.matter finding.decidedAt query ∧
    reviewFindingRecordedConforms records.authorities (some f.contacts.reviewer)
      records.appointments records.initialFindings records.reviewFindings finding

def FaultDecisionWhenRequired (basis : FaultBasis) (disputed : Bool)
    (authority : Option FaultDecisionRecord) (records : DecisionRecords)
    (f : PartOne) (query : Moment) : Prop :=
  let required := match basis with
    | .tutor _ _ => True
    | .provider _ => disputed = true
  required → ∃ row ∈ records.faultOutcomes, authority = some row ∧ row.place = f.place.id ∧
    row.disposition = .fault basis ∧ row.decision.effectiveForForm records f query

/-- The confirmed price and its verified private amendments, in effective order. -/
structure LessonFeeAmendments where
  originalReference : PartOne → Option EvidenceRef := fun _ ↦ none
  authenticReference : EvidenceRef → PartOne → Prop := fun _ _ ↦ False
  amendments : List (PrivateAmendment (LessonId × PlaceId) Amount) := []
  assents : List PrivateAmendmentAssent := []
  furtherAffected : PrivateAmendment (LessonId × PlaceId) Amount → ActorId → Prop :=
    fun _ _ ↦ False
  authenticAssent : PrivateAmendment (LessonId × PlaceId) Amount → PrivateAmendmentAssent → Prop :=
    fun _ _ ↦ False

/-- Sections 4.4 and 6.5. Existing terms carry forward until a duly agreed change takes effect. -/
def LessonFeeAmendments.feeAt (facts : LessonFeeAmendments) (f : PartOne) (query : Moment)
    (amount : Amount) : Prop :=
  let scope := (f.lesson.id, f.place.id)
  let changes := (facts.amendments.filter (fun change ↦ change.replacement.scope == scope)).mergeSort
    (fun first second ↦ decide (first.replacement.effectiveAt.by second.replacement.effectiveAt))
  let original reference : PrivateArrangement (LessonId × PlaceId) Amount :=
    { scope, reference, terms := f.place.feePayable, effectiveAt := f.confirmedAt }
  let verifiedReference reference :=
    facts.originalReference f = some reference ∧ facts.authenticReference reference f
  (¬(∃ reference, verifiedReference reference) ∧ amount = f.place.feePayable) ∨
    ∃ reference, verifiedReference reference ∧ ∃ operative,
      privateArrangementAt
        (fun change person ↦ person = f.lesson.provider ∨ person = f.place.customer ∨
          person = f.place.payer ∨ facts.furtherAffected change person)
        (fun change assent ↦ 0 ≤ change.replacement.terms ∧ facts.authenticAssent change assent)
        facts.assents query (original reference) changes operative ∧
      amount = operative.terms

/-- Check the actual debit against the fee in force. A decrease can leave excess credit to return. -/
def LessonFeeAmendments.paidInFull (facts : LessonFeeAmendments) (f : PartOne)
    (ledger : List CreditPosting) (discounts : List DiscountRecord) (query : Moment) : Prop :=
  ∃ fee, facts.feeAt f query fee ∧
    ((fee = 0 ∧ ∃ discount ∈ discounts, discount.covers f.place query) ∨
      (0 < fee ∧ fee ≤ debitTotal f.place ledger query - creditsRestoredFor f.place ledger query))


/-- §3.2 uses payment of the place, even when a different person paid. -/
def FaultMatchesEvidence (f : PartOne) (basis : FaultBasis) (records : DecisionRecords)
    (ledger : List CreditPosting) (discounts : List DiscountRecord)
    (fees : LessonFeeAmendments) (query : Moment) : Prop :=
  basis.applies (basis.lessonWithResponsibleTutor f.lesson) f.place ∧
  match basis with
  | .tutor finding _ =>
    records.wasResponsibleTutor f.lesson finding ∧
    ∃ attendance, records.originalAttendanceTime f.lesson.id f.place.id attendance ∧
      attendance.by query ∧ fees.paidInFull f ledger discounts attendance
  | .provider _ => True

/-- The original lesson's fault, the accepted standard package and the actual issue record. -/
structure CompensationCreditOrigin where
  originalForm : PartOne
  lesson : Lesson
  original : Place
  fault : FaultBasis
  authority : Option FaultDecisionRecord
  disputed : Bool
  decisions : DecisionRecords
  originalDiscounts : List DiscountRecord
  agreement : RemedyAgreement
  issue : CourseCreditIssue

/-- The return entitlement comes from the terms of the actual top-up transaction. -/
structure TopUpReturnAuthorisation where
  receipt : Nat
  cap : Amount
  appliesAt : Moment → Prop
  returnableBefore : Moment → Amount

/-- The receipt records the amount received. The posting is when credit became usable. -/
def topUpPostingMatches (receipt : TopUpReceipt) (posting : CreditPosting) : Prop :=
  posting.kind = .topUp receipt.id ∧ posting.account = receipt.account ∧
    posting.amount = receipt.received ∧ 0 < receipt.received ∧
    receipt.receivedAt.by posting.point

def CompensationCreditOrigin.matchesPosting (grant : CompensationCreditOrigin)
    (ledger : List CreditPosting) (closed : List FullRefundClosure)
    (ownsAccount : ActorId → AccountId → Prop) (posting : CreditPosting)
    (fees : LessonFeeAmendments) : Prop :=
  grant.originalForm.matches ∧ grant.originalForm.lesson = grant.lesson ∧
    grant.originalForm.place = grant.original ∧
    grant.fault.standardCompensationOffered (grant.fault.lessonWithResponsibleTutor grant.lesson)
      grant.original ∧
    FaultMatchesEvidence grant.originalForm grant.fault grant.decisions ledger
      grant.originalDiscounts fees grant.issue.postedAt ∧
    FaultDecisionWhenRequired grant.fault grant.disputed grant.authority grant.decisions
      grant.originalForm grant.issue.postedAt ∧
    ¬ fullRefundClosedBy grant.original closed posting.point ∧
    courseCreditPostingMatches grant.original grant.agreement grant.issue ownsAccount posting

def topUpReturnedBy (ledger : List CreditPosting) (receipt : Nat) (point : Moment) : Amount :=
  sumAmounts (ledger.filter (fun entry ↦
    decide (entry.kind = .topUpReturn receipt ∧ entry.point.by point))) CreditPosting.amount

/-- A return uses a prior top-up and that transaction's applicable terms. Cumulative
    returns through this posting must fit within the permitted total. -/
def topUpReturnMatches (ledger : List CreditPosting) (receipt : TopUpReceipt)
    (authorisation : TopUpReturnAuthorisation) (posting : CreditPosting) : Prop :=
  posting.kind = .topUpReturn receipt.id ∧ posting.account = receipt.account ∧
    authorisation.receipt = receipt.id ∧ authorisation.appliesAt posting.point ∧
    TopUpReturnBasis receipt authorisation.cap posting.amount ∧
    posting.amount ≤ authorisation.returnableBefore posting.point ∧
    topUpReturnedBy ledger receipt.id posting.point ≤ authorisation.cap ∧
    ∃ original ∈ ledger, topUpPostingMatches receipt original ∧
      original.point.before posting.point

/-- The inputs supply verified receipts, accepted packages and issue records, applicable
    transaction terms (including the verified returnable balance for that receipt) and
    the customers' accounts. Actual lesson refund postings and
    recoveries are accounted for under their own rules. -/
def CreditOriginsValid (ledger : List CreditPosting) (topUps : List TopUpReceipt)
    (grants : List CompensationCreditOrigin)
    (returnAuthorisations : List TopUpReturnAuthorisation)
    (closed : List FullRefundClosure)
    (ownsAccount : ActorId → AccountId → Prop)
    (courseProviderAt : ActorId → Moment → Prop) (fees : LessonFeeAmendments) : Prop :=
  (topUps.map TopUpReceipt.id).Nodup ∧
    (grants.map (fun grant ↦ (grant.original.lesson, grant.original.id))).Nodup ∧
    (returnAuthorisations.map TopUpReturnAuthorisation.receipt).Nodup ∧
    ∀ posting ∈ ledger,
      match posting.kind with
      | .topUp receiptId =>
          (ledger.filter (fun entry ↦ entry.kind == .topUp receiptId)).length = 1 ∧
            ∃ receipt ∈ topUps, topUpPostingMatches receipt posting ∧
              ownsAccount receipt.customer receipt.account ∧
              courseProviderAt receipt.provider receipt.receivedAt
      | .compensation lesson place =>
          (ledger.filter (fun entry ↦ entry.kind == .compensation lesson place)).length = 1 ∧
            ∃ grant ∈ grants, grant.matchesPosting ledger closed ownsAccount posting fees
      | .topUpReturn receiptId =>
          ∃ receipt ∈ topUps, receipt.id = receiptId ∧
            ∃ authorisation ∈ returnAuthorisations,
              topUpReturnMatches ledger receipt authorisation posting
      | _ => True

end SourceV14.CreditEvidence
