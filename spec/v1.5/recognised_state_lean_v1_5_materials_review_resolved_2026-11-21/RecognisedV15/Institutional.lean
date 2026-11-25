import SourceV14.Operations
import RecognisedV15.State

namespace RecognisedV15

open SourceV14 SourceV14.Booking SourceV14.Confirmation SourceV14.Course
  SourceV14.Settlement SourceV14.Operations

/-- Confirmation uses the actual booking evidence and the same seat's credit.
Neither a booking draft nor an actual transfer proves confirmation on its own. -/
def LessonEvidence.confirmedPlace (state : LessonEvidence) (form : PartOne)
    (booking : BookingEvidence) (roster : Option Roster) : Prop :=
  CanConfirmPlace form booking roster state.creditFee.openingCredit state.creditFee.ledger
    state.creditFee.creditRecords state.creditFee.discounts state.teaching.teachingBegan

theorem LessonEvidence.confirmedPlace_iff (direct : StartEvidence) (form : PartOne)
    (booking : BookingEvidence) (roster : Option Roster) :
    (fromDirect direct).confirmedPlace form booking roster ↔
      CanConfirmPlace form booking roster direct.openingCredit direct.ledger
        direct.creditRecords direct.discounts direct.teachingBegan :=
  Iff.rfl

def LessonEvidence.openingPermitted (state : LessonEvidence) (lesson : Lesson)
    (schedule : Schedule) (atTime : Moment) : Prop :=
  CanStart lesson state.toDirect schedule atTime

/-- Occurrence can be reported even if the start was unauthorised. -/
def LessonEvidence.teachingOccurred (state : LessonEvidence) (atTime : Moment) : Prop :=
  state.teaching.teachingBegan = some atTime

theorem LessonEvidence.openingPermitted_iff (direct : StartEvidence) (lesson : Lesson)
    (schedule : Schedule) (atTime : Moment) :
    (fromDirect direct).openingPermitted lesson schedule atTime ↔
      CanStart lesson direct schedule atTime := by
  simp [openingPermitted]

/-- The same group majority, verified exception path, and handler checks
control settlement as in the direct rules. -/
def LessonEvidence.groupSettlementAllowed (state : LessonEvidence) (lesson : Lesson)
    (schedule : Schedule) (roster : Roster) (start expiry query : Moment)
    (reported verified : Bool) (handler : Handler) (confirmed fault : List PlaceId) : Prop :=
  GroupSettlementAvailable lesson state.toDirect schedule roster start expiry query
    reported verified handler confirmed fault

theorem LessonEvidence.groupSettlementAllowed_iff (direct : StartEvidence) (lesson : Lesson)
    (schedule : Schedule) (roster : Roster) (start expiry query : Moment)
    (reported verified : Bool) (handler : Handler) (confirmed fault : List PlaceId) :
    (fromDirect direct).groupSettlementAllowed lesson schedule roster start expiry query
        reported verified handler confirmed fault ↔
      GroupSettlementAvailable lesson direct schedule roster start expiry query
        reported verified handler confirmed fault := by
  simp [groupSettlementAllowed]

/-- Check the selected route using that request’s authority, time and evidence. -/
def PaymentEvidence.instructionPermitted (state : PaymentEvidence)
    (route : PaymentApprovalRoute) (authority : ReviewAuthorities) (facts : HoldFacts)
    (part : PaymentPart) (schedule : PaymentSchedule) (conditions : PaymentInstruction → Prop)
    (instruction : PaymentInstruction) : Prop :=
  route.allows authority facts state.toDirect part schedule conditions instruction

theorem PaymentEvidence.instructionPermitted_iff (direct : HoldHistory)
    (route : PaymentApprovalRoute) (authority : ReviewAuthorities) (facts : HoldFacts)
    (part : PaymentPart) (schedule : PaymentSchedule) (conditions : PaymentInstruction → Prop)
    (instruction : PaymentInstruction) :
    (fromDirect direct).instructionPermitted route authority facts part schedule conditions
        instruction ↔
      route.allows authority facts direct part schedule conditions instruction := by
  simp [instructionPermitted]

theorem PaymentEvidence.executed_iff (state : PaymentEvidence) (part : PaymentPart)
    (receipt : PostedPayment) :
    (∃ e : ExecutedPayment state part, e.receipt = receipt) ↔
      state.payments.actualPaymentWithEvidence receipt ∧ receipt.instruction.part = part.ref := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.recorded, e.samePart⟩
  · rintro ⟨recorded, samePart⟩
    exact ⟨⟨receipt, recorded, samePart⟩, rfl⟩

theorem PaymentEvidence.qualifiedReceipt_iff (state : PaymentEvidence) (part : PaymentPart)
    (receipt : PostedPayment) :
    (∃ q : QualifiedReceipt state part, q.receipt = receipt) ↔
      state.payments.actualPaymentWithEvidence receipt ∧ receipt.instruction.part = part.ref ∧
        state.payments.recipientReceived part.recipient receipt := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.recorded, q.samePart, q.recipientReceived⟩
  · rintro ⟨recorded, samePart, received⟩
    exact ⟨⟨⟨receipt, recorded, samePart⟩, received⟩, rfl⟩

/-- A receipt is attached to the case without dropping evidence of a
misdirection. Qualification does not yet settle the balance. -/
theorem PaymentEvidence.misdirected_execution (state : PaymentEvidence) (part : PaymentPart)
    (receipt : PostedPayment) (recorded : state.payments.actualPaymentWithEvidence receipt)
    (samePart : receipt.instruction.part = part.ref)
    (notReceived : ¬state.payments.recipientReceived part.recipient receipt) :
    (∃ e : ExecutedPayment state part, e.receipt = receipt) ∧
      ¬(∃ q : QualifiedReceipt state part, q.receipt = receipt) :=
  ⟨(executed_iff state part receipt).mpr ⟨recorded, samePart⟩,
    fun h ↦ notReceived ((qualifiedReceipt_iff state part receipt).mp h).2.2⟩

/-- A particular use finding belongs to the verified file. Verification of
a file with no findings does not recognise any material use. -/
structure RecognisedMaterialUse (raw : VerifiedMaterialsUse) (finding : ConfirmedMaterialUse)
    (atTime : Moment) : Prop where
  listed : finding ∈ raw.findings
  verifiedFile : raw.verifiedBy atTime

theorem recognisedMaterialUse_iff (raw : VerifiedMaterialsUse) (finding : ConfirmedMaterialUse)
    (atTime : Moment) :
    RecognisedMaterialUse raw finding atTime ↔ finding ∈ raw.findings ∧ raw.verifiedBy atTime :=
  ⟨fun h ↦ ⟨h.listed, h.verifiedFile⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Completion under the agreed terms and applicable delivery deadline,
including the direct rule's check for any prior full refund closure. -/
structure RecognisedRemedyDelivery (progress : RemedyProgress) (place : Place)
    (evidence : RemedyEvidence) (atTime : Moment) : Prop where
  delivered : progress.deliveredBy place evidence atTime

theorem recognisedRemedyDelivery_iff (progress : RemedyProgress) (place : Place)
    (evidence : RemedyEvidence) (atTime : Moment) :
    RecognisedRemedyDelivery progress place evidence atTime ↔
      progress.deliveredBy place evidence atTime :=
  ⟨fun h ↦ h.delivered, fun h ↦ ⟨h⟩⟩

end RecognisedV15
