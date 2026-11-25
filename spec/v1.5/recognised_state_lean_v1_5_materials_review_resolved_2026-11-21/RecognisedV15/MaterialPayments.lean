import RecognisedV15.Evidence
import RecognisedV15.Payments
import SourceV14.Workflow

namespace RecognisedV15.MaterialPayments

open SourceV14
open SourceV14.Workflow

private def withPosting (payment : PaymentEvidence) (row : Materials.Receipt) : PaymentEvidence :=
  { payment with payments := { payment.payments with
      posted := payment.payments.posted ++ [row.paid]
      agreedRecipientReceipts :=
        payment.payments.agreedRecipientReceipts ++ row.recipientReceipt.toList } }

/-- A shortfall records newly established charges against the retained settlement.
Posting checks payment approval and funds, adds the transfer and optional designee
receipt to the shared ledger, and records the material receipt at payment time.
Verifying a receipt for an existing transfer makes it usable in funding checks
once the evidence is available. Filing that receipt records the filing time only. -/
def Step (course : LessonEvidence) (payment : PaymentEvidence) (before : Materials.History)
    (event : Materials.Event) (after : Materials.History) (following : PaymentEvidence)
    (principal : MaterialsPrincipalContext) : Prop :=
  match event with
  | .identifyShortfall row =>
    row.original ∈ before.originals ∧
    row.check ∈ before.useChecks ∧
    -- Check the per-place increment using the retained shortfalls and newCharges.
    row.conforms (before.shortfalls.map Materials.Shortfall.record) principal ∧
    (∃ charge ∈ row.additionalCharges, 0 < charge.amount) ∧
    (∀ prior ∈ before.shortfalls, prior.record.belongsTo row.original.record = true →
      row.record.addsToPlaceCoveredBy prior.record →
      prior.record.identifiedAt.before row.record.identifiedAt) ∧
    before.pricingAvailable row.check row.record.identifiedAt ∧
    before.combinedCapAllows row.record.lesson row.additionalCharges row.record.identifiedAt
      principal ∧
    (∀ prior ∈ before.shortfalls, prior.record.lesson = row.record.lesson →
      prior.record.material = row.record.material → prior.record.reference ≠ row.record.reference) ∧
    after = { before with shortfalls := row :: before.shortfalls } ∧
    following = payment
  | .post row =>
    0 < row.paid.instruction.amount ∧
    row.paid.id ∉ payment.payments.posted.map PostedPayment.id ∧
    (∀ recipient ∈ row.recipientReceipt, recipient ∉ payment.payments.agreedRecipientReceipts) ∧
    row.conforms before course.toDirect following.toDirect principal ∧
    after = { before with
      receipts := ⟨row.paid, row.funds, row.paid.instruction.atTime,
        some row.paid.instruction.atTime⟩ :: before.receipts } ∧
    following = withPosting payment row
  | .verifyReceipt row verifiedAt reference =>
    before.verifiesReceiptAt row.paid row.entitlement verifiedAt reference ∧
    row.observedAt before course.toDirect payment.toDirect verifiedAt principal ∧
    after = { before with receipts := ⟨row.paid, row.funds, verifiedAt, none⟩ :: before.receipts } ∧
    following = payment
  | .file paid filedAt =>
    before.canFileReceipt paid filedAt ∧
    after = before.fileReceipt paid filedAt ∧
    following = payment
  | other =>
    Materials.Step course.toDirect payment.toDirect before other after principal ∧ following = payment

private theorem withPosting_toDirect (payment : PaymentEvidence) (row : Materials.Receipt) :
    (withPosting payment row).toDirect = row.postingHistory payment.toDirect := by
  cases recipient : row.recipientReceipt <;>
    simp [withPosting, PaymentEvidence.toDirect, Materials.Receipt.postingHistory,
      Materials.withReceipt, recipient]

private theorem toDirect_eq_iff (following payment : PaymentEvidence) :
    following.toDirect = payment.toDirect ↔ following = payment := by
  constructor
  · intro same
    simpa only [PaymentEvidence.fromDirect_toDirect] using congrArg PaymentEvidence.fromDirect same
  · exact congrArg PaymentEvidence.toDirect

private theorem postingFacts (holds next : HoldHistory) (row : Materials.Receipt)
    (recorded : (Materials.Event.post row).recordsPayment holds next) :
    0 < row.paid.instruction.amount ∧ next = row.postingHistory holds := by
  obtain ⟨posted, posting, recipientStep⟩ := recorded
  cases posting with
  | post _ positive _ =>
    refine ⟨positive, ?_⟩
    cases recipient : row.recipientReceipt with
    | none =>
      simpa [Materials.Receipt.postingHistory, Materials.withReceipt, recipient] using recipientStep
    | some designee =>
      simp only [recipient] at recipientStep
      cases recipientStep
      simp [Materials.Receipt.postingHistory, Materials.withReceipt, recipient]

private theorem post_iff (course : LessonEvidence) (payment : PaymentEvidence)
    (before after : Materials.History) (row : Materials.Receipt) (following : PaymentEvidence)
    (principal : MaterialsPrincipalContext) :
    Step course payment before (.post row) after following principal ↔
      Materials.Step course.toDirect payment.toDirect before (.post row) after principal ∧
        (Materials.Event.post row).recordsPayment payment.toDirect following.toDirect := by
  constructor
  · rintro ⟨positive, fresh, freshRecipient, conforms, rfl, rfl⟩
    rw [withPosting_toDirect] at conforms ⊢
    refine ⟨.post fresh freshRecipient conforms, ⟨Materials.withReceipt payment.toDirect row.paid,
      Payment.Step.post row.paid positive fresh, ?_⟩⟩
    cases recipient : row.recipientReceipt with
    | none => simp [Materials.Receipt.postingHistory, recipient]
    | some designee =>
      obtain ⟨_, ⟨_, _, recipientMatches, _⟩, _⟩ := conforms
      have selected : designee ∈ row.recipientReceipt := by simp [recipient]
      obtain ⟨_, samePaid, _, _, destination, _⟩ := recipientMatches designee selected
      have recorded : designee.paid ∈
          (Materials.withReceipt payment.toDirect row.paid).payments.posted := by
        simp [Materials.withReceipt, samePaid]
      have actualDestination :
          designee.paid.instruction.destination = .person designee.designee := by
        simpa only [samePaid] using destination
      have unrecorded : designee ∉
          (Materials.withReceipt payment.toDirect row.paid).payments.agreedRecipientReceipts :=
        freshRecipient designee selected
      simpa [Materials.Receipt.postingHistory, recipient] using
        Payment.Step.agreedRecipient designee recorded actualDestination unrecorded
  · rintro ⟨localStep, recorded⟩
    obtain ⟨positive, exactHistory⟩ := postingFacts payment.toDirect following.toDirect row recorded
    have exactFollowing : following = withPosting payment row :=
      (toDirect_eq_iff following (withPosting payment row)).mp
        (exactHistory.trans (withPosting_toDirect payment row).symm)
    cases localStep with
    | post fresh freshRecipient conforms =>
      rw [← exactHistory] at conforms
      exact ⟨positive, fresh, freshRecipient, conforms, rfl, exactFollowing⟩

/-- The recognised material payment step is exact on both resulting histories
for every material event and every input history. -/
theorem step_iff (course : LessonEvidence) (payment : PaymentEvidence) (before : Materials.History)
    (event : Materials.Event) (after : Materials.History) (following : PaymentEvidence)
    (principal : MaterialsPrincipalContext) :
    Step course payment before event after following principal ↔
      Materials.Step course.toDirect payment.toDirect before event after principal ∧
        event.recordsPayment payment.toDirect following.toDirect := by
  cases event
  case identifyShortfall row =>
    simp only [Step, Materials.Event.recordsPayment, toDirect_eq_iff]
    constructor
    · rintro ⟨retained, verified, computed, additional, ordered, pricing, cap, fresh, rfl, rfl⟩
      exact ⟨.identifyShortfall retained verified computed additional ordered pricing cap fresh, rfl⟩
    · rintro ⟨localStep, rfl⟩
      cases localStep with
      | identifyShortfall retained verified computed additional ordered pricing cap fresh =>
        exact ⟨retained, verified, computed, additional, ordered, pricing, cap, fresh, rfl, rfl⟩
  case post row => exact post_iff course payment before after row following principal
  case verifyReceipt row verifiedAt reference =>
    simp only [Step, Materials.Event.recordsPayment, toDirect_eq_iff]
    constructor
    · rintro ⟨evidence, observed, rfl, rfl⟩
      exact ⟨.verifyReceipt evidence observed, rfl⟩
    · rintro ⟨localStep, rfl⟩
      cases localStep with
      | verifyReceipt evidence observed =>
        exact ⟨evidence, observed, rfl, rfl⟩
  case file paid filedAt =>
    simp only [Step, Materials.Event.recordsPayment, toDirect_eq_iff]
    constructor
    · rintro ⟨fileable, rfl, rfl⟩
      exact ⟨.file fileable, rfl⟩
    · rintro ⟨localStep, rfl⟩
      cases localStep with
      | file fileable => exact ⟨fileable, rfl, rfl⟩
  all_goals simp only [Step, Materials.Event.recordsPayment, toDirect_eq_iff]

end RecognisedV15.MaterialPayments
