import SourceV14.Workflow.Materials
import Init.Data.Rat.Lemmas

/-! §5.4 and §6.3. One settled materials charge and a transfer recorded after payment.
These witnesses check the share calculation, the filing's evidence cutoff and the receipt ledger. -/

namespace SourceV14.FidelityMaterialsTimeChecks

open SourceV14.Workflow.Materials

private def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩
private def lesson : Lesson := ⟨42, .oneToOne, 10, 20, 30, 60⟩
private def place : Place := ⟨1, lesson.id, 40, 50, 60, 70, 100, 100⟩
private def material : MaterialId := 7
private def transferor : ActorId := 1
private def transferee : ActorId := 2

private def whole (m : MaterialId) (holder : ActorId) : MaterialsAllocation m :=
  ⟨"one rights holder", [holder], fun _ _ base ↦ base⟩

private def terms : MaterialsTerms where
  lesson := lesson.id
  adoptedBy := lesson.provider
  agreedAt := tick 0
  agreementReference := "materials terms"
  accountingAndPaymentParty := lesson.provider
  materialsOrBundle := "one text"
  contact := "coordinator"
  licensedUse := (· = material)
  sharesAndAdjustmentsReference := "original share"
  sharesInForce := fun m _ ↦ some (whole m transferor)
  contributors := fun _ ↦ [transferor]
  consents := [⟨material, transferor, "materials terms", tick 0⟩]
  ordinaryShareTime := fun _ _ firstUse _ ↦ firstUse
  paymentDue := tick 20
  paymentDeadline := tick 20
  pricing := .standardBundle [⟨material, 1 / 10⟩]

private def useAuthority : MaterialsUseAuthority where
  authorities :=
    { corePartner := fun _ _ ↦ False
      initialFinding := fun _ _ _ ↦ False
      reviewer := fun _ _ _ ↦ False
      approvesPayment := fun _ _ _ ↦ False
      interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
      originalDecisionMaker := fun _ ↦ none
      originalSettlementProposers := fun _ ↦ []
      originalSettlementApprovers := fun _ ↦ [] }
  matterFor := fun _ ↦ ⟨1, lesson.id, [transferor]⟩
  recusalFor := fun _ ↦ none

private def finding : ConfirmedMaterialUse :=
  ⟨lesson.id, place.id, material, 1, tick 2, lesson.coordinator, tick 4,
    .lessonRecord "observed teaching"⟩

private def used : VerifiedMaterialsUse where
  lesson := lesson
  startedAt := tick 2
  endedAt := tick 3
  tutorReport := some
    ⟨lesson.id, lesson.tutor, lesson.coordinator, tick 1, [material], tick 4, [material]⟩
  authority := useAuthority
  places := [place]
  deliveryReports := []
  findings := [finding]
  verifiesEvidence := fun f ↦ f = finding
  verifiedReportOmission := fun _ ↦ False
  uniquePlaces := by simp
  placeInLesson := by simp [Place.matches, place]
  findingInLesson := by simp [finding]
  findingAtPlace := by simp [finding]

private def charge : MaterialsCharge := ⟨place.id, material, 10⟩
private def original : Settlement :=
  ⟨⟨lesson.id, material, terms.agreementReference, "settlement", 8, tick 5, [place.id], [charge]⟩,
    ⟨used, terms, none, tick 4⟩⟩

private def disposition (effectiveAt : Moment) : MaterialsTransfer material :=
  ⟨transferor, transferee, .voluntaryTransfer, effectiveAt, .sharesAtFirstUse,
    whole material transferee, whole material transferee⟩

private def transfer (recordedAt : Moment) (effectiveAt : Moment := tick 10) : Transfer where
  material := material
  record :=
    { transfer := disposition effectiveAt
      reference := "signed transfer"
      verifiedTerms := fun ref change ↦ ref = "signed transfer" ∧ change = disposition effectiveAt
      transferorShareTime := tick 5
      applicableOwnershipTime := (· = tick 5)
      voluntary := True
      publishedTermsSatisfied := True
      governs := fun id ref p ↦ id = lesson.id ∧ ref = original.record.reference ∧ p = place.id
      originalCollections := fun _ _ _ ↦ []
      shortfallCollections := fun _ _ _ _ ↦ [] }
  sparkDao := lesson.provider
  recordedAt := recordedAt

private def rights (holder : ActorId) (verifiedAt : Moment) : Entitlement where
  original := original
  shortfall := none
  holder := holder
  amount := 10
  verifiedAt := verifiedAt
  sparkDao := lesson.provider
  shareHistory :=
    { originalReference := 17
      agreedSharesAt := fun _ ↦ some (whole material transferor)
      verifiedOriginal := fun agreement ref shares ↦ agreement = terms ∧ ref = 17 ∧
        shares = fun _ ↦ some (whole material transferor) }

private def registered (transfers : List Transfer) : History :=
  { originals := [original], transfers := transfers }

private theorem priced : terms.calculatesVerifiedUse used none (tick 5) := by
  simp [MaterialsTerms.calculatesVerifiedUse, MaterialsTerms.adoptedFor,
    MaterialsTerms.agreedBy, MaterialsTerms.covers, MaterialsPricing.covers,
    VerifiedMaterialsUse.verifiedBy, TutorMaterialsReport.timely, MaterialsUseAuthority.mayCheck,
    ReviewAuthorities.disinterested, DirectInterest.affected, useAuthority, used, finding,
    StandardMaterialsBundle, VerifiedMaterialsUse.combination, VerifiedMaterialsUse.materialsAt,
    materialsCombinationWithinCap, materialsCapBase, MaterialsPricing.charges,
    MaterialsPricing.chargesAt, MaterialsPricing.materials, sumAmounts, materialsCapRate,
    terms, whole, lesson, place, material, tick, Moment.before, Moment.by]
  all_goals decide +kernel

private theorem originalAllocationAt (history : History) (holder : ActorId)
    (verifiedAt knownAt point query : Moment) (seen : point.by verifiedAt)
    (adopted : (tick 0).by verifiedAt) :
    (history.shareEvidence (rights holder verifiedAt) knownAt).allocationAt
      terms place.id point query (whole material transferor) := by
  refine ⟨seen, ⟨rfl, rfl, rfl⟩, whole material transferor, rfl,
    ⟨(terms.lesson, place.id), 17, whole material transferor, tick 0⟩, ?_, adopted, rfl⟩
  simp [History.shareEvidence, rights, privateArrangementAt, terms]

private theorem calculatedCharge : used.chargesFor terms material = [charge] := by decide +kernel

private theorem calculated (history : History) (holder : ActorId)
    (verifiedAt knownAt : Moment)
    (settledBeforeVerification : (tick 5).by verifiedAt)
    (paymentKnown : (tick 20).by knownAt) (verified : verifiedAt.by knownAt)
    (portion : (history.shareEvidence (rights holder verifiedAt) knownAt).portionAt
      terms used charge (tick 2) (tick 20) holder 10) :
    (history.shareEvidence (rights holder verifiedAt) knownAt).eligibleAt
      used terms original.record holder 10 (tick 20) knownAt := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, by simp [original], by simp [original],
    ?_, ?_, (by decide : (tick 3).before (tick 5)), settledBeforeVerification,
    (by decide : (tick 5).by (tick 20)), paymentKnown, verified, ?_, priced, tick 2,
    rfl, fun _ ↦ 10, ?_, ?_, by decide +kernel⟩
  · simpa only [rights, original, List.mem_singleton, forall_eq] using
      (show charge.place ∈ [place.id] ∧ charge.material = material ∧ 0 ≤ charge.amount from
        ⟨by simp [charge], rfl, by decide +kernel⟩)
  · simp [rights, original, calculatedCharge, charge]
  · change [charge] = used.chargesFor terms material
    exact calculatedCharge.symm
  · simpa only [rights, original, calculatedCharge, List.mem_singleton, forall_eq] using portion
  · change (10 : Amount) = sumAmounts (used.chargesFor terms material) (fun _ ↦ 10)
    rw [calculatedCharge]
    decide +kernel

private theorem transfersAt (verifiedAt knownAt recording effectiveAt : Moment) (holder : ActorId)
    (available : recording.by knownAt) :
    ((registered [transfer recording effectiveAt]).shareEvidence (rights holder verifiedAt)
      knownAt).transfers = [(transfer recording effectiveAt).record] := by
  simp [registered, History.shareEvidence, rights, original, Transfer.forMaterial, transfer,
    available]

private theorem appliesAtPayment (history : History) (holder : ActorId)
    (verifiedAt knownAt recording : Moment) :
    (history.shareEvidence (rights holder verifiedAt) knownAt).transferApplies
      used place.id (tick 20) (transfer recording).record := by
  exact ⟨⟨rfl, rfl, rfl⟩, (by decide : (tick 10).by (tick 20)),
    finding, by simp [used], rfl, rfl, (by decide : (tick 2).before (tick 10))⟩

private theorem transfereePortion (verifiedAt knownAt recording : Moment)
    (available : recording.by knownAt) (checked : (tick 10).by verifiedAt)
    (adopted : (tick 0).by verifiedAt) (ownership : (tick 5).by verifiedAt)
    (firstUsed : (tick 2).by verifiedAt) :
    MaterialsShareEvidence.portionAt
      ((registered [transfer recording]).shareEvidence (rights transferee verifiedAt) knownAt)
      terms used charge (tick 2) (tick 20) transferee 10 := by
  refine ⟨trivial, Or.inr (Or.inl ?_)⟩
  refine ⟨(transfer recording).record, ?_, appliesAtPayment _ _ _ _ _, ?_,
    whole material transferor, originalAllocationAt _ _ _ _ _ _ firstUsed adopted,
    (by decide : ("one rights holder" : String) ≠ ""), ?_,
    fun holder ↦ (whole material transferee).portion holder place.id 10,
    ?_, ?_, by decide +kernel⟩
  · rw [transfersAt _ _ _ _ _ available]
    exact List.Mem.head []
  · intro other inRegister _
    rw [transfersAt _ _ _ _ _ available] at inRegister
    exact List.mem_singleton.mp inRegister
  · change (whole material transferor).distributesCharge place.id 10
    simp [MaterialsAllocation.distributesCharge, whole, sumAmounts, Rat.zero_add]
    decide +kernel
  · refine ⟨?_, checked, ?_⟩
    · exact ⟨(by decide : ("signed transfer" : String) ≠ ""), ⟨rfl, rfl⟩,
        ⟨trivial, trivial⟩, (by decide : (tick 5).before (tick 10)), rfl,
        whole material transferor, originalAllocationAt _ _ _ _ _ _ ownership adopted,
        List.Mem.head []⟩
    · have noCollections : (10 : Amount) - 0 = 10 := by decide +kernel
      simp [MaterialsShareEvidence.chargeEstablishedAt, MaterialsShareEvidence.collectionsAtTransfer,
        History.shareEvidence, rights, original, transfer, disposition, charge, whole,
        Moment.before, tick, MaterialsAllocation.distributesCharge, MaterialsAllocation.portion,
        sumAmounts, sumAmountsWhere, Rat.zero_add, noCollections]
      all_goals decide +kernel
  · change (disposition (tick 10)).reallocates
      (fun holder ↦ (whole material transferor).portion holder place.id 10)
      (fun holder ↦ (whole material transferee).portion holder place.id 10)
    refine ⟨by decide, ?_, by decide +kernel, by decide +kernel⟩
    intro holder outside
    have notTransferor : holder ≠ transferor := fun eq ↦ outside (.inl eq)
    have notTransferee : holder ≠ transferee := fun eq ↦ outside (.inr eq)
    simp [MaterialsAllocation.portion, whole, notTransferor, notTransferee]

private theorem originalPortion (history : History) (verifiedAt knownAt : Moment)
    (seen : (tick 2).by verifiedAt) (adopted : (tick 0).by verifiedAt)
    (noApplicable : ∀ record ∈ (history.shareEvidence (rights transferor verifiedAt) knownAt).transfers,
      ¬(history.shareEvidence (rights transferor verifiedAt) knownAt).transferApplies
        used place.id (tick 20) record) :
    (history.shareEvidence (rights transferor verifiedAt) knownAt).portionAt
      terms used charge (tick 2) (tick 20) transferor 10 := by
  refine ⟨trivial, Or.inl ⟨noApplicable, whole material transferor, ?_,
    (by decide : ("one rights holder" : String) ≠ ""), ?_, ?_⟩⟩
  · exact originalAllocationAt _ _ _ _ (tick 2) (tick 20) seen adopted
  · change (whole material transferor).distributesCharge place.id 10
    simp [MaterialsAllocation.distributesCharge, whole, sumAmounts, Rat.zero_add]
    decide +kernel
  · change (10 : Amount) = (whole material transferor).portion transferor place.id 10
    decide +kernel

theorem originalShareAtPaymentBeforeTransferIsRecorded :
    MaterialsShareEvidence.eligibleAt
      ((registered [transfer (tick 30)]).shareEvidence (rights transferor (tick 5)) (tick 20))
      used terms original.record transferor 10 (tick 20) := by
  refine calculated _ _ _ _ (by decide) (by decide) (by decide)
    (originalPortion _ _ _ (by decide) (by decide) ?_)
  intro record known
  simp [History.shareEvidence, registered, transfer, rights, original, tick, Moment.by,
    Moment.before] at known
  exact (List.not_mem_nil known).elim

theorem transferKnownAndVerifiedBeforePayment :
    MaterialsShareEvidence.eligibleAt
      ((registered [transfer (tick 11)]).shareEvidence (rights transferee (tick 15)) (tick 20))
      used terms original.record transferee 10 (tick 20) :=
  calculated _ _ _ _ (by decide) (by decide) (by decide)
    (transfereePortion _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide))

theorem paymentCanBeAttributedAfterLateTransferRegistration :
    MaterialsShareEvidence.eligibleAt
      ((registered [transfer (tick 30)]).shareEvidence (rights transferee (tick 40)) (tick 40))
      used terms original.record transferee 10 (tick 20) (tick 40) :=
  calculated _ _ _ _ (by decide) (by decide) (by decide)
    (transfereePortion _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide))

theorem transferEffectiveAfterPaymentDoesNotChangeItsShare :
    MaterialsShareEvidence.eligibleAt
      ((registered [transfer (tick 30) (tick 35)]).shareEvidence (rights transferor (tick 40))
        (tick 40))
      used terms original.record transferor 10 (tick 20) (tick 40) := by
  refine calculated _ _ _ _ (by decide) (by decide) (by decide)
    (originalPortion _ _ _ (by decide) (by decide) ?_)
  intro record known applies
  rw [transfersAt _ _ _ _ _ (by decide : (tick 30).by (tick 40))] at known
  obtain rfl := List.mem_singleton.mp known
  exact (show ¬(tick 35).by (tick 20) from by decide) applies.2.1

theorem laterVerificationCannotAuthorizePostingAtTheEarlierTime :
    ¬ MaterialsShareEvidence.eligibleAt
      ((registered [transfer (tick 30)]).shareEvidence (rights transferee (tick 40)) (tick 20))
      used terms original.record transferee 10 (tick 20) := by
  intro eligible
  rcases eligible with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, verifiedByPayment, _⟩
  exact (show ¬(tick 40).by (tick 20) from by decide) verifiedByPayment

theorem originalHolderHasNoPositivePortionAtFiling :
    ¬ MaterialsShareEvidence.portionAt
      ((registered [transfer (tick 30)]).shareEvidence (rights transferor (tick 40)) (tick 40))
      terms used charge (tick 2) (tick 20) transferor 10 := by
  intro portion
  rcases portion.2 with
    ⟨noneApplies, _⟩ | ⟨entry, retained, _, _, _, _, _, _, _, transferred, _, amount⟩ |
      ⟨_, _, _, _, composed⟩
  · exact noneApplies (transfer (tick 30)).record (by
      rw [transfersAt _ _ _ _ _ (by decide : (tick 30).by (tick 40))]
      exact List.Mem.head []) (appliesAtPayment _ _ _ _ _)
  · rw [transfersAt _ _ _ _ _ (by decide : (tick 30).by (tick 40))] at retained
    obtain rfl := List.mem_singleton.mp retained
    have impossible : (10 : Amount) ≠ 0 := by decide +kernel
    apply impossible
    have divided := transferred.2.2.2.2.2.2 transferor
    simp [MaterialsShareEvidence.chargeEstablishedAt, MaterialsShareEvidence.collectionsAtTransfer,
      History.shareEvidence, rights, original, transfer, disposition, charge, whole,
      Moment.before, tick, MaterialsAllocation.portion, sumAmountsWhere,
      Rat.zero_add, transferor, transferee] at divided
    exact amount.trans divided
  · rcases composed with ⟨first, firstRetained, _, second, secondRetained, _, distinct, _⟩
    rw [transfersAt _ _ _ _ _ (by decide : (tick 30).by (tick 40))] at firstRetained secondRetained
    exact distinct ((List.mem_singleton.mp secondRetained).trans
      (List.mem_singleton.mp firstRetained).symm)

theorem wrongRecipientDoesNotReduceTheTransfereeBalance :
    let purpose := PaymentPurpose.materialsShare material transferee
    let part : PaymentPartRef := ⟨lesson.id, original.record.obligation, 1, purpose⟩
    let wrong : PostedPayment := ⟨1, ⟨part, .person transferor, 10, 10, tick 20⟩, some 20⟩
    let ledger : PaymentHistory := ⟨[wrong], [], []⟩
    ledger.remainingObligationBefore lesson.id original.record.obligation
      (.person transferee none) 10 (tick 40) (some purpose) = 10 := by
  decide +kernel

theorem verificationChecksTheShareAtPaymentUsingAvailableEvidence
    {ev : Course.StartEvidence} {holds : HoldHistory} {before after : History}
    {receipt : Receipt} {verifiedAt : Moment} {reference : EvidenceRef}
    (verified : Step ev holds before (.verifyReceipt receipt verifiedAt reference) after) :
    let row := receipt.entitlement
    (before.shareEvidence row verifiedAt).eligibleAt row.check.use row.check.terms
      row.original.record row.holder row.amount receipt.paid.instruction.atTime verifiedAt
      (useBasisVerified := row.retainedBasis before)
      (shortfalls := before.shortfalls.map Shortfall.record) := by
  cases verified with
  | verifyReceipt _ observed =>
    rcases observed.2.2.2.2.2.2.2 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, eligible, _⟩
    exact eligible

theorem filingLeavesReceiptAvailabilityUnchanged
    {ev : Course.StartEvidence} {holds : HoldHistory} {before after : History}
    {paid checked : PostedPayment} {filedAt point : Moment}
    (filed : Step ev holds before (.file paid filedAt) after) :
    after.hasVerifiedReceiptAt checked point = before.hasVerifiedReceiptAt checked point := by
  cases filed
  unfold History.fileReceipt History.hasVerifiedReceiptAt
  simp only [List.any_map]
  congr 1
  funext entry
  dsimp only [Function.comp_apply]
  split <;> rfl

#print axioms originalShareAtPaymentBeforeTransferIsRecorded
#print axioms transferKnownAndVerifiedBeforePayment
#print axioms paymentCanBeAttributedAfterLateTransferRegistration
#print axioms transferEffectiveAfterPaymentDoesNotChangeItsShare
#print axioms laterVerificationCannotAuthorizePostingAtTheEarlierTime
#print axioms originalHolderHasNoPositivePortionAtFiling
#print axioms wrongRecipientDoesNotReduceTheTransfereeBalance
#print axioms verificationChecksTheShareAtPaymentUsingAvailableEvidence
#print axioms filingLeavesReceiptAvailabilityUnchanged

end SourceV14.FidelityMaterialsTimeChecks
