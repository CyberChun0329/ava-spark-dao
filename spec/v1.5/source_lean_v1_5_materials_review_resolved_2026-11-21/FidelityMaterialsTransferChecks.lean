import SourceV14.Workflow.Materials
import Init.Data.Rat.Lemmas

/-! §5.4. Two signed transfers on the same charge, with different effective and recording times. -/

namespace SourceV14.FidelityMaterialsTransferChecks

open SourceV14.Workflow.Materials

private def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩
private def lesson : Lesson := ⟨42, .oneToOne, 10, 20, 30, 60⟩
private def place : Place := ⟨1, lesson.id, 40, 50, 60, 70, 100, 100⟩
private def material : MaterialId := 7
private def charge : MaterialsCharge := ⟨place.id, material, 10⟩

private def allocation (m : MaterialId) (reference : String) (shares : List (ActorId × Amount)) :
    MaterialsAllocation m :=
  ⟨reference, shares.map Prod.fst,
    fun holder _ _ ↦ sumAmountsWhere shares (fun row ↦ row.1 == holder) Prod.snd⟩

private def agreed (m : MaterialId) : MaterialsAllocation m :=
  allocation m "original shares" [(1, 5), (2, 3), (5, 2)]

private def laterHoldings (m : MaterialId) : MaterialsAllocation m :=
  allocation m "verified later ownership" [(2, 3), (3, 5), (5, 2)]

private def holdingsAt (m : MaterialId) (atTime : Moment) : Option (MaterialsAllocation m) :=
  if (tick 11).by atTime then some (laterHoldings m) else some (agreed m)

private def terms : MaterialsTerms where
  lesson := lesson.id
  adoptedBy := lesson.provider
  agreedAt := tick 0
  agreementReference := "materials terms"
  accountingAndPaymentParty := lesson.provider
  materialsOrBundle := "one text"
  contact := "coordinator"
  licensedUse := (· = material)
  sharesAndAdjustmentsReference := "original shares"
  sharesInForce := holdingsAt
  contributors := fun _ ↦ [1, 2, 5]
  consents := [1, 2, 5].map fun holder ↦ ⟨material, holder, "materials terms", tick 0⟩
  ordinaryShareTime := fun _ _ firstUse _ ↦ firstUse
  paymentDue := tick 20
  paymentDeadline := tick 25
  pricing := .standardBundle [⟨material, 1 / 10⟩]

private def authority : MaterialsUseAuthority where
  authorities :=
    { corePartner := fun _ _ ↦ False
      initialFinding := fun _ _ _ ↦ False
      reviewer := fun _ _ _ ↦ False
      approvesPayment := fun _ _ _ ↦ False
      interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
      originalDecisionMaker := fun _ ↦ none
      originalSettlementProposers := fun _ ↦ []
      originalSettlementApprovers := fun _ ↦ [] }
  matterFor := fun _ ↦ ⟨1, lesson.id, [1, 2, 5]⟩
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
  authority := authority
  places := [place]
  deliveryReports := []
  findings := [finding]
  verifiesEvidence := fun checked ↦ checked = finding
  verifiedReportOmission := fun _ ↦ False
  uniquePlaces := by simp
  placeInLesson := by simp [Place.matches, place]
  findingInLesson := by simp [finding]
  findingAtPlace := by simp [finding]

private abbrev original : Settlement :=
  ⟨⟨lesson.id, material, terms.agreementReference, "settlement", 8, tick 5, [place.id], [charge]⟩,
    ⟨used, terms, none, tick 4⟩⟩

private abbrev rights (holder : ActorId) (amount : Amount) (verifiedAt : Moment) : Entitlement :=
  { original := original
    shortfall := none
    holder := holder
    amount := amount
    verifiedAt := verifiedAt
    sparkDao := lesson.provider
    shareHistory :=
      { originalReference := 17
        agreedSharesAt := holdingsAt material
        verifiedOriginal := fun actual ref shares ↦ actual = terms ∧ ref = 17 ∧
          shares = holdingsAt material } }

private abbrev makeTransfer (reference : String) (source destination : ActorId)
    (effectiveAt recordedAt : Moment) (remaining : MaterialsAllocation material)
    (collections : List MaterialsCollection) (ownershipAt : Moment := tick 5)
    (priorUse : PriorMaterialsUseAllocation material := .sharesAtFirstUse) : Transfer :=
  let disposition : MaterialsTransfer material :=
    ⟨source, destination, .voluntaryTransfer, effectiveAt, priorUse, remaining, remaining⟩
  { material := material
    record :=
      { transfer := disposition
        reference := reference
        verifiedTerms := fun signed actual ↦ signed = reference ∧ actual = disposition
        transferorShareTime := ownershipAt
        applicableOwnershipTime := (· = ownershipAt)
        voluntary := True
        publishedTermsSatisfied := True
        governs := fun id ref seat ↦ id = lesson.id ∧ ref = original.record.reference ∧ seat = place.id
        originalCollections := fun _ _ _ ↦ collections
        shortfallCollections := fun _ _ _ _ ↦ [] }
    sparkDao := lesson.provider
    recordedAt := recordedAt }

private def collectedA : MaterialsCollection := ⟨1, 2, tick 7⟩
private def collectedB : MaterialsCollection := ⟨2, 1, tick 11⟩

private abbrev first : Transfer :=
  makeTransfer "signed by A and C" 1 3 (tick 10) (tick 10)
    (allocation material "A → C" [(2, 3), (3, 3), (5, 2)]) [collectedA]

private abbrev second : Transfer :=
  makeTransfer "signed by B and D" 2 4 (tick 12) (tick 30)
    (allocation material "B → D" [(1, 3), (4, 2), (5, 2)]) [collectedA, collectedB]

private def history (transfers : List Transfer) : History :=
  { originals := [original], transfers := transfers }

private def evidence (transfers : List Transfer) (verifiedAt knownAt : Moment) :
    MaterialsShareEvidence material :=
  (history transfers).shareEvidence (rights 3 3 verifiedAt) knownAt

private theorem priced : terms.calculatesVerifiedUse used none (tick 5) := by
  simp [MaterialsTerms.calculatesVerifiedUse, MaterialsTerms.adoptedFor,
    MaterialsTerms.agreedBy, MaterialsTerms.covers, MaterialsPricing.covers,
    VerifiedMaterialsUse.verifiedBy, TutorMaterialsReport.timely, MaterialsUseAuthority.mayCheck,
    ReviewAuthorities.disinterested, DirectInterest.affected, authority, used, finding,
    StandardMaterialsBundle, VerifiedMaterialsUse.combination, VerifiedMaterialsUse.materialsAt,
    materialsCombinationWithinCap, materialsCapBase, MaterialsPricing.charges,
    MaterialsPricing.chargesAt, MaterialsPricing.materials, sumAmounts, materialsCapRate,
    terms, holdingsAt, agreed, allocation, lesson, place, material, tick, Moment.before, Moment.by]
  all_goals decide +kernel

private theorem shareAt (transfers : List Transfer) (verifiedAt knownAt point query : Moment)
    (seen : point.by verifiedAt) (adopted : (tick 0).by verifiedAt)
    (shares : MaterialsAllocation material) (selected : holdingsAt material point = some shares) :
    (evidence transfers verifiedAt knownAt).allocationAt
      terms place.id point query shares := by
  refine ⟨seen, ⟨rfl, rfl, rfl⟩, shares, selected,
    ⟨(terms.lesson, place.id), 17, shares, terms.agreedAt⟩, ?_, adopted, rfl⟩
  simp only [evidence, History.shareEvidence, rights, List.filter_nil, List.mergeSort_nil,
    privateArrangementAt]

private theorem applies (transfers : List Transfer) (verifiedAt knownAt postingAt : Moment)
    (row : MaterialsTransferRecord material)
    (governs : row.governs lesson.id original.record.reference place.id)
    (effective : row.transfer.effectiveAt.by postingAt)
    (afterUse : (tick 2).before row.transfer.effectiveAt) :
    (evidence transfers verifiedAt knownAt).transferApplies used place.id postingAt row :=
  ⟨governs, effective, finding, by simp [used], rfl, rfl, afterUse⟩

private def gross (row : MaterialsTransferRecord material) (holder : ActorId) : Amount :=
  let collected := row.originalCollections lesson.id original.record.reference place.id
  sumAmountsWhere collected (fun receipt ↦ receipt.holder == holder) MaterialsCollection.amount +
    row.transfer.settledUncollected.portion holder place.id
      (charge.amount - sumAmounts collected MaterialsCollection.amount)

private theorem firstGross
    (transfers : List Transfer) (verifiedAt knownAt : Moment)
    (adopted : (tick 0).by verifiedAt) (held : (tick 5).by verifiedAt)
    (effective : (tick 10).by verifiedAt) :
    (evidence transfers verifiedAt knownAt).transferPortionsAt terms used charge (tick 2) 10
      first.record (gross first.record) := by
  refine ⟨?_, effective, ?_⟩
  · exact ⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩, by decide, rfl, agreed material,
      shareAt _ _ _ _ _ held adopted _ (ite_eq_right (by decide : ¬ (tick 11).by (tick 5))),
      by decide⟩
  · simp [MaterialsShareEvidence.chargeEstablishedAt, MaterialsShareEvidence.collectionsAtTransfer,
      evidence, History.shareEvidence, rights, original, charge, gross,
      allocation, collectedA, Moment.before, tick, MaterialsAllocation.distributesCharge,
      sumAmounts, sumAmountsWhere, Rat.zero_add]
    all_goals decide +kernel

private theorem secondGross (transfers : List Transfer) :
    (evidence transfers (tick 40) (tick 40)).transferPortionsAt terms used charge (tick 2) 10
      second.record (gross second.record) := by
  refine ⟨?_, (by decide : (tick 12).by (tick 40)), ?_⟩
  · exact ⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩, by decide, rfl, agreed material,
      shareAt _ _ _ _ _ (by decide) (by decide) _
        (ite_eq_right (by decide : ¬ (tick 11).by (tick 5))), by decide⟩
  · simp [MaterialsShareEvidence.chargeEstablishedAt, MaterialsShareEvidence.collectionsAtTransfer,
      evidence, History.shareEvidence, rights, original, charge, gross,
      allocation, collectedA, collectedB, Moment.before, tick,
      MaterialsAllocation.distributesCharge, sumAmounts, sumAmountsWhere, Rat.zero_add]
    all_goals decide +kernel

private theorem firstReallocates :
    first.record.transfer.reallocates
      (fun actor ↦ (agreed material).portion actor place.id 10) (gross first.record) := by
  refine ⟨by decide, ?_, by decide +kernel, by decide +kernel⟩
  intro actor outside
  have notA : actor ≠ 1 := fun eq ↦ outside (.inl eq)
  have notC : actor ≠ 3 := fun eq ↦ outside (.inr eq)
  simp [gross, allocation, agreed, collectedA, MaterialsAllocation.portion, sumAmountsWhere,
    notA, notC, Ne.symm notA, Ne.symm notC, Rat.zero_add]

private theorem applyPairOfReallocation (transfer : MaterialsTransfer material)
    {prior next : ActorId → Amount} (reallocated : transfer.reallocates prior next) :
    transfer.applyPair prior next = next := by
  funext holder
  by_cases named : holder = transfer.transferor ∨ holder = transfer.transferee
  · simp [MaterialsTransfer.applyPair, named]
  · simp [MaterialsTransfer.applyPair, named, reallocated.2.1 holder named]

private theorem agreedCharge : (agreed material).distributesCharge place.id 10 := by
  simp [MaterialsAllocation.distributesCharge, agreed, allocation, sumAmounts, sumAmountsWhere]
  decide +kernel

private theorem portion
    (transfers : List Transfer)
    (seen : ∀ row, row ∈ (evidence transfers (tick 40) (tick 40)).transfers ↔
      row = first.record ∨ row = second.record)
    (holder : ActorId) (amount : Amount)
    (slice : (holder = 1 ∨ holder = 3) ∧ amount = gross first.record holder ∨
      (holder = 2 ∨ holder = 4) ∧ amount = gross second.record holder ∨
      holder = 5 ∧ amount = 2) :
    (evidence transfers (tick 40) (tick 40)).portionAt terms used charge (tick 2) (tick 20)
      holder amount := by
  refine ⟨trivial, Or.inr (Or.inr ⟨agreed material,
    shareAt _ _ _ _ _ (by decide : (tick 2).by (tick 40)) (by decide) _
      (ite_eq_right (by decide : ¬ (tick 11).by (tick 2))), by decide, agreedCharge, ?_⟩)⟩
  · change (evidence transfers (tick 40) (tick 40)).composedPortionAt terms used charge
      (tick 2) (tick 20) 10 (fun actor ↦ (agreed material).portion actor place.id 10) holder amount
    have firstApplies := applies transfers (tick 40) (tick 40) (tick 20) first.record ⟨rfl, rfl, rfl⟩
      (by decide) (by decide)
    have secondApplies := applies transfers (tick 40) (tick 40) (tick 20) second.record
      ⟨rfl, rfl, rfl⟩
      (by decide) (by decide)
    have firstSeen := (seen _).2 (.inl rfl)
    have secondSeen := (seen _).2 (.inr rfl)
    have distinct : second.record ≠ first.record := fun eq ↦
      (by decide : second.record.reference ≠ first.record.reference)
        (congrArg MaterialsTransferRecord.reference eq)
    refine ⟨first.record, firstSeen, firstApplies, second.record, secondSeen, secondApplies,
      distinct, .inl ⟨gross, ?_, ?_⟩⟩
    · intro row retained _
      rcases (seen row).1 retained with rfl | rfl
      · refine ⟨?_, firstGross _ _ _ (by decide) (by decide) (by decide), firstReallocates⟩
        intro other inHistory _ overlap
        rcases (seen other).1 inHistory with rfl | rfl
        · rfl
        · obtain ⟨actor, parties⟩ := overlap
          change (actor = 1 ∨ actor = 3) ∧ (actor = 2 ∨ actor = 4) at parties
          rcases parties with ⟨left | left, right | right⟩ <;>
            cases (left.symm.trans right)
      · refine ⟨?_, secondGross _, by decide, ?_, by decide +kernel, by decide +kernel⟩
        · intro other inHistory _ overlap
          rcases (seen other).1 inHistory with rfl | rfl
          · obtain ⟨actor, parties⟩ := overlap
            change (actor = 2 ∨ actor = 4) ∧ (actor = 1 ∨ actor = 3) at parties
            rcases parties with ⟨left | left, right | right⟩ <;>
              cases (left.symm.trans right)
          · rfl
        · intro actor outside
          change ¬(actor = 2 ∨ actor = 4) at outside
          have notB : actor ≠ 2 := fun eq ↦ outside (.inl eq)
          have notD : actor ≠ 4 := fun eq ↦ outside (.inr eq)
          by_cases isA : actor = 1
          · subst actor
            decide +kernel
          · simp [gross, allocation, agreed, collectedA, collectedB,
              MaterialsAllocation.portion, sumAmountsWhere, notB, notD, Ne.symm notB,
              Ne.symm notD, isA, Ne.symm isA, Rat.zero_add]
    · rcases slice with ⟨party, amount⟩ | ⟨party, amount⟩ | ⟨rfl, rfl⟩
      · exact .inr ⟨first.record, firstSeen, firstApplies, party, amount⟩
      · exact .inr ⟨second.record, secondSeen, secondApplies, party, amount⟩
      · refine .inl ⟨?_, by decide +kernel⟩
        intro row retained _
        rcases (seen row).1 retained with rfl | rfl <;> decide

private theorem filed (transfers : List Transfer) (postingAt : Moment) (holder : ActorId)
    (amount : Amount) (positive : 0 < amount)
    (settled : (tick 5).by postingAt) (known : postingAt.by (tick 40))
    (calculated : (evidence transfers (tick 40) (tick 40)).portionAt
      terms used charge (tick 2) postingAt holder amount) :
    (evidence transfers (tick 40) (tick 40)).eligibleAt
      used terms original.record holder amount postingAt (tick 40) := by
  have charges : used.chargesFor terms material = [charge] := by decide +kernel
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, by simp, by simp,
    ?_, ?_, (by decide : (tick 3).before (tick 5)), (by decide : (tick 5).by (tick 40)), settled,
    known, (by decide : (tick 40).by (tick 40)), ?_, priced, tick 2,
    rfl, fun _ ↦ amount, ?_, ?_, positive⟩
  · simpa only [original, List.mem_singleton, forall_eq] using
      (show charge.place ∈ [place.id] ∧ charge.material = material ∧ 0 ≤ charge.amount from
        ⟨by simp [charge], rfl, by decide +kernel⟩)
  · simp [charges, charge]
  · exact charges.symm
  · simpa only [charges, List.mem_singleton, forall_eq] using calculated
  · change amount = sumAmounts (used.chargesFor terms material) (fun _ ↦ amount)
    simp [charges, sumAmounts, Rat.zero_add]

private theorem knownAtFiling : ∀ row,
    row ∈ (evidence [second, first] (tick 40) (tick 40)).transfers ↔
      row = first.record ∨ row = second.record := by
  intro row
  change row ∈ ([second.record, first.record] : List (MaterialsTransferRecord material)) ↔
    row = first.record ∨ row = second.record
  simp [or_comm]

theorem independentSignedTransfersAtPayment :
    (evidence [second, first] (tick 40) (tick 40)).eligibleAt
      used terms original.record 3 3 (tick 20) (tick 40) ∧
    (evidence [second, first] (tick 40) (tick 40)).eligibleAt
      used terms original.record 4 2 (tick 20) (tick 40) ∧
    (evidence [second, first] (tick 40) (tick 40)).eligibleAt
      used terms original.record 5 2 (tick 20) (tick 40) := by
  exact ⟨filed _ _ 3 3 (by decide +kernel) (by decide) (by decide)
      (portion _ knownAtFiling _ _ (by decide +kernel)),
    filed _ _ 4 2 (by decide +kernel) (by decide) (by decide)
      (portion _ knownAtFiling _ _ (by decide +kernel)),
    filed _ _ 5 2 (by decide +kernel) (by decide) (by decide)
      (portion _ knownAtFiling _ _ (by decide +kernel))⟩

private def payment (id : Nat) (row : MaterialsCollection) : PostedPayment :=
  ⟨id, ⟨⟨lesson.id, original.record.obligation, id, .materialsShare material row.holder⟩,
    .person row.holder, lesson.provider, row.amount, row.collectedAt⟩, some id⟩

private def ledger : PaymentHistory := ⟨[payment 1 collectedA, payment 2 collectedB], [], []⟩

private def received (holder : ActorId) (atTime : Moment) : Amount :=
  ledger.receivedForObligationBefore lesson.id original.record.obligation (.person holder none)
    atTime (some (.materialsShare material holder))

theorem priorCollectionsFollowThePayee :
    let ev := evidence [second, first] (tick 40) (tick 40)
    let unpaid := fun holder amount ↦
      ledger.remainingObligationBefore lesson.id original.record.obligation (.person holder none)
        amount (tick 20) (some (.materialsShare material holder))
    ev.collectionsMatch used terms (tick 20) received ∧
    ev.portionAt terms used charge (tick 2) (tick 20) 1 2 ∧
    ev.portionAt terms used charge (tick 2) (tick 20) 2 1 ∧
    unpaid 1 2 = 0 ∧ unpaid 2 1 = 0 ∧ unpaid 3 3 = 3 ∧ unpaid 4 2 = 2 := by
  refine ⟨?_, portion _ knownAtFiling _ _ (by decide +kernel),
    portion _ knownAtFiling _ _ (by decide +kernel), by decide +kernel⟩
  have charges : used.chargesFor terms material = [charge] := by decide +kernel
  intro row retained _ _
  rcases (knownAtFiling row).1 retained with rfl | rfl
  · refine ⟨?_, ?_⟩
    · simp [charges, MaterialsShareEvidence.collectionsAtTransfer, evidence,
        History.shareEvidence, rights, collectedA, Moment.before, tick]
      decide +kernel
    · intro holder
      by_cases isA : holder = 1
      · subst holder
        decide +kernel
      · simp [charges, MaterialsShareEvidence.collectionsAtTransfer, evidence,
          History.shareEvidence, rights, collectedA, collectedB, received, ledger, payment,
          PaymentHistory.receivedForObligationBefore, PaymentHistory.recipientReceived,
          sumAmounts, sumAmountsWhere, tick, Moment.before, isA, Ne.symm isA]
  · refine ⟨?_, ?_⟩
    · simp [charges, MaterialsShareEvidence.collectionsAtTransfer, evidence,
        History.shareEvidence, rights, collectedA, collectedB, Moment.before, tick]
      decide +kernel
    · intro holder
      by_cases isA : holder = 1
      · subst holder
        decide +kernel
      · by_cases isB : holder = 2
        · subst holder
          decide +kernel
        · simp [charges, MaterialsShareEvidence.collectionsAtTransfer, evidence,
            History.shareEvidence, rights, collectedA, collectedB, received, ledger, payment,
            PaymentHistory.receivedForObligationBefore, PaymentHistory.recipientReceived,
            sumAmounts, sumAmountsWhere, tick, Moment.before, isA, isB, Ne.symm isA, Ne.symm isB]

theorem secondTransferIsAbsentBeforeItIsRecorded :
    (evidence [second, first] (tick 15) (tick 20)).portionAt
      terms used charge (tick 2) (tick 20) 2 3 := by
  have stored : (evidence [second, first] (tick 15) (tick 20)).transfers = [first.record] := rfl
  refine ⟨trivial, Or.inr (Or.inl ⟨first.record, ?_,
    applies _ _ _ _ _ ⟨rfl, rfl, rfl⟩ (by decide) (by decide), ?_, agreed material,
    shareAt _ _ _ _ _ (by decide : (tick 2).by (tick 15)) (by decide) _
      (ite_eq_right (by decide : ¬ (tick 11).by (tick 2))),
    by decide, agreedCharge, gross first.record,
    firstGross _ _ _ (by decide) (by decide) (by decide), firstReallocates, by decide +kernel⟩)⟩
  · rw [stored]
    exact List.mem_singleton_self _
  · intro other retained _
    rw [stored] at retained
    exact List.mem_singleton.mp retained

private abbrev originalSplit : MaterialsAllocation material :=
  allocation material "A and C each receive five" [(1, 5), (5, 5)]

private abbrev changedSplit : MaterialsAllocation material :=
  allocation material "C releases five to A" [(1, 10)]

private def splitSchedule (point : Moment) : Option (MaterialsAllocation material) :=
  if (tick 11).by point then some changedSplit else some originalSplit

private def splitTerms : MaterialsTerms :=
  { terms with ordinaryShareTime := fun _ _ _ settledAt ↦ settledAt }

private abbrev newSplit : PrivateAmendment (LessonId × PlaceId) (MaterialsAllocation material) :=
  ⟨⟨(lesson.id, place.id), 17, originalSplit, tick 0⟩,
    ⟨(lesson.id, place.id), 18, changedSplit, tick 10⟩, tick 9⟩

private def splitAssent (holder : ActorId) : PrivateAmendmentAssent :=
  ⟨18, holder, tick 8, holder⟩

private abbrev allToB : MaterialsAllocation material :=
  allocation material "A transfers the remaining amount to B" [(2, 10)]

private theorem allToBDistributes : allToB.distributesCharge place.id 10 := by
  simp [MaterialsAllocation.distributesCharge, allocation, sumAmounts, sumAmountsWhere]
  decide +kernel

private abbrev wholeCharge : Transfer :=
  makeTransfer "signed by A and B only" 1 2 (tick 10) (tick 10) allToB []
    (tick 5) (.otherwiseAgreed allToB)

private abbrev firstUseDefault : Transfer :=
  makeTransfer "signed by A and B with the first-use default" 1 2 (tick 10) (tick 10) allToB []

private def splitEvidence (row : Transfer) (settledAt : Moment)
    (assents : List PrivateAmendmentAssent) : MaterialsShareEvidence material :=
  { evidence [row] (tick 40) (tick 40) with
      originalSettlementAt := settledAt
      shareHistory :=
        { originalReference := 17
          agreedSharesAt := splitSchedule
          verifiedOriginal := fun actual ref schedule ↦
            actual = splitTerms ∧ ref = 17 ∧ schedule = splitSchedule
          amendments := [newSplit]
          assents := assents
          verifiedAssent := fun change assent ↦ change = newSplit ∧
            (assent = splitAssent 1 ∨ assent = splitAssent 5) } }

private theorem splitAmendments (row : Transfer) (settledAt : Moment)
    (assents : List PrivateAmendmentAssent) :
    (((splitEvidence row settledAt assents).shareHistory.amendments.filter
      (fun change ↦ change.replacement.scope == (splitTerms.lesson, place.id))).mergeSort
      (fun first second ↦ decide (first.replacement.effectiveAt.by second.replacement.effectiveAt))) =
    [newSplit] := by
  change ([newSplit].filter (fun change ↦
    change.replacement.scope == (splitTerms.lesson, place.id))).mergeSort _ = _
  simp [splitTerms, terms]

private theorem originalSplitAt (row : Transfer) (settledAt : Moment)
    (assents : List PrivateAmendmentAssent) (point query : Moment)
    (checked : point.by (tick 40)) (same : splitSchedule point = some originalSplit)
    (pending : ¬ (tick 10).by query) :
    (splitEvidence row settledAt assents).allocationAt
      splitTerms place.id point query originalSplit := by
  refine ⟨checked, ⟨rfl, rfl, rfl⟩, originalSplit, same, newSplit.prior,
    ?_, (by decide : (tick 0).by (tick 40)), rfl⟩
  rw [splitAmendments]
  refine Or.inr ⟨?_, rfl⟩
  exact fun adopted ↦ pending adopted.2.2.2.2.2.2.1

private theorem allToBApplies (row : Transfer) (settledAt : Moment)
    (assents : List PrivateAmendmentAssent) :
    (splitEvidence row settledAt assents).transferApplies used place.id (tick 20)
      wholeCharge.record := by
  exact ⟨⟨rfl, rfl, rfl⟩, by decide, finding, by simp [used], rfl, rfl, by decide⟩

private theorem wholeChargeAuthorised (row : Transfer) (settledAt : Moment)
    (assents : List PrivateAmendmentAssent) :
    wholeCharge.record.authorised lesson.provider
      (fun point ↦ (splitEvidence row settledAt assents).allocationAt
        splitTerms place.id point point) := by
  exact ⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩, by decide, rfl, originalSplit,
    originalSplitAt _ _ _ _ _ (by decide) rfl (by decide), by decide⟩

theorem singleTransferCannotTakeCsFive :
    let ev := splitEvidence wholeCharge (tick 5) [splitAssent 1]
    ev.transferPortionsAt splitTerms used charge (tick 2) 10 wholeCharge.record
      (fun holder ↦ allToB.portion holder place.id 10) ∧
    ¬ ev.portionAt splitTerms used charge (tick 2) (tick 20) 2 10 := by
  refine ⟨?_, ?_⟩
  · refine ⟨wholeChargeAuthorised _ _ _, by decide, ?_⟩
    change (∀ receipt ∈ ([] : List MaterialsCollection), _) ∧ 0 ≤ (10 : Amount) ∧
      allToB.agreementReference ≠ "" ∧ allToB.distributesCharge place.id (10 - 0) ∧
      ∀ holder, allToB.portion holder place.id 10 = 0 + allToB.portion holder place.id (10 - 0)
    rw [show (10 : Amount) - 0 = 10 from by decide +kernel]
    exact ⟨by simp, by decide, by decide, allToBDistributes, fun _ ↦ (Rat.zero_add _).symm⟩
  · intro read
    rcases read.2 with ⟨noTransfer, _⟩ |
      ⟨record, present, _, _, basis, verified, _, _, gross, transferred, pair, _⟩ |
      ⟨_, _, _, _, composed⟩
    · exact noTransfer _ (List.mem_singleton_self _) (allToBApplies _ _ _)
    · have sameRecord : record = wholeCharge.record := List.mem_singleton.mp present
      subst record
      have operativeIsOriginal : basis = originalSplit := by
        change (splitEvidence wholeCharge (tick 5) [splitAssent 1]).allocationAt
          splitTerms place.id (tick 5) (tick 10) basis at verified
        rcases verified with ⟨_, _, selected, scheduled, operative, governing, _, equals⟩
        have original : selected = originalSplit := (Option.some.inj scheduled).symm
        subst selected
        rw [splitAmendments] at governing
        rcases governing with ⟨amended, _⟩ | ⟨_, unchanged⟩
        · have affected :=
            amended.2.2.2.2.2.2.2.2 5 (.inl (by decide))
          obtain ⟨signature, retained, _, holder, _⟩ := affected
          obtain rfl := List.mem_singleton.mp retained
          exact ((by decide : (1 : ActorId) ≠ 5) holder).elim
        · exact equals.trans (congrArg PrivateArrangement.terms unchanged)
      have unchanged := pair.2.1 5 (by decide)
      rw [operativeIsOriginal] at unchanged
      have divided := transferred.2.2.2.2.2.2 5
      have zero : gross 5 = 0 := divided.trans (by decide +kernel)
      rw [zero] at unchanged
      exact (by decide +kernel : ¬ (0 : Amount) = originalSplit.portion 5 place.id 10)
        unchanged
    · rcases composed with ⟨left, leftSeen, _, right, rightSeen, _, distinct, _⟩
      exact distinct ((List.mem_singleton.mp rightSeen).trans (List.mem_singleton.mp leftSeen).symm)

theorem unsettledIncomeUsesItsFirstActualUse :
    (splitEvidence firstUseDefault (tick 15) []).portionAt
      splitTerms used charge (tick 2) (tick 20) 5 5 := by
  let ev := splitEvidence firstUseDefault (tick 15) []
  have basis : ev.allocationAt splitTerms place.id (tick 2) (tick 10) originalSplit := by
    refine ⟨by decide, ⟨rfl, rfl, rfl⟩, originalSplit, rfl, newSplit.prior,
      ?_, by decide, rfl⟩
    rw [splitAmendments]
    refine Or.inr ⟨?_, rfl⟩
    intro amended
    obtain ⟨_, impossible, _⟩ := amended.2.2.2.2.2.2.2.2 5 (.inl (by decide))
    exact List.not_mem_nil impossible
  have distributes : originalSplit.distributesCharge place.id 10 := by
    simp [MaterialsAllocation.distributesCharge, allocation, sumAmounts, sumAmountsWhere]
    decide +kernel
  refine ⟨trivial, .inr (.inl ⟨firstUseDefault.record, List.mem_singleton_self _, ?_,
    fun _ retained _ ↦ List.mem_singleton.mp retained, originalSplit, basis,
    by decide, distributes, (fun holder ↦ originalSplit.portion holder place.id 10), ?_,
    ⟨by decide, fun _ _ ↦ rfl, by decide +kernel, rfl⟩, by decide +kernel⟩)⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, by decide, finding, by simp [used], rfl, rfl, by decide⟩
  · refine ⟨?_, by decide, ?_, by decide, originalSplit, basis, by decide, distributes, ?_⟩
    · exact ⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩, by decide, rfl, originalSplit,
        originalSplitAt _ _ _ _ _ (by decide) rfl (by decide), by decide⟩
    · intro receipt retained
      exact (List.not_mem_nil retained).elim
    · intro holder
      exact (Rat.zero_add (originalSplit.portion holder place.id 10)).symm

theorem authorisedAmendmentAtTransferChangesTheAgreedSplit :
    (splitEvidence wholeCharge (tick 15) [splitAssent 1, splitAssent 5]).portionAt
      splitTerms used charge (tick 2) (tick 20) 2 10 := by
  let ev := splitEvidence wholeCharge (tick 15) [splitAssent 1, splitAssent 5]
  have operative : ev.allocationAt splitTerms place.id (tick 2) (tick 10) changedSplit := by
    refine ⟨by decide, ⟨rfl, rfl, rfl⟩, originalSplit, rfl, newSplit.replacement, ?_, by decide, rfl⟩
    rw [splitAmendments]
    refine Or.inl ⟨⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide,
      ⟨5, .inl (by decide)⟩, ?_⟩, rfl⟩
    intro holder affected
    by_cases isA : holder = 1
    · subst holder
      exact ⟨splitAssent 1, List.mem_cons_self, rfl, rfl, by decide, rfl, .inl rfl⟩
    by_cases isC : holder = 5
    · subst holder
      exact ⟨splitAssent 5, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        rfl, rfl, by decide, rfl, .inr rfl⟩
    have restated : (¬ (holder ∈ originalSplit.holders ↔ holder ∈ changedSplit.holders)) ∨
        (∃ base : Amount, 0 ≤ base ∧ originalSplit.portion holder place.id base ≠
          changedSplit.portion holder place.id base) ∨ False := affected
    simp [MaterialsAllocation.portion, allocation, isA, isC] at restated
  refine ⟨trivial, .inr (.inl ⟨wholeCharge.record, List.mem_singleton_self _, allToBApplies _ _ _,
    fun _ retained _ ↦ List.mem_singleton.mp retained, changedSplit, operative,
    by decide, ?_, (fun holder ↦ allToB.portion holder place.id 10), ?_, ?_,
    by decide +kernel⟩)⟩
  · simp [MaterialsAllocation.distributesCharge, allocation, sumAmounts, sumAmountsWhere]
    decide +kernel
  · refine ⟨wholeChargeAuthorised _ _ _, by decide, ?_, by decide, allToB, rfl,
      by decide, allToBDistributes, ?_⟩
    · intro receipt retained
      exact (List.not_mem_nil retained).elim
    · intro holder
      exact (Rat.zero_add (allToB.portion holder place.id 10)).symm
  · refine ⟨by decide, ?_, by decide +kernel, by decide +kernel⟩
    intro holder outside
    have notA : holder ≠ 1 := fun eq ↦ outside (.inl eq)
    have notB : holder ≠ 2 := fun eq ↦ outside (.inr eq)
    simp [MaterialsAllocation.portion, allocation, notA, notB]

private abbrev overlapping : Transfer :=
  makeTransfer "signed by A and D" 1 4 (tick 10) (tick 30)
    (allocation material "A → D" [(2, 3), (4, 3), (5, 2)]) [collectedA]

theorem overlappingTransfersNeedFurtherTerms (holder : ActorId) (amount : Amount) :
    ¬ (evidence [overlapping, first] (tick 40) (tick 40)).portionAt
      terms used charge (tick 2) (tick 20) holder amount := by
  intro read
  have stored : (evidence [overlapping, first] (tick 40) (tick 40)).transfers =
      [overlapping.record, first.record] := rfl
  have firstSeen : first.record ∈ (evidence [overlapping, first] (tick 40) (tick 40)).transfers := by
    rw [stored]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have conflictSeen :
      overlapping.record ∈ (evidence [overlapping, first] (tick 40) (tick 40)).transfers := by
    rw [stored]
    exact List.mem_cons_self
  have firstApplies := applies [overlapping, first] (tick 40) (tick 40) (tick 20) first.record
    ⟨rfl, rfl, rfl⟩ (by decide) (by decide)
  have conflictApplies := applies [overlapping, first] (tick 40) (tick 40) (tick 20)
    overlapping.record
    ⟨rfl, rfl, rfl⟩ (by decide) (by decide)
  have distinct : overlapping.record ≠ first.record := fun eq ↦
    (by decide : overlapping.record.reference ≠ first.record.reference)
      (congrArg MaterialsTransferRecord.reference eq)
  rcases read.2 with ⟨originalOnly, _⟩ | ⟨row, _, _, unique, _⟩ | ⟨_, _, _, _, combined⟩
  · exact originalOnly _ firstSeen firstApplies
  · exact distinct ((unique _ conflictSeen conflictApplies).trans (unique _ firstSeen firstApplies).symm)
  · rcases combined with ⟨_, _, _, _, _, _, _, independent | sequential⟩
    · obtain ⟨_, compatible, _⟩ := independent
      exact distinct ((compatible _ firstSeen firstApplies).1 _ conflictSeen conflictApplies
        ⟨1, .inl rfl, .inl rfl⟩)
    · obtain ⟨ordered, members, chronological, _⟩ := sequential
      have firstListed := (members _).mpr ⟨firstSeen, firstApplies⟩
      have conflictListed := (members _).mpr ⟨conflictSeen, conflictApplies⟩
      have rows (row) (listed : row ∈ ordered) : row = overlapping.record ∨ row = first.record := by
        have retained := ((members row).mp listed).1
        simpa only [stored, List.mem_cons, List.not_mem_nil, or_false] using retained
      have sameTime (row) (listed : row ∈ ordered) : row.transfer.effectiveAt = tick 10 := by
        rcases rows row listed with rfl | rfl <;> rfl
      have sameSource (row) (listed : row ∈ ordered) : 1 = row.transfer.transferor := by
        rcases rows row listed with rfl | rfl <;> rfl
      cases ordered with
      | nil => exact List.not_mem_nil firstListed
      | cons head rest =>
        cases rest with
        | nil =>
          exact distinct ((List.mem_singleton.mp conflictListed).trans
            (List.mem_singleton.mp firstListed).symm)
        | cons next tail =>
          have earlier := (List.pairwise_cons.mp chronological).1 next List.mem_cons_self
          rw [sameTime head List.mem_cons_self,
            sameTime next (List.mem_cons_of_mem _ List.mem_cons_self)] at earlier
          rcases earlier with before | ⟨_, disjoint⟩
          · exact (by decide : ¬ (tick 10).before (tick 10)) before
          · exact disjoint ⟨1, .inl (sameSource head List.mem_cons_self),
              .inl (sameSource next (List.mem_cons_of_mem _ List.mem_cons_self))⟩

private def collectedC : MaterialsCollection := ⟨3, 1, tick 11⟩

private abbrev onward : Transfer :=
  makeTransfer "signed by C and D" 3 4 (tick 12) (tick 30)
    (allocation material "C → D" [(2, 3), (4, 2), (5, 2)]) [collectedA, collectedC] (tick 11)

private abbrev sequenceEvidence := evidence [onward, first] (tick 40) (tick 40)

private theorem sequenceMembers (row : MaterialsTransferRecord material) :
    row ∈ sequenceEvidence.transfers ↔ row = first.record ∨ row = onward.record := by
  change row ∈ ([onward.record, first.record] : List (MaterialsTransferRecord material)) ↔ _
  simp [or_comm]

private theorem onwardGross :
    sequenceEvidence.transferPortionsAt terms used charge (tick 2) 10
      onward.record (gross onward.record) := by
  refine ⟨?_, (by decide : (tick 12).by (tick 40)), ?_⟩
  · exact ⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩, by decide, rfl, laterHoldings material,
      shareAt _ _ _ _ _ (by decide) (by decide) _
        (ite_eq_left (by decide : (tick 11).by (tick 11))), by decide⟩
  · simp [MaterialsShareEvidence.chargeEstablishedAt, MaterialsShareEvidence.collectionsAtTransfer,
      evidence, History.shareEvidence, rights, original, charge, gross, allocation, collectedA,
      collectedC, Moment.before, tick, MaterialsAllocation.distributesCharge, sumAmounts,
      sumAmountsWhere, Rat.zero_add]
    all_goals decide +kernel

private theorem remainingAfterTheFirstTransfer :
    sequenceEvidence.portionAt terms used charge (tick 2) (tick 11) 3 3 := by
  refine ⟨trivial, .inr (.inl ⟨first.record, (sequenceMembers _).mpr (.inl rfl),
    applies _ _ _ _ _ ⟨rfl, rfl, rfl⟩ (by decide) (by decide), ?_, agreed material,
    shareAt _ _ _ _ _ (by decide : (tick 2).by (tick 40)) (by decide) _
      (ite_eq_right (by decide : ¬ (tick 11).by (tick 2))),
    by decide, agreedCharge, gross first.record,
    firstGross _ _ _ (by decide) (by decide) (by decide), firstReallocates, by decide +kernel⟩)⟩
  intro row retained applicable
  rcases (sequenceMembers row).mp retained with rfl | rfl
  · rfl
  · exact ((by decide : ¬ (tick 12).by (tick 11)) applicable.2.1).elim

private theorem afterTheSecondTransfer (holder : ActorId) (amount : Amount)
    (selected : amount = gross onward.record holder) :
    sequenceEvidence.portionAt terms used charge (tick 2) (tick 20) holder amount := by
  refine ⟨trivial, .inr (.inr ⟨agreed material, shareAt _ _ _ _ _ (by decide : (tick 2).by (tick 40))
    (by decide) _ (ite_eq_right (by decide : ¬ (tick 11).by (tick 2))),
    by decide, agreedCharge, ?_⟩)⟩
  have readsFirst := applies [onward, first] (tick 40) (tick 40) (tick 20) first.record
    ⟨rfl, rfl, rfl⟩ (by decide) (by decide)
  have readsOnward := applies [onward, first] (tick 40) (tick 40) (tick 20) onward.record
    ⟨rfl, rfl, rfl⟩ (by decide) (by decide)
  have distinct : onward.record ≠ first.record := fun eq ↦
    (by decide : onward.record.reference ≠ first.record.reference)
      (congrArg MaterialsTransferRecord.reference eq)
  refine ⟨first.record, (sequenceMembers _).mpr (.inl rfl), readsFirst,
    onward.record, (sequenceMembers _).mpr (.inr rfl), readsOnward, distinct,
    .inr ⟨[first.record, onward.record], ?_, ?_, ?_⟩⟩
  · intro row
    rw [sequenceMembers row]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨fun listed ↦ ⟨listed, ?_⟩, And.left⟩
    rcases listed with rfl | rfl
    · exact readsFirst
    · exact readsOnward
  · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro row retained
    obtain rfl := List.mem_singleton.mp retained
    exact .inl (by decide)
  · have continued : onward.record.transfer.reallocates (gross first.record) (gross onward.record) := by
      refine ⟨by decide, ?_, by decide +kernel, by decide +kernel⟩
      intro actor outside
      have notC : actor ≠ 3 := fun eq ↦ outside (.inl eq)
      have notD : actor ≠ 4 := fun eq ↦ outside (.inr eq)
      simp [gross, allocation, collectedA, collectedC, MaterialsAllocation.portion,
        sumAmountsWhere, notC, notD, Ne.symm notC, Ne.symm notD]
    refine ⟨gross first.record, firstGross _ _ _ (by decide) (by decide) (by decide),
      firstReallocates, ?_⟩
    change sequenceEvidence.transferredInOrder terms used charge (tick 2) 10 holder
      [onward.record] _
      (first.record.transfer.applyPair
        (fun actor ↦ (agreed material).portion actor place.id 10) (gross first.record)) amount
    rw [applyPairOfReallocation _ firstReallocates]
    refine ⟨gross onward.record, onwardGross, continued, ?_⟩
    change amount = onward.record.transfer.applyPair
      (gross first.record) (gross onward.record) holder
    simpa only [applyPairOfReallocation _ continued] using selected

theorem sequentialSignedTransfersAtPayment :
    let cash : PaymentHistory := ⟨[payment 1 collectedA, payment 2 collectedC], [], []⟩
    let unpaid := fun holder amount ↦
      cash.remainingObligationBefore lesson.id original.record.obligation (.person holder none)
        amount (tick 20) (some (.materialsShare material holder))
    sequenceEvidence.eligibleAt used terms original.record 3 3 (tick 11) (tick 40) ∧
    sequenceEvidence.eligibleAt used terms original.record 3 1 (tick 20) (tick 40) ∧
    sequenceEvidence.eligibleAt used terms original.record 4 2 (tick 20) (tick 40) ∧
    unpaid 3 1 = 0 ∧ unpaid 4 2 = 2 := by
  exact ⟨filed _ _ 3 3 (by decide +kernel) (by decide) (by decide)
      remainingAfterTheFirstTransfer,
    filed _ _ 3 1 (by decide +kernel) (by decide) (by decide)
      (afterTheSecondTransfer _ _ (by decide +kernel)),
    filed _ _ 4 2 (by decide +kernel) (by decide) (by decide)
      (afterTheSecondTransfer _ _ (by decide +kernel)), by decide +kernel⟩

private abbrev sameTime : Transfer :=
  makeTransfer "signed by B and D at the first transfer time" 2 4 (tick 10) (tick 30)
    (allocation material "B transfers two to D" [(1, 3), (2, 1), (4, 2), (5, 2)]) [collectedA]

private abbrev afterBatch : Transfer :=
  makeTransfer "signed by C and F" 3 6 (tick 12) (tick 30)
    (allocation material "C transfers two to F" [(4, 2), (5, 2), (6, 2)])
    [collectedA, collectedB, collectedC] (tick 11)

private abbrev mixed := [afterBatch, sameTime, first]
private abbrev mixedEvidence := evidence mixed (tick 40) (tick 40)
private abbrev firstGroupGross := sameTime.record.transfer.applyPair
  (gross first.record) (gross sameTime.record)

private theorem mixedMembers (row : MaterialsTransferRecord material) :
    row ∈ mixedEvidence.transfers ↔ row = afterBatch.record ∨ row = sameTime.record ∨
      row = first.record := by
  change row ∈ ([afterBatch.record, sameTime.record, first.record] :
    List (MaterialsTransferRecord material)) ↔ _
  simp

private theorem mixedApplies (row : MaterialsTransferRecord material)
    (retained : row ∈ mixedEvidence.transfers) :
    mixedEvidence.transferApplies used place.id (tick 20) row := by
  rcases (mixedMembers row).mp retained with rfl | rfl | rfl <;>
    exact applies _ _ _ _ _ ⟨rfl, rfl, rfl⟩ (by decide) (by decide)

private theorem simultaneousReallocation :
    sameTime.record.transfer.reallocates
      (fun actor ↦ (agreed material).portion actor place.id 10) (gross sameTime.record) := by
  refine ⟨by decide, ?_, by decide +kernel, by decide +kernel⟩
  intro actor outside
  have notB : actor ≠ 2 := fun eq ↦ outside (.inl eq)
  have notD : actor ≠ 4 := fun eq ↦ outside (.inr eq)
  by_cases isA : actor = 1
  · subst actor
    decide +kernel
  · simp [gross, allocation, agreed, collectedA, MaterialsAllocation.portion, sumAmountsWhere,
      notB, notD, Ne.symm notB, Ne.symm notD, isA, Ne.symm isA, Rat.zero_add]

private theorem laterReallocation :
    afterBatch.record.transfer.reallocates firstGroupGross (gross afterBatch.record) := by
  refine ⟨by decide, ?_, by decide +kernel, by decide +kernel⟩
  intro actor outside
  change ¬ (actor = 3 ∨ actor = 6) at outside
  have notC : actor ≠ 3 := fun eq ↦ outside (.inl eq)
  have notF : actor ≠ 6 := fun eq ↦ outside (.inr eq)
  by_cases isB : actor = 2
  · subst actor
    decide +kernel
  by_cases isD : actor = 4
  · subst actor
    decide +kernel
  simp [firstGroupGross, MaterialsTransfer.applyPair, gross, allocation, collectedA,
    collectedB, collectedC, MaterialsAllocation.portion, sumAmountsWhere, isB, isD, notC,
    notF, Ne.symm isB, Ne.symm isD, Ne.symm notC, Ne.symm notF]

private theorem simultaneousGross :
    mixedEvidence.transferPortionsAt terms used charge (tick 2) 10
      sameTime.record (gross sameTime.record) := by
  refine ⟨?_, by decide, ?_⟩
  · exact ⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩, by decide, rfl, agreed material,
      shareAt _ _ _ _ _ (by decide) (by decide) _
        (ite_eq_right (by decide : ¬ (tick 11).by (tick 5))), by decide⟩
  · simp [MaterialsShareEvidence.chargeEstablishedAt, MaterialsShareEvidence.collectionsAtTransfer,
      evidence, History.shareEvidence, rights, original, charge, gross, allocation, collectedA,
      Moment.before, tick, MaterialsAllocation.distributesCharge, sumAmounts, sumAmountsWhere]
    all_goals decide +kernel

private theorem afterBatchGross :
    mixedEvidence.transferPortionsAt terms used charge (tick 2) 10
      afterBatch.record (gross afterBatch.record) := by
  refine ⟨?_, by decide, ?_⟩
  · exact ⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩, by decide, rfl, laterHoldings material,
      shareAt _ _ _ _ _ (by decide) (by decide) _
        (ite_eq_left (by decide : (tick 11).by (tick 11))), by decide⟩
  · simp [MaterialsShareEvidence.chargeEstablishedAt, MaterialsShareEvidence.collectionsAtTransfer,
      evidence, History.shareEvidence, rights, original, charge, gross, allocation, collectedA,
      collectedB, collectedC, Moment.before, tick, MaterialsAllocation.distributesCharge,
      sumAmounts, sumAmountsWhere]
    all_goals decide +kernel

private theorem mixedPortion (holder : ActorId) (amount : Amount)
    (selected : amount = gross afterBatch.record holder) :
    mixedEvidence.portionAt terms used charge (tick 2) (tick 20) holder amount := by
  refine ⟨trivial, .inr (.inr ⟨agreed material, shareAt _ _ _ _ _ (by decide : (tick 2).by (tick 40))
    (by decide) _ (ite_eq_right (by decide : ¬ (tick 11).by (tick 2))),
    by decide, agreedCharge, ?_⟩)⟩
  have firstSeen := (mixedMembers _).mpr (.inr (.inr rfl))
  have laterSeen := (mixedMembers _).mpr (.inl rfl)
  have distinct : afterBatch.record ≠ first.record := fun eq ↦
    (by decide : afterBatch.record.reference ≠ first.record.reference)
      (congrArg MaterialsTransferRecord.reference eq)
  refine ⟨first.record, firstSeen, mixedApplies _ firstSeen, afterBatch.record, laterSeen,
    mixedApplies _ laterSeen, distinct, .inr ⟨[first.record, sameTime.record, afterBatch.record],
    ?_, ?_, ?_⟩⟩
  · intro row
    have members : row ∈ [first.record, sameTime.record, afterBatch.record] ↔
        row ∈ mixedEvidence.transfers := by
      rw [mixedMembers]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨fun
        | .inl firstRow => .inr (.inr firstRow)
        | .inr (.inl middleRow) => .inr (.inl middleRow)
        | .inr (.inr lastRow) => .inl lastRow, fun
        | .inl lastRow => .inr (.inr lastRow)
        | .inr (.inl middleRow) => .inr (.inl middleRow)
        | .inr (.inr firstRow) => .inl firstRow⟩
    exact ⟨fun listed ↦ ⟨members.mp listed, mixedApplies _ (members.mp listed)⟩,
      fun ⟨retained, _⟩ ↦ members.mpr retained⟩
  · refine .cons ?_ (.cons ?_ (List.pairwise_singleton _ _))
    · intro row listed
      rcases List.mem_cons.mp listed with rfl | last
      · refine .inr ⟨rfl, ?_⟩
        rintro ⟨actor, fromFirst | fromFirst, fromOther | fromOther⟩ <;>
          cases (fromFirst.symm.trans fromOther)
      · obtain rfl := List.mem_singleton.mp last
        exact .inl (by decide)
    · intro row listed
      obtain rfl := List.mem_singleton.mp listed
      exact .inl (by decide)
  · refine ⟨gross first.record, firstGross _ _ _ (by decide) (by decide) (by decide),
      firstReallocates, ?_⟩
    change mixedEvidence.transferredInOrder terms used charge (tick 2) 10 holder
      [sameTime.record, afterBatch.record] _
      (first.record.transfer.applyPair
        (fun actor ↦ (agreed material).portion actor place.id 10) (gross first.record)) amount
    rw [applyPairOfReallocation _ firstReallocates]
    refine ⟨gross sameTime.record, simultaneousGross, simultaneousReallocation,
      gross afterBatch.record, afterBatchGross, laterReallocation, ?_⟩
    change amount = afterBatch.record.transfer.applyPair firstGroupGross (gross afterBatch.record)
      holder
    simpa only [applyPairOfReallocation _ laterReallocation] using selected

private def mixedLedger : PaymentHistory :=
  ⟨[payment 1 collectedA, payment 2 collectedB, payment 3 collectedC], [], []⟩

private def mixedReceived (holder : ActorId) (point : Moment) : Amount :=
  mixedLedger.receivedForObligationBefore lesson.id original.record.obligation (.person holder none)
    point (some (.materialsShare material holder))

private theorem mixedCollectionsMatch :
    mixedEvidence.collectionsMatch used terms (tick 20) mixedReceived := by
  have charges : used.chargesFor terms material = [charge] := by decide +kernel
  intro row retained _ _
  rcases (mixedMembers row).mp retained with rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_⟩
    · simp [charges, MaterialsShareEvidence.collectionsAtTransfer, evidence,
        History.shareEvidence, rights, collectedA, collectedB, collectedC, Moment.before, tick]
      all_goals decide +kernel
    · intro holder
      by_cases isA : holder = 1
      · subst holder
        decide +kernel
      by_cases isB : holder = 2
      · subst holder
        decide +kernel
      by_cases isC : holder = 3
      · subst holder
        decide +kernel
      simp [charges, MaterialsShareEvidence.collectionsAtTransfer, evidence, History.shareEvidence,
        rights, mixedReceived, mixedLedger, payment, PaymentHistory.receivedForObligationBefore,
        PaymentHistory.recipientReceived, collectedA, collectedB, collectedC, sumAmounts,
        sumAmountsWhere, tick, Moment.before, isA, isB, isC, Ne.symm isA, Ne.symm isB, Ne.symm isC]

theorem independentSameMomentTransfersCanPrecedeAConnectedTransfer :
    let unpaid := fun holder amount ↦
      mixedLedger.remainingObligationBefore lesson.id original.record.obligation (.person holder none)
        amount (tick 20) (some (.materialsShare material holder))
    mixedEvidence.collectionsMatch used terms (tick 20) mixedReceived ∧
    mixedEvidence.eligibleAt used terms original.record 3 1 (tick 20) (tick 40) ∧
    mixedEvidence.eligibleAt used terms original.record 4 2 (tick 20) (tick 40) ∧
    mixedEvidence.eligibleAt used terms original.record 5 2 (tick 20) (tick 40) ∧
    mixedEvidence.eligibleAt used terms original.record 6 2 (tick 20) (tick 40) ∧
    unpaid 3 1 = 0 ∧ unpaid 6 2 = 2 := by
  exact ⟨mixedCollectionsMatch, filed _ _ 3 1 (by decide +kernel) (by decide) (by decide)
      (mixedPortion _ _ (by decide +kernel)),
    filed _ _ 4 2 (by decide +kernel) (by decide) (by decide)
      (mixedPortion _ _ (by decide +kernel)),
    filed _ _ 5 2 (by decide +kernel) (by decide) (by decide)
      (mixedPortion _ _ (by decide +kernel)),
    filed _ _ 6 2 (by decide +kernel) (by decide) (by decide)
      (mixedPortion _ _ (by decide +kernel)), by decide +kernel⟩

#print axioms independentSignedTransfersAtPayment
#print axioms priorCollectionsFollowThePayee
#print axioms secondTransferIsAbsentBeforeItIsRecorded
#print axioms singleTransferCannotTakeCsFive
#print axioms unsettledIncomeUsesItsFirstActualUse
#print axioms authorisedAmendmentAtTransferChangesTheAgreedSplit
#print axioms overlappingTransfersNeedFurtherTerms
#print axioms sequentialSignedTransfersAtPayment
#print axioms independentSameMomentTransfersCanPrecedeAConnectedTransfer

end SourceV14.FidelityMaterialsTransferChecks
