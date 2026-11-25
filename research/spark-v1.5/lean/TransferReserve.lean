import ProvisionWitnessFixture
import RecognisedV15.Workflow

/-! A signed transfer of a previously discharged original and the two different funding readers. -/
namespace SparkGap.TransferReserve

open SourceV14 SourceV14.Confirmation SourceV14.Course SourceV14.Operations
open SourceV14.Workflow.Materials SourceV14.FidelityMaterialsProvisionChecks
open SourceV14.FidelityMaterialsProvisionChecks.TransferFixture

private def remainingSplit : MaterialsAllocation 7 :=
  ⟨"uncollected split after transfer", [99, 3],
    fun holder _ amount ↦ if holder = 99 then amount / 3 else 2 * amount / 3⟩

private def disposition (date : Nat) (uncollected : MaterialsAllocation 7) : MaterialsTransfer 7 :=
  ⟨2, 99, .voluntaryTransfer, time date, .sharesAtFirstUse, uncollected, remainingSplit⟩

private def signed (date : Nat) (collections : List MaterialsCollection)
    (uncollected : MaterialsAllocation 7 := remainingSplit) : Transfer where
  material := 7
  sparkDao := courseLesson.provider
  recordedAt := time date
  record := {
    transfer := disposition date uncollected
    reference := "signed original, place 1"
    verifiedTerms := fun name terms ↦
      name = "signed original, place 1" ∧ terms = disposition date uncollected
    transferorShareTime := time 35
    applicableOwnershipTime := (· = time 35)
    voluntary := True
    publishedTermsSatisfied := True
    governs := fun lesson ref place ↦
      lesson = courseLesson.id ∧ ref = firstOriginal.record.reference ∧ place = seat.id
    originalCollections := fun lesson ref place ↦
      if lesson = courseLesson.id ∧ ref = firstOriginal.record.reference ∧ place = seat.id then
        collections else []
    shortfallCollections := fun _ _ _ _ ↦ [] }

private abbrev settledCash : List MaterialsCollection := [⟨2, 2, time 40⟩, ⟨3, 4, time 45⟩]
private abbrev late := signed 47 settledCash
private abbrev early := signed 37 []

private def afterTransfer (s : Workflow.State) (row : Transfer) : Workflow.State :=
  { s.withHolds s.holds with materials := { s.materials with transfers := row :: s.materials.transfers } }

private abbrev lateState := afterTransfer rootPaid late
private abbrev register (row : Transfer) : Workflow.Event := .materials courseLesson.id (.transfer row)
private abbrev refreshRecord := newProvision 8 6 6 48
private abbrev refresh : Workflow.Event := .materials courseLesson.id (.provision materialTerms refreshRecord)

private def refreshed : Workflow.State :=
  { rootPaid.withHolds rootPaid.holds with
    materials := { rootPaid.materials with provisions := refreshRecord :: rootPaid.materials.provisions }
    activeReserves := Workflow.Reserves.reserve rootPaid.activeReserves refreshRecord.funds }

theorem paidBeforeRegistration :
    Workflow.Step (rootBeforeEvidence (time 44))
      (.materials courseLesson.id (.verifyReceipt oldPayment (time 44) 81)) (rootCanPay (time 44)) ∧
    Workflow.Step (rootCanPay (time 44)) (.materials courseLesson.id (.post payFour)) rootPaid ∧
    rootPaid.holds.payments.posted = [oldPayment.paid, payFour.paid] ∧
    rootPaid.materials.hasVerifiedReceiptAt oldPayment.paid (time 46) = true ∧
    rootPaid.materials.hasVerifiedReceiptAt payFour.paid (time 46) = true ∧
    oldPayment.paid.instruction.amount = 2 ∧ payFour.paid.instruction.amount = 4 :=
  ⟨aSupportedEarlierReceiptCanBeVerified, sufficientFundsAllowTheNewPaymentStep, rfl,
    by decide +kernel, by decide +kernel, rfl, rfl⟩

theorem registerAfterDischarge : Workflow.Step rootPaid (register late) lateState := by
  refine Workflow.Step.materials (sameLesson := ?_) (funds := trivial) (rule := ?_) (payment := rfl)
  · intro id present
    cases present
  · exact .transfer ⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩⟩ (by intro prior member; cases member)

private noncomputable def live (s : Workflow.State) (atTime : Nat) : Amount :=
  sumAmounts (s.materials.liveMaterialBudgetsAt s.holds.payments courseLesson.id (time atTime)
    s.materialsPrincipalContext) Prod.snd

theorem grossControl : live rootPaid 48 = 6 := by decide +kernel

theorem grossWithLaterTransfer : live lateState 48 = 12 := by decide_cbv

theorem timeAndScope :
    lateState = { rootPaid with materials := { rootPaid.materials with transfers := [late] } } ∧
    live lateState 46 = 6 ∧ lateState.holds.payments.posted = rootPaid.holds.payments.posted ∧
    lateState.materials.entitlements = rootPaid.materials.entitlements ∧
    lateState.materials.receipts = rootPaid.materials.receipts ∧
    late.record.governs courseLesson.id firstOriginal.record.reference seat.id ∧
    late.record.originalCollections courseLesson.id firstOriginal.record.reference seat.id =
      settledCash ∧
    rootPaid.materials.paidOriginalCharge rootPaid.holds.payments oldProvision.pending
      (time 48) = true ∧
    lateState.materials.paidOriginalCharge lateState.holds.payments oldProvision.pending
      (time 48) = false := by
  refine ⟨rfl, by decide +kernel, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl,
    by decide +kernel, ?_⟩
  decide_cbv

theorem controlAdmitsRefresh : Workflow.Step rootPaid refresh refreshed := by
  refine Workflow.Step.materials (sameLesson := ?_) (funds := ?_) (rule := ?_) (payment := rfl)
  · intro id present
    exact Option.some.inj present.symm
  · intro entry present
    have eq : entry = ⟨1, .providerFunds, .spendable, 6, 0, 6⟩ := List.mem_singleton.mp present
    subst entry
    decide +kernel
  · refine .provision (by exact List.Mem.head []) ?_
      (by unfold MaterialsShareStatus.holdMustFollowSection62; decide) ?_ ?_ ?_ ?_
    · exact ⟨none, [agreedForm], rosterProof (time 48), List.Mem.head []⟩
    · refine estimateProof 8 6 6 48 ?_ (by decide) ?_ (by decide)
      · unfold MaterialsPricing.covers
        decide +kernel
      · unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
        decide +kernel
    · intro prior present _
      rcases List.mem_cons.mp present with rfl | member
      · decide
      · cases List.mem_singleton.mp member
        decide
    · refine ⟨?_, ?_⟩
      · unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
        decide_cbv
      · intro f b present
        cases present
    · intro prior present _ later
      rcases List.mem_cons.mp present with rfl | member
      · exact absurd later (by decide)
      · cases List.mem_singleton.mp member
        exact absurd later (by decide)

theorem lateTransferBlocksSameRefresh (next : Workflow.State) :
    ¬ Workflow.Step lateState refresh next := by
  intro step
  cases step with
  | materials _ _ material _ =>
    cases material with
    | provision _ _ _ _ _ funding _ =>
      have cash := funding.1
      unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith at cash
      revert cash
      decide_cbv

private abbrev cutEvents : List Workflow.Event := [
  .materials courseLesson.id (.verifyReceipt oldPayment (time 44) 81),
  .materials courseLesson.id (.post payFour)]

theorem directControlPath :
    RecognisedV15.Workflow.Path Workflow.Step (rootBeforeEvidence (time 44))
      (cutEvents ++ [refresh]) refreshed :=
  .next paidBeforeRegistration.1
    (.next paidBeforeRegistration.2.1 (.next controlAdmitsRefresh (.nil _)))

theorem directTransferPath :
    RecognisedV15.Workflow.Path Workflow.Step (rootBeforeEvidence (time 44))
      (cutEvents ++ [register late]) lateState :=
  .next paidBeforeRegistration.1
    (.next paidBeforeRegistration.2.1 (.next registerAfterDischarge (.nil _)))

theorem recognisedControlPath :
    RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step
      (RecognisedV15.Workflow.State.fromDirect (rootBeforeEvidence (time 44)))
      (cutEvents ++ [refresh]) (RecognisedV15.Workflow.State.fromDirect refreshed) :=
  (RecognisedV15.Workflow.path_iff _ _ _).mp directControlPath

theorem recognisedTransferPath :
    RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step
      (RecognisedV15.Workflow.State.fromDirect (rootBeforeEvidence (time 44)))
      (cutEvents ++ [register late]) (RecognisedV15.Workflow.State.fromDirect lateState) :=
  (RecognisedV15.Workflow.path_iff _ _ _).mp directTransferPath

theorem recognisedRefreshBlocked (next : RecognisedV15.Workflow.State) :
    ¬ RecognisedV15.Workflow.Step (RecognisedV15.Workflow.State.fromDirect lateState) refresh next := by
  intro step
  apply lateTransferBlocksSameRefresh next.toDirect
  simpa only [RecognisedV15.Workflow.State.toDirect_fromDirect] using
    RecognisedV15.Workflow.step_to_direct step

/- After holder 2 has collected its entire two, the other four remain with holder 3.
   The same signed record governs future shortfalls separately. -/
private def fourToThree : MaterialsAllocation 7 :=
  ⟨"holder 3 collects the rest", [3], fun _ _ due ↦ due⟩

private abbrev middle := signed 42 [⟨2, 2, time 40⟩] fourToThree
private abbrev verifiedAt41 := rootCanPay (time 41)
private abbrev middleState := afterTransfer verifiedAt41 middle
private abbrev revisedShare : Entitlement := { payFour.entitlement with verifiedAt := time 43 }
private abbrev independentPayout : Receipt := { payFour with entitlement := revisedShare }

private def rechecked (s : Workflow.State) : Workflow.State :=
  { s.withHolds s.holds with
    materials := { s.materials with entitlements := revisedShare :: s.materials.entitlements } }

private abbrev recheckedMiddle := rechecked middleState
private abbrev recheckedEarly := rechecked (afterTransfer verifiedAt41 early)

private abbrev fundsPass (s : Workflow.State) (row : Receipt) : Prop :=
  row.protectsProvisions s.materials (row.postingHistory s.holds).payments s.materialsPrincipalContext

theorem postingGuardDistinguishesTransferTiming :
    independentPayout.funds.covers 10 ∧
    independentPayout.provisionPaymentOverlaps = [] ∧
    independentPayout.excludedProvisionFunds = [] ∧
    fundsPass recheckedMiddle independentPayout ∧ ¬ fundsPass recheckedEarly independentPayout := by
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
    decide +kernel
  · unfold fundsPass Receipt.protectsProvisions
    refine ⟨List.nodup_nil, (fun _ member ↦ nomatch member), List.nodup_nil,
      (fun _ member ↦ nomatch member), by decide_cbv, ?_⟩
    unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
    decide_cbv
  · intro guard
    have funds := guard.2.2.2.2.2
    unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith at funds
    revert funds
    decide_cbv

private def withCash (cash : Amount) : Receipt :=
  { independentPayout with funds := { independentPayout.funds with
      entries := [⟨1, .providerFunds, .spendable, cash, 0, 0⟩] } }

theorem cashBoundaryChecks :
    ¬ fundsPass recheckedMiddle (withCash 9) ∧
    ¬ fundsPass recheckedEarly (withCash 11) ∧ fundsPass recheckedEarly (withCash 12) := by
  refine ⟨?_, ?_, ?_⟩
  · intro guard
    have funds := guard.2.2.2.2.2
    unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith at funds
    revert funds
    decide_cbv
  · intro guard
    have funds := guard.2.2.2.2.2
    unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith at funds
    revert funds
    decide_cbv
  · unfold fundsPass Receipt.protectsProvisions
    refine ⟨List.nodup_nil, (fun _ member ↦ nomatch member), List.nodup_nil,
      (fun _ member ↦ nomatch member), by decide_cbv, ?_⟩
    unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
    decide_cbv

theorem middleTransferPath : Workflow.Step verifiedAt41 (register middle) middleState := by
  refine Workflow.Step.materials (sameLesson := ?_) (funds := trivial) (rule := ?_) (payment := rfl)
  · intro id present
    cases present
  · exact .transfer ⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩⟩ (by intro prior member; cases member)

private abbrev basis := middleState.materials.shareEvidence revisedShare (time 43)
private abbrev subject : MaterialsCharge := ⟨seat.id, 7, 6⟩
private abbrev use := firstOriginal.check.use

private theorem historicalAllocation (point query : Moment) (known : point.by (time 43)) :
    basis.allocationAt materialTerms seat.id point query (shareAllocation 7) := by
  refine ⟨known, ⟨rfl, rfl, rfl⟩, shareAllocation 7, rfl,
    ⟨(materialTerms.lesson, seat.id), 13, shareAllocation 7, time 0⟩, ?_, by decide, rfl⟩
  rw [show basis.shareHistory.amendments = [] from rfl]
  simp only [List.filter_nil, List.mergeSort_nil, privateArrangementAt]
  rfl

private abbrev postAllocation (holder : ActorId) : Amount :=
  (if holder = 2 then 2 else 0) + fourToThree.portion holder seat.id 4

private theorem reallocation :
    middle.record.transfer.reallocates
      (fun holder ↦ (shareAllocation 7).portion holder seat.id 6) postAllocation := by
  refine ⟨by decide, ?_, by decide +kernel, by decide +kernel⟩
  intro holder outside
  have h2 : holder ≠ 2 := fun eq ↦ outside (.inl eq)
  by_cases h3 : holder = 3
  · subst holder
    decide +kernel
  · change (if holder = 2 then 2 else 0) + (if holder ∈ [3] then 4 else 0) =
      (if holder ∈ [2, 3] then (if holder = 2 then 6 / 3 else 2 * 6 / 3) else 0)
    simp [h2, h3, Rat.zero_add]

private theorem portionAfter (point : Moment) (ordered : (time 42).by point) :
    basis.portionAt materialTerms use subject (time 31) point 3 4 := by
  refine ⟨trivial, Or.inr (Or.inl ?_)⟩
  refine ⟨middle.record, List.Mem.head [], ?_, ?_, shareAllocation 7, ?_, by decide, ?_,
    postAllocation, ?_, reallocation, by decide +kernel⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, ordered, _, List.Mem.head [], rfl, rfl, by decide⟩
  · intro other mem _
    exact List.mem_singleton.mp mem
  · exact historicalAllocation (time 31) (time 42) (by decide)
  · unfold MaterialsAllocation.distributesCharge
    decide +kernel
  · refine ⟨⟨by decide, ⟨rfl, rfl⟩, ⟨trivial, trivial⟩, by decide, rfl,
      shareAllocation 7, historicalAllocation (time 35) (time 35) (by decide), List.Mem.head _⟩,
      by decide, ?_, by decide +kernel, ?_⟩
    · intro rec inList
      have same : rec = ⟨2, 2, time 40⟩ := List.mem_singleton.mp inList
      subst rec
      decide
    · refine ⟨by decide, ?_, ?_⟩
      · unfold MaterialsAllocation.distributesCharge
        decide +kernel
      · intro holder
        by_cases h : holder = 2
        · subst holder
          decide +kernel
        · change (if holder = 2 then 2 else 0) + _ =
            sumAmountsWhere [⟨2, 2, time 40⟩] (fun row : MaterialsCollection ↦ row.holder == holder)
              MaterialsCollection.amount + _
          simp [h, Ne.symm h, sumAmounts, sumAmountsWhere]
          apply congrArg (fun amount : Amount ↦ 0 + fourToThree.portion holder seat.id amount)
          decide_cbv

private theorem eligible (point : Moment) (afterOriginal : (time 34).by point)
    (afterTransfer : (time 42).by point) (afterCheck : (time 43).by point) :
    basis.eligibleAt use materialTerms firstOriginal.record 3 4 point point
      (revisedShare.retainedBasis middleState.materials) [] := by
  have charges : use.chargesFor materialTerms revisedShare.original.record.material = [subject] := by
    decide +kernel
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide +kernel,
    ?_, ?_, by decide, by decide, afterOriginal, Or.inr rfl, afterCheck,
    rfl, ⟨List.Mem.head [], (fun _ member ↦ nomatch member)⟩, time 31, rfl,
    fun _ ↦ (4 : Amount), ?_, ?_, by decide⟩
  · intro row member
    rw [show firstOriginal.record.charges = [subject] from charges] at member
    cases List.mem_singleton.mp member
    exact ⟨List.Mem.head [], rfl, by decide⟩
  · intro row member
    rw [charges] at member
    cases List.mem_singleton.mp member
    exact List.Mem.head []
  · intro row member
    rw [charges] at member
    cases List.mem_singleton.mp member
    exact portionAfter point afterTransfer
  · rw [charges]
    decide +kernel

private abbrev heldForCollections (posted : Bool) : HoldHistory :=
  if posted then independentPayout.postingHistory recheckedMiddle.holds else middleState.holds

private theorem receiptsAtTransfer (holder : ActorId) (posted : Bool) :
    (if holder = 2 then (2 : Amount) else 0) =
      (heldForCollections posted).payments.receivedForObligationBefore
        courseLesson.id firstOriginal.record.obligation (.person holder none) (time 42)
        (some (.materialsShare 7 holder)) := by
  by_cases paid : holder = 2
  · subst holder
    cases posted <;> decide_cbv
  · have notOldPurpose : some (PaymentPurpose.materialsShare 7 holder) ≠
        some oldPayment.paid.instruction.part.purpose := by
      intro same
      have eq := Option.some.inj same
      exact paid (PaymentPurpose.materialsShare.inj eq).2
    have tooLate : ¬ payFour.paid.instruction.atTime.before (time 42) := by decide
    unfold PaymentHistory.receivedForObligationBefore sumAmountsWhere
    cases posted
    · change (if holder = 2 then 2 else 0) =
        List.foldl _ 0 [oldPayment.paid]
      simp [paid, notOldPurpose, List.foldl]
    · change (if holder = 2 then 2 else 0) =
        List.foldl _ 0 [oldPayment.paid, payFour.paid]
      simp [paid, notOldPurpose, tooLate, List.foldl]

private theorem collectionsFor (posted : Bool) (point : Moment) :
    basis.collectionsMatch use materialTerms point (fun holder cut ↦
      (heldForCollections posted).payments.receivedForObligationBefore
        courseLesson.id firstOriginal.record.obligation (.person holder none) cut
        (some (.materialsShare 7 holder))) := by
  intro record present _ _
  have unique : record = middle.record := List.mem_singleton.mp present
  subst record
  have charges : use.chargesFor materialTerms revisedShare.original.record.material = [subject] := by
    decide +kernel
  rw [charges]
  change (∀ r ∈ ([⟨2, 2, time 40⟩] : List MaterialsCollection), 0 ≤ r.amount ∧ (time 34).by r.collectedAt ∧
      r.collectedAt.before (time 42)) ∧ _
  constructor
  · intro row member
    cases List.mem_singleton.mp member
    decide
  · intro holder
    refine Eq.trans ?_ (receiptsAtTransfer holder posted)
    by_cases paid : holder = 2
    · subst holder
      decide_cbv
    · change sumAmounts (([⟨2, 2, time 40⟩] : List MaterialsCollection).filter
          (fun rec ↦ rec.holder == holder)) MaterialsCollection.amount =
        (if holder = 2 then 2 else 0)
      simp [paid, Ne.symm paid, sumAmounts]

private theorem retainedProvision :
    middleState.materials.pendingProvisionRecorded (middleState.course courseLesson.id) revisedShare := by
  intro previous member resolved _
  rcases List.mem_cons.mp member with is8 | is7
  · cases is8
    cases (show (8 : Nat) = 7 from resolved.2.1)
  · cases List.mem_singleton.mp is7
    refine ⟨oldProvision, List.Mem.tail _ (List.Mem.head []), rfl,
      ⟨none, [agreedForm], rosterProof (time 20), List.Mem.head []⟩, ?_⟩
    refine estimateProof 7 6 6 20 ?_ (by decide) ?_ (by decide)
    · unfold MaterialsPricing.covers
      decide
    · unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
      decide +kernel

private abbrev establishEvent : Workflow.Event := .materials courseLesson.id (.establish revisedShare)

theorem establishUnaffectedShare : Workflow.Step middleState establishEvent recheckedMiddle := by
  refine Workflow.Step.materials (sameLesson := ?_) (funds := trivial) (rule := ?_) (payment := rfl)
  · intro id present
    exact Option.some.inj present.symm
  · refine .establish (eligible (time 43) (by decide) (by decide) (by decide)) ?_ retainedProvision
    exact collectionsFor false (time 43)

private theorem independentPaymentChecks :
    independentPayout.conformsAt recheckedMiddle.materials (recheckedMiddle.course courseLesson.id)
      (independentPayout.postingHistory recheckedMiddle.holds) (time 45) := by
  have old := baselineSeparate (time 41) (time 45) verifiedAt41.materials.receipts false
    (by decide) (by decide) (by decide)
  rcases old with ⟨purpose, fresh, recipient, oldChecks⟩
  rcases oldChecks with ⟨roster, lesson, form, tutor, began, ended, bundle, feedback, reference,
    payer, original, uniqueOriginal, _, noShortfall, _, dueTerm, deadlineTerm, due, deadline,
    postLift, formFacts, partLesson, partPurpose, obligation, payee, _, facts, outstanding,
    authority, timely, completed⟩
  refine ⟨purpose, fresh, recipient, roster, lesson, form, tutor, began, ended, bundle,
    feedback, reference, payer, original, uniqueOriginal, ?_, noShortfall, ?_, dueTerm,
    deadlineTerm, due, deadline, postLift, formFacts, partLesson, partPurpose, obligation,
    payee, collectionsFor true (time 45), facts, outstanding, authority, timely, completed⟩
  · exact eligible (time 45) (by decide) (by decide) (by decide)
  · constructor
    · intro _ prior member resolved required
      obtain ⟨funding, present, same, roster, covered⟩ :=
        retainedProvision prior member resolved required
      have sameLesson : funding.form.lesson = independentPayout.form.lesson := by
        rcases List.mem_cons.mp present with rfl | member
        · rfl
        · cases List.mem_singleton.mp member
          rfl
      refine ⟨funding, present, same, sameLesson, ?_, covered⟩
      rw [← sameLesson]
      exact roster
    · intro _
      exact retainedProvision

private abbrev payoutEvent : Workflow.Event := .materials courseLesson.id (.post independentPayout)

private def paidMiddle : Workflow.State :=
  { recheckedMiddle.withHolds (independentPayout.postingHistory recheckedMiddle.holds) with
    materials := { recheckedMiddle.materials with
      receipts := ⟨independentPayout.paid, independentPayout.funds, time 45, some (time 45)⟩ ::
        recheckedMiddle.materials.receipts } }

theorem cashPaymentAfterApplicableTransfer : Workflow.Step recheckedMiddle payoutEvent paidMiddle := by
  refine Workflow.Step.materials (sameLesson := ?_) (funds := ?_) (rule := ?_) (payment := ?_)
  · intro id present
    exact Option.some.inj present.symm
  · intro entry member
    cases List.mem_singleton.mp member
    decide +kernel
  · exact .post (by decide +kernel) (fun _ member ↦ nomatch member)
      ⟨List.Mem.head _, independentPaymentChecks, postingGuardDistinguishesTransferTiming.2.2.2.1⟩
  · exact ⟨_, Workflow.Payment.Step.post independentPayout.paid (by decide +kernel) (by decide), rfl⟩

private abbrev orderedPaymentEvents : List Workflow.Event := [
  .materials courseLesson.id (.verifyReceipt oldPayment (time 41) 81),
  register middle, establishEvent, payoutEvent]

theorem directOrderedPaymentPath :
    RecognisedV15.Workflow.Path Workflow.Step (rootBeforeEvidence (time 41))
      orderedPaymentEvents paidMiddle :=
  .next (verifyAt (time 41) (by decide) (by decide))
    (.next middleTransferPath (.next establishUnaffectedShare
      (.next cashPaymentAfterApplicableTransfer (.nil _))))

theorem recognisedOrderedPaymentPath :
    RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step
      (RecognisedV15.Workflow.State.fromDirect (rootBeforeEvidence (time 41)))
      orderedPaymentEvents (RecognisedV15.Workflow.State.fromDirect paidMiddle) :=
  (RecognisedV15.Workflow.path_iff _ _ _).mp directOrderedPaymentPath

theorem paymentOutcome :
    paidMiddle.holds.payments.posted = [oldPayment.paid, independentPayout.paid] ∧
    oldPayment.paid.instruction.destination = .person 2 ∧ oldPayment.paid.instruction.amount = 2 ∧
    independentPayout.paid.instruction.destination = .person 3 ∧
    independentPayout.paid.instruction.amount = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms paidBeforeRegistration
#print axioms registerAfterDischarge
#print axioms grossControl
#print axioms grossWithLaterTransfer
#print axioms timeAndScope
#print axioms controlAdmitsRefresh
#print axioms lateTransferBlocksSameRefresh
#print axioms directControlPath
#print axioms directTransferPath
#print axioms recognisedControlPath
#print axioms recognisedTransferPath
#print axioms recognisedRefreshBlocked
#print axioms postingGuardDistinguishesTransferTiming
#print axioms cashBoundaryChecks
#print axioms middleTransferPath
#print axioms establishUnaffectedShare
#print axioms cashPaymentAfterApplicableTransfer
#print axioms directOrderedPaymentPath
#print axioms recognisedOrderedPaymentPath
#print axioms paymentOutcome

end SparkGap.TransferReserve
