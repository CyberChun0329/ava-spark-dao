import Menu

/-! Fixed next-4 receipt on the two-course accepted-compensation branch. The additional attestation
in the research variant is an external input for the second payment. -/

namespace SparkJoint.SplitReceipt

open SourceV14 SourceV14.Workflow
open SourceV14.FidelityMaterialsProvisionChecks
open SourceV14.Workflow.Materials (Receipt)

abbrev PaymentPath := RecognisedV15.Workflow.Path Step

def beforePayment : State := whenChecked .accepted true

def nextShare : Receipt := JointM.attempt 16 6

def ordinaryEvent : Event := .payment (.post nextShare.paid)

def afterOrdinary (s : State) : State :=
  { s.withHolds (Materials.withReceipt s.holds nextShare.paid) with
    paymentRecords := s.paymentRecords ++ [.post nextShare.paid] }

def atomicOutcome : State := JointM.afterPaymentAt45 beforePayment 16 6

/-- The captured t45 state is reached from the original joint opening. -/
theorem reachesPaymentCheck :
    PaymentPath commonStart (datesBefore45 .accepted true) beforePayment :=
  followsCommonOpening .accepted true

/-- The materials rule in the actual t45 state checks authority and the funding cut.
The existing menu gives the numerical condition for permission to take this event. -/
theorem permissionAt45 :
    ((∃ next, Step beforePayment (JointM.paymentEvent 16 6) next) ↔
      requiredFunds true ≤ observedNet lowerBankCut .accepted) ∧
    requiredFunds true = 10 ∧ observedNet lowerBankCut .accepted = 10 ∧
    Step beforePayment (JointM.paymentEvent 16 6) atomicOutcome := by
  refine ⟨?_, rfl, by decide +kernel, ?_⟩
  · simpa only [beforePayment, cashAtCheck.1, retained] using menu lowerBankCut .accepted true
  · exact JointM.enoughFundsForMaterialsPayment beforePayment 44 .verified44 16 6
      (JointM.retainsVerification _ 44 44 (readyAt45 .accepted)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem postActual (s : State) (fresh : nextShare.paid.id ∉ s.holds.payments.posted.map
    PostedPayment.id) : Step s ordinaryEvent (afterOrdinary s) :=
  Step.payment (event := .post nextShare.paid) trivial
    (Payment.Step.post nextShare.paid (by decide +kernel) fresh)

/-- The separately recorded actual payment uses the exact same t45 state and receipt
as the material permission. This path takes only the ordinary payment event at t45. -/
theorem reachesOrdinaryPosting :
    Step beforePayment ordinaryEvent (afterOrdinary beforePayment) ∧
    PaymentPath commonStart (datesBefore45 .accepted true ++ [ordinaryEvent])
      (afterOrdinary beforePayment) := by
  have actual := postActual beforePayment (by change ¬ (13 : Nat) ∈ [2]; decide)
  exact ⟨actual, append reachesPaymentCheck (.next actual (.nil _))⟩

theorem contemporaneousPermissionAndOccurrence :
    Step beforePayment (JointM.paymentEvent 16 6) atomicOutcome ∧
    Step beforePayment ordinaryEvent (afterOrdinary beforePayment) :=
  ⟨permissionAt45.2.2.2, reachesOrdinaryPosting.1⟩

theorem ordinaryPostingObservations :
    let actual := afterOrdinary beforePayment
    nextShare.paid.id = 13 ∧ nextShare.paid.instruction.amount = 4 ∧
    nextShare.paid.instruction.atTime = tick 45 ∧
    actual.holds.payments.posted = [JointM.earlierPayment, nextShare.paid] ∧
    actual.materials.receipts = beforePayment.materials.receipts ∧
    actual.materials.hasVerifiedReceiptAt nextShare.paid (tick 45) = false ∧
    actual.activeReserves = [mInitial, tAt 6] ∧
    actual.holds = atomicOutcome.holds ∧
    actual.materials.entitlements = atomicOutcome.materials.entitlements ∧
    actual.paymentRecords = atomicOutcome.paymentRecords ++ [.post nextShare.paid] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The original fixed evidence recognises ID 2. With its unchanged evidence input,
there is no verification of ID 13 at any time or reference after the ordinary post. -/
theorem originalCannotVerifyNext (point : Moment) (ref : EvidenceRef) (next : State) :
    ¬ Step (afterOrdinary beforePayment)
      (.materials JointM.materialLesson (.verifyReceipt nextShare point ref)) next := by
  intro step
  cases step with
  | materials _ _ rule _ =>
    cases rule with
    | verifyReceipt evidence _ =>
      have ids := congrArg PostedPayment.id evidence.1.1
      exact (by decide : (13 : Nat) ≠ 2) ids

/-- Filing requires exactly one matching verified record. Ordinary payment leaves
only the earlier share's verified record. -/
theorem originalCannotFileNext (point : Moment) (next : State) :
    ¬ Step (afterOrdinary beforePayment)
      (.materials JointM.materialLesson (.file nextShare.paid point)) next := by
  intro step
  cases step with
  | materials _ _ rule _ =>
    cases rule with
    | file fileable => exact (by decide : (0 : Nat) ≠ 1) fileable.1

private theorem stepKeepsExternalVerifier {s t : State} {event : Event}
    (step : Step s event t) : s.materials.verifiesReceiptAt = t.materials.verifiesReceiptAt := by
  cases step <;> try rfl
  case materials _ _ rule _ => cases rule <;> rfl

private theorem pathKeepsExternalVerifier {s t : State} {events : List Event}
    (path : PaymentPath s events t) : s.materials.verifiesReceiptAt = t.materials.verifiesReceiptAt := by
  induction path with
  | nil => rfl
  | next first _ ih => exact (stepKeepsExternalVerifier first).trans ih

/-- Every reachable state from the unchanged common opening retains the original
external verification input. It excludes an independent verification of receipt 13. -/
theorem commonOpeningCannotVerifyNext {s : State} {events : List Event}
    (reached : PaymentPath commonStart events s) (point : Moment) (ref : EvidenceRef) (next : State) :
    ¬ Step s (.materials JointM.materialLesson (.verifyReceipt nextShare point ref)) next := by
  have unchanged := pathKeepsExternalVerifier reached
  intro step
  cases step with
  | materials _ _ rule _ =>
    cases rule with
    | verifyReceipt evidence _ =>
      rw [← unchanged] at evidence
      exact (by decide : (13 : Nat) ≠ 2) (congrArg PostedPayment.id evidence.1.1)

#print axioms commonOpeningCannotVerifyNext
#print axioms reachesPaymentCheck
#print axioms permissionAt45
#print axioms reachesOrdinaryPosting
#print axioms contemporaneousPermissionAndOccurrence
#print axioms ordinaryPostingObservations
#print axioms originalCannotVerifyNext
#print axioms originalCannotFileNext

/-- Supplying this relation names the external source of the second attestation. -/
abbrev Attestation := PostedPayment → Materials.Entitlement → Moment → EvidenceRef → Prop

/-- Add one possible independently supported association at t46. The supplied
relation witnesses the exact payment, entitlement, time and reference. -/
def withAttestation (s : State) (supplied : Attestation) (ref : EvidenceRef) : State :=
  let history := s.materials
  let verifies : Attestation := fun paid right atTime key ↦
    history.verifiesReceiptAt paid right atTime key ∨
      paid = nextShare.paid ∧ right = nextShare.entitlement ∧ atTime = tick 46 ∧
      key = ref ∧ eligibleSlot atTime ∧ supplied paid right atTime key
  { s with materials := { history with verifiesReceiptAt := verifies } }

def researchStart (supplied : Attestation) (ref : EvidenceRef) : State :=
  withAttestation beforePayment supplied ref

/-- Replay the accepted-compensation prefix from its own research opening. Adding the
future t46 association leaves the actual course, ledger, release and t44 verification
events intact. The t44 material check consumes the old evidence arm. -/
theorem researchAcceptedPrefix (supplied : Attestation) (ref : EvidenceRef) :
    PaymentPath (withAttestation commonStart supplied ref)
      (datesBefore45 .accepted true) (researchStart supplied ref) := by
  let extend := fun (s : State) ↦ withAttestation s supplied ref
  have top {s t : State} {event : Credit.Event} (step : Step s (.credit event) t) :
      Step (extend s) (.credit event) (extend t) := by
    cases step with | credit rule => exact .credit rule
  have book {s t : State} (step : Step s JointT.bookingEvent t) :
      Step (extend s) JointT.bookingEvent (extend t) := by
    cases step with
    | booking funds active places rule price findings materials receipts =>
      exact .booking funds active places rule price findings materials receipts
  have opening : PaymentPath (extend commonStart) prefixEvents (extend booked) := by
    have original := commonPrefix
    cases original with
    | next first rest =>
      cases rest with
      | next second last =>
        cases last
        exact .next (top first) (.next (book second) (.nil _))
  have noticed : PaymentPath (extend booked) JointT.noticeEvents (extend faultStart) :=
    JointT.noticePath (extend booked) deliveryReady
  have compensated : PaymentPath (extend faultStart) (JointTFault.events faultStart)
      (extend fault) := by
    apply JointTFault.path (extend faultStart)
    constructor <;> first | rfl | exact ⟨rfl, rfl⟩
  have release {s t : State} {row check} (step : Step s (.reserveReleased row check) t) :
      Step (extend s) (.reserveReleased row check) (extend t) := by
    cases step with
    | reserveReleased retained same verified => exact .reserveReleased retained same verified
  have verify {s t : State} (step : Step s (JointM.verificationEvent 44) t) :
      Step (extend s) (JointM.verificationEvent 44) (extend t) := by
    cases step with
    | materials lesson funds rule pay =>
      cases rule with
      | verifyReceipt original observed =>
        exact .materials lesson funds (.verifyReceipt (Or.inl original) observed) pay
  have before44 : PaymentPath (extend commonStart) faultEvents (extend faultReleased) :=
    append (append (append opening noticed) compensated)
      (.next (JointM.postEarlierPayment (extend fault) rfl)
        (.next (release faultReleaseStep) (.nil _)))
  exact append before44 (.next (verify (verify44 (readyAt45 .accepted))) (.nil _))

def verifyNext (ref : EvidenceRef) : Event :=
  .materials JointM.materialLesson (.verifyReceipt nextShare (tick 46) ref)

def fileNext : Event := .materials JointM.materialLesson (.file nextShare.paid (tick 47))

def afterIndependentCheck (s : State) : State :=
  { s.withHolds s.holds with materials := { s.materials with
      receipts := ⟨nextShare.paid, nextShare.funds, tick 46, none⟩ :: s.materials.receipts } }

def afterFiling (s : State) : State :=
  { s.withHolds s.holds with materials := s.materials.fileReceipt nextShare.paid (tick 47) }

private theorem postingChecks {s t : State} (paid : Step s (JointM.paymentEvent 16 6) t) :
    nextShare.conforms s.materials (s.course JointM.materialLesson)
      (nextShare.postingHistory s.holds) s.materialsPrincipalContext := by
  cases paid with
  | materials _ _ rule _ =>
    cases rule with
    | post _ _ checks => exact checks

/-- Extract the actual approval-route permission, checked cash, and protection of
other provisions from the t45 materials guard. Its hold-history argument is the
rule's proposed posting on exactly the pre-payment ledger. -/
theorem prePaymentAuthorityAndFunds :
    let posting := nextShare.postingHistory beforePayment.holds
    nextShare.approval.allows nextShare.authority nextShare.facts posting nextShare.part
      nextShare.schedule nextShare.conditions nextShare.paid.instruction ∧
    nextShare.funds.validFor nextShare.form.lesson ∧
    nextShare.funds.checkedAt = nextShare.paid.instruction.atTime ∧
    nextShare.funds.covers nextShare.paid.instruction.amount ∧
    nextShare.protectsProvisions beforePayment.materials posting.payments
      beforePayment.materialsPrincipalContext := by
  have complete := postingChecks permissionAt45.2.2.2
  have fields := complete.2.1
  unfold Receipt.conformsAt Operations.MaterialsPaymentPosted at fields
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, cash, _, _⟩ := fields
  rcases cash with proper | observed
  · exact ⟨proper.2.2.2.2.2.1, proper.1, proper.2.1, proper.2.2.1, complete.2.2⟩
  · cases observed.1

/-- The external receipt input supplies no payment authority. The full materials
posting rule already enabled the very same next share before receipt 13 existed. -/
theorem researchPermission (supplied : Attestation) (ref : EvidenceRef) :
    let start := researchStart supplied ref
    Step start (JointM.paymentEvent 16 6) (JointM.afterPaymentAt45 start 16 6) := by
  refine Step.materials (sameLesson := ?_) (funds := ?_) (rule := ?_) (payment := ?_)
  · intro id present
    exact Option.some.inj present.symm
  · intro entry present
    have same : entry = ⟨1, .providerFunds, .spendable, 16, 6, 0⟩ :=
      List.mem_singleton.mp present
    subst entry
    change Reserves.occupiedElsewhere [mInitial, tAt 6] nextShare.funds 1 + 0 ≤ 6
    decide +kernel
  · exact .post (by change ¬ (13 : Nat) ∈ [2]; decide) (by intro _ present; cases present)
      (postingChecks (s := beforePayment) permissionAt45.2.2.2)
  · exact ⟨_, Payment.Step.post nextShare.paid (by decide +kernel)
      (by change ¬ (13 : Nat) ∈ [2]; decide), rfl⟩

private theorem pendingFromEarlier {s t : State} (step : Step s (JointM.verificationEvent 44) t) :
    s.materials.pendingProvisionRecorded (s.course JointM.materialLesson)
      nextShare.entitlement := by
  cases step with
  | materials _ _ rule _ =>
    cases rule with
    | verifyReceipt _ observed => exact observed.2.2.2.1

/-- Observing payment 13 uses the posted ledger, the same retained entitlement and
the new evidence clock. The authority and funding proof at 45 remains separate. -/
theorem laterSubstantiveChecks (supplied : Attestation) (ref : EvidenceRef) :
    let posted := afterOrdinary (researchStart supplied ref)
    nextShare.observedAt posted.materials (posted.course JointM.materialLesson)
      posted.holds (tick 46) posted.materialsPrincipalContext := by
  have before := (postingChecks permissionAt45.2.2.2).2.1
  refine ⟨List.Mem.tail _ (List.Mem.head []), by decide, ?_, ?_, ?_⟩
  · exact ⟨List.mem_cons_self, by intro _ present; cases present⟩
  · exact pendingFromEarlier (s := faultReleased) (verify44 (readyAt45 .accepted))
  · unfold Receipt.conformsAt Operations.MaterialsPaymentPosted at before ⊢
    rcases before with
      ⟨purpose, fresh, recipient, roster, use, form, tutor, began, ended, bundle, reports,
        reference, payer, settled, unique, eligible, shortfall, provision, due, deadline,
        scheduled, latest, lift, facts, partLesson, partPurpose, obligation, destination,
        collects, covers, outstanding, cash, onTime, complete⟩
    refine ⟨purpose, fresh, recipient, roster, use, form, tutor, began, ended, bundle,
      reports, reference, payer, settled, unique, ?_, shortfall, provision, due, deadline,
      scheduled, latest, lift, facts, partLesson, partPurpose, obligation, destination,
      collects, covers, outstanding, ?_, onTime, complete⟩
    · unfold MaterialsShareEvidence.eligibleAt at eligible ⊢
      rcases eligible with
        ⟨scope, material, terms, key, paymentTime, settled, fresh, charges, nonnegative,
          included, taught, shareTime, knownCharge, _, _, portion, basis, allocation⟩
      exact ⟨scope, material, terms, key, paymentTime, settled, fresh, charges, nonnegative,
        included, taught, shareTime, knownCharge, (by decide : (tick 45).by (tick 46)),
        (by decide : (tick 35).by (tick 46)), portion, basis, allocation⟩
    · cases cash with
      | inl authorised => exact Or.inl authorised
      | inr observed => cases observed.1

/-- For ID 13 the old evidence arm still cannot succeed. A qualifying check must
use the supplied reference and exactly t46; no previously reached receipt is assumed. -/
theorem laterCheckRequiresAttestation (supplied : Attestation) (ref key : EvidenceRef)
    (point : Moment) (next : State)
    (step : Step (afterOrdinary (researchStart supplied ref))
      (.materials JointM.materialLesson (.verifyReceipt nextShare point key)) next) :
    point = tick 46 ∧ key = ref ∧ eligibleSlot point ∧
      supplied nextShare.paid nextShare.entitlement point key := by
  cases step with
  | materials _ _ rule _ =>
    cases rule with
    | verifyReceipt evidence _ =>
      rcases evidence with old | added
      · exact ((by decide : (13 : Nat) ≠ 2) (congrArg PostedPayment.id old.1.1)).elim
      · exact added.2.2

private theorem verifyAttested (supplied : Attestation) (ref : EvidenceRef)
    (attested : supplied nextShare.paid nextShare.entitlement (tick 46) ref) :
    let posted := afterOrdinary (researchStart supplied ref)
    Step posted (verifyNext ref) (afterIndependentCheck posted) := by
  refine Step.materials (sameLesson := ?_) (funds := trivial) (rule := ?_) (payment := rfl)
  · intro id present
    exact Option.some.inj present.symm
  · exact .verifyReceipt (Or.inr ⟨rfl, rfl, rfl, rfl, eligibleLate, attested⟩)
      (laterSubstantiveChecks supplied ref)

private theorem fileChecked (supplied : Attestation) (ref : EvidenceRef) :
    let verified := afterIndependentCheck (afterOrdinary (researchStart supplied ref))
    Step verified fileNext (afterFiling verified) := by
  refine Step.materials (sameLesson := ?_) (funds := trivial) (rule := .file ?_) (payment := rfl)
  · intro id present
    exact Option.some.inj present.symm
  · exact ⟨rfl, _, List.Mem.head _, rfl, rfl, (by decide : (tick 46).by (tick 47))⟩

/-- One permission at the split pre-state and three actual transitions from that state.
The completed path is conditional on the exact external attestation. -/
theorem splitFromPaymentCheck (supplied : Attestation) (ref : EvidenceRef)
    (attested : supplied nextShare.paid nextShare.entitlement (tick 46) ref) :
    let start := researchStart supplied ref
    Step start (JointM.paymentEvent 16 6) (JointM.afterPaymentAt45 start 16 6) ∧
    PaymentPath start [ordinaryEvent, verifyNext ref, fileNext]
      (afterFiling (afterIndependentCheck (afterOrdinary start))) := by
  refine ⟨researchPermission supplied ref, .next (postActual _ ?_)
    (.next (verifyAttested supplied ref attested) (.next (fileChecked supplied ref) (.nil _)))⟩
  change ¬ (13 : Nat) ∈ [2]
  decide

theorem recognisedSplitFromPaymentCheck (supplied : Attestation) (ref : EvidenceRef)
    (attested : supplied nextShare.paid nextShare.entitlement (tick 46) ref) :
    let start := researchStart supplied ref
    let embed := RecognisedV15.Workflow.State.fromDirect
    RecognisedV15.Workflow.Step (embed start) (JointM.paymentEvent 16 6)
      (embed (JointM.afterPaymentAt45 start 16 6)) ∧
    RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step (embed start)
      [ordinaryEvent, verifyNext ref, fileNext]
      (embed (afterFiling (afterIndependentCheck (afterOrdinary start)))) := by
  have witness := splitFromPaymentCheck supplied ref attested
  exact ⟨RecognisedV15.Workflow.step_from_direct witness.1,
    RecognisedV15.Workflow.path_from_direct witness.2⟩

/-- The added t46 attestation is a fixed external input at the research opening.
Both locked representations execute the same accepted prefix and all three split events. -/
theorem fullAcceptedSplit (supplied : Attestation) (ref : EvidenceRef)
    (attested : supplied nextShare.paid nextShare.entitlement (tick 46) ref) :
    let opening := withAttestation commonStart supplied ref
    let start := researchStart supplied ref
    let filed := afterFiling (afterIndependentCheck (afterOrdinary start))
    let events := datesBefore45 .accepted true ++ [ordinaryEvent, verifyNext ref, fileNext]
    PaymentPath opening events filed ∧
      RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step
        (RecognisedV15.Workflow.State.fromDirect opening) events
        (RecognisedV15.Workflow.State.fromDirect filed) := by
  have path := append (researchAcceptedPrefix supplied ref)
    (splitFromPaymentCheck supplied ref attested).2
  exact ⟨path, RecognisedV15.Workflow.path_from_direct path⟩

theorem formalOrdinaryApproval :
    ∃ grant : PaymentApproval, nextShare.approval = .ordinary grant ∧ grant.id = 93 ∧
      grant.approver = 10 ∧ grant.executor = 10 ∧ grant.grantedAt = tick 38 ∧
      grant ∈ beforePayment.holds.approvals := by
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, List.Mem.tail _ (List.Mem.head [])⟩

theorem exactFixedPayment :
    let paid := nextShare.paid
    nextShare.form.place.normalFee = 120 ∧ nextShare.form.place.feePayable = 120 ∧
    JointM.earlierPayment.id = 2 ∧ JointM.earlierPayment.instruction.amount = 2 ∧
    JointM.earlierPayment.instruction.atTime = tick 40 ∧
    JointM.earlierPayment.instruction.part.obligation = paid.instruction.part.obligation ∧
    JointM.earlierPayment.instruction.part.purpose = .materialsShare 7 2 ∧
    paid.id = 13 ∧ paid.instruction.part.lesson = 42 ∧ paid.instruction.part.obligation = 51 ∧
    paid.instruction.part.purpose = .materialsShare 7 3 ∧
    paid.instruction.destination = .person 3 ∧ paid.instruction.executor = 10 ∧
    paid.instruction.atTime = tick 45 ∧ paid.instruction.amount = 4 ∧
    nextShare.entitlement.holder = 3 ∧ nextShare.entitlement.amount = 4 ∧
    nextShare.funds = mFunds 16 6 (tick 45) := by
  repeat' constructor

/-- The shared ledger, current grants, and held funds agree at the endpoints.
The ordinary payment adds its own generic journal entry. Verification and filing
use distinct clocks in the split trace. -/
theorem splitAccountingAndClocks (supplied : Attestation) (ref : EvidenceRef) :
    let start := researchStart supplied ref
    let posted := afterOrdinary start
    let verified := afterIndependentCheck posted
    let filed := afterFiling verified
    posted.holds = verified.holds ∧ verified.holds = filed.holds ∧ filed.holds = atomicOutcome.holds ∧
    filed.holds.payments.posted = [JointM.earlierPayment, nextShare.paid] ∧
    posted.activeReserves = [mInitial, tAt 6] ∧ verified.activeReserves = posted.activeReserves ∧
    filed.activeReserves = verified.activeReserves ∧ filed.activeReserves = atomicOutcome.activeReserves ∧
    nextShare.entitlement ∈ filed.materials.entitlements ∧
    filed.materials.entitlements = atomicOutcome.materials.entitlements ∧
    filed.materials.provisions = atomicOutcome.materials.provisions ∧
    start.materials.receipts.map (fun entry ↦ (entry.paid.id, entry.verifiedAt, entry.filedAt)) =
      [(2, tick 44, none)] ∧
    posted.materials.receipts = start.materials.receipts ∧
    verified.materials.receipts = ⟨nextShare.paid, nextShare.funds, tick 46, none⟩ ::
      start.materials.receipts ∧
    filed.materials.receipts = ⟨nextShare.paid, nextShare.funds, tick 46, some (tick 47)⟩ ::
      start.materials.receipts ∧
    atomicOutcome.materials.receipts =
      ⟨nextShare.paid, nextShare.funds, tick 45, some (tick 45)⟩ :: start.materials.receipts ∧
    posted.materials.hasVerifiedReceiptAt nextShare.paid (tick 46) = false ∧
    filed.materials.hasVerifiedReceiptAt nextShare.paid (tick 45) = false ∧
    filed.materials.hasVerifiedReceiptAt nextShare.paid (tick 46) = true ∧
    atomicOutcome.materials.hasVerifiedReceiptAt nextShare.paid (tick 45) = true ∧
    filed.paymentRecords = atomicOutcome.paymentRecords ++ [.post nextShare.paid] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.Mem.tail _ (List.Mem.head []),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Applying the existing current-budget reader at the different evidence clocks
keeps both estimates at t45 on the split path. With both shares verified, material
8 alone still needs six. Filing preserves that reading. -/
theorem budgetsFollowVerification (supplied : Attestation) (ref : EvidenceRef) :
    let posted := afterOrdinary (researchStart supplied ref)
    let verified := afterIndependentCheck posted
    let filed := afterFiling verified
    let budgets := fun (s : State) atTime ↦
      s.materials.liveMaterialBudgetsAt s.holds.payments 42 atTime s.materialsPrincipalContext
    let material7 : MaterialsFundingKey := ⟨42, 1, 7, "agreed materials terms"⟩
    let material8 : MaterialsFundingKey := ⟨42, 1, 8, "agreed materials terms"⟩
    budgets posted (tick 45) = [(material8, 6), (material7, 6)] ∧
    budgets verified (tick 45) = [(material8, 6), (material7, 6)] ∧
    budgets verified (tick 46) = [(material8, 6)] ∧ budgets filed (tick 47) = [(material8, 6)] ∧
    budgets filed (tick 47) = budgets atomicOutcome (tick 47) := by
  let budgets := fun (s : State) atTime ↦
    s.materials.liveMaterialBudgetsAt s.holds.payments 42 atTime s.materialsPrincipalContext
  let posted := afterOrdinary beforePayment
  let verified := afterIndependentCheck posted
  let filed := afterFiling verified
  change budgets posted (tick 45) = _ ∧ budgets verified (tick 45) = _ ∧
    budgets verified (tick 46) = _ ∧ budgets filed (tick 47) = _ ∧
    budgets filed (tick 47) = budgets atomicOutcome (tick 47)
  dsimp only [budgets, posted, verified, filed]
  decide +kernel

#print axioms researchPermission
#print axioms prePaymentAuthorityAndFunds
#print axioms researchAcceptedPrefix
#print axioms laterSubstantiveChecks
#print axioms laterCheckRequiresAttestation
#print axioms splitFromPaymentCheck
#print axioms recognisedSplitFromPaymentCheck
#print axioms fullAcceptedSplit
#print axioms formalOrdinaryApproval
#print axioms exactFixedPayment
#print axioms splitAccountingAndClocks
#print axioms budgetsFollowVerification


end SparkJoint.SplitReceipt

