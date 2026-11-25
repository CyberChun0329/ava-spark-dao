
namespace SourceV14.FidelityMaterialsProvisionChecks.JointM

open Confirmation Course Operations Workflow.Materials

/-! The two-course research fixture retains the locked M3 course and material evidence.
The two lesson files share one credit book and one provider funding entry. -/

def materialLesson : LessonId := lesson.id

def otherLesson : LessonId := 100

def materialFile : Workflow.LessonFile :=
  Workflow.LessonFile.fromEvidence fixedCourse

def materialAuthority : ReviewAuthorities := plannedPayout.authority

def openingPayments : PaymentHistory := { recorded.payments with posted := [] }

def openingHolds : HoldHistory := { recorded with payments := openingPayments }

def observedHolds : HoldHistory := recorded

def heldMaterialFunds : Workflow.Reserves.Reservation := ⟨lesson.provider, lesson.id, 1, 12⟩

def materialHistory (availableAt : Nat) (verifiedAt : Option Nat := none)
    (certificate : Moment → Prop := fun _ ↦ True) : History :=
  let source := evidenceHistory (tick availableAt)
    (verifiedAt.toList.map (fun n ↦ verifiedEarlier (tick n)))
  { source with verifiesReceiptAt := fun paid entitlement point reference ↦
    source.verifiesReceiptAt paid entitlement (tick availableAt) reference ∧
    (tick availableAt).by point ∧ certificate point }

def start (availableAt : Nat) (otherFile : Workflow.LessonFile)
    (credit : Workflow.CreditBook) (certificate : Moment → Prop := fun _ ↦ True) : Workflow.State :=
  { ((rootBefore (tick availableAt)).withHolds openingHolds) with
    lessons := fun id ↦ if id = materialLesson then materialFile else otherFile
    credit := { credit with creditRecords :=
      { credit.creditRecords with payments := openingPayments } }
    materials := materialHistory availableAt none certificate
    activeReserves := [heldMaterialFunds] }

theorem startProvisionsForM (availableAt : Nat) (otherFile : Workflow.LessonFile)
    (credit : Workflow.CreditBook) (certificate : Moment → Prop) :
    ∀ row ∈ (start availableAt otherFile credit certificate).materials.provisions,
      row.pending.lesson ≠ otherLesson := by
  intro row present
  have isM : row = provision 8 6 12 21 ∨ row = first := by
    simpa [start, materialHistory, evidenceHistory, beforePosting] using present
  rcases isM with rfl | rfl <;> decide

def earlierPayment : PostedPayment := earlierPayout.paid

theorem earlierPaymentAmountAndTime :
    earlierPayment.instruction.amount = 2 ∧ earlierPayment.instruction.atTime = tick 40 :=
  ⟨rfl, rfl⟩

def earlierPaymentEvent : Workflow.Event := .payment (.post earlierPayout.paid)

def afterEarlierPayment (s : Workflow.State) : Workflow.State :=
  { s.withHolds observedHolds with
    paymentRecords := s.paymentRecords ++ [.post earlierPayout.paid] }

theorem postEarlierPayment (s : Workflow.State) (holds : s.holds = openingHolds) :
    Workflow.Step s earlierPaymentEvent (afterEarlierPayment s) := by
  exact Workflow.Step.payment (event := .post earlierPayout.paid) trivial
    (holds ▸ Workflow.Payment.Step.post earlierPayout.paid (by decide +kernel) (by decide))

/-- The fields from M3 that the endpoint uses after the other course has progressed. -/
structure HasMaterialEvidence (s : Workflow.State) (availableAt : Nat)
    (verifiedAt : Option Nat) (certificate : Moment → Prop := fun _ ↦ True) : Prop where
  courseFile : s.lessons materialLesson = materialFile
  holds : s.holds = observedHolds
  history : s.materials = materialHistory availableAt verifiedAt certificate
  principal : s.materialsPrincipalContext = {}

def verificationEvent (atTime : Nat) : Workflow.Event :=
  .materials materialLesson (.verifyReceipt earlierPayout (tick atTime) 81)

def afterVerification (s : Workflow.State) (atTime : Nat) : Workflow.State :=
  { s.withHolds s.holds with
    materials := { s.materials with
      receipts := verifiedEarlier (tick atTime) :: s.materials.receipts } }

private def materialCourse (book : Workflow.CreditBook) : StartEvidence :=
  materialFile.evidence book

private theorem retainsRoster (book : Workflow.CreditBook) (point : Moment) :
    (materialCourse book).rosterFormsAt lesson point none [form] := fixedRoster point

private theorem retainsEffectiveTutor (book : Workflow.CreditBook) :
    EffectiveTutorAt lesson (materialCourse book) (tick 30) lesson.tutor := by
  refine ⟨none, ?_, rfl⟩
  simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement,
    materialCourse, materialFile, Workflow.LessonFile.evidence, Workflow.LessonFile.fromEvidence,
    fixedCourse]

private theorem retainsProvision (book : Workflow.CreditBook) (availableAt : Moment)
    (receipts : List ReceiptRecord) (observed : Bool) :
    (evidenceHistory availableAt receipts).pendingProvisionRecorded (materialCourse book)
      (payout observed).entitlement := by
  intro prior saved resolved required
  have found : prior = (provision 8 6 12 21).pending ∨ prior = first.pending := by
    simpa only [evidenceHistory, beforePosting, List.map_cons, List.map_nil,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using saved
  rcases found with rfl | rfl
  · cases observed <;> cases (show (8 : Nat) = 7 from resolved.2.1)
  · cases observed <;> exact ⟨first, List.Mem.tail _ (List.Mem.head []), rfl,
      ⟨none, [form], retainsRoster book _, List.Mem.head []⟩, firstProvision⟩

def attempt (gross committed : Amount) : Receipt := newPayout 3 4 gross committed

private def checkedPayout (observed : Bool) (gross committed : Amount) : Receipt :=
  if observed then earlierPayout else attempt gross committed

/-- Only the credit book and the current cash snapshot differ from the locked M3 checks. -/
private theorem payoutChecks (book : Workflow.CreditBook) (availableAt knownAt : Moment)
    (receipts : List ReceiptRecord) (observed : Bool) (gross committed : Amount)
    (fresh : (payout observed).paid.id ∉ receipts.map (·.paid.id))
    (paymentKnown : (payout observed).paid.instruction.atTime.by knownAt)
    (shareKnown : (tick 35).by knownAt)
    (available : observed = false →
      (attempt gross committed).funds.validFor lesson ∧ (attempt gross committed).funds.covers 4) :
    (checkedPayout observed gross committed).conformsAt (evidenceHistory availableAt receipts)
      (materialCourse book) (checkHistory observed) knownAt observed := by
  have original := ordinaryOrObservedChecks availableAt knownAt receipts observed fresh
    paymentKnown shareKnown
  rcases original with
    ⟨purpose, fresh, recipient, roster, use, formMatched, tutor, began, ended, bundle, reports,
      reference, payer, settled, unique, eligible, shortfall, provision, due, deadline, scheduled,
      latestExecution, lift, facts, partLesson, partPurpose, obligation, destination, collects,
      covers, outstanding, cash, onTime, completeOnTime⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases observed <;> exact purpose
  · cases observed <;> exact fresh
  · cases observed <;> exact recipient
  · cases observed <;> exact roster
  · cases observed <;> exact use
  · cases observed <;> exact formMatched
  · cases observed <;> exact retainsEffectiveTutor book
  · cases observed <;> exact began
  · cases observed <;> exact ended
  · cases observed <;> exact bundle
  · cases observed <;> exact reports
  · cases observed <;> exact reference
  · cases observed <;> exact payer
  · cases observed <;> exact settled
  · cases observed <;> exact unique
  · cases observed <;> exact eligible
  · cases observed <;> exact shortfall
  · cases observed <;> exact provision
  · cases observed <;> exact Or.inl ⟨rfl, trivial⟩
  · cases observed <;> exact Or.inl ⟨rfl, trivial⟩
  · cases observed <;> exact scheduled
  · cases observed <;> exact latestExecution
  · cases observed <;> exact lift
  · cases observed <;> exact facts
  · cases observed <;> exact partLesson
  · cases observed <;> exact partPurpose
  · cases observed <;> exact obligation
  · cases observed <;> exact destination
  · cases observed <;> exact collects
  · cases observed <;> exact covers
  · cases observed <;> exact outstanding
  · cases observed
    · exact .inl ⟨(available rfl).1, rfl, (available rfl).2, filedPayment⟩
    · exact cash
  · cases observed <;> exact onTime
  · cases observed <;> exact completeOnTime

theorem verifyEarlierPayment (s : Workflow.State) (availableAt n : Nat)
    {certificate : Moment → Prop} (evidence : HasMaterialEvidence s availableAt none certificate)
    (available : (tick availableAt).by (tick n)) (verified : certificate (tick n))
    (paymentKnown : (tick 40).by (tick n)) (shareKnown : (tick 35).by (tick n)) :
    Workflow.Step s (verificationEvent n) (afterVerification s n) := by
  refine Workflow.Step.materials (sameLesson := ?_) (funds := trivial) (rule := ?_) (payment := rfl)
  · intro id present
    exact Option.some.inj present.symm
  · unfold Workflow.State.course
    rw [evidence.courseFile, evidence.holds, evidence.history, evidence.principal]
    refine .verifyReceipt ⟨⟨rfl, rfl, rfl, rfl⟩, available, verified⟩
      ⟨List.Mem.head [], paymentKnown, ?_,
        retainsProvision s.credit (tick availableAt) [] true, ?_⟩
    · exact ⟨List.Mem.head [], by simp [earlierPayout, newPayout, verifiedShare]⟩
    · exact payoutChecks s.credit (tick availableAt) (tick n) [] true 0 0 (by simp) paymentKnown
        shareKnown (by simp)

theorem retainsVerification (s : Workflow.State) (availableAt n : Nat)
    {certificate : Moment → Prop} (evidence : HasMaterialEvidence s availableAt none certificate) :
    HasMaterialEvidence (afterVerification s n) availableAt (some n) certificate := by
  refine ⟨evidence.courseFile, evidence.holds, ?_, evidence.principal⟩
  unfold afterVerification
  rw [evidence.history]
  rfl


/-- The receipt histories compared at the proposed t45 payment. -/
inductive ReceiptStatus where
  | unverified
  | verified44
  | verified46

def ReceiptStatus.point : ReceiptStatus → Option Nat
  | .unverified => none
  | .verified44 => some 44
  | .verified46 => some 46

def ReceiptStatus.requiredFunds : ReceiptStatus → Amount
  | .verified44 => 10
  | .unverified | .verified46 => 12

private theorem coversAmount (gross committed amount : Amount) :
    (attempt gross committed).funds.covers amount ↔ max 0 amount ≤ gross - committed := by
  change max 0 (amount - 0) ≤ 0 + (gross - committed) ↔ max 0 amount ≤ gross - committed
  simp only [Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero, Rat.zero_add]

private theorem validFunds (gross committed : Amount) (nonnegative : 0 ≤ committed)
    (netNonnegative : 0 ≤ gross - committed) :
    (attempt gross committed).funds.validFor lesson := by
  refine ⟨rfl, rfl, by simp [attempt, newPayout], ?_⟩
  intro entry present
  have entryValue : entry = ⟨1, .providerFunds, .spendable, gross, committed, 0⟩ := by
    simpa [attempt, newPayout] using present
  subst entry
  exact ⟨nonnegative, (Rat.le_iff_sub_nonneg committed gross).mpr netNonnegative,
    show (0 : Amount) ≤ 0 by decide, netNonnegative⟩

private theorem sameThreshold {actual required net : Amount} (equal : actual = required) :
    actual ≤ net ↔ required ≤ net := equal ▸ Iff.rfl

/-- The local guard evaluates to 4 + 6 using t44 evidence, or 4 + (6 + 2) otherwise. -/
private theorem provisionThreshold (availableAt : Nat) (certificate : Moment → Prop)
    (status : ReceiptStatus) (gross committed : Amount) :
    (attempt gross committed).protectsProvisions
      (materialHistory availableAt status.point certificate)
      ((attempt gross committed).postingHistory observedHolds).payments ↔
    status.requiredFunds ≤ gross - committed := by
  unfold Receipt.protectsProvisions
  constructor
  · intro protects
    have available := (coversAmount gross committed _).mp protects.2.2.2.2.2
    refine (sameThreshold ?_).mp available
    cases status <;> decide_cbv
  · intro available
    refine ⟨by simp [attempt, newPayout], by simp [attempt, newPayout],
      by simp [attempt, newPayout], by simp [attempt, newPayout], ?_, ?_⟩
    · cases status <;> decide_cbv
    · apply (coversAmount gross committed _).mpr
      refine (sameThreshold ?_).mpr available
      cases status <;> decide_cbv

def paymentEvent (gross committed : Amount) : Workflow.Event :=
  .materials materialLesson (.post (attempt gross committed))

def afterPaymentAt45 (s : Workflow.State) (gross committed : Amount) : Workflow.State :=
  let row := attempt gross committed
  { s.withHolds (row.postingHistory s.holds) with
    materials := { s.materials with
      receipts := ⟨row.paid, row.funds, tick 45, some (tick 45)⟩ :: s.materials.receipts } }

theorem enoughFundsForMaterialsPayment (s : Workflow.State) (availableAt : Nat)
    (status : ReceiptStatus) (gross committed : Amount) {certificate : Moment → Prop}
    (evidence : HasMaterialEvidence s availableAt status.point certificate)
    (occupied : Workflow.Reserves.occupiedElsewhere s.activeReserves
      (attempt gross committed).funds 1 ≤ committed)
    (nonnegative : 0 ≤ committed) (enough : status.requiredFunds ≤ gross - committed) :
    Workflow.Step s (paymentEvent gross committed) (afterPaymentAt45 s gross committed) := by
  have fourBelowFloor : (4 : Amount) ≤ status.requiredFunds := by cases status <;> decide
  have fundsValid := validFunds gross committed nonnegative
    (Rat.le_trans (show (0 : Amount) ≤ 4 by decide) (Rat.le_trans fourBelowFloor enough))
  have cash : (attempt gross committed).funds.covers 4 := by
    exact (coversAmount gross committed 4).mpr (Rat.le_trans fourBelowFloor enough)
  refine Workflow.Step.materials (sameLesson := ?_) (funds := ?_) (rule := ?_) (payment := ?_)
  · intro id present
    exact Option.some.inj present.symm
  · intro entry present
    have entryValue : entry = ⟨1, .providerFunds, .spendable, gross, committed, 0⟩ := by
      simpa [attempt, newPayout] using present
    subst entry
    change Workflow.Reserves.occupiedElsewhere s.activeReserves (attempt gross committed).funds 1
      + 0 ≤ committed
    simpa only [Rat.add_zero] using occupied
  · unfold Workflow.State.course
    rw [evidence.courseFile, evidence.holds, evidence.history, evidence.principal]
    refine .post (by change ¬ (13 : Nat) ∈ [2]; decide) (by simp [attempt, newPayout]) ⟨?_, ?_, ?_⟩
    · simp [materialHistory, evidenceHistory, beforePosting, reconciledHistory, attempt, newPayout]
    · have fresh : plannedPayout.paid.id ∉
          (status.point.toList.map (fun n ↦ verifiedEarlier (tick n))).map (·.paid.id) := by
        cases status <;> decide
      exact payoutChecks s.credit (tick availableAt) (tick 45)
        (status.point.toList.map (fun n ↦ verifiedEarlier (tick n))) false gross committed fresh
        (by decide) (by decide) (fun _ ↦ ⟨fundsValid, cash⟩)
    · exact (provisionThreshold availableAt certificate status gross committed).mpr enough
  · refine ⟨_, Workflow.Payment.Step.post (attempt gross committed).paid
      (by change (0 : Amount) < 4; decide) ?_, rfl⟩
    rw [evidence.holds]
    change ¬ (13 : Nat) ∈ [2]
    decide

theorem insufficientFundsBlockMaterialsPayment (s next : Workflow.State) (availableAt : Nat)
    (status : ReceiptStatus) (gross committed : Amount) {certificate : Moment → Prop}
    (evidence : HasMaterialEvidence s availableAt status.point certificate)
    (insufficient : ¬ status.requiredFunds ≤ gross - committed) :
    ¬ Workflow.Step s (paymentEvent gross committed) next := by
  intro step
  cases step with
  | materials _ _ rule _ =>
    cases rule with
    | post _ _ payment =>
      have budget := payment.2.2
      rw [evidence.history, evidence.holds, evidence.principal] at budget
      exact insufficient ((provisionThreshold availableAt certificate status gross committed).mp
        budget)

theorem paymentKeepsReserves (s : Workflow.State) (gross committed : Amount) :
    (afterPaymentAt45 s gross committed).activeReserves = s.activeReserves := rfl

theorem paymentKeepsMaterialProvisions (s : Workflow.State) (gross committed : Amount) :
    (afterPaymentAt45 s gross committed).materials.provisions = s.materials.provisions := rfl

theorem paymentPostsFour (s : Workflow.State) (gross committed : Amount) :
    (afterPaymentAt45 s gross committed).holds.payments.posted =
      s.holds.payments.posted ++ [(attempt gross committed).paid] ∧
    (attempt gross committed).paid.instruction.amount = 4 := ⟨rfl, rfl⟩

#print axioms postEarlierPayment
#print axioms verifyEarlierPayment
#print axioms enoughFundsForMaterialsPayment
#print axioms insufficientFundsBlockMaterialsPayment

end SourceV14.FidelityMaterialsProvisionChecks.JointM
