import SourceV14.Workflow
import Init.Data.Rat.Lemmas

/-! §§4.4 and 5.3. Same-lesson materials budgets and the cases already funded at booking. -/

namespace SourceV14.FidelityMaterialsProvisionChecks

open Confirmation Course Operations Workflow.Materials

private def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩
private def lesson : Lesson := ⟨42, .oneToOne, 10, 20, 30, 40⟩
private def place : Place := ⟨1, lesson.id, 50, 60, 70, 80, 120, 120⟩
private def schedule : Booking.Schedule := ⟨lesson.id, tick 30, tick 32, "UTC", tick 1, tick 2⟩
private def paymentTerms : PaymentTerms := ⟨.fixed (tick 50), .fixed (tick 60)⟩
private def termsReference : String := "agreed materials terms"

private def form : PartOne where
  lesson := lesson
  place := place
  contacts := ⟨"Spark", "provider", "student-channel", none, "coordinator", 50, "lead",
    none, none, 60, "reviewer", 70, "alternative", true, 80, "escalation"⟩
  rulesVersion := "1.5"
  confirmedAt := tick 4
  customerRepresentatives := []
  schedule := schedule
  serviceTerms := "agreed service"
  serviceItems := [1]
  discountBasis := none
  privateRoster := none
  rosterLock := none
  groupRescheduleCutoff := none
  oneToOneAdvanceCutoff := some (.fixed (tick 18))
  cancelChangeTerms := "change terms"
  noFaultTerms := "no-fault terms"
  applicableStartTerms := "start terms"
  tutorAgreementRef := "teaching agreement"
  absentGroupPlacePay := none
  materialsOrBundle := some "bundle"
  materialsTermsRef := some termsReference
  materialsPayer := some lesson.provider
  deadlines := ⟨.fixed (tick 55), tick 60, none, paymentTerms, paymentTerms, paymentTerms,
    paymentTerms, .fixed (tick 70), tick 72, tick 65, tick 66, .fixed (tick 80)⟩

private def allocation (material : MaterialId) : MaterialsAllocation material :=
  ⟨"two holders", [2, 3], fun holder _ charge ↦ if holder = 2 then charge / 3 else 2 * charge / 3⟩

private def terms : MaterialsTerms where
  lesson := lesson.id
  adoptedBy := lesson.provider
  agreedAt := tick 0
  agreementReference := termsReference
  accountingAndPaymentParty := lesson.provider
  materialsOrBundle := "bundle"
  contact := "coordinator"
  licensedUse := fun material ↦ material ∈ [7, 8]
  sharesAndAdjustmentsReference := "original shares"
  sharesInForce := fun material _ ↦ some (allocation material)
  contributors := fun _ ↦ [2, 3]
  consents := [7, 8].flatMap (fun material ↦
    [2, 3].map (fun holder ↦ ⟨material, holder, termsReference, tick 0⟩))
  ordinaryShareTime := fun _ _ firstUse _ ↦ firstUse
  paymentDue := tick 50
  paymentDeadline := tick 60
  pricing := .standardBundle [⟨7, 1 / 20⟩, ⟨8, 1 / 20⟩]

private def provision (material : MaterialId) (budget secured : Amount) (seconds : Nat) :
    PendingMaterialsFundingRecord where
  pending := ⟨lesson.id, place.id, material, termsReference, tick seconds,
    ⟨false, false, false, false⟩, budget⟩
  form := form
  otherAmountsOwed := 0
  funds := ⟨lesson.id, lesson.provider, tick seconds, [⟨1, .providerFunds, .spendable,
    secured, 0, secured⟩]⟩
  verifiedEstimate := fun pending ↦ pending.budget = budget

private def before : History := { terms := [terms] }
private def first := provision 7 6 6 20
private def afterFirst : History := { before with provisions := [first] }
private def noPayments : PaymentHistory := ⟨[], [], []⟩

private noncomputable def budgetsWith (history : History) (payments : PaymentHistory)
    (row : PendingMaterialsFundingRecord) : List (MaterialsFundingKey × Amount) :=
  ({ history with provisions := row :: history.provisions } : History).liveMaterialBudgetsAt
    payments row.pending.lesson row.pending.checkedAt

private def beforeBooking (base : StartEvidence) : StartEvidence :=
  { base with
    effectiveForms := [form]
    groupRoster := none
    bookings := []
    teachingBegan := none }

private theorem formMatches : form.matches := by
  simp [PartOne.matches, form, lesson, place, schedule, paymentTerms, Place.matches,
    Place.validFees, Booking.Schedule.valid, Contacts.complete, PayAndReviewTerms.valid,
    PaymentTerms.valid, PaymentDeadline.valid, AdvanceWindow.validAt, termsReference,
    Moment.by, Moment.before, tick]
  all_goals decide +kernel

private theorem formRetained (base : StartEvidence) (atTime : Moment) :
    ∃ roster forms, (beforeBooking base).rosterFormsAt lesson atTime roster forms ∧
      form ∈ forms := by
  refine ⟨none, [form], ⟨⟨⟨by simp [beforeBooking], ?_⟩, rfl⟩, rfl⟩, List.Mem.head []⟩
  intro found present
  have same : found = form := List.mem_singleton.mp present
  subst found
  exact ⟨rfl, formMatches⟩

private theorem independentEstimate (material : MaterialId) (budget secured : Amount)
    (seconds : Nat)
    (covered : terms.pricing.covers material) (nonnegative : 0 ≤ budget)
    (secures : (provision material budget secured seconds).funds.secures budget)
    (spendable : 0 ≤ secured) :
    PendingMaterialsProvision form terms (provision material budget secured seconds).pending
      (provision material budget secured seconds).otherAmountsOwed
      (provision material budget secured seconds).funds
      (provision material budget secured seconds).verifiedEstimate := by
  refine ⟨formMatches, rfl, rfl, rfl, rfl, rfl, rfl, covered, Or.inl rfl, rfl, nonnegative,
    (show (0 : Amount) ≤ 0 by decide), rfl, ?_, ?_⟩
  · simp [provision, CurrentLessonFunds.validFor, FundingEntry.valid, FundingEntry.available,
      form, spendable]
    rw [Rat.sub_eq_add_neg, show -(0 : Amount) = 0 by decide, Rat.add_zero]
    exact Rat.le_refl
  · simpa [provision, Rat.add_zero] using secures

theorem firstPendingShareCanBeProvided (base : StartEvidence) (holds : HoldHistory) :
    Step (beforeBooking base) holds before (.provision terms first) afterFirst := by
  refine .provision (history := before) (row := first) (by simp [before])
    (formRetained base (tick 20)) ?_ ?_ (by simp [before]) ?_
    (by simp [History.provisionsStillCovered, before])
  · simp [first, provision, MaterialsShareStatus.holdMustFollowSection62]
  · refine independentEstimate 7 6 6 20 ?_ (by decide) ?_ (by decide)
    · simp [terms, MaterialsPricing.covers, MaterialsPricing.materials]
    · unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
      decide +kernel
  · refine ⟨?_, by simp [beforeBooking]⟩
    change first.funds.secures (sumAmounts (budgetsWith before noPayments first) Prod.snd)
    unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
    decide +kernel

theorem cannotDuplicateSixAcrossTwoKnownPendingShares
    (base : StartEvidence) (holds : HoldHistory) (next : History) :
    ¬ Step (beforeBooking base) holds afterFirst (.provision terms (provision 8 6 6 21)) next := by
  intro occurrence
  cases occurrence with
  | provision _ _ _ _ _ joint _ =>
    have impossible : ¬ (provision 8 6 6 21).funds.secures
        (sumAmounts (budgetsWith afterFirst noPayments (provision 8 6 6 21)) Prod.snd) := by
      unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
      decide +kernel
    exact impossible joint.1

theorem backfilledBudgetCannotReuseFundsAtAKnownLaterCheck
    (base : StartEvidence) (holds : HoldHistory) (next : History) :
    ¬ Step (beforeBooking base) holds afterFirst (.provision terms (provision 8 6 6 19)) next := by
  intro occurrence
  cases occurrence with
  | provision _ _ _ _ _ _ preserved =>
    have later := preserved first (List.Mem.head []) rfl (by decide)
    have impossible : ¬ first.funds.secures (sumAmounts
        (({ afterFirst with provisions := [provision 8 6 6 19, first] } : History
          ).liveMaterialBudgetsAt noPayments lesson.id (tick 20)) Prod.snd) := by
      unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
      decide +kernel
    exact impossible later.1

theorem twoPendingSharesCanUseTwelve (base : StartEvidence) (holds : HoldHistory) :
    let second := provision 8 6 12 21
    Step (beforeBooking base) holds afterFirst (.provision terms second)
      { afterFirst with provisions := [second, first] } := by
  dsimp only
  refine .provision (history := afterFirst) (row := provision 8 6 12 21)
    (by simp [afterFirst, before]) (formRetained base (tick 21)) ?_ ?_ ?_ ?_ ?_
  · simp [provision, MaterialsShareStatus.holdMustFollowSection62]
  · refine independentEstimate 8 6 12 21 ?_ (by decide) ?_ (by decide)
    · simp [terms, MaterialsPricing.covers, MaterialsPricing.materials]
    · unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
      decide +kernel
  · intro prior saved same
    have eq : prior = first := List.mem_singleton.mp saved
    subst prior
    exact (show (7 : Nat) ≠ 8 by decide) (congrArg MaterialsFundingKey.material same) |>.elim
  · refine ⟨?_, by simp [beforeBooking]⟩
    change (provision 8 6 12 21).funds.secures
      (sumAmounts (budgetsWith afterFirst noPayments (provision 8 6 12 21)) Prod.snd)
    unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
    decide +kernel
  · simp [History.provisionsStillCovered, afterFirst, first, provision, tick, Moment.before]

theorem revisingTheSameEstimateDoesNotCountItTwice (base : StartEvidence) (holds : HoldHistory) :
    let revised := provision 7 5 5 21
    Step (beforeBooking base) holds afterFirst (.provision terms revised)
      { afterFirst with provisions := [revised, first] } := by
  dsimp only
  refine .provision (history := afterFirst) (row := provision 7 5 5 21)
    (by simp [afterFirst, before]) (formRetained base (tick 21)) ?_ ?_ ?_ ?_ ?_
  · simp [provision, MaterialsShareStatus.holdMustFollowSection62]
  · refine independentEstimate 7 5 5 21 ?_ (by decide) ?_ (by decide)
    · simp [terms, MaterialsPricing.covers, MaterialsPricing.materials]
    · unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
      decide +kernel
  · intro prior saved _
    have eq : prior = first := List.mem_singleton.mp saved
    subst prior
    decide
  · refine ⟨?_, by simp [beforeBooking]⟩
    change (provision 7 5 5 21).funds.secures
      (sumAmounts (budgetsWith afterFirst noPayments (provision 7 5 5 21)) Prod.snd)
    unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
    decide +kernel
  · simp [History.provisionsStillCovered, afterFirst, first, provision, tick, Moment.before]

private def taught : PlaceFundingOutcome :=
  ⟨place.id, .ordinarySettlement place.feePayable, "service provided", [⟨.teachingBegan, true⟩]⟩

private def cancelled : PlaceFundingOutcome :=
  ⟨place.id, .noFaultCancellation false 0, "no teaching", []⟩

private def taughtCase : FundingCase := ⟨[(place, taught)], fun _ ↦ true⟩
private def cancelledCase : FundingCase := ⟨[(place, cancelled)], fun _ ↦ false⟩

private def bookedFirst : FundingExpense where
  obligation := 51
  lesson := lesson.id
  kind := .materialsShare 7 2
  agreementReference := termsReference
  component := "first share"
  amount := 6
  agreedRecipient := none
  outcomes := [(place.id, taught.caseReference)]
  conditions := []
  materialsPortions := [⟨place.id, 6⟩]

private def bookingTerms : FundingTerms :=
  ⟨⟨lesson.id, lesson.provider, tick 2, 1, [FundingFormTerms.fromForm form],
    [taught, cancelled], [bookedFirst], [], []⟩, noPayments⟩

private def booked (otherFields : BookingEvidence) : BookingEvidence :=
  { otherFields with funding := ⟨bookingTerms, (provision 7 6 120 2).funds⟩ }

private def withBooking (base : StartEvidence) (booking : BookingEvidence) : StartEvidence :=
  { beforeBooking base with bookings := [(form, booked booking)], bookedRosters := [] }

private theorem cancelledCaseIsPossible :
    cancelledCase.possible bookingTerms lesson [place] := by
  refine ⟨by simp [cancelledCase], Or.inl rfl, by simp [cancelledCase], ?_⟩
  intro p outcome selection
  have same : (p, outcome) = (place, cancelled) := List.mem_singleton.mp selection
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨List.Mem.head [], List.Mem.tail taught (List.Mem.head []), rfl,
    ⟨by simp [cancelled], rfl, rfl, rfl⟩⟩

theorem provisionCannotIgnoreARetainedBookingCase (base : StartEvidence)
    (booking : BookingEvidence) (holds : HoldHistory) (next : History) :
    ¬ Step (withBooking base booking) holds before (.provision terms first) next := by
  intro occurrence
  cases occurrence with
  | provision _ _ _ _ _ joint _ =>
    have secured := joint.2 form (booked booking) (List.Mem.head []) rfl (by decide)
      none (Or.inr ⟨by simp [withBooking], Or.inl rfl⟩) cancelledCase cancelledCaseIsPossible
      (by simp [withBooking, beforeBooking])
    have impossible : ¬ first.funds.secures
        (cancelledCase.remainingCostWithMaterials bookingTerms (tick 20) []) := by
      unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
      decide +kernel
    exact impossible secured

theorem bookedMaterialsAmountCoversThatSameShareOnly :
    taughtCase.remainingCostWithMaterials bookingTerms (tick 21)
      (budgetsWith before bookingTerms.payments first) = 6 ∧
    taughtCase.remainingCostWithMaterials bookingTerms (tick 21)
      (budgetsWith afterFirst bookingTerms.payments (provision 8 6 12 21)) = 12 := by
  constructor <;> decide +kernel

theorem aNoTeachingAlternativeCanShareTheReserve :
    cancelledCase.remainingCostWithMaterials bookingTerms (tick 21)
      (budgetsWith afterFirst bookingTerms.payments (provision 8 6 12 21)) = 120 := by
  decide +kernel

theorem recordedTeachingExcludesTheNoTeachingCase (scenario : FundingCase)
    (possible : scenario.possible bookingTerms lesson [place])
    (selected : scenario.selections = [(place, cancelled)])
    (compatible : (∃ began ∈ some (tick 10), began.by (tick 20)) →
      scenario.facts .teachingBegan = true) : False := by
  have teaching := compatible ⟨tick 10, rfl, by decide⟩
  have outcome := possible.2.2.2 place cancelled (by simp [selected])
  have noTeaching : scenario.facts .teachingBegan = false := outcome.2.2.2.2.1
  rw [teaching] at noTeaching
  cases noTeaching

private def originalForProvision : Settlement :=
  let finding : ConfirmedMaterialUse :=
    ⟨lesson.id, place.id, 7, 1, tick 31, lesson.coordinator, tick 33, .lessonRecord "actual use"⟩
  let authority : MaterialsUseAuthority :=
    ⟨{ corePartner := fun _ _ ↦ False
       initialFinding := fun _ _ _ ↦ False
       reviewer := fun _ _ _ ↦ False
       approvesPayment := fun _ _ _ ↦ False
       interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
       originalDecisionMaker := fun _ ↦ none
       originalSettlementProposers := fun _ ↦ []
       originalSettlementApprovers := fun _ ↦ [] },
      fun _ ↦ ⟨17, lesson.id, [2, 3]⟩, fun _ ↦ none⟩
  let use : VerifiedMaterialsUse :=
    { lesson := lesson
      startedAt := tick 30
      endedAt := tick 32
      tutorReport := none
      authority := authority
      places := [place]
      deliveryReports := []
      findings := [finding]
      verifiesEvidence := (· = finding)
      verifiedReportOmission := fun _ ↦ False
      uniquePlaces := by simp
      placeInLesson := by simp [place, Place.matches]
      findingInLesson := by simp [finding]
      findingAtPlace := by simp [finding] }
  ⟨⟨lesson.id, 7, termsReference, "original settlement", bookedFirst.obligation, tick 34,
     [place.id], use.chargesFor terms 7⟩, ⟨use, terms, none, tick 33⟩⟩

private def verifiedShare (holder : ActorId) (amount : Amount) : Entitlement :=
  ⟨originalForProvision, none, holder, amount, tick 35, lesson.provider,
    { originalReference := 13
      agreedSharesAt := fun _ ↦ some (allocation 7)
      verifiedOriginal := fun agreement reference shares ↦ agreement = terms ∧ reference = 13 ∧
        shares = (fun _ ↦ some (allocation 7)) }⟩

private def receipt (holder recipient : ActorId) (amount : Amount) : PostedPayment :=
  ⟨holder, ⟨⟨lesson.id, bookedFirst.obligation, 1, .materialsShare 7 holder⟩,
    .person recipient, lesson.provider, amount, tick 40⟩, some holder⟩

private def reconciledHistory (entries : List PostedPayment) : History :=
  { afterFirst with
    originals := [originalForProvision]
    entitlements := [verifiedShare 2 2, verifiedShare 3 4]
    receipts := entries.map (fun paid ↦
      ⟨paid, first.funds, paid.instruction.atTime, some paid.instruction.atTime⟩) }

private noncomputable def stillNeeded (receipts : List PostedPayment)
    (returns : List ReturnedPayment := []) : Amount :=
  sumAmounts (budgetsWith (reconciledHistory receipts) ⟨receipts, returns, []⟩
    (provision 8 6 6 42)) Prod.snd

theorem onlyFullyReceivedSharesDischargeTheOriginalBudget :
    stillNeeded [receipt 2 2 2] = 12 ∧
    stillNeeded [receipt 2 2 2, receipt 3 99 4] = 12 ∧
    stillNeeded [receipt 2 2 2, receipt 3 3 4] = 6 ∧
    stillNeeded [receipt 2 2 2, receipt 3 3 4] [⟨11, 3, 1, tick 41, 12⟩] = 12 := by
  repeat' constructor <;> decide +kernel

private def outsideTransfer : Transfer where
  material := 7
  sparkDao := lesson.provider
  recordedAt := tick 38
  record :=
    { transfer := ⟨2, 99, .voluntaryTransfer, tick 36, .sharesAtFirstUse,
        allocation 7, allocation 7⟩
      reference := "verified transfer for another lesson"
      verifiedTerms := fun _ _ ↦ True
      transferorShareTime := tick 35
      applicableOwnershipTime := (· = tick 35)
      voluntary := True
      publishedTermsSatisfied := True
      governs := fun id _ _ ↦ id = 55
      originalCollections := fun _ _ _ ↦ []
      shortfallCollections := fun _ _ _ _ ↦ [] }

theorem anotherLessonsTransferDoesNotRetainThisPaidCharge :
    let receipts := [receipt 2 2 2, receipt 3 3 4]
    ({ reconciledHistory receipts with transfers := [outsideTransfer] } : History
      ).paidOriginalCharge ⟨receipts, [], []⟩ first.pending (tick 42) = true := by
  simp only [History.paidOriginalCharge, reconciledHistory, List.any_cons, List.any_nil,
    Bool.or_false, List.filter_cons, List.filter_nil, originalForProvision, outsideTransfer,
    lesson]
  simp only [show (42 : LessonId) ≠ 55 by decide, decide_false]
  decide +kernel

private def beforePosting (receipts : List PostedPayment := []) : History :=
  { reconciledHistory receipts with provisions := [provision 8 6 12 21, first] }

private def newPayout (holder : ActorId) (amount balance committed : Amount) : Receipt :=
  let entitlement := verifiedShare holder (if holder = 2 then 2 else 4)
  let paid := receipt holder holder amount
  let part : PaymentPart := ⟨paid.instruction.part, .person holder none, entitlement.amount⟩
  {
    entitlement := entitlement
    form := form
    agreedRecipient := none
    recipientReceipt := none
    part := part
    paid := { id := holder + 10, instruction := { paid.instruction with atTime := tick 45 },
              evidence := paid.evidence }
    authority := { originalForProvision.check.use.authority.authorities with
      approvesPayment := fun ref actor atTime ↦
        ref = part.ref ∧ actor = lesson.provider ∧ atTime = tick 38 }
    facts :=
      { terms := fun _ ↦ ⟨30, 70, 50, .exact (tick 65), tick 55, tick 60, tick 66, 80⟩
        termsApply := fun _ ↦ True
        acceptedPaymentConcern := fun _ _ _ _ ↦ False
        reviewerCannotActInTime := fun _ _ ↦ False
        temporaryAuthority := fun _ _ _ _ ↦ False
        allegedFactsWouldChangePayment := fun _ _ _ ↦ False
        separatelyIdentifiable := fun _ _ ↦ True
        establishedParts := fun id purpose ↦
          if id = part.ref.lesson ∧ purpose = part.ref.purpose then [part] else []
        paymentAffected := fun _ _ ↦ False
        decisionPending := fun _ _ _ ↦ False
        partFallsUnderDecision := fun _ _ _ ↦ False
        decisionConcernsWholeGroup := fun _ _ ↦ False
        isGroupLesson := fun _ ↦ False
        affectsWholeSettlement := fun _ ↦ False
        groupSettlementParts := fun _ ↦ [] }
    approval := .ordinary ⟨90 + holder, lesson.provider, lesson.provider, tick 38, none, none,
      [⟨part.ref, .person holder, part.amount, none⟩]⟩
    schedule := ⟨tick 50, tick 60, none, .date (tick 80)⟩
    dueTrigger := none
    executionTrigger := none
    conditions := fun _ ↦ True
    afterLift := []
    funds := ⟨lesson.id, lesson.provider, tick 45,
      [⟨1, .providerFunds, .spendable, balance, committed, 0⟩]⟩ }

private def protectedOnBooks : ProvisionFundingExclusion :=
  ⟨⟨lesson.id, place.id, 8, termsReference⟩, 1, 6, 61⟩

private def netPayout : Receipt :=
  let attempt := newPayout 2 2 12 6
  { attempt with
    excludedProvisionFunds := [protectedOnBooks]
    verifiesProvisionExclusion := fun funds paid entry ↦
      funds = attempt.funds ∧ paid = attempt.paid ∧ entry = protectedOnBooks }

theorem canPayTwoWhileProtectingTheRemainingTen :
    (newPayout 2 2 12 0).protectsProvisions beforePosting noPayments := by
  unfold Receipt.protectsProvisions
  refine ⟨by simp [newPayout], by simp [newPayout], by simp [newPayout], by simp [newPayout], ?_, ?_⟩
  · decide +kernel
  · unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
    decide +kernel

theorem cannotPayByUsingCashStillProtectedForASecondMaterial :
    ¬ (newPayout 2 2 6 0).protectsProvisions beforePosting noPayments := by
  intro allowed
  have cash := allowed.2.2.2.2.2
  unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith at cash
  revert cash
  decide +kernel

theorem elevenCannotCoverTwoAndBothRemainingProvisions :
    ¬ (newPayout 2 2 11 0).protectsProvisions beforePosting noPayments := by
  intro allowed
  have cash := allowed.2.2.2.2.2
  unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith at cash
  revert cash
  decide +kernel

theorem aVerifiedExcludedProvisionAlreadyHasItsFunds :
    netPayout.protectsProvisions beforePosting noPayments := by
  unfold Receipt.protectsProvisions
  refine ⟨by simp [netPayout, newPayout], by simp [netPayout, newPayout],
    by simp [netPayout], ?_, ?_, ?_⟩
  · intro row included
    rw [List.mem_singleton.mp included]
    refine ⟨by decide +kernel, ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
    · refine ⟨(provision 8 6 12 21).pending, List.Mem.head _, rfl, ?_⟩
      decide +kernel
    · exact ⟨_, List.Mem.head [], rfl, rfl, by decide +kernel⟩
  · decide +kernel
  · unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
    decide +kernel

theorem cannotTreatAnUnverifiedExclusionAsProtectedCash :
    ¬ ({ netPayout with verifiesProvisionExclusion := fun _ _ _ ↦ False } : Receipt
      ).protectsProvisions beforePosting noPayments := by
  intro allowed
  exact (allowed.2.2.2.1 protectedOnBooks (List.Mem.head [])).2.1

theorem verifiedPastReceiptReducesTheStillPayableProvision :
    let earlier := receipt 2 2 2
    (newPayout 3 4 10 0).protectsProvisions (beforePosting [earlier]) ⟨[earlier], [], []⟩ := by
  unfold Receipt.protectsProvisions
  refine ⟨by simp [newPayout], by simp [newPayout], by simp [newPayout], by simp [newPayout], ?_, ?_⟩
  · decide +kernel
  · unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
    decide +kernel

theorem aReceiptCountsFromVerificationEvenIfFiledLater :
    let actual := receipt 2 2 2
    let other := receipt 3 3 4
    let fullLedger : PaymentHistory := ⟨[actual, other], [], []⟩
    let fullHistory : History := { beforePosting with
      receipts := [⟨actual, first.funds, tick 45, some (tick 46)⟩,
        ⟨other, first.funds, tick 40, none⟩] }
    let budgets := fun checkedAt ↦
      sumAmounts (fullHistory.liveMaterialBudgetsAt fullLedger lesson.id (tick checkedAt)) Prod.snd
    let attempt := newPayout 3 4 10 0
    let protects := fun verifiedAt ↦
      attempt.protectsProvisions
        { beforePosting with receipts := [⟨actual, first.funds, tick verifiedAt, none⟩] }
        ⟨[actual], [], []⟩
    (budgets 44 = 12 ∧ budgets 45 = 6 ∧ budgets 46 = 6) ∧
      (¬ protects 46 ∧ protects 45 ∧ protects 44) := by
  dsimp only
  constructor
  · repeat' constructor <;> decide +kernel
  constructor
  · intro allowed
    have cash := allowed.2.2.2.2.2
    unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith at cash
    revert cash
    decide +kernel
  · constructor <;> (
      unfold Receipt.protectsProvisions
      refine ⟨by simp [newPayout], by simp [newPayout], by simp [newPayout], by simp [newPayout],
        by decide +kernel, ?_⟩
      unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
      decide +kernel)

theorem misdirectedReceiptCannotFundAnotherPayment :
    let earlier := receipt 2 99 2
    ¬ (newPayout 3 4 10 0).protectsProvisions (beforePosting [earlier]) ⟨[earlier], [], []⟩ := by
  dsimp only
  intro allowed
  have cash := allowed.2.2.2.2.2
  unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith at cash
  revert cash
  decide +kernel

theorem returnedCashDoesNotDischargeItsShare :
    let earlier := receipt 2 2 2
    let returned : ReturnedPayment := ⟨11, earlier.id, 1, tick 41, 12⟩
    ¬ (newPayout 3 4 10 0).protectsProvisions
      (beforePosting [earlier]) ⟨[earlier], [returned], []⟩ := by
  dsimp only
  intro allowed
  have cash := allowed.2.2.2.2.2
  unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith at cash
  revert cash
  decide +kernel

theorem protectionAppliesThroughTheNewPaymentStep
    (ev : StartEvidence) (holds : HoldHistory) (next : History) :
    let attempt := newPayout 2 2 6 0
    ¬ Step ev { holds with payments := noPayments } beforePosting (.post attempt) next := by
  dsimp only
  intro occurrence
  cases occurrence with
  | post _ _ accepted =>
    have cash := accepted.2.2.2.2.2.2.2
    dsimp only [Receipt.postingHistory, newPayout, withReceipt] at cash
    unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith at cash
    revert cash
    decide +kernel

-- The paired root fixture follows the independent A2ArchiveRootPair review construction.
private def earlierPayout : Receipt :=
  { newPayout 2 2 0 0 with paid := receipt 2 2 2 }

private def plannedPayout : Receipt := newPayout 3 4 10 0

private def payout (observed : Bool) : Receipt :=
  if observed then earlierPayout else plannedPayout

private def grant (holder : ActorId) (amount : Amount) : PaymentApproval :=
  ⟨90 + holder, lesson.provider, lesson.provider, tick 38, none, none,
    [⟨(receipt holder holder amount).instruction.part, .person holder, amount, none⟩]⟩

private def recorded : HoldHistory where
  payments := ⟨[earlierPayout.paid], [], []⟩
  temporary := []
  formal := []
  lifts := []
  approvals := [grant 2 2, grant 3 4]
  approvalArrangements := []
  originalSettlements := []

private def checkHistory (observed : Bool) : HoldHistory :=
  if observed then recorded else plannedPayout.postingHistory recorded

private def evidenceHistory (availableAt : Moment) (receipts : List ReceiptRecord := []) : History :=
  { beforePosting with
    receipts := receipts
    verifiesReceiptAt := fun paid entitlement point reference ↦
      paid = earlierPayout.paid ∧ entitlement = earlierPayout.entitlement ∧
      point = availableAt ∧ reference = 81 }

private def fixedCourse : StartEvidence where
  effectiveForms := [form]
  groupRoster := none
  bookings := []
  scheduleHistory := []
  changes := []
  openingCredit := fun _ ↦ 0
  creditRecords :=
    ⟨[], [], [], [], fun _ _ ↦ False, fun _ _ ↦ False, [], recorded.payments,
      plannedPayout.authority, {}⟩
  ledger := []
  discounts := []
  notices := []
  academicTeamAt := fun _ _ _ ↦ False
  teachingBegan := some (tick 30)
  teachingEnded := some (tick 32)
  studentsTakingLesson := [place.student]
  afterLesson := ⟨[], [], [], [], [], []⟩
  studentFaults :=
    { findings := []
      decisions :=
        { authorities := plannedPayout.authority
          terms := plannedPayout.facts.terms ⟨0, lesson.id, []⟩
          appointments := []
          faultOutcomes := []
          faultMatterCovers := fun _ _ ↦ False
          wasResponsibleTutor := fun _ _ ↦ False
          originalAttendanceTime := fun _ _ _ ↦ False }
      recordedStudentOutcome := fun _ ↦ False }

private theorem fixedRoster (point : Moment) :
    fixedCourse.rosterFormsAt lesson point none [form] := by
  refine ⟨⟨⟨by simp [fixedCourse], ?_⟩, rfl⟩, rfl⟩
  intro found present
  have same : found = form := List.mem_singleton.mp present
  subst found
  exact ⟨rfl, formMatches⟩

private theorem effectiveTutor :
    EffectiveTutorAt lesson fixedCourse (tick 30) lesson.tutor := by
  refine ⟨none, ?_, rfl⟩
  simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement, fixedCourse]

private theorem firstProvision :
    PendingMaterialsProvision form terms first.pending first.otherAmountsOwed first.funds
      first.verifiedEstimate := by
  refine independentEstimate 7 6 6 20 ?_ (by decide) ?_ (by decide)
  · simp [terms, MaterialsPricing.covers, MaterialsPricing.materials]
  · unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
    decide +kernel

private theorem pendingRecorded (availableAt : Moment) (receipts : List ReceiptRecord)
    (observed : Bool) :
    (evidenceHistory availableAt receipts).pendingProvisionRecorded fixedCourse
      (payout observed).entitlement := by
  intro prior saved resolved required
  have found : prior = (provision 8 6 12 21).pending ∨ prior = first.pending := by
    simpa only [evidenceHistory, beforePosting, List.map_cons, List.map_nil,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using saved
  rcases found with rfl | rfl
  · cases observed <;> cases (show (8 : Nat) = 7 from resolved.2.1)
  · cases observed <;> exact ⟨first, List.Mem.tail _ (List.Mem.head []), rfl,
      ⟨none, [form], fixedRoster _, List.Mem.head []⟩, firstProvision⟩

private theorem portionVerified (availableAt knownAt : Moment) (receipts : List ReceiptRecord)
    (observed : Bool) :
    let row := payout observed
    ((evidenceHistory availableAt receipts).shareEvidence row.entitlement knownAt).portionAt
      terms originalForProvision.check.use ⟨place.id, 7, 6⟩ (tick 31)
      row.paid.instruction.atTime row.entitlement.holder row.entitlement.amount := by
  cases observed <;> refine ⟨trivial, Or.inl ⟨?_, allocation 7, ?_, by decide, ?_, ?_⟩⟩
  all_goals first
    | intro transfer present
      cases present
    | refine ⟨(by decide : (tick 31).by (tick 35)), ⟨rfl, rfl, rfl⟩, allocation 7, rfl,
        ⟨(terms.lesson, place.id), 13, allocation 7, tick 0⟩, ?_,
        (by decide : (tick 0).by (tick 35)), rfl⟩
      simp [payout, earlierPayout, plannedPayout, newPayout, verifiedShare,
        privateArrangementAt, History.shareEvidence, terms]
    | change (allocation 7).distributesCharge place.id 6
      unfold MaterialsAllocation.distributesCharge
      decide +kernel
    | change (_ : Amount) = (allocation 7).portion _ place.id 6
      decide +kernel

private theorem entitlementVerified (availableAt knownAt : Moment) (receipts : List ReceiptRecord)
    (observed : Bool) (paymentKnown : (payout observed).paid.instruction.atTime.by knownAt)
    (shareKnown : (tick 35).by knownAt) :
    let row := payout observed
    let history := evidenceHistory availableAt receipts
    (history.shareEvidence row.entitlement knownAt).eligibleAt
      originalForProvision.check.use terms originalForProvision.record row.entitlement.holder
      row.entitlement.amount row.paid.instruction.atTime knownAt
      (useBasisVerified := row.entitlement.retainedBasis history) (shortfalls := []) := by
  let amounts : PlaceId → Amount := fun _ ↦ (payout observed).entitlement.amount
  cases observed <;>
    refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, by simp [originalForProvision], ?_, ?_, ?_,
      (by decide : (tick 32).before (tick 34)), (by decide : (tick 34).by (tick 35)),
      (by change (tick 34).by _; decide), paymentKnown, shareKnown, rfl, ?_,
      tick 31, rfl, amounts, ?_, ?_,
      by decide +kernel⟩
  all_goals first
    | decide +kernel
    | intro charge present
      have charges : originalForProvision.check.use.chargesFor terms 7 = [⟨place.id, 7, 6⟩] := by
        decide +kernel
      change charge ∈ originalForProvision.check.use.chargesFor terms 7 at present
      rw [charges] at present
      cases List.mem_singleton.mp present
      first
      | exact portionVerified availableAt knownAt receipts false
      | exact portionVerified availableAt knownAt receipts true
    | simp [Entitlement.retainedBasis, payout, earlierPayout, plannedPayout, newPayout,
        verifiedShare, evidenceHistory, beforePosting, reconciledHistory]

private theorem originalPermission :
    originalExecutorMayPay plannedPayout.authority plannedPayout.facts (checkHistory false)
      (grant 3 4) plannedPayout.part plannedPayout.schedule plannedPayout.conditions
      plannedPayout.paid.instruction := by
  unfold originalExecutorMayPay
  rw [HoldHistory.factsAt_of_noPartRevisions _ rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, trivial, by decide, ?_, ?_, ?_, ?_⟩
  · unfold HoldFacts.isCanonicalPart
    decide +kernel
  · unfold HoldHistory.approvalRecorded
    decide +kernel
  · simp [PaymentApproval.authorisedAtGrant, grant, plannedPayout, newPayout]
  · unfold PaymentApproval.validAt
    decide
  · rw [HoldHistory.approvalCovers_of_noPartRevisions _ rfl]
    refine ⟨⟨plannedPayout.part.ref, .person 3, 4, none⟩, List.Mem.head [], ?_⟩
    unfold ApprovalScopeEntry.covers
    decide +kernel
  · unfold PaymentHistory.validOutstandingPayment PaymentHistory.distinctReceipts
      PaymentHistory.validReturns
    decide +kernel
  · unfold HoldHistory.distinctFormalDecisions
    decide
  · simp [HoldHistory.paymentOnHold, HoldHistory.formalInForce, HoldHistory.validFormalHold,
      HoldHistory.temporaryInForce, checkHistory, Receipt.postingHistory, withReceipt, recorded,
      plannedPayout, newPayout]
  · exact HoldHistory.noUnresolvedScopeWithoutRevisions _ rfl _ _ _ _ _
  · unfold HoldHistory.remainingPortionBefore
    decide +kernel

private theorem filedPayment :
    plannedPayout.approval.filedPayment plannedPayout.authority plannedPayout.facts
      (checkHistory false) plannedPayout.part plannedPayout.schedule
      plannedPayout.conditions plannedPayout.paid plannedPayout.afterLift := by
  refine ⟨?_, Or.inl rfl, originalPermission, ?_⟩
  · unfold PaymentHistory.actualPaymentWithEvidence
    decide
  · rintro ⟨time, ⟨hold, lift, released, _⟩, _⟩
    have impossible := released.1.1
    simp [checkHistory, Receipt.postingHistory, withReceipt, recorded, plannedPayout,
      newPayout] at impossible

private theorem earlierPaymentObserved :
    earlierPayout.approval.observedPayment earlierPayout.authority earlierPayout.facts
      recorded earlierPayout.part earlierPayout.paid := by
  unfold PaymentApprovalRoute.observedPayment
  rw [HoldHistory.factsAt_of_noPartRevisions _ rfl]
  refine ⟨?_, ?_, ?_, by decide, ?_, ?_, Or.inl rfl, ?_⟩
  · unfold HoldFacts.isCanonicalPart
    decide +kernel
  · unfold HoldHistory.approvalRecorded
    decide +kernel
  · simp [PaymentApproval.authorisedAtGrant, earlierPayout, newPayout]
  · refine ⟨⟨earlierPayout.part.ref, .person 2, 2, none⟩, List.Mem.head [], ?_⟩
    exact ⟨rfl, Or.inl rfl, by decide, by simp⟩
  · unfold PaymentHistory.actualPaymentWithEvidence
    decide
  · unfold PaymentHistory.validOutstandingPayment PaymentHistory.distinctReceipts
      PaymentHistory.validReturns
    decide +kernel

private theorem ordinaryOrObservedChecks (availableAt knownAt : Moment)
    (receipts : List ReceiptRecord) (observed : Bool)
    (fresh : (payout observed).paid.id ∉ receipts.map (·.paid.id))
    (paymentKnown : (payout observed).paid.instruction.atTime.by knownAt)
    (shareKnown : (tick 35).by knownAt) :
    (payout observed).conformsAt (evidenceHistory availableAt receipts) fixedCourse
      (checkHistory observed) knownAt observed := by
  refine ⟨?_, fresh, ?_, ?_⟩
  · cases observed <;> rfl
  · cases observed <;> simp [Receipt.recipientMatches, payout, earlierPayout, plannedPayout,
      newPayout]
  unfold MaterialsPaymentPosted
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Iff.rfl, Iff.rfl⟩
  · refine ⟨none, [form], ?_, ?_, ?_⟩
    · cases observed <;> exact fixedRoster _
    · cases observed <;> exact List.Mem.head []
    · intro selected contained _
      have same : selected = place := by
        cases observed <;>
          simpa [originalForProvision, payout, earlierPayout, plannedPayout, newPayout,
            Entitlement.check, verifiedShare] using contained
      subst selected
      cases observed <;> exact ⟨form, List.Mem.head [], rfl, rfl, rfl, rfl, rfl⟩
  · cases observed <;> rfl
  · cases observed <;> exact formMatches
  · cases observed <;> exact effectiveTutor
  · cases observed <;> rfl
  · cases observed <;> rfl
  · cases observed <;> rfl
  · cases observed <;> simp [payout, earlierPayout, plannedPayout, newPayout,
      Entitlement.check, verifiedShare, originalForProvision]
  · cases observed <;> rfl
  · cases observed <;> rfl
  · cases observed <;> exact List.Mem.head []
  · intro other present _ _ _
    cases observed <;> exact List.mem_singleton.mp present
  · cases observed
    · exact entitlementVerified availableAt knownAt receipts false paymentKnown shareKnown
    · exact entitlementVerified availableAt knownAt receipts true paymentKnown shareKnown
  · cases observed <;> trivial
  · constructor
    · intro _ prior saved resolved required
      have found : prior = (provision 8 6 12 21).pending ∨ prior = first.pending := by
        simpa only [evidenceHistory, beforePosting, List.map_cons, List.map_nil,
          List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using saved
      rcases found with rfl | rfl
      · cases observed <;> cases (show (8 : Nat) = 7 from resolved.2.1)
      · cases observed <;> exact ⟨first, List.Mem.tail _ (List.Mem.head []), rfl, rfl,
          ⟨none, [form], fixedRoster _, List.Mem.head []⟩, firstProvision⟩
    · intro _
      exact pendingRecorded availableAt receipts observed
  · cases observed <;> exact Or.inl ⟨rfl, trivial⟩
  · cases observed <;> exact Or.inl ⟨rfl, trivial⟩
  · cases observed <;> rfl
  · cases observed <;> rfl
  · cases observed <;> rfl
  · cases observed <;> simp [HoldFacts.matchesForm, payout, earlierPayout, plannedPayout, newPayout]
  · cases observed <;> rfl
  · cases observed <;> rfl
  · cases observed <;> rfl
  · cases observed <;> rfl
  · intro transfer present
    cases present
  · unfold HoldFacts.coversObligation
    cases observed <;> decide +kernel
  · cases observed
    · change (4 : Amount) ≤ (checkHistory false).payments.remainingObligationBefore
        lesson.id 51 (.person 3 none) 4 (tick 45) (some (.materialsShare 7 3))
      decide +kernel
    · change (2 : Amount) ≤ recorded.payments.remainingObligationBefore lesson.id 51
        (.person 2 none) 2 (tick 40) (some (.materialsShare 7 2))
      decide +kernel
  · cases observed
    · refine Or.inl ⟨?_, rfl, ?_, filedPayment⟩
      · unfold CurrentLessonFunds.validFor FundingEntry.valid FundingEntry.available
        decide +kernel
      · unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
        decide +kernel
    · exact Or.inr ⟨rfl, earlierPaymentObserved⟩

private def rootBefore (availableAt : Moment) (receipts : List ReceiptRecord := []) :
    Workflow.State where
  lessons := fun _ ↦ Workflow.LessonFile.fromEvidence fixedCourse
  credit := Workflow.CreditBook.fromEvidence fixedCourse
  holds := recorded
  cancelled := []
  settlement := {}
  redress := {}
  materials := evidenceHistory availableAt receipts
  review := Workflow.Review.History.empty
  debts := {}
  activeReserves := []
  paymentRecords := []
  separateBookings := []

private def verifiedEarlier (point : Moment) : ReceiptRecord :=
  ⟨earlierPayout.paid, earlierPayout.funds, point, none⟩

private def ready (point : Moment) : Workflow.State := rootBefore point [verifiedEarlier point]

private def afterPayment : Workflow.State :=
  { (ready (tick 44)).withHolds (checkHistory false) with
    materials := evidenceHistory (tick 44)
      [⟨plannedPayout.paid, plannedPayout.funds, tick 45, some (tick 45)⟩,
       verifiedEarlier (tick 44)] }

private theorem verifiesEarlierPayment (point : Moment) (paymentKnown : (tick 40).by point)
    (shareKnown : (tick 35).by point) :
    Workflow.Step (rootBefore point)
      (.materials lesson.id (.verifyReceipt earlierPayout point 81)) (ready point) := by
  refine Workflow.Step.materials (sameLesson := ?_) (funds := trivial)
    (rule := ?_) (payment := rfl)
  · intro id present
    exact Option.some.inj present.symm
  · change Step fixedCourse recorded (evidenceHistory point)
      (.verifyReceipt earlierPayout point 81) _
    refine .verifyReceipt ⟨rfl, rfl, rfl, rfl⟩
      ⟨List.Mem.head [], paymentKnown, ?_, pendingRecorded point [] true, ?_⟩
    · exact ⟨List.Mem.head [], by simp [earlierPayout, newPayout, verifiedShare]⟩
    · exact ordinaryOrObservedChecks point point [] true (by simp) paymentKnown shareKnown

theorem aSupportedEarlierReceiptCanBeVerified :
    Workflow.Step (rootBefore (tick 44))
      (.materials lesson.id (.verifyReceipt earlierPayout (tick 44) 81)) (ready (tick 44)) :=
  verifiesEarlierPayment (tick 44) (by decide) (by decide)

theorem aLaterReceiptCannotBeBackdated (after : Workflow.State) :
    ¬ Workflow.Step (rootBefore (tick 46))
      (.materials lesson.id (.verifyReceipt earlierPayout (tick 44) 81)) after := by
  intro step
  cases step with
  | materials _ _ material _ =>
    cases material with
    | verifyReceipt evidence _ =>
      exact (by decide : tick 44 ≠ tick 46) evidence.2.2.1

theorem filingCannotCreateReceiptAvailability (after : Workflow.State) :
    ¬ Workflow.Step (rootBefore (tick 44))
      (.materials lesson.id (.file earlierPayout.paid (tick 46))) after := by
  intro step
  cases step with
  | materials _ _ material _ =>
    cases material with
    | file fileable =>
      exact (by decide : (0 : Nat) ≠ 1) fileable.1

theorem payoutScheduleMatchesTheFixedPostLiftDate :
    postLiftTermMatches plannedPayout.form.deadlines.postLiftPay plannedPayout.schedule := by
  change tick 80 = tick 80
  rfl

theorem sufficientFundsAllowTheNewPaymentStep :
    Workflow.Step (ready (tick 44)) (.materials lesson.id (.post plannedPayout)) afterPayment := by
  refine Workflow.Step.materials (sameLesson := ?_) (funds := ?_) (rule := ?_) (payment := ?_)
  · intro id present
    exact Option.some.inj present.symm
  · intro entry present
    have same : entry = ⟨1, .providerFunds, .spendable, 10, 0, 0⟩ := by
      simpa [plannedPayout, newPayout] using present
    subst entry
    simp [Workflow.Reserves.occupiedElsewhere, Receipt.provisionFundsOutsideAvailable,
      ready, rootBefore, plannedPayout, newPayout, sumAmounts, sumAmountsWhere]
    decide +kernel
  · change Step fixedCourse recorded (evidenceHistory (tick 44) [verifiedEarlier (tick 44)])
      (.post plannedPayout) _
    refine .post (by decide) (by simp [plannedPayout, newPayout]) ⟨?_, ?_, ?_⟩
    · simp [evidenceHistory, beforePosting, reconciledHistory, plannedPayout, newPayout]
    · exact ordinaryOrObservedChecks (tick 44) (tick 45) [verifiedEarlier (tick 44)] false
        (by decide) (by decide) (by decide)
    · unfold Receipt.protectsProvisions
      refine ⟨by simp [plannedPayout, newPayout], by simp [plannedPayout, newPayout],
        by simp [plannedPayout, newPayout], by simp [plannedPayout, newPayout],
        by decide +kernel, ?_⟩
      unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith
      decide +kernel
  · refine ⟨_, Workflow.Payment.Step.post plannedPayout.paid (by decide +kernel)
      (by decide), rfl⟩

theorem aLateVerifiedReceiptCannotFundTheEarlierPayment (after : Workflow.State) :
    Workflow.Step (rootBefore (tick 46))
      (.materials lesson.id (.verifyReceipt earlierPayout (tick 46) 81)) (ready (tick 46)) ∧
    ¬ Workflow.Step (ready (tick 46)) (.materials lesson.id (.post plannedPayout)) after := by
  refine ⟨verifiesEarlierPayment (tick 46) (by decide) (by decide), ?_⟩
  intro step
  cases step with
  | materials _ _ material _ =>
    cases material with
    | post _ _ accepted =>
      have cash := accepted.2.2.2.2.2.2.2
      unfold CurrentLessonFunds.covers CurrentLessonFunds.coversWith at cash
      revert cash
      decide +kernel

private def afterFiling : Workflow.State :=
  { afterPayment with materials := afterPayment.materials.fileReceipt earlierPayout.paid (tick 46) }

/-- This follows the actual verification and posting transitions above. Filing has
    the same verified time and leaves the ledger and reserves in place. -/
theorem administrativeFilingAfterPayment :
    Workflow.Step afterPayment (.materials lesson.id (.file earlierPayout.paid (tick 46)))
      afterFiling ∧
    afterFiling.materials.receipts =
      [⟨plannedPayout.paid, plannedPayout.funds, tick 45, some (tick 45)⟩,
       ⟨earlierPayout.paid, earlierPayout.funds, tick 44, some (tick 46)⟩] ∧
    afterFiling.holds = afterPayment.holds ∧ afterFiling.activeReserves = afterPayment.activeReserves :=
  ⟨by
    refine Workflow.Step.materials (sameLesson := ?_) (funds := trivial)
      (rule := .file ?_) (payment := rfl)
    · intro id present
      exact Option.some.inj present.symm
    · exact ⟨by decide, _, List.Mem.tail _ (List.Mem.head []), rfl, rfl, by decide⟩,
   rfl, rfl, rfl⟩

theorem administrativeFilingCannotRepeat (after : Workflow.State) :
    ¬ Workflow.Step afterFiling (.materials lesson.id (.file earlierPayout.paid (tick 47))) after := by
  intro step
  cases step with
  | materials _ _ material _ =>
    cases material with
    | file fileable =>
      rcases fileable.2 with ⟨entry, present, same, unfiled, _⟩
      rcases List.mem_cons.mp present with eq | remaining
      · cases eq
        cases (show some (tick 45) = none from unfiled)
      · cases List.mem_singleton.mp remaining
        cases (show some (tick 46) = none from unfiled)

#print axioms firstPendingShareCanBeProvided
#print axioms cannotDuplicateSixAcrossTwoKnownPendingShares
#print axioms backfilledBudgetCannotReuseFundsAtAKnownLaterCheck
#print axioms twoPendingSharesCanUseTwelve
#print axioms revisingTheSameEstimateDoesNotCountItTwice
#print axioms provisionCannotIgnoreARetainedBookingCase
#print axioms bookedMaterialsAmountCoversThatSameShareOnly
#print axioms aNoTeachingAlternativeCanShareTheReserve
#print axioms recordedTeachingExcludesTheNoTeachingCase
#print axioms onlyFullyReceivedSharesDischargeTheOriginalBudget
#print axioms anotherLessonsTransferDoesNotRetainThisPaidCharge
#print axioms canPayTwoWhileProtectingTheRemainingTen
#print axioms cannotPayByUsingCashStillProtectedForASecondMaterial
#print axioms elevenCannotCoverTwoAndBothRemainingProvisions
#print axioms aVerifiedExcludedProvisionAlreadyHasItsFunds
#print axioms cannotTreatAnUnverifiedExclusionAsProtectedCash
#print axioms verifiedPastReceiptReducesTheStillPayableProvision
#print axioms aReceiptCountsFromVerificationEvenIfFiledLater
#print axioms misdirectedReceiptCannotFundAnotherPayment
#print axioms returnedCashDoesNotDischargeItsShare
#print axioms protectionAppliesThroughTheNewPaymentStep
#print axioms aSupportedEarlierReceiptCanBeVerified
#print axioms aLaterReceiptCannotBeBackdated
#print axioms filingCannotCreateReceiptAvailability
#print axioms payoutScheduleMatchesTheFixedPostLiftDate
#print axioms sufficientFundsAllowTheNewPaymentStep
#print axioms aLateVerifiedReceiptCannotFundTheEarlierPayment
#print axioms administrativeFilingAfterPayment
#print axioms administrativeFilingCannotRepeat

end SourceV14.FidelityMaterialsProvisionChecks
