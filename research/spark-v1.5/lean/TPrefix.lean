import RecognisedV15.Workflow

namespace JointT

open SourceV14 SourceV14.Booking SourceV14.Confirmation SourceV14.Course
open SourceV14.CreditEvidence SourceV14.Settlement
open SourceV14.Workflow

def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩

def lesson : Lesson := ⟨100, .oneToOne, 10, 20, 30, 2⟩

def place : Place := ⟨1, lesson.id, 101, 102, 102, 103, 4, 4⟩

def schedule : Schedule := ⟨lesson.id, tick 32, tick 33, "UTC", tick 26, tick 27⟩

def paymentTerms : PaymentTerms := ⟨.fixed (tick 80), .fixed (tick 80)⟩

def form : PartOne where
  lesson := lesson
  place := place
  contacts := ⟨"Spark", "provider", "student", some "tutor", "coordinator", 31, "lead",
    none, none, 40, "reviewer", 41, "alternative", true, 50, "escalation"⟩
  rulesVersion := "1.5"
  confirmedAt := tick 31
  customerRepresentatives := []
  schedule := schedule
  serviceTerms := "agreed teaching"
  serviceItems := [1, 2]
  discountBasis := none
  privateRoster := none
  rosterLock := none
  groupRescheduleCutoff := none
  oneToOneAdvanceCutoff := some (.fixed (tick 31))
  cancelChangeTerms := "agreed changes"
  noFaultTerms := "no-fault terms"
  applicableStartTerms := "start conditions"
  tutorAgreementRef := "teaching agreement"
  absentGroupPlacePay := none
  materialsOrBundle := none
  materialsTermsRef := none
  materialsPayer := none
  deadlines := ⟨.fixed (tick 60), tick 60, none, paymentTerms, paymentTerms, paymentTerms,
    paymentTerms, .fixed (tick 70), tick 72, tick 65, tick 66, .fixed (tick 80)⟩

theorem formMatches : form.matches := by
  simp [PartOne.matches, form, place, lesson, schedule, paymentTerms, Place.matches,
    Place.validFees, Schedule.valid, Contacts.complete, PayAndReviewTerms.valid,
    PaymentTerms.valid, PaymentDeadline.valid, AdvanceWindow.validAt, Moment.by, Moment.before,
    tick] <;> decide +kernel

def someTeaching : FundingCondition := ⟨.teachingBegan, true⟩

def noTeaching : FundingCondition := ⟨.teachingBegan, false⟩

def tutorAtFault : FundingFact :=
  .agreedCase form.tutorAgreementRef "Tutor for the original lesson was at fault"

def providerAtFault : FundingFact :=
  .agreedCase form.applicableStartTerms "Provider arranging, administration or notice was at fault"

def standardUntaught : PlaceFundingOutcome :=
  ⟨place.id, .standardCompensation false 0, "compensation without teaching",
    [noTeaching, ⟨.partyAtFaultForDisruption, true⟩]⟩

def standardTaught : PlaceFundingOutcome :=
  ⟨place.id, .standardCompensation true 0, "tutor fault compensation after teaching",
    [someTeaching, ⟨tutorAtFault, true⟩]⟩

def providerCompensationTaught : PlaceFundingOutcome :=
  ⟨place.id, .standardCompensation true 0, "provider fault compensation after teaching",
    [someTeaching, ⟨providerAtFault, true⟩]⟩

def fullRefund : PlaceFundingOutcome :=
  ⟨place.id, .fullRefund, "closure by full refund", []⟩

def noFaultUntaught : PlaceFundingOutcome :=
  ⟨place.id, .noFaultCancellation false 0, "no-fault without teaching", [noTeaching]⟩

def ordinary : PlaceFundingOutcome :=
  ⟨place.id, .ordinarySettlement 4, "ordinary settlement",
    [someTeaching, ⟨tutorAtFault, false⟩]⟩

def partialNoFault : PlaceFundingOutcome :=
  ⟨place.id, .noFaultCancellation true 2, "no-fault with partial teaching", [someTeaching]⟩

def tutorExpense : FundingExpense where
  obligation := 1002
  lesson := lesson.id
  kind := .tutorPay lesson.tutor
  agreementReference := form.tutorAgreementRef
  component := "normal tutor pay"
  amount := lesson.normalTutorFee
  agreedRecipient := none
  outcomes := []
  conditions := [someTeaching, ⟨tutorAtFault, false⟩]

private def termConditions : List FundingConditionRecord :=
  [⟨.outcome place.id standardUntaught.caseReference, form.serviceTerms, noTeaching, 1101⟩,
    ⟨.outcome place.id standardUntaught.caseReference, form.serviceTerms,
      ⟨.partyAtFaultForDisruption, true⟩, 1101⟩,
    ⟨.outcome place.id standardTaught.caseReference, form.serviceTerms, someTeaching, 1101⟩,
    ⟨.outcome place.id standardTaught.caseReference, form.tutorAgreementRef,
      ⟨tutorAtFault, true⟩, 1102⟩,
    ⟨.outcome place.id providerCompensationTaught.caseReference, form.serviceTerms,
      someTeaching, 1101⟩,
    ⟨.outcome place.id providerCompensationTaught.caseReference, form.applicableStartTerms,
      ⟨providerAtFault, true⟩, 1103⟩,
    ⟨.outcome place.id noFaultUntaught.caseReference, form.noFaultTerms, noTeaching, 1104⟩,
    ⟨.outcome place.id ordinary.caseReference, form.serviceTerms, someTeaching, 1101⟩,
    ⟨.outcome place.id ordinary.caseReference, form.tutorAgreementRef,
      ⟨tutorAtFault, false⟩, 1102⟩,
    ⟨.outcome place.id partialNoFault.caseReference, form.noFaultTerms, someTeaching, 1104⟩,
    ⟨.expense tutorExpense.obligation, form.tutorAgreementRef, someTeaching, 1102⟩,
    ⟨.expense tutorExpense.obligation, form.tutorAgreementRef, ⟨tutorAtFault, false⟩, 1102⟩]

def inventory : VerifiedFundingInventory where
  lesson := lesson.id
  provider := lesson.provider
  recordedAt := tick 28
  evidence := 1105
  forms := [FundingFormTerms.fromForm form]
  outcomes :=
    [standardUntaught, standardTaught, providerCompensationTaught, fullRefund, noFaultUntaught,
      ordinary]
  expenses := [tutorExpense]
  conditionRecords := termConditions
  partialNoFault := [⟨place.id, form.noFaultTerms, 1104, .possible [partialNoFault]⟩]

def noPayments : PaymentHistory := ⟨[], [], []⟩

def fundingTerms : FundingTerms := ⟨inventory, noPayments⟩

def fundingEntry : FundingEntry := ⟨1, .providerFunds, .spendable, 22, 12, 10⟩

def funds : CurrentLessonFunds := ⟨lesson.id, lesson.provider, tick 29, [fundingEntry]⟩

def funding : FundingCheck := ⟨fundingTerms, funds⟩

def tutorAgreement : TutorAgreement where
  lesson := lesson.id
  provider := lesson.provider
  tutor := lesson.tutor
  reference := form.tutorAgreementRef
  termsAgreedAt := tick 27
  service := form.serviceTerms
  serviceItems := form.serviceItems
  fee := lesson.normalTutorFee
  payment := paymentTerms
  tutorResponsibilities := "Provide the agreed teaching"
  providerResponsibilities := "Arrange teaching and administer the lesson"
  signatures :=
    [⟨lesson.provider, form.tutorAgreementRef, "Provider signature"⟩,
      ⟨lesson.tutor, form.tutorAgreementRef, "Tutor signature"⟩]

def signatures : Signatures :=
  ⟨lesson.id, place.id, lesson.coordinator, place.customer, tick 28, tick 28,
    lesson.provider, tick 30, lesson.tutor, tick 30, tick 30, place.customer, none⟩

def topUpReceipt : TopUpReceipt :=
  ⟨1000, place.payer, lesson.provider, place.account, 4, tick 25⟩

def topUpPosting : CreditPosting :=
  ⟨1000, place.account, .topUp topUpReceipt.id, 4, tick 25⟩

def debit : CreditPosting := ⟨1001, place.account, .lessonDebit lesson.id place.id, 4, tick 31⟩

private def documents : List BookingTermDocument :=
  [⟨.rules form.rulesVersion, 1106⟩, ⟨.tutorAgreement form.tutorAgreementRef, 1102⟩]

private def provisions : List BookingTermsProvision :=
  [⟨form, lesson.coordinator, place.customer, tick 28, tick 28, documents⟩,
    ⟨form, lesson.coordinator, lesson.tutor, tick 28, tick 28, documents⟩]

def booking : BookingEvidence :=
  { signatures
    tutorAgreement
    formation := ⟨lesson.id, lesson.provider, form.applicableStartTerms, tick 29, true⟩
    funding
    debit := some debit
    agreedDocuments := documents
    provisions }

def initialCredit (payments : PaymentHistory) (authorities : ReviewAuthorities) : CreditBook where
  openingCredit := fun _ ↦ 0
  creditRecords :=
    { topUps := [topUpReceipt]
      grants := []
      topUpReturns := []
      closed := []
      ownsAccount := fun actor account ↦ actor = place.payer ∧ account = place.account
      courseProviderAt := fun provider _ ↦ provider = lesson.provider
      verifiedRefunds := []
      payments
      paymentAuthorities := authorities }
  ledger := [topUpPosting]
  discounts := []

def preTopUpCredit (payments : PaymentHistory) (authorities : ReviewAuthorities) : CreditBook :=
  let after := initialCredit payments authorities
  { after with creditRecords := { after.creditRecords with topUps := [] }, ledger := [] }

def freshT (decisions : DecisionRecords) : LessonFile where
  effectiveForms := []
  groupRoster := none
  bookings := []
  scheduleHistory := []
  changes := []
  notices := []
  academicTeamAt := fun id actor _ ↦ id = lesson.id ∧ (actor = lesson.coordinator ∨ actor = 31)
  teachingBegan := none
  teachingEnded := none
  verifiedOneToOneAbsence := none
  studentsTakingLesson := []
  afterLesson := ⟨[], [], [], [], [], []⟩
  studentFaults := ⟨[], decisions, fun _ ↦ False⟩
  tutorReplacements := []
  rosterReview := none
  clockBoundaries := []
  tutorPayAmendments := {}
  groupRegisters := []
  verifiesGroupRegister := fun _ ↦ False
  bookedRosters := []

def localBookingEvent : SourceV14.Workflow.Booking.Event :=
  .confirmPlace form booking none (.debit debit)

def bookingEvent : SourceV14.Workflow.Event := .booking localBookingEvent

def bookedCourse (s : State) : StartEvidence :=
  let before := s.course lesson.id
  { before with
    ledger := before.ledger ++ [debit]
    bookings := [(form, booking)]
    effectiveForms := [form]
    scheduleHistory := [schedule] }

def booked (s : State) : State :=
  { s.withCourse lesson.id (bookedCourse s) with
    activeReserves := Reserves.reserve s.activeReserves funds }

theorem outcomes :
    fundingTerms.outcomes =
      [standardUntaught, standardTaught, providerCompensationTaught, fullRefund, noFaultUntaught,
        ordinary, partialNoFault] := rfl

theorem onlyExpense : fundingTerms.expenses = [tutorExpense] := rfl

theorem tutorExpenseOwed : tutorExpense.owedAt noPayments (tick 29) = 2 := by decide +kernel

theorem customerCosts :
    standardUntaught.customerCost place = 10 ∧ standardTaught.customerCost place = 6 ∧
    providerCompensationTaught.customerCost place = 6 ∧ fullRefund.customerCost place = 4 ∧
    noFaultUntaught.customerCost place = 4 ∧ ordinary.customerCost place = 0 ∧
    partialNoFault.customerCost place = 2 := by decide +kernel

theorem selectOne (scenario : FundingCase)
    (possible : scenario.possible fundingTerms lesson [place]) :
    ∃ outcome ∈ fundingTerms.outcomes, scenario.selections = [(place, outcome)] ∧
      outcome.matchesFacts scenario.facts := by
  have one : scenario.selections.length = 1 := possible.2.1.resolve_right (by decide)
  obtain ⟨⟨p, row⟩, selection⟩ := List.length_eq_one_iff.mp one
  have selected : (p, row) ∈ scenario.selections := by simp [selection]
  obtain ⟨same, present, _, fits⟩ := possible.2.2.2 p row selected
  obtain rfl := List.mem_singleton.mp same
  exact ⟨row, present, selection, fits⟩

theorem expensesByFacts (scenario : FundingCase) :
    scenario.expenses fundingTerms =
      if scenario.facts .teachingBegan && !(scenario.facts tutorAtFault) then [tutorExpense]
      else [] := by
  cases teaches : scenario.facts .teachingBegan <;>
    cases fault : scenario.facts tutorAtFault <;>
      simp [FundingCase.expenses, onlyExpense, tutorExpense, FundingCondition.holds, someTeaching,
        teaches, fault]

theorem remainingCostByFacts (scenario : FundingCase) (row : PlaceFundingOutcome)
    (selection : scenario.selections = [(place, row)]) :
    scenario.remainingCost fundingTerms (tick 29) =
      row.customerCost place +
        (if scenario.facts .teachingBegan && !(scenario.facts tutorAtFault) then 2 else 0) := by
  rw [FundingCase.remainingCost, selection, expensesByFacts]
  split <;> simp [sumAmounts, fundingTerms, tutorExpenseOwed, Rat.zero_add]

private theorem conditionsValid :
    ∀ record ∈ inventory.conditionRecords, record.matchesInventory inventory := by
  simp [inventory, termConditions, FundingConditionRecord.matchesInventory, FundingCondition.valid,
    FundingFormTerms.fromForm, VerifiedFundingInventory.allOutcomes,
    PartialNoFaultRecord.cases, form, tutorAtFault, providerAtFault,
    standardUntaught, standardTaught, providerCompensationTaught, fullRefund, noFaultUntaught,
    ordinary, partialNoFault, tutorExpense, someTeaching, noTeaching]

private theorem outcomeValid (row : PlaceFundingOutcome) (member : row ∈ fundingTerms.outcomes) :
    row.validFor place ∧
    row.conditions.Perm (inventory.conditionsFor (.outcome row.place row.caseReference)) ∧
    ∃ facts, row.matchesFacts facts := by
  simp only [outcomes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨?_, by decide +kernel, fun f ↦ f == .partyAtFaultForDisruption, ?_⟩
    · simp [PlaceFundingOutcome.validFor, standardUntaught, noTeaching, FundingCondition.valid]
    · simp [PlaceFundingOutcome.matchesFacts, standardUntaught, noTeaching, FundingCondition.holds]
  · refine ⟨?_, by decide +kernel, fun _ ↦ true, ?_⟩
    · simp [PlaceFundingOutcome.validFor, standardTaught, someTeaching, FundingCondition.valid,
        tutorAtFault, form, unappliedHalfPriceBenefit, appliedHalfPriceBenefit, halfPriceBenefit,
        place] <;> decide +kernel
    · simp [PlaceFundingOutcome.matchesFacts, standardTaught, someTeaching, FundingCondition.holds]
  · refine ⟨?_, by decide +kernel, fun _ ↦ true, ?_⟩
    · simp [PlaceFundingOutcome.validFor, providerCompensationTaught, someTeaching,
        FundingCondition.valid, providerAtFault, form, unappliedHalfPriceBenefit,
        appliedHalfPriceBenefit, halfPriceBenefit, place] <;> decide +kernel
    · simp [PlaceFundingOutcome.matchesFacts, providerCompensationTaught, someTeaching,
        FundingCondition.holds]
  · exact ⟨by simp [PlaceFundingOutcome.validFor, fullRefund], by decide +kernel,
      fun _ ↦ false, by simp [PlaceFundingOutcome.matchesFacts, fullRefund]⟩
  · exact ⟨by simp [PlaceFundingOutcome.validFor, noFaultUntaught, noTeaching,
      FundingCondition.valid], by decide +kernel, fun _ ↦ false,
      by simp [PlaceFundingOutcome.matchesFacts, noFaultUntaught, noTeaching, FundingCondition.holds]⟩
  · refine ⟨?_, by decide +kernel, fun f ↦ f == .teachingBegan, ?_⟩
    · simp [PlaceFundingOutcome.validFor, ordinary, someTeaching, FundingCondition.valid,
        tutorAtFault, form, place] <;> decide +kernel
    · simp [PlaceFundingOutcome.matchesFacts, ordinary, someTeaching, FundingCondition.holds,
        tutorAtFault]
  · refine ⟨?_, by decide +kernel, fun f ↦ f == .teachingBegan, ?_⟩
    · simp [PlaceFundingOutcome.validFor, partialNoFault, someTeaching, FundingCondition.valid] <;>
        decide +kernel
    · simp [PlaceFundingOutcome.matchesFacts, partialNoFault, someTeaching, FundingCondition.holds]

theorem fundingTermsValid : fundingTerms.validFor lesson [place] (tick 29) := by
  refine ⟨rfl, rfl, by decide, by decide, ?_, conditionsValid, by decide +kernel, ?_, ?_,
    by simp [fundingTerms, noPayments, PaymentHistory.distinctReceipts],
    by simp [fundingTerms, noPayments, PaymentHistory.validReturns],
    by simp [fundingTerms, noPayments], ?_, ?_⟩
  · simp [fundingTerms, inventory, FundingFormTerms.fromForm, form]
  · intro row present
    obtain ⟨valid, conditions, facts⟩ := outcomeValid row present
    exact ⟨⟨place, by simp, valid⟩, conditions, facts⟩
  · intro p present
    obtain rfl := List.mem_singleton.mp present
    refine ⟨?_, ⟨fullRefund, by simp [outcomes], rfl, rfl⟩,
      ⟨noFaultUntaught, by simp [outcomes], rfl, rfl⟩⟩
    intro received
    cases received
    · exact ⟨standardUntaught, by simp [outcomes], rfl, 0, rfl⟩
    · exact ⟨standardTaught, by simp [outcomes], rfl, 0, rfl⟩
  · intro expense present
    rw [onlyExpense] at present
    obtain rfl := List.mem_singleton.mp present
    refine ⟨rfl, by decide, by decide, by decide, rfl, ?_, by decide +kernel, ?_⟩
    · simp [tutorExpense]
    · simp [fundingTerms, noPayments]
  · refine ⟨by decide, ?_, ?_⟩
    · simp [fundingTerms, inventory, PartialNoFaultRecord.matchesForm, FundingFormTerms.fromForm,
        form, partialNoFault, PlaceFundingOutcome.isPartialNoFault]
    · simp [fundingTerms, inventory, standardUntaught, standardTaught, providerCompensationTaught, fullRefund,
        noFaultUntaught, ordinary, PlaceFundingOutcome.isPartialNoFault]

private theorem fundingCaseChecked (scenario : FundingCase)
    (possible : scenario.possible fundingTerms lesson [place]) :
    scenario.checked fundingTerms funds := by
  obtain ⟨row, member, selection, fits⟩ := selectOne scenario possible
  have noPaid : scenario.paidTeaching fundingTerms (tick 29) = 0 := by
    simp [FundingCase.paidTeaching, FundingTerms.paidTeachingBefore, fundingTerms, noPayments,
      sumAmounts]
  change ((scenario.expenses fundingTerms).map FundingExpense.key).Nodup ∧
    ((scenario.expenses fundingTerms).map FundingExpense.obligation).Nodup ∧
    funds.secures
      (scenario.remainingCost fundingTerms (tick 29) +
        scenario.paidTeaching fundingTerms (tick 29) - scenario.paidTeaching fundingTerms (tick 29))
  rw [expensesByFacts, remainingCostByFacts scenario row selection, noPaid]
  unfold CurrentLessonFunds.secures CurrentLessonFunds.coversWith
  by_cases teaching : scenario.facts .teachingBegan = true
  · by_cases tutorFault : scenario.facts tutorAtFault = true
    · rw [teaching, tutorFault]
      simp only [outcomes, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide +kernel
    · have tutorNotAtFault : scenario.facts tutorAtFault = false := Bool.eq_false_iff.mpr tutorFault
      rw [teaching, tutorNotAtFault]
      simp only [outcomes, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [PlaceFundingOutcome.matchesFacts, standardUntaught, FundingCondition.holds,
          noTeaching, teaching] at fits
      all_goals decide +kernel
  · have noTeaching : scenario.facts .teachingBegan = false := Bool.eq_false_iff.mpr teaching
    simp only [noTeaching, Bool.false_and, Bool.false_eq_true, ite_false]
    simp only [outcomes, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel

theorem fundingSecured : funding.securedBefore lesson [place] (tick 31) := by
  refine ⟨⟨?_, by simp, by simp, ?_, fundingTermsValid, fundingCaseChecked⟩, by decide⟩
  · refine ⟨rfl, rfl, by decide, ?_⟩
    simp [funding, funds, FundingEntry.valid, FundingEntry.available, fundingEntry] <;> decide +kernel
  · intro p member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨by unfold Place.matches; decide, by unfold Place.validFees; decide⟩

private def creditLedger (includeDebit : Bool) : List CreditPosting :=
  match includeDebit with
  | false => [topUpPosting]
  | true => [topUpPosting, debit]

private theorem topUpMatches : topUpPostingMatches topUpReceipt topUpPosting := by
  unfold topUpPostingMatches
  decide +kernel

private theorem creditValid (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (distinct : payments.distinctReceipts) (includeDebit : Bool) (closureSeen : Moment → Prop) :
    ValidCreditHistory (fun _ ↦ 0) (creditLedger includeDebit)
      (initialCredit payments authorities).creditRecords closureSeen := by
  have origins : ∀ p ∈ creditLedger includeDebit,
      p = topUpPosting ∨ p = debit := by
    cases includeDebit <;> simp [creditLedger]
  refine ⟨⟨by simp [initialCredit], by simp [initialCredit], by simp [initialCredit], ?_⟩,
    by cases includeDebit <;> decide +kernel, by cases includeDebit <;> decide +kernel,
    distinct, ?_, ?_, by simp [initialCredit]⟩
  · intro p member
    rcases origins p member with rfl | rfl
    · exact ⟨by cases includeDebit <;> decide +kernel, topUpReceipt,
        List.mem_singleton_self _, topUpMatches, ⟨rfl, rfl⟩, rfl⟩
    · trivial
  · intro p member
    rcases origins p member with rfl | rfl
    · exact ⟨by decide, trivial⟩
    · refine ⟨by decide, ?_⟩
      cases includeDebit
      · exact False.elim ((by decide : debit ∉ [topUpPosting]) member)
      · change debit.amount ≤ balanceBefore (fun _ ↦ 0) [topUpPosting, debit]
          debit.account debit.point
        decide +kernel
  · intro p member bound
    cases includeDebit <;> rcases origins p member with rfl | rfl <;>
      simp [returnedFrom, creditLedger, sumAmountsWhere, topUpPosting, debit,
        topUpReceipt, place, lesson] <;> decide +kernel

theorem validCredit (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (distinct : payments.distinctReceipts) (closureSeen : Moment → Prop) :
    ValidCreditHistory (fun _ ↦ 0) [topUpPosting, debit]
      (initialCredit payments authorities).creditRecords closureSeen :=
  creditValid payments authorities distinct true closureSeen

theorem topUpStep (s : State) (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (book : s.credit = preTopUpCredit payments authorities) (distinct : payments.distinctReceipts) :
    Step s (.credit (.topUp topUpReceipt topUpPosting))
      { s with credit := initialCredit payments authorities } := by
  apply Step.credit
  rw [book]
  exact ⟨topUpMatches, creditValid payments authorities distinct false (fun _ ↦ True), rfl⟩

private theorem signaturesValid : signatures.valid form (some debit.point) := by
  simp [Signatures.valid, signatures, form, lesson, place, debit, TermsProvidedInTime,
    Moment.before, tick]

private theorem tutorAgreementValid : tutorAgreement.agreedBeforeAcceptance form signatures := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, by decide, rfl, rfl, rfl, rfl, by decide, by decide⟩
  intro actor member
  have who : actor = lesson.provider ∨ actor = lesson.tutor := by
    simpa only [tutorAgreement, List.mem_cons, List.not_mem_nil, or_false] using member
  rcases who with rfl | rfl
  · exact ⟨⟨lesson.provider, form.tutorAgreementRef, "Provider signature"⟩,
      List.mem_cons_self, rfl, rfl, by decide⟩
  · exact ⟨⟨lesson.tutor, form.tutorAgreementRef, "Tutor signature"⟩,
      by simp [tutorAgreement], rfl, rfl, by decide⟩

private theorem bookingTermsProvided : booking.providedAgreedTerms form := by
  refine ⟨?_, ?_, ?_⟩
  · intro ref member
    have which : ref = .rules form.rulesVersion ∨ ref = .tutorAgreement form.tutorAgreementRef :=
      by simpa only [form, Option.toList_none, List.map_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] using member
    rcases which with rfl | rfl
    · exact ⟨⟨.rules form.rulesVersion, 1106⟩, List.mem_cons_self, rfl⟩
    · exact ⟨⟨.tutorAgreement form.tutorAgreementRef, 1102⟩, by simp [booking, documents], rfl⟩
  · refine ⟨⟨form, lesson.coordinator, place.customer, tick 28, tick 28, documents⟩,
      List.mem_cons_self, ⟨rfl, rfl, rfl, ?_⟩, rfl, rfl⟩
    exact fun _ h ↦ h
  · refine ⟨⟨form, lesson.coordinator, lesson.tutor, tick 28, tick 28, documents⟩,
      by simp [booking, provisions], ⟨rfl, rfl, rfl, ?_⟩, ?_⟩
    · exact fun _ h ↦ h
    · simp [TermsProvidedInTime, booking, signatures, debit, Moment.before, tick]

theorem canConfirm (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (distinct : payments.distinctReceipts) (began : Option Moment)
    (afterBooking : ∀ time, began = some time → (tick 31).before time) :
    CanConfirmPlace form booking none (fun _ ↦ 0) [topUpPosting, debit]
      (initialCredit payments authorities).creditRecords [] began := by
  refine ⟨formMatches, trivial, rfl, rfl, rfl, rfl, by decide, afterBooking, signaturesValid,
    tutorAgreementValid, by decide, by decide, by decide, ?_,
    List.mem_cons_self, fundingSecured, by decide, by decide,
    validCredit payments authorities distinct _, ?_, ?_, bookingTermsProvided⟩
  · simp [booking, signatures]
  · exact ⟨formMatches, by unfold PaidInFull; decide +kernel, by decide, rfl⟩
  · refine ⟨by simp, ?_⟩
    exact ⟨formMatches.2.2.1, by decide, rfl, rfl, rfl, rfl, by decide +kernel⟩

private theorem localBookingStep (s : State) (decisions : DecisionRecords)
    (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (fresh : s.lessons lesson.id = freshT decisions)
    (credit : s.credit = initialCredit payments authorities) (distinct : payments.distinctReceipts) :
    SourceV14.Workflow.Booking.Step (s.course lesson.id) localBookingEvent (bookedCourse s) := by
  have current : s.course lesson.id =
      (freshT decisions).evidence (initialCredit payments authorities) := by
    simp only [State.course, fresh, credit]
  unfold SourceV14.Workflow.Booking.Step bookedCourse
  rw [current]
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro f retained
      change f ∈ [] ∨ ∃ b : BookingEvidence, (f, b) ∈ [] at retained
      simp at retained
    · change ∀ r ∈ (none : Option Roster), r.lesson = lesson.id
      simp
    · change ∀ row ∈ ([] : List Schedule), row.lesson = lesson.id
      simp
  · refine ⟨?_, Or.inl ⟨rfl, ?_⟩, by decide, Or.inl rfl, ⟨rfl, ?_⟩, ?_, ?_, rfl⟩
    · change ∀ b ∈ ([] : List (PartOne × BookingEvidence)), b.1.place.id ≠ place.id
      simp
    · intro f retained
      change f ∈ [] ∨ ∃ b : BookingEvidence, (f, b) ∈ [] at retained
      simp at retained
    · change ∀ row ∈ [topUpPosting], row.id ≠ debit.id ∧ row.point ≠ debit.point
      simp only [List.mem_singleton, forall_eq]
      decide
    · exact canConfirm payments authorities distinct none (by simp)
    · refine ⟨none, ?_, rfl, rfl⟩
      simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement, LessonFile.evidence,
        freshT]

theorem noMaterialBudgetForFreshLesson (s : State)
    (otherLessons : ∀ row ∈ s.materials.provisions, row.pending.lesson ≠ lesson.id) :
    s.materials.liveMaterialBudgetsAt s.holds.payments lesson.id (tick 31)
      s.materialsPrincipalContext = [] := by
  let estimates := (s.materials.provisions.map (·.pending)).filter (fun row ↦
    row.lesson == lesson.id && decide (row.checkedAt.by (tick 31)))
  have empty : estimates = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro pending present
    obtain ⟨row, retained, rfl⟩ := List.mem_map.mp present
    simp [otherLessons row retained]
  change List.map _ ((estimates.filter _).filter _) = []
  rw [empty]
  rfl

theorem noFundingReceiptsBeforeT (history : PaymentHistory)
    (noEarlier : ∀ row ∈ history.posted, row.instruction.part.lesson = lesson.id →
      ¬ row.instruction.atTime.before (tick 29)) :
    localBookingEvent.readsFundingReceipts history := by
  let posted := history.posted.filter (fun row ↦ row.instruction.part.lesson == lesson.id &&
    row.evidence.isSome && decide (row.instruction.atTime.before (tick 29)))
  have empty : posted = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p retained
    by_cases same : p.instruction.part.lesson = lesson.id
    · simp [same, noEarlier p retained same]
    · simp [same]
  change [].Perm posted ∧
    [].Perm (history.returned.filter fun row ↦ decide (row.returnedAt.before (tick 29)) &&
      posted.any (fun receipt ↦ receipt.id == row.paidReceipt)) ∧
    [].Perm (history.agreedRecipientReceipts.filter fun row ↦ decide (row.paid ∈ posted))
  simp [empty]

/-- The other lesson may already occupy the declared 12 units. Confirmation records the
    debit, form, original schedule, funding inventory, and a 10-unit reservation in the same step. -/
theorem bookingStep (s : State) (decisions : DecisionRecords)
    (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (fresh : s.lessons lesson.id = freshT decisions)
    (credit : s.credit = initialCredit payments authorities) (distinct : payments.distinctReceipts)
    (available : Reserves.occupiedElsewhere s.activeReserves funds 1 ≤ 12)
    (noMaterialsBudget : s.materials.liveMaterialBudgetsAt s.holds.payments lesson.id (tick 31)
      s.materialsPrincipalContext = [])
    (receipts : localBookingEvent.readsFundingReceipts s.holds.payments) :
    Step s bookingEvent (booked s) := by
  refine Step.booking (event := localBookingEvent) (after := bookedCourse s) (discount := none)
    ?_ trivial trivial (localBookingStep s decisions payments authorities fresh credit distinct)
    (Or.inl rfl) trivial ?_ receipts
  · intro entry present
    have same : entry = fundingEntry := List.mem_singleton.mp present
    subst entry
    exact available
  · intro nonempty
    exact (nonempty noMaterialsBudget).elim

theorem recognisedBookingStep (s : State) (decisions : DecisionRecords)
    (payments : PaymentHistory) (authorities : ReviewAuthorities)
    (fresh : s.lessons lesson.id = freshT decisions)
    (credit : s.credit = initialCredit payments authorities) (distinct : payments.distinctReceipts)
    (available : Reserves.occupiedElsewhere s.activeReserves funds 1 ≤ 12)
    (noMaterialsBudget : s.materials.liveMaterialBudgetsAt s.holds.payments lesson.id (tick 31)
      s.materialsPrincipalContext = [])
    (receipts : localBookingEvent.readsFundingReceipts s.holds.payments) :
    RecognisedV15.Workflow.Step (.fromDirect s) bookingEvent (.fromDirect (booked s)) :=
  (RecognisedV15.Workflow.step_iff s (booked s) bookingEvent).mp
    (bookingStep s decisions payments authorities fresh credit distinct available noMaterialsBudget
      receipts)

theorem bookedOtherLesson (s : State) (id : LessonId) (different : id ≠ lesson.id) :
    (booked s).lessons id = s.lessons id := by
  simp [booked, State.withCourse, different]

theorem bookedThisCourse (s : State) : (booked s).course lesson.id = bookedCourse s := by
  simp [booked, State.course, State.withCourse]

theorem bookedWithSharedReservation (s : State)
    (active : s.activeReserves = [⟨10, 42, 1, 12⟩]) :
    (booked s).activeReserves = [⟨10, 42, 1, 12⟩, ⟨10, 100, 1, 10⟩] := by
  change Reserves.reserve s.activeReserves funds = _
  rw [active]
  rfl

#print axioms topUpStep
#print axioms bookingStep
#print axioms recognisedBookingStep

end JointT
