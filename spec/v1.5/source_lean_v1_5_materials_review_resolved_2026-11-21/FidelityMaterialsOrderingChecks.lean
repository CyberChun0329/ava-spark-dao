import SourceV14.Workflow

/-!
Independent, source-shaped late-recording example for the zero-row chronology gate.
The two actual auxiliary uses are stated explicitly. Earlier verification of A is
administratively retained after the later B verification/shortfall. No report or
pre-check is fabricated to conceal actual known use. A single signed prospective
check covers all four complete per-place combinations, each priced below the cap.

This file proves the material processing prefix from a course-ready evidence
record; it does not reconstruct the lesson's earlier booking/credit history.
Form construction borrows the plain Contacts/PayAndReviewTerms shape seen in
FidelityMaterialsProvisionChecks after first_pass.md, with independent values.
-/

namespace A1FactualPrefix
open SourceV14 SourceV14.Workflow.Materials
open SourceV14.Confirmation SourceV14.Course

def tick (n : Nat) : Moment := ⟨n, 0⟩
def lesson : Lesson := ⟨42, .group, 10, 20, 30, 60⟩
def placeA : Place := ⟨1, lesson.id, 40, 50, 60, 70, 100, 100⟩
def placeB : Place := ⟨2, lesson.id, 41, 51, 61, 71, 100, 100⟩
def material : MaterialId := 7
def auxiliary : MaterialId := 8
def pricing : MaterialsPricing := .otherCombination [material, auxiliary]
  (fun _ _ used m ↦ if m = material then (if auxiliary ∈ used then 5 else 4) else 0)

def allocation (m : MaterialId) : MaterialsAllocation m :=
  ⟨"one holder", [1], fun _ _ base ↦ base⟩

def terms : MaterialsTerms where
  lesson := lesson.id
  adoptedBy := lesson.provider
  agreedAt := tick 0
  agreementReference := "terms"
  accountingAndPaymentParty := lesson.provider
  materialsOrBundle := "materials"
  contact := "coordinator"
  licensedUse := fun m ↦ m ∈ [material, auxiliary]
  sharesAndAdjustmentsReference := "shares"
  sharesInForce := fun m _ ↦ some (allocation m)
  contributors := fun _ ↦ [1]
  consents := [⟨material, 1, "terms", tick 0⟩, ⟨auxiliary, 1, "terms", tick 0⟩]
  ordinaryShareTime := fun _ _ firstUse _ ↦ firstUse
  paymentDue := tick 20
  paymentDeadline := tick 20
  pricing := pricing

def authority : MaterialsUseAuthority where
  authorities :=
    { corePartner := fun _ _ ↦ False
      initialFinding := fun _ _ _ ↦ False
      reviewer := fun _ _ _ ↦ False
      approvesPayment := fun _ _ _ ↦ False
      interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
      originalDecisionMaker := fun _ ↦ none
      originalSettlementProposers := fun _ ↦ []
      originalSettlementApprovers := fun _ ↦ [] }
  matterFor := fun _ ↦ ⟨1, lesson.id, [1]⟩
  recusalFor := fun _ ↦ none

def aMain : ConfirmedMaterialUse :=
  ⟨42, 1, material, 1, ⟨2, 1⟩, 30, tick 4, .lessonRecord "A main actual use"⟩
def bMain : ConfirmedMaterialUse :=
  ⟨42, 2, material, 1, ⟨2, 1⟩, 30, tick 4, .lessonRecord "B main actual use"⟩
def aAux : ConfirmedMaterialUse :=
  ⟨42, 1, auxiliary, 2, ⟨2, 3⟩, 30, tick 6, .lessonRecord "A auxiliary actual use"⟩
def bAux : ConfirmedMaterialUse :=
  ⟨42, 2, auxiliary, 2, ⟨2, 5⟩, 30, tick 8, .lessonRecord "B auxiliary actual use"⟩
def actualEvidence (finding : ConfirmedMaterialUse) : Prop :=
  finding ∈ [aMain, bMain, aAux, bAux]

def originalUse : VerifiedMaterialsUse where
  lesson := lesson
  startedAt := tick 2
  endedAt := tick 3
  tutorReport := none
  authority := authority
  places := [placeA, placeB]
  deliveryReports := []
  findings := [aMain, bMain]
  verifiesEvidence := actualEvidence
  verifiedReportOmission := fun _ ↦ False
  uniquePlaces := by decide
  placeInLesson := by simp [Place.matches, placeA, placeB]
  findingInLesson := by simp [aMain, bMain, lesson]
  findingAtPlace := by simp [aMain, bMain, placeA, placeB]

def bUse : VerifiedMaterialsUse :=
  { originalUse with
    findings := [aMain, bMain, bAux]
    findingInLesson := by simp [originalUse, aMain, bMain, bAux, lesson]
    findingAtPlace := by simp [originalUse, aMain, bMain, bAux, placeA, placeB] }

def aUse : VerifiedMaterialsUse :=
  { originalUse with
    places := [placeA]
    findings := [aMain, aAux]
    uniquePlaces := by simp
    placeInLesson := by simp [originalUse, Place.matches, placeA]
    findingInLesson := by simp [originalUse, aMain, aAux, lesson]
    findingAtPlace := by simp [aMain, aAux, placeA] }

def originalCheck : UseCheck := ⟨originalUse, terms, none, tick 4⟩
def bCheck : UseCheck := ⟨bUse, terms, none, tick 8⟩
def aCheck : UseCheck := ⟨aUse, terms, none, tick 6⟩

def combinations : List (List CombinationPart) :=
  [[⟨terms, [⟨placeA, [material]⟩, ⟨placeB, [material]⟩], [], []⟩],
   [⟨terms, [⟨placeA, [material]⟩, ⟨placeB, [material, auxiliary]⟩], [], []⟩],
   [⟨terms, [⟨placeA, [material, auxiliary]⟩, ⟨placeB, [material]⟩], [], []⟩],
   [⟨terms, [⟨placeA, [material, auxiliary]⟩, ⟨placeB, [material, auxiliary]⟩], [], []⟩]]

def plan : CombinationCheck :=
  ⟨lesson, tick 1, tick 1, "signed prospective options", combinations,
    fun reference teaching point options ↦
      reference = "signed prospective options" ∧ teaching = lesson ∧
      point = tick 1 ∧ options = combinations⟩

def original : Settlement :=
  ⟨⟨42, material, "terms", "original", 1, tick 5, [1, 2],
    [⟨1, material, 4⟩, ⟨2, material, 4⟩]⟩, originalCheck⟩
def bShortfall : Shortfall :=
  ⟨original, ⟨42, material, "terms", "original", "B recorded first", 2, tick 9,
    [⟨1, material, 0⟩, ⟨2, material, 1⟩]⟩, bCheck⟩
def aShortfall : Shortfall :=
  ⟨original, ⟨42, material, "terms", "original", "A verified earlier", 3, tick 7,
    [⟨1, material, 1⟩]⟩, aCheck⟩

def hPlan : History := { terms := [terms], combinationChecks := [plan] }
def hOriginalChecked : History := { hPlan with useChecks := [originalCheck] }
def hOriginal : History := { hOriginalChecked with originals := [original] }
def hBChecked : History := { hOriginal with useChecks := [bCheck, originalCheck] }
def hB : History := { hBChecked with shortfalls := [bShortfall] }
def hA : History := { hB with useChecks := [aCheck, bCheck, originalCheck] }
def hBoth : History := { hA with shortfalls := [aShortfall, bShortfall] }

theorem adopted : terms.adoptedFor lesson := by
  simp [MaterialsTerms.adoptedFor, MaterialsTerms.agreedBy, MaterialsPricing.materials,
    terms, pricing, lesson, material, auxiliary, tick, Moment.by, Moment.before]

theorem all_findings_authentic :
    originalUse.verifiedBy (tick 4) ∧ bUse.verifiedBy (tick 8) ∧ aUse.verifiedBy (tick 6) := by
  simp [VerifiedMaterialsUse.verifiedBy, MaterialsUseAuthority.mayCheck,
    ReviewAuthorities.disinterested, DirectInterest.affected, authority,
    originalUse, bUse, aUse, actualEvidence, aMain, bMain, aAux, bAux,
    lesson, placeA, placeB, tick, Moment.before, Moment.by,
    MaterialUseEvidence.reference]
  all_goals decide +kernel

theorem original_computed : original.conforms := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem b_computed : bShortfall.conforms [] := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, rfl, by decide, by decide, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem a_computed_without_future : aShortfall.conforms [bShortfall.record] := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, rfl, by decide, by decide, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem b_stays_computed_after_a :
    bShortfall.conforms [aShortfall.record, bShortfall.record] := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, rfl, by decide, by decide, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem all_pricing_available_at_each_actual_step :
    hOriginalChecked.pricingAvailable originalCheck (tick 5) ∧
    hBChecked.pricingAvailable bCheck (tick 9) ∧
    hA.pricingAvailable aCheck (tick 7) := by
  simp [History.pricingAvailable, History.checkedNonstandardPricing, History.usesKnownAt,
    UseCheck.matchesPricing, UseCheck.coveredThrough, CombinationPart.coversUse,
    hOriginalChecked, hBChecked, hOriginal, hA, hB, hPlan,
    plan, combinations, original, bShortfall, originalCheck, bCheck, aCheck,
    originalUse, bUse, aUse, aMain, bMain, aAux, bAux, terms, pricing,
    VerifiedMaterialsUse.combination, VerifiedMaterialsUse.materialsAt,
    MaterialsTerms.covers, MaterialsPricing.covers, MaterialsPricing.materials,
    lesson, placeA, placeB, material, auxiliary, tick, Moment.before, Moment.by,
    List.eraseDups_cons, -List.mem_eraseDups]

theorem original_step (ev : StartEvidence) (holds : HoldHistory) :
    Step ev holds hOriginalChecked (.settle original) hOriginal := by
  refine .settle (List.Mem.head []) original_computed
    all_pricing_available_at_each_actual_step.1 ?_ ?_
  · unfold History.combinedCapAllows
    decide +kernel
  · simp [hOriginalChecked, hPlan]

theorem b_step (ev : StartEvidence) (holds : HoldHistory) :
    Step ev holds hBChecked (.identifyShortfall bShortfall) hB := by
  refine .identifyShortfall (List.Mem.head []) (List.Mem.head _) b_computed ?_ ?_
    all_pricing_available_at_each_actual_step.2.1 ?_ ?_
  · exact ⟨⟨2, material, 1⟩, by decide, by decide⟩
  · simp [hBChecked, hOriginal, hOriginalChecked, hPlan]
  · unfold History.combinedCapAllows
    decide +kernel
  · simp [hBChecked, hOriginal, hOriginalChecked, hPlan]

theorem a_all_other_shortfall_premises :
    aShortfall.original ∈ hA.originals ∧ aShortfall.check ∈ hA.useChecks ∧
    aShortfall.conforms (hA.shortfalls.map Shortfall.record) ∧
    (∃ charge ∈ aShortfall.additionalCharges, 0 < charge.amount) ∧
    hA.pricingAvailable aShortfall.check aShortfall.record.identifiedAt ∧
    hA.combinedCapAllows aShortfall.record.lesson aShortfall.additionalCharges
      aShortfall.record.identifiedAt ∧
    (∀ prior ∈ hA.shortfalls, prior.record.lesson = aShortfall.record.lesson →
      prior.record.material = aShortfall.record.material →
      prior.record.reference ≠ aShortfall.record.reference) := by
  refine ⟨List.Mem.head [], List.Mem.head _, a_computed_without_future,
    ⟨⟨1, material, 1⟩, by decide, by decide⟩,
    all_pricing_available_at_each_actual_step.2.2, ?_, ?_⟩
  · unfold History.combinedCapAllows
    decide +kernel
  · intro prior saved _ _
    obtain rfl := List.mem_singleton.mp saved
    decide

theorem a_root_accepted_after_zero_row_fix (s : Workflow.State)
    (retained : s.materials = hA)
    (uncorrected : s.materialsPrincipalContext = {}) :
    Workflow.Step s (.materials 42 (.identifyShortfall aShortfall))
      { s.withHolds s.holds with materials := { hA with
          shortfalls := aShortfall :: hA.shortfalls } } := by
  obtain ⟨original, verified, computed, positive, pricing, cap, fresh⟩ :=
    a_all_other_shortfall_premises
  refine .materials ?_ trivial ?_ rfl
  · intro id present
    cases present
    rfl
  · rw [retained, uncorrected]
    refine .identifyShortfall original verified computed positive ?_ pricing cap fresh
    intro prior present _ overlap
    obtain rfl := List.mem_singleton.mp present
    obtain ⟨charge, chargeIn, _, earlier, earlierIn, samePlace, earlierPositive⟩ := overlap
    have hA : aShortfall.record.charges = [⟨1, material, 1⟩] := rfl
    have hB : bShortfall.record.charges = [⟨1, material, 0⟩, ⟨2, material, 1⟩] := rfl
    rw [hA] at chargeIn
    obtain rfl := List.mem_singleton.mp chargeIn
    rw [hB] at earlierIn
    rcases List.mem_cons.mp earlierIn with same | rest
    · subst earlier
      exact (by decide : ¬ (0 : Amount) < 0) earlierPositive |>.elim
    · obtain rfl := List.mem_singleton.mp rest
      exact (by decide : (2 : PlaceId) ≠ 1) samePlace |>.elim

#print axioms adopted
#print axioms all_findings_authentic
#print axioms original_computed
#print axioms b_computed
#print axioms a_computed_without_future
#print axioms b_stays_computed_after_a
#print axioms all_pricing_available_at_each_actual_step
#print axioms original_step
#print axioms b_step
#print axioms a_all_other_shortfall_premises
#print axioms a_root_accepted_after_zero_row_fix

end A1FactualPrefix

namespace A1FactualPrefix
open SourceV14 SourceV14.Workflow.Materials
open SourceV14.Confirmation SourceV14.Course

def schedule : Booking.Schedule := ⟨42, tick 2, tick 3, "UTC", tick 0, tick 0⟩
def paymentTerms : PaymentTerms := ⟨.fixed (tick 20), .fixed (tick 20)⟩
def form (place : Place) : PartOne where
  lesson := lesson
  place := place
  contacts := ⟨"provider", "contact", "student notices", none, "coordinator", 50, "lead",
    none, none, 60, "reviewer", 70, "alternative", true, 80, "escalation"⟩
  rulesVersion := "1.5"
  confirmedAt := tick 0
  customerRepresentatives := []
  schedule := schedule
  serviceTerms := "service"
  serviceItems := [1, 2]
  discountBasis := none
  privateRoster := some 10
  rosterLock := some (tick 0)
  groupRescheduleCutoff := some (.fixed (tick 0))
  oneToOneAdvanceCutoff := none
  cancelChangeTerms := "changes"
  noFaultTerms := "no fault"
  applicableStartTerms := "start"
  tutorAgreementRef := "tutor terms"
  absentGroupPlacePay := some 30
  materialsOrBundle := some "materials"
  materialsTermsRef := some "terms"
  materialsPayer := some lesson.provider
  deadlines := ⟨.fixed (tick 20), tick 20, none, paymentTerms, paymentTerms, paymentTerms,
    paymentTerms, .fixed (tick 30), tick 30, tick 30, tick 30, .fixed (tick 30)⟩

def roster : Settlement.Roster := ⟨42, 10, [placeA, placeB], tick 0⟩
def course (base : StartEvidence) : StartEvidence :=
  { base with
    effectiveForms := [form placeA, form placeB]
    groupRoster := some roster
    bookings := []
    teachingBegan := some (tick 2)
    teachingEnded := some (tick 3)
    rosterReview := none
    tutorReplacements := [] }

theorem forms_match : (form placeA).matches ∧ (form placeB).matches := by
  simp [PartOne.matches, form, lesson, placeA, placeB, schedule, paymentTerms, Place.matches,
    Place.validFees, Booking.Schedule.valid, Contacts.complete, PayAndReviewTerms.valid,
    PaymentTerms.valid, PaymentDeadline.valid, AdvanceWindow.validAt,
    Moment.by, Moment.before, tick]
  all_goals decide +kernel

theorem roster_forms (base : StartEvidence) (query : Moment) :
    (course base).rosterFormsAt lesson query (some roster) [form placeA, form placeB] := by
  have formsMatchLocal : ∀ f ∈ [form placeA, form placeB], f.lesson = lesson ∧ f.matches := by
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨rfl, forms_match.1⟩
    · obtain rfl := List.mem_singleton.mp member
      exact ⟨rfl, forms_match.2⟩
  have usesRoster : ∀ f ∈ [form placeA, form placeB], FormUsesRoster f roster := by
    intro f member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨List.Mem.head _, rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp member
      exact ⟨List.Mem.tail _ (List.Mem.head []), rfl, rfl⟩
  have formsFor : ∀ f ∈ [form placeA, form placeB],
      (course base).formForRoster lesson roster f := by
    intro f member
    exact ⟨(formsMatchLocal f member).1, (formsMatchLocal f member).2, usesRoster f member,
      Or.inl member, fun _ _ _ ↦ member⟩
  have placesHaveForms : ∀ p ∈ roster.places,
      ∃ f ∈ [form placeA, form placeB], f.place = p := by
    intro p member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨form placeA, List.Mem.head _, rfl⟩
    · obtain rfl := List.mem_singleton.mp member
      exact ⟨form placeB, List.Mem.tail _ (List.Mem.head []), rfl⟩
  have registered : RegisterMatchesForms roster (course base) lesson := by
    refine ⟨rfl, rfl, ⟨by simp [course], formsMatchLocal⟩, rfl, ?_,
      (by change ([1, 2] : List Nat).Nodup; decide), usesRoster⟩
    intro p member
    obtain ⟨f, contained, same⟩ := placesHaveForms p member
    exact ⟨f, contained, same.symm⟩
  have valid : roster.valid lesson roster.lockedAt := by
    simp [Settlement.Roster.valid, roster, Place.matches, placeA, placeB, lesson,
      tick, Moment.by, Moment.before]
  refine ⟨⟨⟨roster, registered, valid, rfl⟩, ?_⟩, by decide, formsFor, placesHaveForms⟩
  intro p member
  obtain ⟨f, contained, same⟩ := placesHaveForms p member
  exact ⟨f, formsFor f contained, same⟩

theorem arrangement_forms (base : StartEvidence) :
    (course base).arrangementFormsAt lesson (tick 1) (some roster)
      [form placeA, form placeB] := by
  refine ⟨⟨roster, rfl, by decide⟩, roster_forms base (tick 1)⟩

theorem uses_match_course (base : StartEvidence) :
    originalCheck.matchesCourse (course base) ∧
    bCheck.matchesCourse (course base) ∧ aCheck.matchesCourse (course base) := by
  have tutor : EffectiveTutorAt lesson (course base) (tick 2) lesson.tutor := by
    refine ⟨none, ?_, rfl⟩
    simp [StartEvidence.effectiveReplacement, StartEvidence.latestReplacement, course]
  constructor
  · refine ⟨lesson, some roster, [form placeA, form placeB], roster_forms base _,
      rfl, tutor, rfl, rfl, ?_, ?_⟩
    · simp [originalCheck, originalUse]
    · intro place included _
      simp only [originalCheck, originalUse, List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl
      · exact ⟨form placeA, by simp, rfl, rfl, rfl, rfl⟩
      · exact ⟨form placeB, by simp, rfl, rfl, rfl, rfl⟩
  constructor
  · refine ⟨lesson, some roster, [form placeA, form placeB], roster_forms base _,
      rfl, tutor, rfl, rfl, ?_, ?_⟩
    · simp [bCheck, bUse, originalUse]
    · intro place included _
      simp only [bCheck, bUse, originalUse, List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl
      · exact ⟨form placeA, by simp, rfl, rfl, rfl, rfl⟩
      · exact ⟨form placeB, by simp, rfl, rfl, rfl, rfl⟩
  · refine ⟨lesson, some roster, [form placeA, form placeB], roster_forms base _,
      rfl, tutor, rfl, rfl, ?_, ?_⟩
    · simp [aCheck, aUse, originalUse]
    · intro place included _
      obtain rfl := List.mem_singleton.mp included
      exact ⟨form placeA, by simp, rfl, rfl, rfl, rfl⟩

theorem plan_conforms (base : StartEvidence) : plan.conforms (course base) [terms] := by
  refine ⟨by decide, by decide, by simp [plan, combinations], ⟨rfl, rfl, rfl, rfl⟩,
    ⟨some roster, [form placeA, form placeB], arrangement_forms base, ?_⟩, ?_⟩
  · simp [plan, combinations, form, terms, tick, Moment.before, Moment.by]
  · simp [plan, combinations, CombinationPart.agreedAdjustments, MaterialsTerms.covers,
      MaterialsPricing.covers, MaterialsPricing.materials, MaterialsPricing.charges,
      MaterialsPricing.chargesAt, pricing, terms, materialsCapRate, materialsCapBase,
      material, auxiliary, placeA, placeB, lesson, tick, Moment.before, Moment.by, sumAmounts]
    simp only [forall_and, forall_eq']
    decide +kernel

theorem all_material_prefix_steps (base : StartEvidence) (holds : HoldHistory) :
    Step (course base) holds {} (.adopt lesson terms) { terms := [terms] } ∧
    Step (course base) holds { terms := [terms] } (.checkCombination plan) hPlan ∧
    Step (course base) holds hPlan (.verify originalCheck) hOriginalChecked ∧
    Step (course base) holds hOriginalChecked (.settle original) hOriginal ∧
    Step (course base) holds hOriginal (.verify bCheck) hBChecked ∧
    Step (course base) holds hBChecked (.identifyShortfall bShortfall) hB ∧
    Step (course base) holds hB (.verify aCheck) hA := by
  refine ⟨.adopt adopted (by simp), .checkCombination (plan_conforms base) (by simp),
    .verify (List.Mem.head []) (by simp [originalCheck, originalUse])
      (uses_match_course base).1 ⟨adopted, all_findings_authentic.1⟩,
    original_step _ _,
    .verify (List.Mem.head []) (by simp [bCheck, bUse, originalUse])
      (uses_match_course base).2.1 ⟨adopted, all_findings_authentic.2.1⟩,
    b_step _ _,
    .verify (List.Mem.head []) (by simp [aCheck, aUse, originalUse])
      (uses_match_course base).2.2 ⟨adopted, all_findings_authentic.2.2⟩⟩

/- Each of these seven local transitions is the actual relation called by the
root Materials constructor; none is a pure helper bypass. The following root
theorem makes the precise starting-record assumptions explicit. -/
theorem original_root_step (s : Workflow.State) (known : s.materials = hOriginalChecked)
    (uncorrected : s.materialsPrincipalContext = {}) :
    Workflow.Step s (.materials 42 (.settle original))
      { s.withHolds s.holds with materials := hOriginal } := by
  refine .materials ?_ trivial ?_ rfl
  · intro id present
    cases present
    rfl
  · rw [known, uncorrected]
    exact original_step _ _

theorem b_root_step (s : Workflow.State) (known : s.materials = hBChecked)
    (uncorrected : s.materialsPrincipalContext = {}) :
    Workflow.Step s (.materials 42 (.identifyShortfall bShortfall))
      { s.withHolds s.holds with materials := hB } := by
  refine .materials ?_ trivial ?_ rfl
  · intro id present
    cases present
    rfl
  · rw [known, uncorrected]
    exact b_step _ _

def rooted (s : Workflow.State) (history : History) : Workflow.State :=
  { s.withHolds s.holds with materials := history }

def prepared (s : Workflow.State) : Workflow.State :=
  (s.withHolds s.holds).withCourse 42 (course ((s.withHolds s.holds).course 42))

theorem prepared_has_required_course (s : Workflow.State) :
    ((prepared s).withHolds (prepared s).holds).course 42 =
      course ((s.withHolds s.holds).course 42) := by
  rfl

theorem lift_local (s : Workflow.State) {before after : History} {event : Event}
    (sameLesson : ∀ id ∈ event.recordLesson, id = 42)
    (funds : event.fundingContext s.activeReserves)
    (payment : event.recordsPayment s.holds s.holds)
    (reserves : event.reservations s.activeReserves = s.activeReserves)
    (uncorrected : s.materialsPrincipalContext = {})
    (localStep : Step ((s.withHolds s.holds).course 42) s.holds before event after) :
    Workflow.Step (rooted s before) (.materials 42 event) (rooted s after) := by
  have context : (rooted s before).materialsPrincipalContext = {} := uncorrected
  have localRule : Step ((rooted s before).course 42) s.holds before event after
      (rooted s before).materialsPrincipalContext := by
    rw [context]
    exact localStep
  have accepted := Workflow.Step.materials (s := rooted s before) (holds := s.holds)
    sameLesson funds localRule payment
  simpa only [rooted, Workflow.State.withHolds, reserves] using accepted

/- Full seven-step material trace at the active root from a course-ready root.
The course starts without an adopted material correction. The surrounding
root state is untouched except shared-ledger
synchronisation and these material fields. No unverified material-history seed
is assumed. Earlier booking/credit event reachability is outside this witness. -/
theorem complete_material_root_prefix (s : Workflow.State) (base : StartEvidence)
    (ready : (s.withHolds s.holds).course 42 = course base)
    (uncorrected : s.materialsPrincipalContext = {}) :
    Workflow.Step (rooted s {}) (.materials 42 (.adopt lesson terms))
      (rooted s { terms := [terms] }) ∧
    Workflow.Step (rooted s { terms := [terms] }) (.materials 42 (.checkCombination plan))
      (rooted s hPlan) ∧
    Workflow.Step (rooted s hPlan) (.materials 42 (.verify originalCheck))
      (rooted s hOriginalChecked) ∧
    Workflow.Step (rooted s hOriginalChecked) (.materials 42 (.settle original))
      (rooted s hOriginal) ∧
    Workflow.Step (rooted s hOriginal) (.materials 42 (.verify bCheck))
      (rooted s hBChecked) ∧
    Workflow.Step (rooted s hBChecked) (.materials 42 (.identifyShortfall bShortfall))
      (rooted s hB) ∧
    Workflow.Step (rooted s hB) (.materials 42 (.verify aCheck)) (rooted s hA) := by
  rcases all_material_prefix_steps base s.holds with ⟨p1, p2, p3, p4, p5, p6, p7⟩
  rw [← ready] at p1 p2 p3 p4 p5 p6 p7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lift_local s (by intro id seen; cases seen; rfl) trivial rfl rfl uncorrected p1
  · exact lift_local s (by intro id seen; cases seen; rfl) trivial rfl rfl uncorrected p2
  · exact lift_local s (by intro id seen; cases seen; rfl) trivial rfl rfl uncorrected p3
  · exact lift_local s (by intro id seen; cases seen; rfl) trivial rfl rfl uncorrected p4
  · exact lift_local s (by intro id seen; cases seen; rfl) trivial rfl rfl uncorrected p5
  · exact lift_local s (by intro id seen; cases seen; rfl) trivial rfl rfl uncorrected p6
  · exact lift_local s (by intro id seen; cases seen; rfl) trivial rfl rfl uncorrected p7

#print axioms forms_match
#print axioms roster_forms
#print axioms arrangement_forms
#print axioms uses_match_course
#print axioms plan_conforms
#print axioms all_material_prefix_steps
#print axioms original_root_step
#print axioms b_root_step
#print axioms prepared_has_required_course
#print axioms complete_material_root_prefix

end A1FactualPrefix
