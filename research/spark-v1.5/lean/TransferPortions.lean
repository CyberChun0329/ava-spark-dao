import TransferReviewPath

/-! A scoped bridge to the native share reader. This asks how it divides a contingent
amount if a later, separately supported disposition gives 0 or 50. Neither hypothetical
record is installed or asserted as an operative shortfall or payment. -/

namespace TransferCase

open SourceV14 SourceV14.Workflow

def faceValue (awarded : Bool) : Amount := if awarded then 50 else 0
def contingentCharge (awarded : Bool) : MaterialsCharge := ⟨seat, mat, faceValue awarded⟩

def queriedOriginal (q : Task) (awarded : Bool) : Materials.Settlement :=
  ⟨⟨lessonId q, mat, (agreement q).agreementReference, ref q,
    if q = .oldReview then 501 else 601, if q = .oldReview then tick 20 else tick 52,
    [seat], [if q = .oldReview then contingentCharge true else contingentCharge awarded]⟩,
   useCheck q⟩

def assumedSupplement (q : Task) (awarded : Bool) : MaterialsShortfall :=
  ⟨lessonId q, mat, (agreement q).agreementReference, ref q,
    "hypothetical C0 shortfall", 502, tick 52, [contingentCharge awarded]⟩

def queryRow (q : Task) (awarded : Bool) (candidate : ActorId) (asked : Amount) :
    Materials.Entitlement :=
  let original := queriedOriginal q awarded
  let supplement : Materials.Shortfall :=
    ⟨original, assumedSupplement q awarded, useCheck q⟩
  { original
    shortfall := if q = .oldReview then some supplement else none
    holder := candidate
    amount := asked
    verifiedAt := tick 55
    sparkDao := 10
    shareHistory :=
      { originalReference := 9007
        agreedSharesAt := (agreement q).sharesInForce mat
        verifiedOriginal := fun signed doc schedule ↦ signed = agreement q ∧ doc = 9007 ∧
          schedule = (agreement q).sharesInForce mat } }

def reader (p : Policy) (q : Task) (b : Bool) : MaterialsShareEvidence mat :=
  (transferred p).materials.shareEvidence (queryRow q b 0 0) (tick 60)

theorem amountAskedDoesNotSetTheReader (p : Policy) (q : Task) (b : Bool) (actor : ActorId)
    (asked : Amount) :
    (transferred p).materials.shareEvidence (queryRow q b actor asked) (tick 60) = reader p q b :=
  rfl

private abbrev signed (q : Task) : MaterialsTransferRecord mat := (signedRow q).record

private theorem visible (p : Policy) (q : Task) (b : Bool) :
    (reader p q b).transfers =
      (if p = .assign then [signed .oldReview] else []) ++ [signed .teaching] := by
  cases p <;> rfl

private theorem shareAt (p : Policy) (q : Task) (b : Bool) (point asOf : Moment)
    (prior : point.by (tick 55)) :
    (reader p q b).allocationAt (agreement q) seat point asOf (sole mat .O) :=
  ⟨prior, ⟨rfl, rfl, rfl⟩, _, rfl, ⟨(lessonId q, seat), 9007, sole mat .O, tick 0⟩,
    by simp only [reader, Materials.History.shareEvidence, queryRow, queriedOriginal,
      agreement, List.filter_nil, List.mergeSort_nil, privateArrangementAt],
    by change (tick 0).by (tick 55); decide, rfl⟩

private theorem onlyInitial {p : Policy} {q : Task} {b : Bool} {point asOf : Moment}
    {a : MaterialsAllocation mat} (h : (reader p q b).allocationAt (agreement q) seat point asOf a) :
    a = sole mat .O := by
  obtain ⟨_, _, initial, hi, arrangement, operative, _, final⟩ := h
  change some (sole mat .O) = some initial at hi
  obtain rfl := Option.some.inj hi
  simp only [reader, Materials.History.shareEvidence, queryRow, queriedOriginal, agreement,
    List.filter_nil, List.mergeSort_nil, privateArrangementAt] at operative
  subst arrangement
  exact final

private theorem distributes (e : Expert) (b : Bool) :
    (sole mat e).distributesCharge seat (faceValue b) := by
  cases e <;> cases b <;>
    simp [MaterialsAllocation.distributesCharge, sole, faceValue, sumAmounts] <;> decide +kernel

private theorem applicable (p : Policy) (q : Task) (b : Bool) :
    (reader p q b).transferApplies (useCheck q).use seat (tick 60) (signedRow q).record := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_, finding q, List.mem_cons_self, rfl, rfl, ?_⟩
  all_goals cases q <;> decide

private theorem appliesOnlyToItsCase {p : Policy} {q q' : Task} {b : Bool}
    (h : (reader p q b).transferApplies (useCheck q).use seat (tick 60) (signedRow q').record) :
    q = q' := by
  have ids := h.1.1
  cases q <;> cases q' <;> first | rfl | cases ids

private theorem singleApplicable {p : Policy} {q : Task} {b : Bool} {row : MaterialsTransferRecord mat}
    (seen : row ∈ (reader p q b).transfers)
    (applies : (reader p q b).transferApplies (useCheck q).use seat (tick 60) row) :
    row = (signedRow q).record ∧ (q = .teaching ∨ p = .assign) := by
  rw [visible] at seen
  cases p with
  | retain =>
    change row ∈ [signed .teaching] at seen
    obtain rfl := List.mem_singleton.mp seen
    obtain rfl := appliesOnlyToItsCase applies
    exact ⟨rfl, Or.inl rfl⟩
  | assign =>
    change row ∈ [(signedRow .oldReview).record, (signedRow .teaching).record] at seen
    rcases List.mem_cons.mp seen with rfl | last
    · obtain rfl := appliesOnlyToItsCase applies
      exact ⟨rfl, Or.inr rfl⟩
    · obtain rfl := List.mem_singleton.mp last
      obtain rfl := appliesOnlyToItsCase applies
      exact ⟨rfl, Or.inr rfl⟩

private theorem signedIfCovered {p : Policy} {q : Task} (b : Bool)
    (covered : q = .teaching ∨ p = .assign) :
    (signedRow q).record ∈ (reader p q b).transfers := by
  change signed q ∈ (reader p q b).transfers
  rw [visible]
  rcases covered with rfl | rfl
  · cases p with
    | retain => exact List.mem_cons_self
    | assign => exact List.mem_cons_of_mem _ List.mem_cons_self
  · cases q with
    | teaching => exact List.mem_cons_of_mem _ List.mem_cons_self
    | oldReview => exact List.mem_cons_self

private def net (b : Bool) (actor : ActorId) := (sole mat .N).portion actor seat (faceValue b)

private theorem transferGross (p : Policy) (q : Task) (b : Bool) :
    (reader p q b).transferPortionsAt (agreement q) (useCheck q).use (contingentCharge b)
      (firstUse q) (faceValue b) (signedRow q).record (net b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ⟨rfl, rfl, by decide, by decide⟩, ⟨trivial, List.mem_cons_self⟩,
      ?_, rfl, sole mat .O, shareAt _ _ _ _ _ (by change (tick 1).by (tick 55); decide), List.mem_cons_self⟩
    all_goals cases q <;> decide
  · change (signedRow q).record.transfer.effectiveAt.by (tick 55)
    cases q <;> decide
  · cases q <;> intro r hr <;> change r ∈ [] at hr <;> cases hr
  · cases q <;> cases b <;> change (0 : Amount) ≤ _ <;> decide +kernel
  · cases q with
    | teaching =>
      refine ⟨sole mat .N, rfl, by decide, distributes .N b, ?_⟩
      intro a
      change net b a = 0 + (sole mat .N).portion a seat (faceValue b)
      simp [net, Rat.zero_add]
    | oldReview =>
      change (sole mat .N).agreementReference ≠ "" ∧ (sole mat .N).distributesCharge seat (faceValue b - 0) ∧
        ∀ a, net b a = 0 + (sole mat .N).portion a seat (faceValue b - 0)
      have subtractZero : faceValue b - 0 = faceValue b := by cases b <;> decide +kernel
      simpa [net, subtractZero, Rat.zero_add] using
        (show (sole mat .N).agreementReference ≠ "" ∧
          (sole mat .N).distributesCharge seat (faceValue b) from ⟨by decide, distributes _ _⟩)

private theorem uniqueGross {p : Policy} {q : Task} {b : Bool} {gross : ActorId → Amount}
    (h : (reader p q b).transferPortionsAt (agreement q) (useCheck q).use (contingentCharge b)
      (firstUse q) (faceValue b) (signedRow q).record gross) (actor : ActorId) :
    gross actor = net b actor := by
  have split := h.2.2.2.2
  cases q with
  | teaching =>
    obtain ⟨a, ha, _, _, parts⟩ := split
    change a = sole mat .N at ha
    subst a
    have part := parts actor
    change gross actor = 0 + (sole mat .N).portion actor seat (faceValue b) at part
    simpa [net, Rat.zero_add] using part
  | oldReview =>
    have part := split.2.2 actor
    change gross actor = 0 + (sole mat .N).portion actor seat (faceValue b - 0) at part
    have subtractZero : faceValue b - 0 = faceValue b := by cases b <;> decide +kernel
    simpa [net, Rat.zero_add, subtractZero] using part

private theorem reallocatesToN (q : Task) (b : Bool) :
    (signedRow q).record.transfer.reallocates
      (fun a ↦ (sole mat .O).portion a seat (faceValue b)) (net b) := by
  refine ⟨by change who .O ≠ who .N; decide, ?_, ?_, ?_⟩
  · intro actor outside
    have old : actor ≠ who .O := fun h ↦ outside (Or.inl h)
    have new : actor ≠ who .N := fun h ↦ outside (Or.inr h)
    simp [net, MaterialsAllocation.portion, sole, old, new]
  all_goals cases q <;> cases b <;> decide +kernel

private theorem singleBasis (p : Policy) (q : Task) (b : Bool) :
    (reader p q b).transferBasisAt (agreement q) (contingentCharge b) (firstUse q)
      (signedRow q).record (sole mat .O) := by
  cases q <;> apply shareAt
  · change (tick 32).by (tick 55); decide
  · change (tick 10).by (tick 55); decide

private theorem fallbackBasis (p : Policy) (q : Task) (b : Bool) :
    (reader p q b).allocationAt (agreement q) seat (firstUse q) (tick 60) (sole mat .O) := by
  apply shareAt
  cases q <;> decide

/-- The native reader gives exactly one amount per actor in each of the two hypothetical
economic outcomes. The history supplies its actual retained, dated transfer records. -/
theorem nativePortionIff (p : Policy) (q : Task) (b : Bool) (actor : ActorId) (amount : Amount) :
    (reader p q b).portionAt (agreement q) (useCheck q).use (contingentCharge b)
      (firstUse q) (tick 60) actor amount ↔ amount = delta p q actor b := by
  let e := reader p q b
  let charge := contingentCharge b
  let use := (useCheck q).use
  let source := e.allocationAt (agreement q) seat (firstUse q) (tick 60)
  let applies := e.transferApplies use seat (tick 60)
  let base := faceValue b
  let allowed := ∀ record ∈ e.transfers, ¬applies record
  let shape := ((if q = .oldReview then 0 ≤ base else True) ∧
    ((allowed ∧ ∃ a, source a ∧ a.agreementReference ≠ "" ∧
      a.distributesCharge seat base ∧ amount = a.portion actor seat base) ∨
    (∃ r ∈ e.transfers, applies r ∧ (∀ t ∈ e.transfers, applies t → t = r) ∧
      ∃ a, e.transferBasisAt (agreement q) charge (firstUse q) r a ∧
      a.agreementReference ≠ "" ∧ a.distributesCharge seat base ∧
      ∃ g, e.transferPortionsAt (agreement q) use charge (firstUse q) base r g ∧
      r.transfer.reallocates (fun i ↦ a.portion i seat base) g ∧ amount = g actor) ∨
    ∃ a, source a ∧ a.agreementReference ≠ "" ∧ a.distributesCharge seat base ∧
      e.composedPortionAt (agreement q) use charge (firstUse q) (tick 60) base
        (fun i ↦ a.portion i seat base) actor amount))
  have hshape : e.portionAt (agreement q) use charge (firstUse q) (tick 60) actor amount ↔ shape := by
    dsimp only [shape, allowed, applies, source, base, charge, use, e]
    cases q with
    | teaching => rfl
    | oldReview =>
      have supplement : (reader p .oldReview b).shortfall = some (assumedSupplement .oldReview b) := rfl
      have total : sumAmountsWhere (assumedSupplement .oldReview b).charges (·.place == seat)
          (·.amount) = faceValue b := by cases b <;> decide +kernel
      have place : (contingentCharge b).place = seat := rfl
      simp only [MaterialsShareEvidence.portionAt, supplement, place, total, ite_true]
      rfl
  refine hshape.trans ?_
  change shape ↔ _
  have sign : (if q = .oldReview then 0 ≤ faceValue b else True) := by
    cases q <;> cases b <;> decide +kernel
  have targetYes (covered : q = .teaching ∨ p = .assign) : delta p q actor b = net b actor := by
    rcases covered with rfl | rfl
    · rfl
    · cases q <;> rfl
  have targetNo (uncovered : ¬(q = .teaching ∨ p = .assign)) :
      delta p q actor b = (sole mat .O).portion actor seat (faceValue b) := by
    cases q <;> cases p <;> simp_all [delta, allocation, faceValue]
  constructor
  · rintro ⟨_, original | unique | many⟩
    · obtain ⟨noneApply, a, ha, _, _, value⟩ := original
      obtain rfl := onlyInitial ha
      have uncovered : ¬(q = .teaching ∨ p = .assign) := fun covered ↦
        noneApply _ (signedIfCovered b covered) (applicable p q b)
      exact value.trans (targetNo uncovered).symm
    · obtain ⟨row, seen, applies, _, _, _, _, _, gross, h, _, amountEq⟩ := unique
      obtain ⟨rfl, covered⟩ := singleApplicable seen applies
      exact (amountEq.trans (uniqueGross h actor)).trans (targetYes covered).symm
    · obtain ⟨_, _, _, _, first, firstSeen, firstApplies, second, secondSeen, secondApplies,
        different, _⟩ := many
      exact False.elim (different ((singleApplicable secondSeen secondApplies).1.trans
        (singleApplicable firstSeen firstApplies).1.symm))
  · intro amountEq
    refine ⟨sign, ?_⟩
    by_cases covered : q = .teaching ∨ p = .assign
    · refine Or.inr (Or.inl ⟨(signedRow q).record, signedIfCovered b covered, applicable p q b,
        fun row seen applies ↦ (singleApplicable seen applies).1, sole mat .O, singleBasis _ _ _,
        by decide, distributes _ _, net b, transferGross _ _ _, reallocatesToN _ _,
        amountEq.trans (targetYes covered)⟩)
    · exact Or.inl ⟨fun _ seen applies ↦ covered (singleApplicable seen applies).2,
        sole mat .O, fallbackBasis _ _ _, by decide, distributes _ _, amountEq.trans (targetNo covered)⟩

/-- Changing between the two case amounts affects the candidate precisely when the supplied
decision-specific authority marks them interested. Both share computations read the same root
transfer history. This equality is a case witness for the independently supplied interest input. -/
theorem nativeExposure (p : Policy) (q : Task) (e : Expert) :
    (authority p).disinterested (matter q) (who e) (tick 50) ↔
      ∃ amount, (reader p q false).portionAt (agreement q) (useCheck q).use (contingentCharge false)
          (firstUse q) (tick 60) (who e) amount ∧
        (reader p q true).portionAt (agreement q) (useCheck q).use (contingentCharge true)
          (firstUse q) (tick 60) (who e) amount := by
  rw [interestFromAmounts]
  simp only [nativePortionIff]
  exact ⟨fun h ↦ ⟨_, rfl, h.symm⟩, fun ⟨_, h, k⟩ ↦ k.symm.trans h⟩

/-- Re-running the original C0 check with the original gross and no independently
adopted change yields zero incremental principal. The root path has filed neither a
C0 shortfall nor a C1 material settlement. -/
theorem unchangedCheckAddsZero (p : Policy) :
    (assumedSupplement .oldReview true).newCharges originalMaterial.record []
        ((useCheck .oldReview).use.chargesFor (agreement .oldReview) mat) {}
        (useCheck .oldReview).use.findings = [contingentCharge false] ∧
    (terminal p p).materials.shortfalls = [] ∧
    (terminal p p).materials.originals = [originalMaterial] := by
  exact ⟨by decide +kernel, by cases p <;> rfl, by cases p <;> rfl⟩

#print axioms unchangedCheckAddsZero
#print axioms amountAskedDoesNotSetTheReader
#print axioms nativePortionIff
#print axioms nativeExposure

end TransferCase
