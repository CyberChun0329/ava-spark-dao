import TimedTransferPortions

/-! Research-only consistency check at the old C0 review entry. The two contingent
charges and all remaining interests require independent evidence. The query
does not record an award, entitlement, or payment. -/

namespace ReviewInterestCandidate

open SourceV14 SourceV14.Workflow TransferCase

/-- Supported alternatives for this one prospective shortfall and any remaining
direct effects of the decision, including other effects on the handler's own receivables. -/
structure ExposureInputs where
  availableAt : Moment
  deniedCharge : Amount
  awardedCharge : Amount
  otherInterests : DirectInterest

/-- Independent evidence must bind both amounts and residual flags to the actual matter,
original settlement, prospective claim, place, reviewer and decision point. The alternatives
must suffice to determine the prospective shortfall's effect on the handler's receivables. -/
abbrev VerifiesInputs :=
  ReviewMatter → MaterialsSettlementRecord → String → PlaceId → ActorId → Moment →
    ExposureInputs → Prop

private def claimReference : String :=
  (TimedTransferCase.assumedSupplement .oldReview false).reference

/-- A carrier for the native share query. Its synthetic shortfall is prospective. -/
private def query (point : Moment) (gross : Amount) : Materials.Entitlement :=
  let base := TimedTransferCase.queryRow .oldReview false 0 0
  let supplement := { TimedTransferCase.assumedSupplement .oldReview false with
    identifiedAt := point, charges := [⟨seat, mat, gross⟩] }
  { base with
    original := originalMaterial
    shortfall := some ⟨originalMaterial, supplement, originalMaterial.check⟩
    verifiedAt := point }

def shareReader (s : State) (point : Moment) (gross : Amount) :
    MaterialsShareEvidence mat :=
  s.materials.shareEvidence (query point gross) point

def portion (s : State) (finding : ReviewFinding) (gross amount : Amount) : Prop :=
  (shareReader s finding.decidedAt gross).portionAt originalMaterial.check.terms
    originalMaterial.check.use ⟨seat, mat, gross⟩ (firstUse .oldReview) finding.decidedAt
    finding.reviewer amount

/-- Compare the actual authority input used by the review with the native portions
at decision time. Missing evidence or an indeterminate portion cannot certify this step. -/
def ExposureMatches (verifies : VerifiesInputs) (input : Option ExposureInputs)
    (s : State) (e : Review.Evidence) (finding : ReviewFinding) : Prop :=
  match input with
  | none => False
  | some facts =>
    finding.matter = matter .oldReview ∧
    originalMaterial ∈ s.materials.originals ∧
    originalMaterial.check ∈ s.materials.useChecks ∧
    originalMaterial.check.terms ∈ s.materials.terms ∧
    originalMaterial.record.settledAt.by facts.availableAt ∧
    facts.availableAt.by finding.decidedAt ∧
    verifies finding.matter originalMaterial.record claimReference seat finding.reviewer
      finding.decidedAt facts ∧
    ∃ denied awarded : Amount,
      (∀ amount, portion s finding facts.deniedCharge amount ↔ amount = denied) ∧
      (∀ amount, portion s finding facts.awardedCharge amount ↔ amount = awarded) ∧
      (s.review.authorities (s.reviewEvidence e).authority).interest
        finding.matter finding.reviewer finding.decidedAt =
      { facts.otherInterests with
        amountOwedToHandler := facts.otherInterests.amountOwedToHandler ||
          decide (denied ≠ awarded) }

/-- The native old-review transition still supplies authorisation and all other review
conditions. The research wrapper additionally requires a consistent interest report. -/
def CheckedStep (verifies : VerifiesInputs) (input : Option ExposureInputs)
    (s : State) (e : Review.Evidence) (finding : ReviewFinding) (after : State) : Prop :=
  ExposureMatches verifies input s e finding ∧
    Step s (.review e (.decideReview (lesson .oldReview) none finding)) after

private def pre (recorded supplied : Policy) : State :=
  afterInitial (transferred recorded) supplied

/-- Extract the genuine last root step from the existing four-step witness. -/
private theorem nativeReviewStep (recorded supplied : Policy) :
    Step (pre recorded supplied)
      (.review (evidence supplied) (.decideReview (lesson .oldReview) none
        (reviewed (oldReviewer supplied)))) (terminal recorded supplied) := by
  have path := judgingPath recorded supplied
  change DirectPath (transferred recorded) [
    .review (evidence supplied) (.appoint (appointment .teaching .O)),
    .review (evidence supplied) (.appoint (appointment .oldReview (oldReviewer supplied))),
    .review (evidence supplied) (.decideInitial teachingForm terms (initial .O)),
    .review (evidence supplied) (.decideReview (lesson .oldReview) none
      (reviewed (oldReviewer supplied)))] (terminal recorded supplied) at path
  cases path with
  | next step remaining =>
    cases step with
    | review _ _ _ appointmentRule =>
      cases appointmentRule
      cases remaining with
      | next step remaining =>
        cases step with
        | review _ _ _ appointmentRule =>
          cases appointmentRule
          cases remaining with
          | next step remaining =>
            cases step with
            | review _ _ _ findingRule =>
              cases findingRule
              cases remaining with
              | next last done =>
                cases done
                exact last

private def otherClear : DirectInterest := ⟨false, false, false, false⟩

private def fixtureInput (availableAt : Moment) (otherInterests : DirectInterest) :
    ExposureInputs :=
  ⟨availableAt, 0, 50, otherInterests⟩

/-- Case assumptions for the denial/award comparison and residual effects only. -/
private def fixtureEvidence (facts : ExposureInputs) : VerifiesInputs :=
  fun m original claim place actor point input ↦
    m = matter .oldReview ∧ original = originalMaterial.record ∧ claim = claimReference ∧
    place = seat ∧ (actor = who .O ∨ actor = who .N) ∧ point = tick 51 ∧ input = facts

private def caseInputs : ExposureInputs := fixtureInput (tick 45) otherClear

private theorem nativePortion (recorded supplied : Policy) (a : Expert) (award : Bool)
    (amount : Amount) :
    portion (pre recorded supplied) (reviewed a) (TimedTransferCase.faceValue award) amount ↔
      amount = delta recorded .oldReview (who a) award := by
  cases award <;> exact TimedTransferCase.nativePortionIff recorded .oldReview _ (who a) amount

/-- Both matching distributions pass the same real review entry. -/
theorem acceptsMatched (p : Policy) :
    CheckedStep (fixtureEvidence caseInputs) (some caseInputs)
      (pre p p) (evidence p) (reviewed (oldReviewer p)) (terminal p p) := by
  refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, _, _, nativePortion p p _ false, nativePortion p p _ true,
    ?_⟩, nativeReviewStep p p⟩
  · cases p <;> exact List.mem_cons_self
  · cases p <;> exact List.mem_cons_self
  · cases p <;> exact List.mem_cons_self
  · decide
  · cases p <;> decide
  · refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
    cases p with
    | retain => exact Or.inr rfl
    | assign => exact Or.inl rfl
  · cases p <;> rfl

/-- A retained-interest report lets N make the native review after assignment.
The checked entry rejects this same event and pre-state for every successor. -/
theorem rejectsStale :
    Step (pre .assign .retain) (.review (evidence .retain)
      (.decideReview (lesson .oldReview) none (reviewed .N))) (terminal .assign .retain) ∧
    ¬∃ after, CheckedStep (fixtureEvidence caseInputs) (some caseInputs)
      (pre .assign .retain) (evidence .retain) (reviewed .N) after := by
  refine ⟨nativeReviewStep .assign .retain, ?_⟩
  rintro ⟨_, ⟨_, _, _, _, _, _, _, denied, awarded, hDenied, hAward, report⟩, _⟩
  have deniedEq := (nativePortion .assign .retain .N false denied).mp ((hDenied denied).mpr rfl)
  have awardedEq := (nativePortion .assign .retain .N true awarded).mp ((hAward awarded).mpr rfl)
  rw [deniedEq, awardedEq] at report
  have flag := congrArg DirectInterest.amountOwedToHandler report
  change false = true at flag
  contradiction

/-- The distinct C1 transfer already present in the retained path leaves the C0
decision on its original allocation. A C0 transfer first recorded after review
is also invisible at the review point, even with its earlier effective date. -/
theorem lateArchiveLeavesPriorReader (gross : Amount) :
    let s := pre .retain .retain
    let late := { signedRow .oldReview with recordedAt := tick 52 }
    shareReader { s with materials := { s.materials with transfers := late :: s.materials.transfers } }
      (reviewed .N).decidedAt gross =
      shareReader s (reviewed .N).decidedAt gross := rfl

/-- Other effects on the handler's own receivables survive the transfer.
A flag reporting O as unaffected cannot be certified when that effect is present. -/
theorem rejectsErasedOtherReceivable :
    let extra := fixtureInput (tick 45) { otherClear with amountOwedToHandler := true }
    ¬∃ after, CheckedStep (fixtureEvidence extra) (some extra)
      (pre .assign .assign) (evidence .assign) (reviewed .O) after := by
  dsimp only
  rintro ⟨_, ⟨_, _, _, _, _, _, _, _, _, _, _, report⟩, _⟩
  have flag := congrArg DirectInterest.amountOwedToHandler report
  change false = true at flag
  contradiction

theorem missingOrLateEvidenceCannotCertify :
    (¬∃ after, CheckedStep (fixtureEvidence caseInputs) none (pre .assign .assign)
      (evidence .assign) (reviewed .O) after) ∧
    (let late := fixtureInput (tick 52) otherClear
     ¬∃ after, CheckedStep (fixtureEvidence late) (some late) (pre .assign .assign)
      (evidence .assign) (reviewed .O) after) := by
  constructor
  · rintro ⟨_, impossible, _⟩
    exact impossible
  · dsimp only
    rintro ⟨_, ⟨_, _, _, _, _, available, _⟩, _⟩
    exact (by decide : ¬ (tick 52).by (tick 51)) available

#print axioms acceptsMatched
#print axioms rejectsStale
#print axioms lateArchiveLeavesPriorReader
#print axioms rejectsErasedOtherReceivable
#print axioms missingOrLateEvidenceCannotCertify

end ReviewInterestCandidate
