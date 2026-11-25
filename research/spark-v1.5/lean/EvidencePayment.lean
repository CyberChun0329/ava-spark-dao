import Menu

/-! Research evidence for the fixed material payment. External predicates describe
what evidence establishes. They neither interpret v1.5 nor grant any authority. -/

namespace GovernanceEvidenceTrial

open SourceV14 SourceV14.Workflow
open SourceV14.FidelityMaterialsProvisionChecks
open SparkJoint

abbrev RState := RecognisedV15.Workflow.State
abbrev RStep := RecognisedV15.Workflow.Step
abbrev RPath := RecognisedV15.Workflow.Path RStep

/-- Actual debit coordinates for the two transfers subtracted from the given opening cut. -/
structure CashCut where
  earlierPool : ActorId × Nat
  bankPool : ActorId × Nat
  earlierDebitAt : Moment
  adjustment : BankCorrection

/-- External trust boundary. In particular, effective release is an input;
v1.5 does not specify who can make this interim release effective. -/
structure ExternalEvidence where
  reconcilesCash :
    CashCut → PostedPayment → Moment → Amount → Moment → Prop
  supportsReceiptAtCheck : Event → Moment → Prop
  confirmsPartialDelivery : ReviewMatter → PartialReceiptRecord → Moment → Prop
  excludesRelevantProviderFault : ReviewMatter → ProviderCheckRecord → Moment → Prop
  effectiveRelease : ReviewMatter → Reserves.Release → Prop

def cashReady (e : ExternalEvidence) (cash : CashCut) : Prop :=
  cash.earlierPool = (10, 1) ∧ cash.bankPool = (10, 1) ∧
    cash.earlierDebitAt = JointM.earlierPayment.instruction.atTime ∧
    (tick 29).before cash.earlierDebitAt ∧
    cash.earlierDebitAt.before cash.adjustment.debitAt ∧
    cash.adjustment.debitAt.before (tick 45) ∧
    0 < cash.adjustment.unrecoverableDebit ∧
    e.reconcilesCash cash JointM.earlierPayment (tick 29) 22 (tick 45)

/-- The receipt check concerns the exact old payment, entitlement and reference 81
in the fixture's t44 event. The external predicate confirms its usability at t45. -/
def paymentInputs (e : ExternalEvidence) (cash : CashCut) (early : Bool) : Prop :=
  cashReady e cash ∧ (early = true → e.supportsReceiptAtCheck (JointM.verificationEvent 44) (tick 45))

/-- Select one of the two already constructed pending reductions. -/
inductive Reduction where
  | toEight
  | toSix

def Reduction.outcome : Reduction → Outcome
  | .toEight => .pendingTeachingOnly
  | .toSix => .pendingChecked

def Reduction.row : Reduction → Reserves.Release
  | .toEight => teachingOnlyRelease
  | .toSix => pendingRelease

def Reduction.basis (r : Reduction) (e : ExternalEvidence) : Prop :=
  e.confirmsPartialDelivery pendingMatter partialReceipt r.row.occurred ∧
    (r = .toSix → e.excludesRelevantProviderFault pendingMatter providerCheck r.row.occurred) ∧
    e.effectiveRelease pendingMatter r.row

def releaseInputs (e : ExternalEvidence) : Outcome → Prop
  | .pendingTeachingOnly => Reduction.toEight.basis e
  | .pendingChecked => Reduction.toSix.basis e
  | _ => True

def postingInputs (e : ExternalEvidence) (cash : CashCut) (kind : Outcome)
    (early : Bool) : Prop :=
  paymentInputs e cash early ∧ releaseInputs e kind

def paymentEvent (cash : CashCut) (kind : Outcome) : Event :=
  JointM.paymentEvent (grossAtCheck cash.adjustment) (retained kind)

def checkedPost (e : ExternalEvidence) (cash : CashCut) (kind : Outcome)
    (early : Bool) (next : RState) : Prop :=
  postingInputs e cash kind early ∧
    RStep (RecognisedV15.Workflow.State.fromDirect (whenChecked kind early)) (paymentEvent cash kind) next

/-- Same pre-state and same post as the fixture. A passing numeric guard is
sufficient for the researched posting only together with the declared inputs. -/
theorem checkedPaymentIff (e : ExternalEvidence) (cash : CashCut) (kind : Outcome)
    (early : Bool) :
    (∃ next, checkedPost e cash kind early next) ↔
      postingInputs e cash kind early ∧ requiredFunds early ≤ observedNet cash.adjustment kind := by
  constructor
  · rintro ⟨next, inputs, post⟩
    exact ⟨inputs, (recognisedMenu cash.adjustment kind early).mp ⟨next, post⟩⟩
  · rintro ⟨inputs, enough⟩
    obtain ⟨next, post⟩ := (recognisedMenu cash.adjustment kind early).mpr enough
    exact ⟨next, inputs, post⟩

/-- The accepted-compensation path remains the primary comparison. -/
theorem acceptedPayment (e : ExternalEvidence) (cash : CashCut) (early : Bool)
    (inputs : paymentInputs e cash early)
    (enough : requiredFunds early ≤ observedNet cash.adjustment .accepted) :
    ∃ next, checkedPost e cash .accepted early next ∧
      RPath (RecognisedV15.Workflow.State.fromDirect commonStart)
        (datesBefore45 .accepted early ++ [paymentEvent cash .accepted]) next := by
  obtain ⟨next, post⟩ := (menu cash.adjustment .accepted early).mpr enough
  exact ⟨RecognisedV15.Workflow.State.fromDirect next,
    ⟨⟨inputs, trivial⟩, RecognisedV15.Workflow.step_from_direct post⟩,
    RecognisedV15.Workflow.path_from_direct
      (append (followsCommonOpening .accepted early) (.next post (.nil next)))⟩

/-- The strengthened event combines the fixed inventory proof with external
support for the fact filters and for the release's separate effect. -/
def Reduction.verifies (r : Reduction) (e : ExternalEvidence) (row : Reserves.Release) : Prop :=
  (match r with
    | .toEight => verifiesTeachingOnlyRelease afterPendingReceipt row
    | .toSix => verifiesPendingRelease afterPendingReceipt row) ∧ r.basis e

def Reduction.event (r : Reduction) (e : ExternalEvidence) : Event :=
  .reserveReleased r.row (r.verifies e)

theorem releaseStep (r : Reduction) (e : ExternalEvidence) (basis : r.basis e) :
    Step afterPendingReceipt (r.event e) (at45 r.outcome) := by
  have initial : afterPendingReceipt.activeReserves = [mInitial, tInitial] := rfl
  cases r with
  | toEight =>
    have reduced : (10 : Amount) - teachingOnlyRelease.amount = 8 := by decide +kernel
    change Step afterPendingReceipt (.reserveReleased teachingOnlyRelease
      (Reduction.toEight.verifies e)) { afterPendingReceipt with activeReserves := [mInitial, tAt 8] }
    rw [← reduced]
    refine releaseUpdates (first := [mInitial]) (last := []) initial rfl ?_ ?_
    · unfold teachingOnlyRelease release Reserves.Release.matches
      decide +kernel
    · exact ⟨noReleaseWithoutAccounting (releaseAfterTeachingOnly checkedPartial initial), basis⟩
  | toSix =>
    have checked : checkedPending afterPendingReceipt partialReceipt providerCheck := by
      refine ⟨checkedPartial, rfl, ?_⟩
      simp [SparkJoint.authority, pendingMatter, providerCheck, ReviewAuthorities.disinterested,
        DirectInterest.affected]
    have reduced : (10 : Amount) - pendingRelease.amount = 6 := by decide +kernel
    change Step afterPendingReceipt (.reserveReleased pendingRelease
      (Reduction.toSix.verifies e)) { afterPendingReceipt with activeReserves := [mInitial, tAt 6] }
    rw [← reduced]
    refine releaseUpdates (first := [mInitial]) (last := []) initial rfl ?_ ?_
    · unfold pendingRelease release Reserves.Release.matches
      decide +kernel
    · exact ⟨noReleaseWithoutAccounting (releaseWhileTutorDecisionOpen checked initial), basis⟩

def pendingEventsWithEvidence (r : Reduction) (e : ExternalEvidence) (early : Bool) : List Event :=
  history .pendingUnreleased ++ [r.event e] ++
    (if early then [JointM.verificationEvent 44] else [])

/-- Reducing T's reservation and then posting M's fixed payment are separate
steps in the same recognised-state path, using the same resulting reservation. -/
theorem pendingPayment (r : Reduction) (e : ExternalEvidence) (cash : CashCut) (early : Bool)
    (basis : r.basis e) (inputs : paymentInputs e cash early)
    (enough : requiredFunds early ≤ observedNet cash.adjustment r.outcome) :
    ∃ next, checkedPost e cash r.outcome early next ∧
      RPath (RecognisedV15.Workflow.State.fromDirect commonStart)
        (pendingEventsWithEvidence r e early ++ [paymentEvent cash r.outcome]) next := by
  have reducedPath : RecognisedV15.Workflow.Path Step commonStart
      (history .pendingUnreleased ++ [r.event e]) (at45 r.outcome) :=
    append pendingReceiptPath (.next (releaseStep r e basis) (.nil _))
  have beforePost : RecognisedV15.Workflow.Path Step commonStart
      (pendingEventsWithEvidence r e early) (whenChecked r.outcome early) := by
    cases early
    · simpa [pendingEventsWithEvidence, whenChecked] using reducedPath
    · exact append reducedPath (.next (verify44 (readyAt45 r.outcome)) (.nil _))
  obtain ⟨next, post⟩ := (menu cash.adjustment r.outcome early).mpr enough
  exact ⟨RecognisedV15.Workflow.State.fromDirect next,
    ⟨⟨inputs, by cases r <;> exact basis⟩, RecognisedV15.Workflow.step_from_direct post⟩,
    RecognisedV15.Workflow.path_from_direct (append beforePost (.next post (.nil next)))⟩

/-- Lack of effective release rules out this research event. The frozen
workflow takes the supplied verifier as an input to its general event. -/
theorem noResearchReleaseWithoutAuthority (r : Reduction) (e : ExternalEvidence)
    {s next : State} (missing : ¬ e.effectiveRelease pendingMatter r.row) :
    ¬ Step s (r.event e) next := by
  intro event
  exact missing (noReleaseWithoutAccounting event).2.2.2

theorem wrongPoolCannotSupportPost (e : ExternalEvidence) (cash : CashCut)
    (kind : Outcome) (early : Bool) (wrong : cash.bankPool ≠ (10, 1)) :
    ¬ ∃ next, checkedPost e cash kind early next := by
  rintro ⟨_, ⟨⟨ready, _⟩, _⟩, _⟩
  exact wrong ready.2.1

theorem lateDebitCannotSupportPost (e : ExternalEvidence) (cash : CashCut)
    (kind : Outcome) (early : Bool) (late : ¬ cash.adjustment.debitAt.before (tick 45)) :
    ¬ ∃ next, checkedPost e cash kind early next := by
  rintro ⟨_, ⟨⟨ready, _⟩, _⟩, _⟩
  exact late ready.2.2.2.2.2.1

theorem noEarlyPostLabelWithoutMatchedReceipt (e : ExternalEvidence) (cash : CashCut)
    (kind : Outcome) (missing : ¬ e.supportsReceiptAtCheck (JointM.verificationEvent 44) (tick 45)) :
    ¬ ∃ next, checkedPost e cash kind true next := by
  rintro ⟨_, ⟨⟨_, usable⟩, _⟩, _⟩
  exact missing (usable rfl)

theorem noReducedPostWithoutRelease (e : ExternalEvidence) (cash : CashCut) (r : Reduction)
    (early : Bool) (missing : ¬ e.effectiveRelease pendingMatter r.row) :
    ¬ ∃ next, checkedPost e cash r.outcome early next := by
  rintro ⟨_, ⟨_, basis⟩, _⟩
  have supported : r.basis e := by cases r <;> exact basis
  exact missing supported.2.2

theorem unreleasedAtTheseCutsCannotPost (e : ExternalEvidence) (cash : CashCut) (early : Bool)
    (which : cash.adjustment = lowerBankCut ∨ cash.adjustment = upperBankCut) :
    ¬ ∃ next, checkedPost e cash .pendingUnreleased early next := by
  intro supported
  have enough := ((checkedPaymentIff e cash .pendingUnreleased early).mp supported).2
  rcases which with low | high
  · rw [low] at enough
    cases early <;> revert enough <;> decide +kernel
  · rw [high] at enough
    cases early <;> revert enough <;> decide +kernel

theorem noSixPostWithoutProviderExclusion (e : ExternalEvidence) (cash : CashCut) (early : Bool)
    (missing : ¬ e.excludesRelevantProviderFault pendingMatter providerCheck pendingRelease.occurred) :
    ¬ ∃ next, checkedPost e cash .pendingChecked early next := by
  rintro ⟨_, ⟨_, basis⟩, _⟩
  exact missing (basis.2.1 rfl)

section FixtureChecks

private def cash16 : CashCut := ⟨(10, 1), (10, 1), tick 40, lowerBankCut⟩
private def cash18 : CashCut := ⟨(10, 1), (10, 1), tick 40, upperBankCut⟩

variable (e : ExternalEvidence)

-- Exercise the exact concrete endpoint while keeping external premises explicit.
example (inputs : paymentInputs e cash16 true) :
    ∃ next, checkedPost e cash16 .accepted true next ∧
      RPath (RecognisedV15.Workflow.State.fromDirect commonStart)
        (datesBefore45 .accepted true ++ [paymentEvent cash16 .accepted]) next :=
  acceptedPayment e cash16 true inputs (by decide +kernel)

example (inputs : paymentInputs e cash16 true) (basis : Reduction.toSix.basis e) :
    ∃ next, checkedPost e cash16 .pendingChecked true next ∧
      RPath (RecognisedV15.Workflow.State.fromDirect commonStart)
        (pendingEventsWithEvidence .toSix e true ++ [paymentEvent cash16 .pendingChecked]) next :=
  pendingPayment .toSix e cash16 true basis inputs (by decide +kernel)

example (inputs : paymentInputs e cash18 true) (basis : Reduction.toEight.basis e) :
    ∃ next, checkedPost e cash18 .pendingTeachingOnly true next ∧
      RPath (RecognisedV15.Workflow.State.fromDirect commonStart)
        (pendingEventsWithEvidence .toEight e true ++
          [paymentEvent cash18 .pendingTeachingOnly]) next :=
  pendingPayment .toEight e cash18 true basis inputs (by decide +kernel)

-- Changing just the debit time or pool preserves the old arithmetic.
private def late16 : CashCut := { cash16 with adjustment := { lowerBankCut with debitAt := tick 46 } }
private def wrongPool16 : CashCut := { cash16 with bankPool := (10, 2) }

example : grossAtCheck late16.adjustment = 16 ∧ grossAtCheck wrongPool16.adjustment = 16 := by
  decide +kernel

example : ¬ ∃ next, checkedPost e late16 .accepted true next :=
  lateDebitCannotSupportPost e late16 .accepted true (by decide +kernel)

example : ¬ ∃ next, checkedPost e wrongPool16 .accepted true next :=
  wrongPoolCannotSupportPost e wrongPool16 .accepted true (by decide +kernel)

end FixtureChecks

#print axioms checkedPaymentIff
#print axioms acceptedPayment
#print axioms releaseStep
#print axioms pendingPayment
#print axioms noResearchReleaseWithoutAuthority
#print axioms wrongPoolCannotSupportPost
#print axioms lateDebitCannotSupportPost
#print axioms noEarlyPostLabelWithoutMatchedReceipt
#print axioms noReducedPostWithoutRelease
#print axioms unreleasedAtTheseCutsCannotPost
#print axioms noSixPostWithoutProviderExclusion

end GovernanceEvidenceTrial
