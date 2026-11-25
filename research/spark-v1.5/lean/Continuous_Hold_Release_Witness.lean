import SourceV14

namespace SourceV14.ContinuousHoldReleaseWitness

open Booking Confirmation Course Operations

private def day (n : Nat) : Moment := ⟨n * 86400, 0⟩

private theorem beforeDay (time : Moment) (n : Nat) :
    time.before (day n) ↔ time.seconds < (day n).seconds := by
  simp [Moment.before, day]

private theorem dayBy (n : Nat) (time : Moment) :
    (day n).by time ↔ (day n).seconds ≤ time.seconds := by
  cases time
  simp [Moment.by, Moment.before, day]
  omega

private def heldPart : PaymentPart := ⟨⟨1, 2, 1, .tutorPay 10⟩, .person 10 none, 100⟩
private def otherPart : PaymentPart := { heldPart with ref.portion := 2 }
private def matter : ReviewMatter := ⟨1, 1, [12, 30]⟩
private def terms : ReviewTerms := ⟨30, 31, 32, .second 0, day 25, day 20, day 25, 33⟩
private def facts : HoldFacts where
  terms := fun _ ↦ terms
  termsApply := fun _ ↦ True
  acceptedPaymentConcern := fun _ _ _ _ ↦ True
  reviewerCannotActInTime := fun _ _ ↦ True
  temporaryAuthority := fun _ _ _ _ ↦ True
  allegedFactsWouldChangePayment := fun _ _ _ ↦ True
  separatelyIdentifiable := fun _ _ ↦ True
  establishedParts := fun _ _ ↦ [heldPart, otherPart]
  paymentAffected := fun _ _ ↦ True
  decisionPending := fun _ _ _ ↦ False
  partFallsUnderDecision := fun _ _ _ ↦ False
  decisionConcernsWholeGroup := fun _ _ ↦ False
  isGroupLesson := fun _ ↦ False
  affectsWholeSettlement := fun _ ↦ False
  groupSettlementParts := fun _ ↦ []

private def authority : ReviewAuthorities :=
  ⟨fun _ _ ↦ True, fun _ _ _ ↦ True, fun _ actor _ ↦ actor = 20,
    fun _ actor _ ↦ actor = 21, fun _ _ _ ↦ ⟨false, false, false, false⟩,
    fun _ ↦ none, [], [], fun _ ↦ [], fun _ ↦ []⟩

private def holdA : FormalHold := ⟨1, matter, .payment, [heldPart], 20, day 5, day 5, "A", day 6⟩
private def holdB (start : Nat) : FormalHold :=
  ⟨2, matter, .payment, [heldPart], 20, day start, day start, "B", day (start + 1)⟩
private def liftA : FormalLift := ⟨1, .paymentParts [heldPart.ref], 20, day 10, day 10⟩
private def liftB : FormalLift := ⟨2, .all, 20, day 20, day 20⟩
private def approval : PaymentApproval :=
  ⟨1, 21, 31, day 3, some (day 23), none,
    [⟨heldPart.ref, .person 10, 100, none⟩, ⟨otherPart.ref, .person 10, 100, none⟩]⟩
private def history (start : Nat) : HoldHistory :=
  ⟨⟨[], [], []⟩, [], [holdA, holdB start], [liftA, liftB], [approval], [], [], []⟩
private def schedule (expiry release : Nat) : PaymentSchedule :=
  ⟨day 4, day expiry, none, .period (2 * 86400) (.second ((release + 2) * 86400))⟩
private def instruction (part : PaymentPart) (when : Nat) : PaymentInstruction :=
  ⟨part.ref, .person 10, 31, 100, day when⟩
private def allowed (h : HoldHistory) (expiry release when : Nat) : Prop :=
  originalApprovalAfterLift authority facts h approval heldPart (schedule expiry release)
    (day release) (fun _ ↦ True) (instruction heldPart when)

private theorem validA (start : Nat) : (history start).validFormalHold authority facts holdA := by
  simp [HoldHistory.validFormalHold, FormalHold.mayImpose, ReviewAuthorities.mayImposeOrLift,
    ReviewAuthorities.disinterested, DirectInterest.affected, HoldFacts.isCanonicalPart,
    HoldHistory.originallyApprovedBy, HoldHistory.originalSettlementActor,
    HoldHistory.notTemporarySetter, PaymentHistory.remainingBefore,
    PaymentHistory.receivedForPartBefore, history, holdA, facts, matter, heldPart, otherPart,
    authority, approval, sumAmounts, day, Moment.by, Moment.before]
  decide +kernel

private theorem validB (start : Nat) :
    (history start).validFormalHold authority facts (holdB start) := by
  simp [HoldHistory.validFormalHold, FormalHold.mayImpose, ReviewAuthorities.mayImposeOrLift,
    ReviewAuthorities.disinterested, DirectInterest.affected, HoldFacts.isCanonicalPart,
    HoldHistory.originallyApprovedBy, HoldHistory.originalSettlementActor,
    HoldHistory.notTemporarySetter, PaymentHistory.remainingBefore,
    PaymentHistory.receivedForPartBefore, history, holdB, facts, matter, heldPart, otherPart,
    authority, approval, sumAmounts, day, Moment.by, Moment.before]
  decide +kernel

private theorem validLiftA (start : Nat) :
    (history start).validLift authority facts holdA liftA := by
  simp [HoldHistory.validLift, FormalLift.mayLift, FormalLift.covers, FormalHold.covers,
    ReviewAuthorities.mayImposeOrLift, ReviewAuthorities.disinterested, DirectInterest.affected,
    HoldHistory.originallyApprovedBy, HoldHistory.originalSettlementActor,
    HoldHistory.notTemporarySetter, history, holdA, liftA, authority, approval, day,
    Moment.by, Moment.before]

private theorem validLiftB (start : Nat) (early : start < 20) :
    (history start).validLift authority facts (holdB start) liftB := by
  have before : (day start).before (day 20) := (beforeDay _ _).2 (by simp [day]; omega)
  simp [HoldHistory.validLift, FormalLift.mayLift, FormalLift.covers,
    ReviewAuthorities.mayImposeOrLift, ReviewAuthorities.disinterested, DirectInterest.affected,
    HoldHistory.originallyApprovedBy, HoldHistory.originalSettlementActor,
    HoldHistory.notTemporarySetter, history, holdB, liftB, authority, approval, before,
    Moment.by]

private theorem aInForce (start : Nat) (time : Moment)
    (begun : (day 5).by time) (early : time.before (day 10)) :
    (history start).formalInForce authority facts holdA heldPart.ref time := by
  refine ⟨validA start, ⟨heldPart, by simp [holdA], rfl⟩, begun, ?_⟩
  rintro ⟨lift, member, valid, _, lifted⟩
  simp [history] at member
  rcases member with rfl | rfl
  · change (day 10).by time at lifted
    rw [dayBy] at lifted
    rw [beforeDay] at early
    omega
  · have wrong : liftB.hold = holdA.id := valid.1.1
    cases wrong

private theorem bInForce (start : Nat) (time : Moment)
    (begun : (day start).by time) (early : time.before (day 20)) :
    (history start).formalInForce authority facts (holdB start) heldPart.ref time := by
  refine ⟨validB start, ⟨heldPart, by simp [holdB], rfl⟩, begun, ?_⟩
  rintro ⟨lift, member, valid, _, lifted⟩
  simp [history] at member
  rcases member with rfl | rfl
  · have wrong : liftA.hold = (holdB start).id := valid.1.1
    cases wrong
  · change (day 20).by time at lifted
    rw [dayBy] at lifted
    rw [beforeDay] at early
    omega

private theorem noHoldAtOrAfter20 (start : Nat) (early : start < 20) (time : Moment)
    (after : (day 20).by time) :
    ¬ (history start).paymentOnHold authority facts heldPart.ref time := by
  rintro (⟨hold, inForce⟩ | ⟨temporary, inForce⟩)
  · have member := inForce.1.1
    simp [history] at member
    rcases member with rfl | rfl
    · refine inForce.2.2.2 ⟨liftA, by simp [history], validLiftA _,
        by simp [liftA, FormalLift.covers], ?_⟩
      change (day 10).by time
      rw [dayBy] at after ⊢
      simp [day] at after ⊢
      omega
    · exact inForce.2.2.2 ⟨liftB, by simp [history], validLiftB start early, trivial, after⟩
  · simpa [history] using inForce.1

private theorem overlapsFromDeadline (time : Moment) (after : (day 8).by time)
    (early : time.before (day 20)) :
    (history 9).paymentOnHold authority facts heldPart.ref time := by
  by_cases beforeLiftA : time.before (day 10)
  · refine Or.inl ⟨holdA, aInForce 9 time ?_ beforeLiftA⟩
    rw [dayBy] at after ⊢
    simp [day] at after ⊢
    omega
  · refine Or.inl ⟨holdB 9, bInForce 9 time ?_ early⟩
    rw [dayBy, beforeDay] at *
    simp [day] at beforeLiftA ⊢
    omega

private theorem releaseAt20 (start : Nat) (early : start < 20) :
    (history start).paymentReleasedAt authority facts heldPart.ref (day 20) := by
  refine ⟨holdB start, liftB, ⟨validB start, ⟨heldPart, by simp [holdB], rfl⟩,
    by simp [history], validLiftB start early, trivial, ?_, ?_⟩,
    ⟨Or.inr rfl, noHoldAtOrAfter20 start early _ (Or.inr rfl), ?_⟩⟩
  · simp [HoldHistory.distinctFormalDecisions, history, holdA, holdB]
  · rintro ⟨lift, member, valid, _, earlier⟩
    simp [history] at member
    rcases member with rfl | rfl
    · have wrong : liftA.hold = (holdB start).id := valid.1.1
      cases wrong
    · simp [liftB, Moment.before] at earlier
  · intro time after before
    change (day 20).by time at after
    rw [dayBy] at after
    rw [beforeDay] at before
    omega

private theorem heldPartCanonical : facts.isCanonicalPart heldPart := by
  simp [HoldFacts.isCanonicalPart, facts, heldPart, otherPart]
  decide +kernel

private theorem openedAt20 : postLiftWindowOpened authority facts (history 9) heldPart
    (schedule 8 20) (day 20) := by
  refine ⟨heldPartCanonical, releaseAt20 9 (by decide),
    ⟨holdA, aInForce 9 _ (by decide) (by decide)⟩, by decide +kernel, by decide,
    ⟨by decide, noHoldAtOrAfter20 9 (by decide) _ (by decide), overlapsFromDeadline⟩,
    ?_⟩
  simp [HoldHistory.resolvesDeadline, history, schedule, ClockBoundary.after, ClockBoundary.find,
    day]

/-- Formal holds over days 5–10 and 9–20 release the portion on day 20. -/
theorem overlappingHoldsPermitPaymentAtDay21 : allowed (history 9) 8 20 21 := by
  refine ⟨⟨⟨openedAt20, by decide, ?_, by decide +kernel⟩, ?_,
    noHoldAtOrAfter20 9 (by decide) _ (by decide)⟩, ?_⟩
  · simp [schedule, DeadlineTerm.cutoff, ClockCutoff.metBy, instruction, day]
  · simp [PaymentHistory.validOutstandingPayment, PaymentHistory.distinctReceipts,
      PaymentHistory.validReturns, PaymentHistory.remainingBefore,
      PaymentHistory.receivedForPartBefore, PaymentRecipient.accepts, history, instruction,
      heldPart, sumAmounts]
    decide +kernel
  · simp [HoldHistory.approvalRecorded, PaymentApproval.authorisedAtGrant,
      PaymentApproval.originallyCovered, PaymentApproval.validAt, PaymentApproval.covers,
      ApprovalScopeEntry.covers, ApprovalScopeEntry.remainingBefore,
      PaymentHistory.receivedForPartBefore, PaymentRecipient.accepts, authority, approval, history,
      instruction, schedule, heldPart, otherPart, sumAmounts, day, Moment.by, Moment.before]
    decide +kernel

/-- Lifting A cannot start the clock while B still covers the same payment portion. -/
theorem firstFormalLiftDoesNotStartWindow :
    ¬ postLiftWindowOpened authority facts (history 9) heldPart (schedule 8 10) (day 10) := by
  intro opened
  exact opened.2.2.2.2.2.1.2.1
    (Or.inl ⟨holdB 9, bInForce 9 _ (by decide) (by decide)⟩)

/-- After a gap, a later release does not reopen the original approval's window. -/
theorem laterReleaseAfterGapDoesNotResetWindow :
    (history 12).paymentReleasedAt authority facts heldPart.ref (day 20) ∧
      ¬ allowed (history 12) 8 20 21 := by
  refine ⟨releaseAt20 12 (by decide), ?_⟩
  intro permitted
  have heldAtGap := permitted.1.1.1.2.2.2.2.2.1.2.2 (day 11) (by decide) (by decide)
  rcases heldAtGap with ⟨hold, active⟩ | ⟨temporary, active⟩
  · have member := active.1.1
    simp [history] at member
    rcases member with rfl | rfl
    · exact active.2.2.2 ⟨liftA, by simp [history], validLiftA _,
        by simp [liftA, FormalLift.covers], by decide⟩
    · exact (by decide : ¬ (day 12).by (day 11)) active.2.2.1
  · simpa [history] using active.1

/-- The same unresolved obligation has another portion with its own unaffected execution path. -/
theorem otherPortionMayExecuteOnItsOriginalClock :
    originalExecutorMayPay authority facts (history 9) approval otherPart (schedule 8 20)
      (fun _ ↦ True) (instruction otherPart 8) := by
  simp [originalExecutorMayPay, HoldFacts.isCanonicalPart, HoldHistory.approvalRecorded,
    PaymentApproval.authorisedAtGrant, PaymentApproval.validAt, PaymentApproval.covers,
    ApprovalScopeEntry.covers, ApprovalScopeEntry.remainingBefore,
    PaymentHistory.validOutstandingPayment, PaymentHistory.distinctReceipts,
    PaymentHistory.validReturns, PaymentHistory.remainingBefore,
    PaymentHistory.receivedForPartBefore,
    PaymentRecipient.accepts, HoldHistory.distinctFormalDecisions, HoldHistory.paymentOnHold,
    HoldHistory.formalInForce, HoldHistory.validFormalHold, FormalHold.covers,
    HoldHistory.temporaryInForce, history, holdA, holdB, authority, approval, facts, heldPart,
    otherPart, schedule, instruction, sumAmounts, day, Moment.by, Moment.before]
  decide +kernel

private def temporary : TemporaryHold :=
  ⟨{ matter with id := 2 }, 31, heldPart, heldPart.ref, "temporary", day 3, day 4⟩

private def temporaryTailHistory : HoldHistory :=
  { history 9 with formal := [holdA], lifts := [liftA], temporary := [temporary] }

private theorem reviewerIsNotTemporarySetter (atTime : Moment) :
    temporaryTailHistory.notTemporarySetter authority facts matter 20 atTime := by
  intro hold member _ _ _
  have equality : hold = temporary := by simpa [temporaryTailHistory] using member
  subst hold
  decide

private theorem validAWithTemporaryTail :
    temporaryTailHistory.validFormalHold authority facts holdA := by
  obtain ⟨_, allowedHold, noPriorApproval, _, noPriorActor⟩ := validA 9
  exact ⟨by simp [temporaryTailHistory], allowedHold, noPriorApproval,
    reviewerIsNotTemporarySetter _, noPriorActor⟩

private theorem validLiftAWithTemporaryTail :
    temporaryTailHistory.validLift authority facts holdA liftA := by
  obtain ⟨allowedLift, noPriorApproval, noPriorActor, _⟩ := validLiftA 9
  exact ⟨allowedLift, noPriorApproval, noPriorActor, reviewerIsNotTemporarySetter _⟩

private theorem temporaryInForceUpToExpiry (time : Moment) (begun : (day 4).by time)
    (early : time.before (day 20)) :
    temporaryTailHistory.temporaryInForce authority facts temporary heldPart.ref time := by
  refine ⟨by simp [temporaryTailHistory], ?_, rfl, begun, early, ?_⟩
  · simp [TemporaryHold.maySetAside, temporary, terms, facts, authority,
      ReviewAuthorities.disinterested, DirectInterest.affected, HoldFacts.isCanonicalPart,
      heldPart, otherPart, matter, day, Moment.before,
      PaymentHistory.remainingBefore, PaymentHistory.receivedForPartBefore, temporaryTailHistory,
      history, sumAmounts]
    decide +kernel
  · rintro ⟨hold, caseMatch, _, valid, _, _⟩
    have equal : hold = holdA := by simpa [temporaryTailHistory] using valid.1
    subst hold
    simp [holdA, temporary, matter, ReviewMatter.sameCase] at caseMatch

private theorem noHoldAtTemporaryExpiry :
    ¬ temporaryTailHistory.paymentOnHold authority facts heldPart.ref (day 20) := by
  rintro (⟨hold, active⟩ | ⟨temp, active⟩)
  · have equality : hold = holdA := by simpa [temporaryTailHistory] using active.1.1
    subst hold
    exact active.2.2.2 ⟨liftA, by simp [temporaryTailHistory], validLiftAWithTemporaryTail,
      by simp [liftA, FormalLift.covers], by decide⟩
  · have equality : temp = temporary := by simpa [temporaryTailHistory] using active.1
    subst temp
    exact (by decide : ¬ (day 20).before (day 20)) active.2.2.2.2.1

private theorem aInForceWithTemporaryTail (time : Moment) (begun : (day 5).by time)
    (early : time.before (day 10)) :
    temporaryTailHistory.formalInForce authority facts holdA heldPart.ref time := by
  have active := aInForce 9 time begun early
  refine ⟨validAWithTemporaryTail, active.2.1, begun, ?_⟩
  rintro ⟨lift, member, _, _, lifted⟩
  have equality : lift = liftA := by simpa [temporaryTailHistory] using member
  subst lift
  exact active.2.2.2 ⟨liftA, by simp [history], validLiftA 9,
    by simp [liftA, FormalLift.covers], lifted⟩

private theorem heldUntilTemporaryExpiry (time : Moment) (after : (day 4).by time)
    (early : time.before (day 20)) :
    temporaryTailHistory.paymentOnHold authority facts heldPart.ref time :=
  Or.inr ⟨temporary, temporaryInForceUpToExpiry time after early⟩

/-- Temporary coverage at the original deadline cannot supply the required formal hold. -/
theorem noWindowWithoutFormalHoldAtOriginalDeadline :
    temporaryTailHistory.firstUnheldFrom authority facts heldPart.ref (day 4) (day 20) ∧
      ¬ postLiftWindowOpened authority facts temporaryTailHistory heldPart (schedule 4 20)
        (day 20) := by
  refine ⟨⟨by decide, noHoldAtTemporaryExpiry, heldUntilTemporaryExpiry⟩, ?_⟩
  intro opened
  obtain ⟨hold, active⟩ := opened.2.2.1
  have equal : hold = holdA := by simpa [temporaryTailHistory] using active.1.1
  subst hold
  exact (by decide : ¬ (day 5).by (day 4)) active.2.2.1

/-- An effective temporary hold in a different case keeps the same portion held until expiry. -/
theorem temporaryTailDelaysReleaseToExpiry :
    ¬ temporaryTailHistory.paymentReleasedAt authority facts heldPart.ref (day 10) ∧
      postLiftWindowOpened authority facts temporaryTailHistory heldPart (schedule 8 20)
        (day 20) := by
  constructor
  · rintro ⟨_, _, _, _, unheld, _⟩
    exact unheld (Or.inr ⟨temporary, temporaryInForceUpToExpiry _ (by decide) (by decide)⟩)
  · refine ⟨heldPartCanonical, ?_, ⟨holdA, aInForceWithTemporaryTail _ (by decide) (by decide)⟩,
      by decide +kernel, by decide, ⟨by decide, noHoldAtTemporaryExpiry, ?_⟩, ?_⟩
    · refine ⟨holdA, liftA, ⟨validAWithTemporaryTail, ⟨heldPart, by simp [holdA], rfl⟩,
        by simp [temporaryTailHistory], validLiftAWithTemporaryTail,
        by simp [liftA, FormalLift.covers],
        by simp [HoldHistory.distinctFormalDecisions, temporaryTailHistory], ?_⟩,
        ⟨by decide, noHoldAtTemporaryExpiry, ?_⟩⟩
      · rintro ⟨lift, member, _, _, earlier⟩
        have equality : lift = liftA := by simpa [temporaryTailHistory] using member
        subst lift
        simp [Moment.before] at earlier
      · intro time began early
        exact Or.inr ⟨temporary, temporaryInForceUpToExpiry time (by
          change (day 10).by time at began
          rw [dayBy] at began ⊢
          simp [day] at began ⊢
          omega) early⟩
    · intro time after early
      exact heldUntilTemporaryExpiry time (by
        change (day 8).by time at after
        rw [dayBy] at after ⊢
        simp [day] at after ⊢
        omega) early
    · simp [HoldHistory.resolvesDeadline, temporaryTailHistory, history, schedule,
        ClockBoundary.after, ClockBoundary.find, day]

#print axioms overlappingHoldsPermitPaymentAtDay21
#print axioms firstFormalLiftDoesNotStartWindow
#print axioms laterReleaseAfterGapDoesNotResetWindow
#print axioms noWindowWithoutFormalHoldAtOriginalDeadline
#print axioms otherPortionMayExecuteOnItsOriginalClock
#print axioms temporaryTailDelaysReleaseToExpiry

end SourceV14.ContinuousHoldReleaseWitness
