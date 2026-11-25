import SourceV14.Workflow

namespace SourceV14.FidelityHoldCorrectionChecks

open SourceV14

private def day (n : Nat) : Moment := ⟨n, 0⟩
private def old : PaymentPart := ⟨⟨1, 2, 3, .other⟩, .person 80 none, 60⟩
private def resized : PaymentPart := { old with amount := 45 }
private def renamed : PaymentPart := { resized with ref := { old.ref with portion := 4 }, amount := 35 }
private def sibling : PaymentPart := { renamed with ref := { old.ref with portion := 5 }, amount := 20 }
private def increased : PaymentPart := { renamed with amount := 70 }

private def matter : ReviewMatter := ⟨1, 1, [80]⟩
private def terms : ReviewTerms := ⟨91, 92, 93, day 12, day 12, day 9, day 8, 94⟩
private def authority : ReviewAuthorities where
  corePartner := fun _ _ ↦ False
  initialFinding := fun _ _ _ ↦ False
  reviewer := fun _ actor _ ↦ actor = 90
  approvesPayment := fun _ actor _ ↦ actor = 91
  interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
  originalDecisionMaker := fun _ ↦ none
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

private def facts : HoldFacts where
  terms := fun _ ↦ terms
  termsApply := fun _ ↦ True
  acceptedPaymentConcern := fun _ _ _ _ ↦ True
  reviewerCannotActInTime := fun _ _ ↦ True
  temporaryAuthority := fun _ actor part _ ↦ actor = 92 ∧ part = old.ref
  allegedFactsWouldChangePayment := fun _ _ _ ↦ True
  separatelyIdentifiable := fun _ _ ↦ True
  establishedParts := fun _ _ ↦ [renamed, sibling]
  paymentAffected := fun _ _ ↦ True
  decisionPending := fun _ _ _ ↦ False
  partFallsUnderDecision := fun _ _ _ ↦ False
  decisionConcernsWholeGroup := fun _ _ ↦ False
  isGroupLesson := fun _ ↦ False
  affectsWholeSettlement := fun _ ↦ False
  groupSettlementParts := fun _ ↦ []

private def first : FormalHold :=
  ⟨101, matter, .payment, [old], 90, day 2, day 2, "The amount is disputed.", day 6⟩
private def second : FormalHold :=
  ⟨102, { matter with id := 2 }, .payment, [resized], 90, day 6, day 6,
    "Separate unresolved basis.", day 8⟩
private def firstLift : FormalLift := ⟨101, .paymentParts [old.ref], 90, day 8, day 8⟩
private def secondLift : FormalLift := ⟨102, .all, 90, day 10, day 10⟩
private def temporary : TemporaryHold :=
  ⟨matter, 92, old, old.ref, "The amount is disputed.", day 1, day 2⟩
private def resize : HoldPartRevision := ⟨old, resized, 1, 2, day 1, day 4, day 4⟩
private def rename : HoldPartRevision := ⟨resized, renamed, 2, 3, day 3, day 7, day 7⟩
private def increase : HoldPartRevision := { rename with corrected := increased }

private def originalApproval : PaymentApproval :=
  ⟨15, 91, 89, day 1, none, none, [⟨old.ref, .person 80, 60, none⟩]⟩
private def replacement : PaymentApproval :=
  ⟨16, 91, 89, day 10, none, none, [⟨renamed.ref, .person 80, 35, none⟩]⟩
private def siblingApproval : PaymentApproval :=
  ⟨17, 91, 89, day 6, none, none, [⟨sibling.ref, .person 80, 20, none⟩]⟩
private def ordinaryApproval : PaymentApproval :=
  { replacement with id := 18, grantedAt := day 7 }

private def held : HoldHistory :=
  { payments := ⟨[], [], []⟩, temporary := [], formal := [first, second]
    lifts := [firstLift, secondLift]
    approvals := [originalApproval, replacement, siblingApproval, ordinaryApproval]
    partRevisions := [resize, rename] }

private def schedule : PaymentSchedule := ⟨day 3, day 7, none, .date (day 14)⟩
private def windowSchedule : PaymentSchedule :=
  { schedule with originalExecutionDeadline := day 5 }
private def instruction (part : PaymentPart) (time : Moment) : PaymentInstruction :=
  ⟨part.ref, .person 80, 89, part.amount, time⟩

theorem lateHoldRevisionUsesEffectiveDate :
    let history := { held with partRevisions := [resize, { rename with recordedAt := day 9 }] }
    let originalFacts := { facts with establishedParts := fun _ _ ↦ [old, sibling] }
    ((history.withPartRevisionsKnownAt (day 8)).factsAt originalFacts (day 7)).establishedParts
      1 .other = [sibling, resized] ∧
    ((history.withPartRevisionsKnownAt (day 10)).factsAt originalFacts (day 7)).establishedParts
      1 .other = [sibling, renamed] := by
  decide +kernel

#print axioms lateHoldRevisionUsesEffectiveDate

theorem rootAdoptionRetainsExactPriorAndCurrent
    {state next : Workflow.State} {evidence : Workflow.Review.Evidence} {lesson : Lesson}
    {original : Workflow.Review.OriginalRecord} {correction : PaymentCorrectionCase}
    (edge : Workflow.Step state
      (.review evidence (.recordCorrection lesson (.monetary original correction))) next) :
    next.holds = state.holds.withPartRevision original.outcome correction := by
  cases edge
  rfl

theorem exactVersionsAtTheirActualTimes :
    (held.factsAt facts (day 2)).isCanonicalPart old ∧
    ¬(held.factsAt facts (day 2)).isCanonicalPart resized ∧
    (held.factsAt facts (day 6)).isCanonicalPart resized ∧
    ¬(held.factsAt facts (day 6)).isCanonicalPart old ∧
    (held.factsAt facts (day 8)).isCanonicalPart renamed := by
  have parts2 : (held.factsAt facts (day 2)).establishedParts 1 .other = [sibling, old] :=
    by decide +kernel
  have parts6 : (held.factsAt facts (day 6)).establishedParts 1 .other = [sibling, resized] :=
    by decide +kernel
  have parts8 : (held.factsAt facts (day 8)).establishedParts 1 .other = [sibling, renamed] :=
    by decide +kernel
  simp only [HoldFacts.isCanonicalPart, show old.ref.lesson = 1 from rfl,
    show old.ref.purpose = .other from rfl, show resized.ref.lesson = 1 from rfl,
    show resized.ref.purpose = .other from rfl, show renamed.ref.lesson = 1 from rfl,
    show renamed.ref.purpose = .other from rfl, parts2, parts6, parts8]
  simp [old, resized, renamed, sibling] <;> decide +kernel

private theorem reviewerMayHold (c : ReviewMatter) (atTime : Moment) :
    authority.mayImposeOrLift c 90 atTime := by
  simp [ReviewAuthorities.mayImposeOrLift, ReviewAuthorities.disinterested, authority,
    DirectInterest.affected]

private theorem reviewerIsNotApprover (h : HoldHistory) (sameApprovals : h.approvals = held.approvals)
    (ref : PaymentPartRef) (atTime : Moment) :
    ¬h.originallyApprovedBy authority ref 90 atTime := by
  rintro ⟨approval, recorded, actor, _⟩
  rw [sameApprovals] at recorded
  simp [held] at recorded
  rcases recorded with rfl | rfl | rfl | rfl <;> contradiction

private theorem validHoldFor (h : HoldHistory) (hold : FormalHold) (part : PaymentPart)
    (recorded : hold ∈ h.formal) (approvals : h.approvals = held.approvals)
    (noTemp : h.temporary = [])
    (noOriginals : h.originalSettlements = [])
    (actor : hold.imposedBy = 90) (scope : hold.portions = [part])
    (effective : hold.decidedAt.by hold.effectiveAt) (sameLesson : part.ref.lesson = hold.matter.lesson)
    (payment : hold.subject = .payment)
    (unpaid : 0 < h.remainingPortionBefore part hold.effectiveAt)
    (canonical : (h.factsAt facts hold.effectiveAt).isCanonicalPart part) :
    h.validFormalHold authority facts hold := by
  refine ⟨recorded, ⟨?_, effective, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [actor]
    exact reviewerMayHold _ _
  · simp [scope]
  · intro row member
    have same : row = part := by simpa [scope] using member
    subst row
    exact ⟨sameLesson, canonical, unpaid⟩
  · simp [HoldHistory.factsAt, facts]
  · rw [payment]
    simp [scope, HoldHistory.factsAt, facts]
  · intro row _
    rw [actor]
    exact reviewerIsNotApprover h approvals row.ref hold.decidedAt
  · simp [HoldHistory.notTemporarySetter, noTemp]
  · simp [HoldHistory.originalSettlementActor, noOriginals]

private theorem firstValid : held.validFormalHold authority facts first := by
  exact validHoldFor held first old (by simp [held]) rfl rfl rfl rfl rfl
    (by decide +kernel) rfl rfl (by decide +kernel) exactVersionsAtTheirActualTimes.1

private theorem secondValid : held.validFormalHold authority facts second := by
  exact validHoldFor held second resized (by simp [held]) rfl rfl rfl rfl rfl
    (by decide +kernel) rfl rfl (by decide +kernel) exactVersionsAtTheirActualTimes.2.2.1

private theorem validLiftByReviewer (hold : FormalHold) (lift : FormalLift)
    (allowed : lift.mayLift authority hold) (actor : lift.decidedBy = 90) :
    held.validLift authority facts hold lift := by
  refine ⟨allowed, ?_, ?_, ?_⟩
  · intro part _ _
    rw [actor]
    exact reviewerIsNotApprover held rfl part.ref lift.decidedAt
  · simp [HoldHistory.originalSettlementActor, held]
  · simp [HoldHistory.notTemporarySetter, held]

private theorem firstLiftValid : held.validLift authority facts first firstLift := by
  apply validLiftByReviewer _ _ _ rfl
  exact ⟨rfl, reviewerMayHold _ _, by decide +kernel, by decide +kernel, by decide +kernel,
    by simp [firstLift, first, FormalHold.covers]⟩

private theorem secondLiftValid : held.validLift authority facts second secondLift := by
  exact validLiftByReviewer _ _
    ⟨rfl, reviewerMayHold _ _, by decide +kernel, by decide +kernel, by decide +kernel,
      trivial⟩ rfl

private theorem beforeExcludesOtherBy {a b : Moment} (before : a.before b) (other : b.by a) :
    False := by
  rcases other with other | rfl
  · unfold Moment.before at *
    omega
  · unfold Moment.before at before
    omega

private theorem firstHeld (time : Moment) (starts : (day 2).by time) (before : time.before (day 8))
    (through : Moment)
    (mapped : through = day 7 ∨ through = day 11) :
    held.formalInForce authority facts first renamed.ref time through := by
  refine ⟨firstValid, starts, old, by simp [first], ?_, ?_⟩
  · rcases mapped with rfl | rfl <;> decide +kernel
  · rintro ⟨lift, recorded, legal, _, effective⟩
    have chose : lift = firstLift ∨ lift = secondLift := by simpa [held] using recorded
    rcases chose with rfl | rfl
    · exact beforeExcludesOtherBy before effective
    · have impossible : secondLift.hold = first.id := legal.1.1
      contradiction

private theorem secondHeld (time : Moment) (starts : (day 6).by time) (before : time.before (day 10)) :
    held.formalInForce authority facts second renamed.ref time (day 11) := by
  refine ⟨secondValid, starts, resized, by simp [second], by decide +kernel, ?_⟩
  rintro ⟨lift, recorded, legal, _, effective⟩
  have chose : lift = firstLift ∨ lift = secondLift := by simpa [held] using recorded
  rcases chose with rfl | rfl
  · have impossible : firstLift.hold = second.id := legal.1.1
    contradiction
  · exact beforeExcludesOtherBy before effective

theorem firstHoldStillBlocksTheRenamedPart :
    held.formalInForce authority facts first renamed.ref (day 7) ∧
    ¬Operations.PaymentApprovalRoute.allows (.ordinary ordinaryApproval) authority facts held
      renamed schedule (fun _ ↦ True) (instruction renamed (day 7)) := by
  have active : held.formalInForce authority facts first renamed.ref (day 7) :=
    firstHeld (day 7) (by decide +kernel) (by decide +kernel) (day 7) (Or.inl rfl)
  refine ⟨active, ?_⟩
  intro permit
  rcases permit with ⟨_, _, _, _, _, _, _, _, _, _, clear, _, _⟩
  exact clear (Or.inl ⟨first, active⟩)

private theorem noActiveDecision
    {hold : FormalHold} (valid : held.validFormalHold authority facts hold)
    {part : PaymentPart} (source : part ∈ hold.portions) (time : Moment)
    (after : time = day 10 ∨ time = day 11) :
    ∃ lift ∈ held.lifts, held.validLift authority facts hold lift ∧
      lift.covers part.ref ∧ lift.effectiveAt.by time := by
  have selected : hold = first ∨ hold = second := by simpa [held] using valid.1
  rcases selected with rfl | rfl
  · have : part = old := by simpa [first] using source
    subst part
    exact ⟨firstLift, by simp [held], firstLiftValid, by simp [firstLift, FormalLift.covers],
      by rcases after with rfl | rfl <;> decide +kernel⟩
  · exact ⟨secondLift, by simp [held], secondLiftValid, trivial,
      by rcases after with rfl | rfl <;> decide +kernel⟩

private theorem clearAfterBothLifts (time : Moment) (after : time = day 10 ∨ time = day 11) :
    ¬held.paymentOnHold authority facts renamed.ref time (day 11) ∧
    ¬held.paymentHoldScopeUnresolved authority facts renamed.ref time (day 11) := by
  constructor
  · rintro (⟨hold, valid, _, part, source, _, absent⟩ | ⟨temp, present, _⟩)
    · exact absent (noActiveDecision valid source time after)
    · simp [held] at present
  · rintro (⟨hold, valid, _, part, source, _, absent⟩ | ⟨temp, present, _⟩)
    · exact absent (noActiveDecision valid source time after)
    · simp [held] at present

private theorem continuousFromFive :
    held.firstUnheldFrom authority facts renamed.ref (day 5) (day 10) (day 11) := by
  have clearAtTen := clearAfterBothLifts (day 10) (Or.inl rfl)
  refine ⟨by decide +kernel, clearAtTen.1, clearAtTen.2, ?_⟩
  intro time afterFive beforeTen
  have afterFiveSeconds : 5 ≤ time.seconds := by
    rcases afterFive with after | rfl
    · simp only [Moment.before, day] at after
      omega
    · decide
  by_cases beforeEight : time.before (day 8)
  · have starts : (day 2).by time := Or.inl (Or.inl (by simpa [day] using
      (show 2 < time.seconds by omega)))
    exact Or.inl ⟨first, firstHeld time starts beforeEight (day 11) (Or.inr rfl)⟩
  · have afterEightSeconds : 8 ≤ time.seconds := by
      have noEarlier : ¬time.seconds < 8 := fun earlier ↦ beforeEight (Or.inl earlier)
      omega
    have starts : (day 6).by time := Or.inl (Or.inl (by simpa [day] using
      (show 6 < time.seconds by omega)))
    exact Or.inl ⟨second, secondHeld time starts beforeTen⟩

theorem onlyFinalLiftOpensTheOriginalWindow :
    ¬postLiftWindowOpened authority facts held renamed windowSchedule (day 8) (day 11) ∧
    postLiftWindowOpened authority facts held renamed windowSchedule (day 10) (day 11) := by
  constructor
  · intro window
    obtain ⟨_, _, _, _, clear, _, _⟩ := window.2.1
    exact clear (Or.inl ⟨second, secondHeld (day 8) (by decide +kernel) (by decide +kernel)⟩)
  · have heldAtDeadline :=
      firstHeld (day 5) (by decide +kernel) (by decide +kernel) (day 11) (Or.inr rfl)
    have clearAtTen := clearAfterBothLifts (day 10) (Or.inl rfl)
    refine ⟨?_, ?_, ⟨first, heldAtDeadline⟩, by decide +kernel,
      by decide +kernel, continuousFromFive, trivial⟩
    · have same :
          (held.factsAt facts (day 11)).establishedParts 1 .other = [sibling, renamed] :=
        by decide +kernel
      simp [HoldFacts.isCanonicalPart, renamed, resized, old, same]
      decide +kernel
    · refine ⟨second, secondLift, ?_, by simpa [secondLift] using
        (show held.firstUnheldFrom authority facts renamed.ref (day 10) (day 10) (day 11) from
          ⟨Or.inr rfl, clearAtTen.1, clearAtTen.2, fun time atTen beforeTen ↦
            False.elim (beforeExcludesOtherBy beforeTen atTen)⟩)⟩
      refine ⟨secondValid, by simp [held], secondLiftValid, ?_, resized,
        by simp [second], by decide +kernel, trivial, ?_⟩
      · unfold HoldHistory.distinctFormalDecisions
        decide +kernel
      rintro ⟨lift, recorded, legal, _, earlier⟩
      have chose : lift = firstLift ∨ lift = secondLift := by simpa [held] using recorded
      rcases chose with rfl | rfl
      · have impossible : firstLift.hold = second.id := legal.1.1
        contradiction
      · exact beforeExcludesOtherBy earlier (Or.inr rfl)

theorem changedReferenceUsesNewApprovalAfterThatLift :
    Operations.PaymentApprovalRoute.allows (.liftReplacement originalApproval replacement (day 10))
      authority facts held renamed windowSchedule (fun _ ↦ True) (instruction renamed (day 11)) ∧
    ¬Operations.PaymentApprovalRoute.allows (.liftOriginal originalApproval (day 10))
      authority facts held renamed windowSchedule (fun _ ↦ True) (instruction renamed (day 11)) := by
  have clear := clearAfterBothLifts (day 11) (Or.inr rfl)
  have notCovered : ¬held.approvalCovers originalApproval renamed (instruction renamed (day 11)) := by
    change ¬originalApproval.covers held.payments renamed (instruction renamed (day 11))
    rintro ⟨entry, entered, sameRef, _⟩
    have : entry = ⟨old.ref, .person 80, 60, none⟩ := by simpa [originalApproval] using entered
    subst entry
    exact (by decide +kernel : old.ref ≠ renamed.ref) sameRef
  have amounts : held.payments.validOutstandingPayment renamed (instruction renamed (day 11)) :=
    ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel,
      by simp [PaymentHistory.distinctReceipts, held], by simp [PaymentHistory.validReturns, held]⟩
  have conditions : postLiftPaymentConditions authority facts held renamed windowSchedule (day 10)
      (instruction renamed (day 11)) :=
    ⟨⟨onlyFinalLiftOpensTheOriginalWindow.2, by decide +kernel,
        by change (day 11).by (day 14); decide +kernel,
        by decide +kernel⟩, amounts, clear.1, clear.2, by decide +kernel⟩
  have ids : (held.approvals.map PaymentApproval.id).Nodup := by
    simp [held, originalApproval, replacement, siblingApproval, ordinaryApproval]
  refine ⟨⟨conditions, ⟨by simp [held], ids⟩, ⟨by simp [held], ids⟩, ?_, ?_,
    by decide +kernel, Or.inr notCovered, by decide +kernel, by decide +kernel, ?_, ?_,
    ?_, rfl, trivial⟩, ?_⟩
  · simp [PaymentApproval.authorisedAtGrant, originalApproval, authority]
  · change originalApproval.originallyCovered old
    exact ⟨⟨old.ref, .person 80, 60, none⟩, by simp [originalApproval], rfl,
      by decide +kernel, by decide +kernel, by simp⟩
  · simp [PaymentApproval.authorisedAtGrant, replacement, authority]
  · simp [PaymentApproval.validAt, replacement, instruction, day, Moment.by, Moment.before]
  · exact ⟨⟨renamed.ref, .person 80, 35, none⟩, by simp [replacement], rfl, rfl,
      by simp, by decide +kernel⟩
  · intro permit
    exact notCovered permit.2.2.2.2.2.2.1

private def pendingScope : HoldHistory :=
  { held with formal := [first], lifts := [firstLift], partRevisions := [resize, increase] }

private theorem pendingOldCanonical :
    (pendingScope.factsAt facts (day 2)).isCanonicalPart old := by
  have same : (pendingScope.factsAt facts (day 2)).establishedParts 1 .other = [sibling, old] :=
    by decide +kernel
  simp only [HoldFacts.isCanonicalPart, show old.ref.lesson = 1 from rfl,
    show old.ref.purpose = .other from rfl, same]
  simp [old, sibling, renamed, resized] <;> decide +kernel

theorem largerUnsplitAmountRequiresScopeResolution :
    pendingScope.paymentHoldScopeUnresolved authority facts increased.ref (day 7) ∧
    ¬Operations.PaymentApprovalRoute.allows (.ordinary ordinaryApproval)
      authority facts pendingScope increased schedule (fun _ ↦ True)
      { instruction increased (day 7) with amount := 35 } := by
  have valid : pendingScope.validFormalHold authority facts first :=
    validHoldFor pendingScope first old (by simp [pendingScope]) rfl rfl rfl rfl rfl
      (by decide +kernel) rfl rfl (by decide +kernel) pendingOldCanonical
  have unresolved : pendingScope.paymentHoldScopeUnresolved authority facts increased.ref (day 7) :=
    Or.inl ⟨first, valid, by decide +kernel, old, by simp [first], by decide +kernel, by
      rintro ⟨lift, member, _, _, after⟩
      have : lift = firstLift := by simpa [pendingScope] using member
      subst lift
      exact (by decide +kernel : ¬firstLift.effectiveAt.by (day 7)) after⟩
  refine ⟨unresolved, ?_⟩
  intro permit
  rcases permit with ⟨_, _, _, _, _, _, _, _, _, _, _, clear, _⟩
  exact clear unresolved

theorem anUnaffectedSiblingCanExecute :
    Operations.PaymentApprovalRoute.allows (.ordinary siblingApproval) authority facts held
      sibling schedule (fun _ ↦ True) (instruction sibling (day 7)) := by
  have out : ¬held.paymentOnHold authority facts sibling.ref (day 7) := by
    rintro (⟨hold, legal, _, part, source, relation, _⟩ | ⟨_, recorded, _⟩)
    · have relevant : hold = first ∨ hold = second := by simpa [held] using legal.1
      rcases relevant with rfl | rfl
      · have : part = old := by simpa [first] using source
        subst part
        exact (by decide +kernel : renamed.ref ≠ sibling.ref) relation.1
      · have : part = resized := by simpa [second] using source
        subst part
        exact (by decide +kernel : renamed.ref ≠ sibling.ref) relation.1
    · simp [held] at recorded
  have certain : ¬held.paymentHoldScopeUnresolved authority facts sibling.ref (day 7) := by
    rintro (⟨hold, legal, _, part, source, relation, _⟩ | ⟨_, recorded, _⟩)
    · have relevant : hold = first ∨ hold = second := by simpa [held] using legal.1
      rcases relevant with rfl | rfl
      · have : part = old := by simpa [first] using source
        subst part
        exact (by decide +kernel : renamed.ref ≠ sibling.ref) relation.1
      · have : part = resized := by simpa [second] using source
        subst part
        exact (by decide +kernel : renamed.ref ≠ sibling.ref) relation.1
    · simp [held] at recorded
  have canonical : (held.factsAt facts (day 7)).isCanonicalPart sibling := by
    have same : (held.factsAt facts (day 7)).establishedParts 1 .other = [sibling, renamed] :=
      by decide +kernel
    simp only [HoldFacts.isCanonicalPart, show sibling.ref.lesson = 1 from rfl,
      show sibling.ref.purpose = .other from rfl, same]
    simp [sibling, renamed, resized, old] <;> decide +kernel
  refine ⟨canonical, ?_, ?_, ?_, ?_, rfl, ?_, trivial, by decide +kernel, ?_, out, certain,
    by decide +kernel⟩
  · exact ⟨by simp [held], by
      simp [held, originalApproval, replacement, siblingApproval, ordinaryApproval]⟩
  · simp [PaymentApproval.authorisedAtGrant, siblingApproval, authority]
  · simp [PaymentApproval.validAt, siblingApproval, instruction, day, Moment.by, Moment.before]
  · refine ⟨⟨sibling.ref, .person 80, 20, none⟩, by simp [siblingApproval], rfl, rfl, by simp, ?_⟩
    decide +kernel
  · exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel,
      by simp [PaymentHistory.distinctReceipts, held], by simp [PaymentHistory.validReturns, held]⟩
  · simp [HoldHistory.distinctFormalDecisions, held, first, second]

private def temporaryHistory : HoldHistory := { held with temporary := [temporary], formal := [] }

theorem oldTemporaryHoldExpiresAtItsRecordedCutoff :
    temporaryHistory.paymentOnHold authority facts renamed.ref (day 8) ∧
    ¬temporaryHistory.paymentOnHold authority facts renamed.ref (day 9) := by
  have valid : temporary.maySetAside authority
      (temporaryHistory.factsAt facts temporary.effectiveAt) temporaryHistory.payments := by
    have original : (temporaryHistory.factsAt facts temporary.effectiveAt).isCanonicalPart old :=
      exactVersionsAtTheirActualTimes.1
    refine ⟨trivial, rfl, original, rfl, rfl, by decide +kernel, trivial, trivial,
      by simp [ReviewAuthorities.disinterested, authority, DirectInterest.affected], trivial,
      by decide +kernel, ⟨rfl, rfl⟩, trivial, by simp [HoldHistory.factsAt, facts],
      by decide +kernel, by decide +kernel⟩
  refine ⟨Or.inr ⟨temporary, by simp [temporaryHistory], valid, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · rintro ⟨_, _, impossible, _⟩
    simp [HoldHistory.validFormalHold, temporaryHistory] at impossible
  · rintro (⟨_, impossible, _⟩ | ⟨temp, recorded, _, _, _, before, _⟩)
    · simp [HoldHistory.validFormalHold, temporaryHistory] at impossible
    · have : temp = temporary := by simpa [temporaryHistory] using recorded
      subst temp
      exact (by decide +kernel : ¬(day 9).before terms.temporaryHoldExpiry) before

private def receipt : PostedPayment := ⟨20, instruction renamed (day 7), some 200⟩
private def withReceipt : HoldHistory :=
  { held with payments := { held.payments with posted := [receipt] } }

theorem observedTransferCanEnterTheRootLedgerDuringAnEffectiveHold
    (state : Workflow.State) (before : state.holds = held) :
    Workflow.Step state (.payment (.post receipt))
      { state.withHolds withReceipt with paymentRecords := state.paymentRecords ++ [.post receipt] } ∧
    withReceipt.payments.actualPaymentWithEvidence receipt := by
  constructor
  · apply Workflow.Step.payment
    · trivial
    · rw [before]
      exact Workflow.Payment.Step.post receipt (by decide +kernel) (by simp [held])
  · exact ⟨by simp [withReceipt], rfl⟩

private def branch : HoldPartRevision :=
  { rename with
    corrected := { renamed with ref := { renamed.ref with portion := 6 } }
    correctedOutcome := 4
    adoptedAt := day 8
    recordedAt := day 8 }

private def conflicting : HoldHistory := { held with partRevisions := [resize, rename, branch] }

theorem competingAdoptedSuccessorsDoNotAuthoriseEitherReference :
    (conflicting.factsAt facts (day 8)).establishedParts 1 .other = [sibling] ∧
    ¬(conflicting.factsAt facts (day 8)).isCanonicalPart renamed ∧
    ¬(conflicting.factsAt facts (day 8)).isCanonicalPart branch.corrected := by
  have parts : (conflicting.factsAt facts (day 8)).establishedParts 1 .other = [sibling] :=
    by decide +kernel
  refine ⟨parts, ?_, ?_⟩
  · intro canonical
    have member : renamed ∈ [sibling] := by
      simpa only [show renamed.ref.lesson = 1 from rfl,
        show renamed.ref.purpose = .other from rfl, parts] using canonical.1
    exact (by decide +kernel : renamed ∉ [sibling]) member
  · intro canonical
    have member : branch.corrected ∈ [sibling] := by
      simpa only [show branch.corrected.ref.lesson = 1 from rfl,
        show branch.corrected.ref.purpose = .other from rfl, parts] using canonical.1
    exact (by decide +kernel : branch.corrected ∉ [sibling]) member

private def earlierReceipt (payee : ActorId) : PostedPayment :=
  ⟨19, { instruction old (day 3) with destination := .person payee, amount := 30 }, some 201⟩
private def laterReceipt : PostedPayment :=
  ⟨22, { instruction renamed (day 8) with amount := 5 }, some 202⟩
private def completionHistory (payee : ActorId) : HoldHistory :=
  { held with payments := ⟨[earlierReceipt payee, laterReceipt], [], []⟩ }

theorem completionCountsAnEarlierReferenceOnlyForTheCorrectPayee :
    (completionHistory 80).fullyRetainedPortionBy renamed (.exact (day 8)) (day 8) ∧
    ¬(completionHistory 81).fullyRetainedPortionBy renamed (.exact (day 8)) (day 8) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · simp [PaymentHistory.distinctReceipts, completionHistory, earlierReceipt, laterReceipt]
    · simp [PaymentHistory.validReturns, completionHistory, sumAmounts] <;> decide +kernel
    · unfold ClockCutoff.forEveryOrder
      decide +kernel
  · intro completed
    have wronglyCounted := completed.2.2
    unfold ClockCutoff.forEveryOrder at wronglyCounted
    exact of_decide_eq_false (by decide +kernel) wronglyCounted

private def currentPayee : PaymentPart := { old with recipient := .person 81 (some 80) }
private def currentPayeeApproval : PaymentApproval :=
  { originalApproval with id := 19, grantedAt := day 6 }
private def changedPayeeHistory : HoldHistory :=
  { held with
    formal := []
    lifts := []
    partRevisions := [{ resize with corrected := currentPayee }]
    approvals := [originalApproval, currentPayeeApproval] }

theorem aSharedDestinationCannotCarryAnOldApprovalToANewPayee :
    originalApproval.covers changedPayeeHistory.payments currentPayee
      (instruction currentPayee (day 7)) ∧
    ¬changedPayeeHistory.approvalCovers originalApproval currentPayee
      (instruction currentPayee (day 7)) ∧
    changedPayeeHistory.approvalCovers currentPayeeApproval currentPayee
      (instruction currentPayee (day 7)) := by
  refine ⟨?_, by change ¬False; simp, ?_⟩
  · exact ⟨⟨old.ref, .person 80, 60, none⟩, by simp [originalApproval], rfl, rfl,
      by simp, by decide +kernel⟩
  · exact ⟨⟨old.ref, .person 80, 60, none⟩, by simp [currentPayeeApproval, originalApproval],
      rfl, rfl, by simp, by decide +kernel⟩

#print axioms rootAdoptionRetainsExactPriorAndCurrent
#print axioms exactVersionsAtTheirActualTimes
#print axioms firstHoldStillBlocksTheRenamedPart
#print axioms onlyFinalLiftOpensTheOriginalWindow
#print axioms changedReferenceUsesNewApprovalAfterThatLift
#print axioms largerUnsplitAmountRequiresScopeResolution
#print axioms anUnaffectedSiblingCanExecute
#print axioms oldTemporaryHoldExpiresAtItsRecordedCutoff
#print axioms observedTransferCanEnterTheRootLedgerDuringAnEffectiveHold
#print axioms competingAdoptedSuccessorsDoNotAuthoriseEitherReference
#print axioms completionCountsAnEarlierReferenceOnlyForTheCorrectPayee
#print axioms aSharedDestinationCannotCarryAnOldApprovalToANewPayee

end SourceV14.FidelityHoldCorrectionChecks
