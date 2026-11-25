import PendingProjection
import TNormal

namespace SparkJoint
open SourceV14 SourceV14.Workflow
open JointT (form lesson place)

def pendingMatter : ReviewMatter := ⟨902, lesson.id, [101, 102, 20]⟩

def pendingTerms : ReviewTerms :=
  ⟨30, 41, 31, .exact (tick 70), tick 72, tick 65, tick 66, 50⟩

def published : Workflow.Review.PublishedContacts :=
  ⟨lesson.id, ⟨.policy, 10, 30, "Spark coordinator", 41, "Spark alternative"⟩, tick 34⟩

def intake : Workflow.Review.Intake :=
  ⟨lesson, pendingTerms, some form, published,
    ⟨pendingMatter, place.student, .student place .service, 30, tick 35⟩⟩

def authority : ReviewAuthorities where
  corePartner := fun actor time ↦ actor = 90 ∧ (tick 28).by time
  initialFinding := fun _ _ _ ↦ False
  reviewer := fun _ _ _ ↦ False
  approvesPayment := fun _ _ _ ↦ False
  interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
  originalDecisionMaker := fun _ ↦ none
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

def pendingReviewEvidence : Workflow.Review.Evidence where
  authority
  holds :=
    { terms := fun _ ↦ pendingTerms
      termsApply := (· = pendingMatter)
      acceptedPaymentConcern := fun _ _ _ _ ↦ False
      reviewerCannotActInTime := fun _ _ ↦ False
      temporaryAuthority := fun _ _ _ _ ↦ False
      allegedFactsWouldChangePayment := fun _ _ _ ↦ False
      separatelyIdentifiable := fun _ _ ↦ False
      establishedParts := fun _ _ ↦ []
      paymentAffected := fun _ _ ↦ False
      decisionPending := fun _ _ _ ↦ False
      partFallsUnderDecision := fun _ _ _ ↦ False
      decisionConcernsWholeGroup := fun _ _ ↦ False
      isGroupLesson := fun _ ↦ False
      affectsWholeSettlement := fun _ ↦ False
      groupSettlementParts := fun _ ↦ [] }
  concernFacts :=
    { effectivePlace := fun p time ↦ p = place ∧ time = tick 35
      tutorAffected := fun _ _ ↦ False
      relevantShareClaimantAffected := fun _ _ ↦ False
      believesUseOmitted := fun _ _ ↦ False
      relevantContributor := fun _ _ ↦ False
      coordinatorUnreachable := fun _ _ ↦ False
      coordinatorPersonallyInterested := fun _ _ ↦ False
      complaintAboutCoordinator := fun _ ↦ False }
  publishedTerms := fun _ _ _ ↦ False
  replyTrigger := fun _ _ ↦ none
  verifiedReplyTrigger := fun _ _ ↦ False
  replyLegalDeadline := fun _ ↦ none
  verifiedFactCheck := fun _ ↦ False
  originalOutcome := fun _ ↦ False
  recordedAmount := fun _ _ _ ↦ False

def publishEvent : Event :=
  .review pendingReviewEvidence (.publishContacts lesson pendingTerms published)

def intakeEvent : Event := .review pendingReviewEvidence (.receive intake)

def afterPublication (s : State) : State :=
  { s with review := { s.review with publications := s.review.publications ++ [published] } }

def pending (s : State) : State :=
  { afterPublication s with
    review := { (afterPublication s).review with intakes := s.review.intakes ++ [intake] } }

theorem pendingIntake {s : State}
    (fresh : s.review = Workflow.Review.History.empty)
    (retains : form ∈ (s.course lesson.id).effectiveForms) :
    RecognisedV15.Workflow.Path Step s [publishEvent, intakeEvent] (pending s) := by
  refine .next (m := afterPublication s) ?_ (.next ?_ (.nil _))
  · refine .review trivial ?_ ?_ ?_
    · simp [Workflow.Review.Event.readsMaterialsTerms]
    · intro row h
      cases h
    · refine .publishContacts _ _ _ rfl ?_ ?_
      · exact ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩
      · simp [fresh, Workflow.Review.History.empty]
  · refine .review trivial ?_ ?_ ?_
    · simp [Workflow.Review.Event.readsMaterialsTerms]
    · intro row h
      cases h
    · refine .receive intake ?_ ⟨rfl, by decide⟩ ?_ ?_ ?_
      · simp [afterPublication, intake]
      · refine ⟨⟨rfl, JointT.formMatches, by decide, Or.inl retains⟩, ?_, rfl⟩
        refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
        intro deadline equal
        cases equal
        rfl
      · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩, ⟨rfl, ⟨rfl, rfl⟩, rfl⟩, Or.inl rfl⟩
      · simp [afterPublication, fresh, Workflow.Review.History.empty]

/-- These are the three signed observations for this fixture. Neither
a request to investigate the missing teaching item nor its intake is a finding. -/
structure PartialReceiptRecord where
  lesson : LessonId
  place : PlaceId
  itemReceived : Nat
  studentStatement : EvidenceRef
  sessionRecord : EvidenceRef

structure ProviderCheckRecord where
  lesson : LessonId
  place : PlaceId
  scheduleAndAccess : EvidenceRef
  deliveryNotice : EvidenceRef
  neutralVerifier : ActorId
  checkedAt : Moment

def partialReceipt : PartialReceiptRecord := ⟨100, 1, 1, 1171, 1172⟩
def providerCheck : ProviderCheckRecord := ⟨100, 1, 1173, 1174, 31, tick 41⟩

/-- This certificate records the verification of facts, independently of
deciding whether the tutor breached the agreed teaching scope. -/
def checkedPartialReceipt (s : State) (receipt : PartialReceiptRecord) : Prop :=
  intake ∈ s.review.intakes ∧
  s.review.initialFindings = [] ∧ s.review.reviewFindings = [] ∧
  (s.course lesson.id).teachingBegan = some (tick 32) ∧
  (s.course lesson.id).teachingEnded = some (tick 33) ∧
  receipt = partialReceipt

def checkedPending (s : State) (receipt : PartialReceiptRecord) (check : ProviderCheckRecord) :
    Prop :=
  checkedPartialReceipt s receipt ∧ check = providerCheck ∧
  authority.disinterested pendingMatter check.neutralVerifier check.checkedAt

def pendingRelease := release 4 (tick 41) 1175

def verifiesPendingRelease (s : State) (r : Reserves.Release) : Prop :=
  r = pendingRelease ∧ checkedPending s partialReceipt providerCheck ∧
    ∀ sc : FundingCase, sc.possible JointT.fundingTerms lesson [place] →
      sc.facts .teachingBegan = true → sc.facts JointT.providerAtFault = false →
      sc.remainingCost JointT.fundingTerms pendingCut ≤ 10 - r.amount

theorem releaseWhileTutorDecisionOpen {s : State}
    (openCase : checkedPending s partialReceipt providerCheck)
    (reserves : s.activeReserves = [mInitial, tInitial]) :
    Step s (.reserveReleased pendingRelease (verifiesPendingRelease s))
      {s with activeReserves := [mInitial, tAt 6]} := by
  have h : (10 - (4 : Amount)) = 6 := by decide +kernel
  rw [← h]
  refine releaseUpdates (first := [mInitial]) (last := []) reserves rfl ?_ ?_
  · unfold pendingRelease release Reserves.Release.matches
    decide +kernel
  · refine ⟨rfl, openCase, ?_⟩
    rw [show pendingRelease.amount = 4 from rfl, h]
    exact fun _ possible teaching provider ↦ pendingCap possible teaching provider

def teachingOnlyRelease := release 2 (tick 41) 1176

def verifiesTeachingOnlyRelease (s : State) (r : Reserves.Release) : Prop :=
  r = teachingOnlyRelease ∧ checkedPartialReceipt s partialReceipt ∧
    ∀ sc : FundingCase, sc.possible JointT.fundingTerms lesson [place] →
      sc.facts .teachingBegan = true →
      sc.remainingCost JointT.fundingTerms pendingCut ≤ 10 - r.amount

theorem releaseAfterTeachingOnly {s : State}
    (verified : checkedPartialReceipt s partialReceipt)
    (reserves : s.activeReserves = [mInitial, tInitial]) :
    Step s (.reserveReleased teachingOnlyRelease (verifiesTeachingOnlyRelease s))
      {s with activeReserves := [mInitial, tAt 8]} := by
  have h : (10 - (2 : Amount)) = 8 := by decide +kernel
  rw [← h]
  refine releaseUpdates (first := [mInitial]) (last := []) reserves rfl ?_ ?_
  · unfold teachingOnlyRelease release Reserves.Release.matches
    decide +kernel
  · refine ⟨rfl, verified, ?_⟩
    rw [show teachingOnlyRelease.amount = 2 from rfl, h]
    exact fun _ possible teaching ↦ teachingCapEight possible teaching

end SparkJoint
