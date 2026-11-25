import TransferEligibility
import JointHistory

/-! Root events of a constructed case. Opening records supply both identified uses,
the earlier paid amount and a separate due wage. The input that maps contingent financial
exposure to a review authority is varied independently below to test the native boundary. -/

namespace TransferCase

open SourceV14 SourceV14.Workflow
open SourceV14.Confirmation

abbrev DirectPath := RecognisedV15.Workflow.Path SourceV14.Workflow.Step
abbrev RecognisedPath := RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step

def firstUse : Task → Moment | .teaching => tick 32 | .oldReview => tick 10
def endOfClass : Task → Moment | .teaching => tick 33 | .oldReview => tick 11
def checkedUse : Task → Moment | .teaching => tick 34 | .oldReview => tick 12
def usePlace (q : Task) : Place := ⟨seat, lessonId q, 101, 102, 102, 103, 500, 500⟩
def finding (q : Task) : ConfirmedMaterialUse :=
  ⟨lessonId q, seat, mat, 1, firstUse q, (lesson q).coordinator, checkedUse q,
    .lessonRecord (ref q)⟩

def useCheck (q : Task) : Materials.UseCheck where
  use :=
    { lesson := lesson q
      startedAt := firstUse q
      endedAt := endOfClass q
      tutorReport := none
      authority := ⟨authority .retain, fun _ ↦ matter q, fun _ ↦ none⟩
      places := [usePlace q]
      deliveryReports := []
      findings := [finding q]
      verifiesEvidence := (· = finding q)
      verifiedReportOmission := fun _ ↦ False
      uniquePlaces := by simp
      placeInLesson := by simp [Place.matches, usePlace, lesson]
      findingInLesson := by simp [finding, lesson]
      findingAtPlace := by simp [finding, usePlace] }
  terms := agreement q
  advanceCheck := none
  checkedAt := checkedUse q

theorem separateUseChecks (q : Task) :
    (useCheck q).use.verifiedBy (checkedUse q) ∧
    (useCheck q).use.firstConfirmedUse mat = some (firstUse q) := by
  cases q <;>
    simp [VerifiedMaterialsUse.verifiedBy, VerifiedMaterialsUse.firstConfirmedUse, useCheck,
      finding, MaterialsUseAuthority.mayCheck, ReviewAuthorities.disinterested, DirectInterest.affected,
      authority, interest, delta, allocation, MaterialsAllocation.portion, signedRow, sole, lesson,
      lessonId, matter, mat, seat, ref, who, usePlace, firstUse, endOfClass, checkedUse,
      Moment.by, Moment.before, tick, MaterialUseEvidence.reference]

def originalMaterial : Materials.Settlement :=
  ⟨⟨lessonId .oldReview, mat, (agreement .oldReview).agreementReference, ref .oldReview, 501, tick 20,
    [seat], [⟨seat, mat, 50⟩]⟩, useCheck .oldReview⟩

def oldPart : PaymentPart :=
  ⟨oldReceipt.instruction.part, .person (who .O) none, oldReceipt.instruction.amount⟩

def originalDecision : Review.OriginalRecord :=
  ⟨⟨matter .oldReview, 1400, 77, tick 20⟩, some oldPart⟩

def wageDecision : Review.OriginalRecord := ⟨⟨⟨890, 89, [81]⟩, 1480, 78, tick 23⟩, some wage⟩

/-- Both actual-use checks and the historical settlement, receipt and mature liability are
supplied in the opening state. Their production predates the proved path. -/
def teachingForm : PartOne :=
  { JointT.form with place := usePlace .teaching
                     materialsOrBundle := some (agreement .teaching).materialsOrBundle
                     materialsTermsRef := some (agreement .teaching).agreementReference
                     materialsPayer := some (agreement .teaching).accountingAndPaymentParty }

def holds0 : HoldHistory := ⟨openingPayments, [], [], [], [], [], [], [], []⟩

def opening : State :=
  let other := SparkJoint.commonStart
  let file := fun q ↦ { other.lessons (lessonId q) with
    effectiveForms := if q = .teaching then [teachingForm] else []
    bookings := []
    teachingBegan := some (firstUse q)
    teachingEnded := some (endOfClass q) }
  { other.withHolds holds0 with
    lessons := fun lid ↦ if lid = lessonId .teaching then file .teaching
      else if lid = lessonId .oldReview then file .oldReview else other.lessons lid
    materials := { terms := [agreement .oldReview, agreement .teaching]
                   useChecks := [useCheck .oldReview, useCheck .teaching]
                   originals := [originalMaterial] }
    review := { Review.History.empty with originals := [originalDecision, wageDecision]
                                          initialFindings := [priorFinding] }
    activeReserves := [⟨10, lessonId .oldReview, 1, 50⟩, ⟨10, 89, 1, 80⟩]
    paymentRecords := [.post oldReceipt] }

def publication : Review.PublishedContacts :=
  ⟨lessonId .oldReview, ⟨.materialsTerms, 10, 30, "coordinator", 41, "alternative"⟩, tick 35⟩
def intake : Review.Intake :=
  ⟨lesson .oldReview, terms, none, publication,
    ⟨matter .oldReview, who .O, .share, 30, tick 36⟩⟩
def trigger : ConcernAppointmentTrigger :=
  ⟨matter .oldReview, .partyRequestedReview (who .O), tick 37, 1900⟩

/-- Qualification is an evidence argument to the native root workflow. The scoped
case-binding assumption selects the signed exposure from TransferEligibility. -/
def evidence (mode : Policy) : Review.Evidence :=
  { SparkJoint.pendingReviewEvidence with
    authority := authority mode
    publishedTerms := fun l pub t ↦ l = lesson .oldReview ∧ pub = publication.publication ∧ t = terms
    concernFacts := { SparkJoint.pendingReviewEvidence.concernFacts with
      relevantShareClaimantAffected := fun m a ↦ m = matter .oldReview ∧
        delta .retain .oldReview a false ≠ delta .retain .oldReview a true } }

def withReview (s : State) (next : Review.History) : State := { s with review := next }
def published : State := withReview opening { opening.review with publications := [publication] }
def admitted : State := withReview published { published.review with intakes := [intake] }
def requested : State :=
  withReview admitted { admitted.review with appointmentTriggers := [trigger] }

def admissionLabels : List Event :=
  [.review (evidence .retain) (.publishContacts (lesson .oldReview) terms publication),
   .review (evidence .retain) (.receive intake),
   .review (evidence .retain) (.requestAppointment intake trigger)]

theorem admissionPath : DirectPath opening admissionLabels requested := by
  refine .next (m := published) ?_ (.next (m := admitted) ?_ (.next ?_ (.nil _)))
  · apply Step.review
    · trivial
    · trivial
    · intro _ h; cases h
    apply Review.Step.publishContacts
    · rfl
    · exact ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩
    · simp [opening, Review.History.empty]
  · apply Step.review
    · trivial
    · trivial
    · intro _ h; cases h
    apply Review.Step.receive
    · exact List.mem_cons_self
    · exact ⟨rfl, by decide⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩, ⟨rfl, by decide +kernel⟩,
        Or.inl rfl⟩
    · simp [published, withReview, opening, Review.History.empty]
  · apply Step.review
    · trivial
    · trivial
    · intro _ h; cases h
    apply Review.Step.requestAppointment
    · exact List.mem_cons_self
    · exact ⟨⟨rfl, rfl⟩, by decide, by decide, Or.inl rfl⟩
    · simp [admitted, published, withReview, opening, Review.History.empty]

def addTransfer (s : State) (q : Task) : State :=
  { s.withHolds s.holds with materials := { s.materials with transfers := signedRow q :: s.materials.transfers } }

def transferred : Policy → State
  | .retain => addTransfer requested .teaching
  | .assign => addTransfer (addTransfer requested .teaching) .oldReview

def transferLabel (q : Task) : Event := .materials (lessonId q) (.transfer (signedRow q))
def transferLabels : Policy → List Event
  | .retain => [transferLabel .teaching]
  | .assign => [transferLabel .teaching, transferLabel .oldReview]

private theorem addTransferStep (s : State) (q : Task)
    (fresh : ∀ previous ∈ s.materials.transfers, previous.material = mat →
      previous.record.reference ≠ (signedRow q).record.reference) :
    Step s (transferLabel q) (addTransfer s q) := by
  apply Step.materials
  · simp [Materials.Event.recordLesson]
  · trivial
  · apply Materials.Step.transfer _ fresh
    cases q <;> exact ⟨by decide, ⟨rfl, rfl, by decide, by decide⟩, trivial, List.mem_cons_self⟩
  · rfl

theorem transferPath (p : Policy) : DirectPath requested (transferLabels p) (transferred p) := by
  have first := addTransferStep requested .teaching (by simp [requested, admitted, published,
    withReview, opening])
  cases p with
  | retain => exact .next first (.nil _)
  | assign =>
    refine .next first (.next (addTransferStep _ .oldReview ?_) (.nil _))
    intro row h _
    change row ∈ [signedRow .teaching] at h
    obtain rfl := List.mem_singleton.mp h
    decide

def afterTeachingAppointment (s : State) : State :=
  withReview s { s.review with appointments := s.review.appointments ++ [appointment .teaching .O] }
def afterAppointments (s : State) (p : Policy) : State :=
  let m := afterTeachingAppointment s
  withReview m { m.review with appointments := m.review.appointments ++ [appointment .oldReview (oldReviewer p)] }
def afterInitial (s : State) (p : Policy) : State :=
  let m := afterAppointments s p
  withReview m { m.review with initialFindings := m.review.initialFindings ++ [initial .O] }
def terminal (documented supplied : Policy) : State :=
  let m := afterInitial (transferred documented) supplied
  withReview m { m.review with reviewFindings := m.review.reviewFindings ++ [reviewed (oldReviewer supplied)] }

def judgingLabels (p : Policy) : List Event :=
  [.review (evidence p) (.appoint (appointment .teaching .O)),
   .review (evidence p) (.appoint (appointment .oldReview (oldReviewer p))),
   .review (evidence p) (.decideInitial teachingForm terms (initial .O)),
   .review (evidence p) (.decideReview (lesson .oldReview) none (reviewed (oldReviewer p)))]

private theorem effectiveTeachingForm : teachingForm.matches := by
  simp [PartOne.matches, teachingForm, JointT.form, usePlace, lessonId, seat, JointT.lesson,
    JointT.schedule, JointT.paymentTerms, Place.matches, Place.validFees, Booking.Schedule.valid,
    Contacts.complete, PayAndReviewTerms.valid, PaymentTerms.valid, PaymentDeadline.valid,
    AdvanceWindow.validAt, Moment.by, Moment.before, JointT.tick, agreement, mat] <;> decide +kernel

private theorem roleAtTime (p : Policy) (q : Task) :
    (authority p).disinterested (matter q) (who (chosen p q)) (tick 46) := by
  cases p <;> cases q <;> unfold ReviewAuthorities.disinterested DirectInterest.affected <;>
    decide +kernel

/-- The root receives the exposure view for this decision as evidence. The extra policy
parameter makes eligibility under a stale but well-typed view testable in the same state. -/
theorem judgingPath (documented supplied : Policy) :
    DirectPath (transferred documented) (judgingLabels supplied) (terminal documented supplied) := by
  let s := transferred documented
  have rh : s.review = requested.review := by cases documented <;> rfl
  have hh : s.holds = holds0 := by cases documented <;> rfl
  have ff : teachingForm ∈ (s.course (lessonId .teaching)).effectiveForms := by
    cases documented <;> exact List.mem_cons_self
  refine .next (m := afterTeachingAppointment s) ?_
    (.next (m := afterAppointments s supplied) ?_
    (.next (m := afterInitial s supplied) ?_ (.next ?_ (.nil _))))
  · apply Step.review
    · trivial
    · trivial
    · intro _ h; cases h
    apply Review.Step.appoint
    · exact ⟨rfl, rfl, by decide, rfl, roleAtTime supplied .teaching⟩
    · change appointment .teaching .O ∉ s.review.appointments
      rw [rh]
      simp [requested, admitted, published, withReview, opening, Review.History.empty]
  · apply Step.review
    · trivial
    · trivial
    · intro _ h; cases h
    apply Review.Step.appoint
    · exact ⟨rfl, rfl, by change (tick 46).by (tick 46); decide, rfl, roleAtTime supplied .oldReview⟩
    · change appointment .oldReview (oldReviewer supplied) ∉ s.review.appointments ++ [appointment .teaching .O]
      rw [rh]
      cases supplied <;> decide
  · apply Step.review
    · trivial
    · trivial
    · intro _ h; cases h
    apply Review.Step.decideInitial
    · refine ⟨⟨rfl, effectiveTeachingForm, by decide, Or.inl ff⟩, rfl, ?_⟩
      exact ⟨rfl, rfl, rfl, fun d h ↦ by cases h; rfl, rfl, rfl, rfl, rfl⟩
    · change s.holds.temporarySettersRecorded _ _ _ _
      rw [hh]
      simp [HoldHistory.temporarySettersRecorded, holds0, Review.History.authorities, State.reviewEvidence,
        evidence, authority]
    · have gate := (roleMenu supplied .teaching .O).mpr rfl
      rcases gate with ⟨_, ⟨ok, dis, why, sub, avail, advice⟩, _⟩
      have designated : (authority supplied).interest (matter .teaching) terms.leadAcademicTutor
          (initial .O).decidedAt |>.affected := by
        cases supplied <;> unfold DirectInterest.affected <;> decide +kernel
      have apt : appointment .teaching .O ∈ (afterAppointments s supplied).review.appointments :=
        by simp [afterAppointments, afterTeachingAppointment, withReview]
      have applies : (appointment .teaching .O).applies
          ((afterAppointments s supplied).review.authorities (authority supplied))
          (matter .teaching) (who .O) (initial .O).decidedAt :=
        ⟨rfl, rfl, by decide, rfl, dis⟩
      exact ⟨List.mem_cons_self, ⟨ok, dis, why, Or.inr ⟨designated, Or.inr ⟨_, apt, applies⟩⟩,
        avail, advice⟩, fun _ ↦ ⟨_, apt, applies⟩⟩
    · change initial .O ∉ s.review.initialFindings
      rw [rh]
      decide
  · apply Step.review
    · trivial
    · trivial
    · intro _ h; cases h
    apply Review.Step.decideReview
    · rfl
    · exact Or.inl ⟨intake, by change intake ∈ s.review.intakes; rw [rh]; exact List.mem_cons_self,
        ⟨rfl, rfl⟩, by change (tick 36).by (tick 51); decide⟩
    · simp
    · change s.holds.temporarySettersRecorded _ _ _ _
      rw [hh]
      simp [HoldHistory.temporarySettersRecorded, holds0, Review.History.authorities, State.reviewEvidence,
        evidence, authority]
    · have gate := (roleMenu supplied .oldReview (oldReviewer supplied)).mpr rfl
      rcases gate with ⟨_, ⟨⟨ok, free, original, _⟩, why, _, available⟩, _⟩
      have apt : appointment .oldReview (oldReviewer supplied) ∈
          (afterInitial s supplied).review.appointments := by simp [afterInitial, afterAppointments, withReview]
      have applies : (appointment .oldReview (oldReviewer supplied)).applies
          ((afterInitial s supplied).review.authorities (authority supplied))
          (matter .oldReview) (who (oldReviewer supplied)) (tick 51) := ⟨rfl, rfl, by change (tick 46).by (tick 51); decide, rfl, free⟩
      refine ⟨List.mem_cons_self, ⟨⟨ok, free, original, ?_⟩, why, Or.inr ⟨_, apt, applies⟩,
        available⟩, ?_⟩
      · change ∀ m a t, (m, a, t) ∈ [] ++ s.review.originals.map _ → _ → _ → a ≠ who (oldReviewer supplied)
        rw [rh]
        cases supplied <;>
          simp [requested, admitted, published, withReview, opening, originalDecision, wageDecision,
            reviewed, matter, oldReviewer, who, lessonId] <;>
          rintro _ a _ (⟨_, rfl, _⟩ | ⟨_, rfl, _⟩) _ _ <;> decide
      · change didNotMakeOriginalFinding (s.review.initialFindings ++ [initial .O]) _ _ _
        rw [rh]
        cases supplied <;>
          simp [didNotMakeOriginalFinding, requested, admitted, published, withReview, opening,
            priorFinding, initial, reviewed, matter, lessonId, who, oldReviewer, ReviewMatter.sameCase]
    · intro entry mem _ _
      change entry ∈ s.review.intakes at mem
      rw [rh] at mem
      obtain rfl := List.mem_singleton.mp mem
      refine ⟨appointment .oldReview (oldReviewer supplied), ?_, by change (tick 36).by (tick 46); decide, rfl, rfl,
        by change (tick 46).by (tick 51); decide, rfl, ?_⟩
      · simp [afterInitial, afterAppointments, withReview]
      · exact roleAtTime supplied .oldReview
    · change reviewed (oldReviewer supplied) ∉ s.review.reviewFindings
      rw [rh]
      cases supplied <;> decide

theorem fullPath (p : Policy) :
    DirectPath opening (admissionLabels ++ transferLabels p ++ judgingLabels p) (terminal p p) :=
  SparkJoint.append (SparkJoint.append admissionPath (transferPath p)) (judgingPath p p)

theorem recognisedFullPath (p : Policy) :
    RecognisedPath (RecognisedV15.Workflow.State.fromDirect opening)
      (admissionLabels ++ transferLabels p ++ judgingLabels p)
      (RecognisedV15.Workflow.State.fromDirect (terminal p p)) :=
  RecognisedV15.Workflow.path_from_direct (fullPath p)

/-- In the same state containing both signed records, the source root also accepts a
different interest report, leading it to accept N for the old review. -/
theorem suppliedInterestIsIndependent :
    (transferred .assign).materials.transfers = [signedRow .oldReview, signedRow .teaching] ∧
    DirectPath (transferred .assign) (judgingLabels .retain) (terminal .assign .retain) ∧
    (terminal .assign .retain).review.reviewFindings = [reviewed .N] ∧
    DirectPath (transferred .assign) (judgingLabels .assign) (terminal .assign .assign) ∧
    (terminal .assign .assign).review.reviewFindings = [reviewed .O] :=
  ⟨rfl, judgingPath _ _, rfl, judgingPath _ _, rfl⟩

theorem observedEndpoint (p : Policy) :
    let s := terminal p p
    s.review.intakes = [intake] ∧ s.review.initialFindings = [priorFinding, initial .O] ∧
    s.review.reviewFindings = [reviewed (oldReviewer p)] ∧
    s.materials.useChecks = [useCheck .oldReview, useCheck .teaching] ∧
    s.holds.payments.receivedForPartBefore oldPart.ref (.person (who .O) none) (tick 60) = 50 ∧
    s.holds.payments.receivedForPartBefore oldPart.ref (.person (who .N) none) (tick 60) = 0 ∧
    s.holds.payments.remainingBefore oldPart (tick 60) = 0 ∧
    wageDecision ∈ s.review.originals ∧ wageTerms.due = .fixed (tick 25) ∧
    (tick 25).before (tick 60) ∧ s.holds.payments.remainingBefore wage (tick 60) = 80 ∧
    s.activeReserves = opening.activeReserves ∧ s.holds.payments = openingPayments := by
  cases p <;>
    exact ⟨rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide, rfl, by decide, by decide +kernel, rfl, rfl⟩

#print axioms separateUseChecks
#print axioms admissionPath
#print axioms transferPath
#print axioms judgingPath
#print axioms fullPath
#print axioms recognisedFullPath
#print axioms suppliedInterestIsIndependent
#print axioms observedEndpoint

end TransferCase
