import RecognisedV15.State

namespace RecognisedV15.Correction

open SourceV14

/-- Fix the original record, the review being checked, and the supplied
evidence. The audit records which checks it has made for this case. -/
structure Case where
  lesson : Lesson
  correction : PaymentCorrectionCase
  authorities : ReviewAuthorities
  appointments : List ReviewAppointment
  outcomes : List RecordedSettlementOutcome
  monetaryOutcome : EvidenceRef → Option PaymentPart
  credits : List Booking.CreditPosting
  refundPlace : Option Place
  scope : CorrectedMonetaryScope
  priorMaterialsParts : List PaymentPart := []
  otherRefundPrincipals : List (ObligationId × Amount) := []

inductive Event where
  | review
  | additionalReceipt (record : CorrectionPaymentRecord)

/- A sequence of checks against the direct Review definitions. Recording
a check leaves the supplied ledger untouched. -/
namespace Direct

inductive State where
  | original
  | reviewed (receipts : List CorrectionPaymentRecord)

inductive Step (caseData : Case) (inputs : DirectInputs) : State → Event → State → Prop where
  | review (finding : caseData.correction.recorded caseData.lesson caseData.authorities
      caseData.appointments caseData.outcomes caseData.monetaryOutcome inputs.payment.payments
      caseData.priorMaterialsParts) :
    Step caseData inputs .original .review (.reviewed [])
  | receipt (done : List CorrectionPaymentRecord) (record : CorrectionPaymentRecord)
      (paid : caseData.correction.additionalPaymentPosted caseData.lesson
        inputs.payment.payments caseData.credits caseData.refundPlace record
        caseData.scope caseData.otherRefundPrincipals) :
    Step caseData inputs (.reviewed done) (.additionalReceipt record) (.reviewed (record :: done))

end Direct

structure RecordedReview (caseData : Case) (state : RecognisedV15.State) : Prop where
  meetsRule : caseData.correction.recorded caseData.lesson caseData.authorities
    caseData.appointments caseData.outcomes caseData.monetaryOutcome state.payment.payments
    caseData.priorMaterialsParts

structure RecognisedReceipt (caseData : Case) (state : RecognisedV15.State) where
  record : CorrectionPaymentRecord
  provesReceipt : caseData.correction.additionalPaymentPosted caseData.lesson
    state.payment.payments caseData.credits caseData.refundPlace record
    caseData.scope caseData.otherRefundPrincipals

inductive AuditState (caseData : Case) (state : RecognisedV15.State) where
  | original
  | reviewed (finding : RecordedReview caseData state)
      (receipts : List (RecognisedReceipt caseData state))

inductive Step (caseData : Case) (state : RecognisedV15.State) :
    AuditState caseData state → Event → AuditState caseData state → Prop where
  | review (finding : RecordedReview caseData state) :
    Step caseData state .original .review (.reviewed finding [])
  | receipt (finding : RecordedReview caseData state)
      (done : List (RecognisedReceipt caseData state)) (paid : RecognisedReceipt caseData state) :
    Step caseData state (.reviewed finding done) (.additionalReceipt paid.record)
      (.reviewed finding (paid :: done))

/-- The review status and each receipt identity are observable. -/
def AuditState.view {caseData : Case} {state : RecognisedV15.State} :
    AuditState caseData state → Direct.State
  | .original => .original
  | .reviewed _ receipts => .reviewed (receipts.map RecognisedReceipt.record)

theorem matching_direct_step {caseData : Case} {state : RecognisedV15.State}
    {before after : AuditState caseData state} {event : Event}
    (allowed : Step caseData state before event after) :
    Direct.Step caseData state.toDirect before.view event after.view := by
  cases allowed with
  | review finding => exact .review finding.meetsRule
  | receipt _ done paid => exact .receipt (done.map RecognisedReceipt.record) paid.record paid.provesReceipt

theorem matching_recognised_step {caseData : Case} {state : RecognisedV15.State}
    {before : AuditState caseData state} {after : Direct.State} {event : Event}
    (allowed : Direct.Step caseData state.toDirect before.view event after) :
    ∃ result : AuditState caseData state, Step caseData state before event result ∧ result.view = after := by
  cases before with
  | original =>
    cases allowed with
    | review rule =>
      let finding : RecordedReview caseData state := ⟨rule⟩
      exact ⟨.reviewed finding [], .review finding, rfl⟩
  | reviewed finding done =>
    cases allowed with
    | receipt _ record rule =>
      let paid : RecognisedReceipt caseData state := ⟨record, rule⟩
      exact ⟨.reviewed finding (paid :: done), .receipt finding done paid, rfl⟩

theorem bisimulation (caseData : Case) (inputs : DirectInputs) :
    let state := RecognisedV15.State.fromDirect inputs
    (AuditState.original : AuditState caseData state).view = Direct.State.original ∧
    (∀ before after event, Step caseData state before event after →
      Direct.Step caseData inputs before.view event after.view) ∧
    (∀ (before : AuditState caseData state) (after : Direct.State) event,
      Direct.Step caseData inputs before.view event after →
      ∃ result : AuditState caseData state, Step caseData state before event result ∧ result.view = after) := by
  dsimp
  refine ⟨rfl, ?_, ?_⟩
  · intro _ _ _ allowed
    simpa using matching_direct_step allowed
  · intro before after event allowed
    have allowed' : Direct.Step caseData (RecognisedV15.State.fromDirect inputs).toDirect
        before.view event after := by simpa using allowed
    exact matching_recognised_step allowed'

/-- A finite sequence of audit events, with exact order and labels. -/
inductive Trace {σ : Type} (step : σ → Event → σ → Prop) : σ → List Event → σ → Prop where
  | nil (state : σ) : Trace step state [] state
  | cons {before intermediate after : σ} {event : Event} {rest : List Event}
      (next : step before event intermediate) (tail : Trace step intermediate rest after) :
    Trace step before (event :: rest) after

theorem matching_direct_trace {caseData : Case} {state : RecognisedV15.State}
    {before after : AuditState caseData state} {events : List Event}
    (trace : Trace (Step caseData state) before events after) :
    Trace (Direct.Step caseData state.toDirect) before.view events after.view := by
  induction trace with
  | nil current => exact .nil current.view
  | cons next _ matched => exact .cons (matching_direct_step next) matched

theorem matching_recognised_trace {caseData : Case} {state : RecognisedV15.State}
    {before : AuditState caseData state} {after : Direct.State} {events : List Event}
    (trace : Trace (Direct.Step caseData state.toDirect) before.view events after) :
    ∃ result : AuditState caseData state,
      Trace (Step caseData state) before events result ∧ result.view = after := by
  generalize same : before.view = start at trace
  induction trace generalizing before with
  | nil current => exact ⟨before, .nil before, same⟩
  | cons next _ ih =>
    rw [← same] at next
    obtain ⟨intermediate, matched, sameView⟩ := matching_recognised_step next
    obtain ⟨result, tail, finish⟩ := ih sameView
    exact ⟨result, .cons matched tail, finish⟩

end RecognisedV15.Correction
