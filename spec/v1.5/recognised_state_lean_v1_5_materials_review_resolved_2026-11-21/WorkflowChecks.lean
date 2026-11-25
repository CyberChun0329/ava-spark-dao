import Lean
import RecognisedV15.Workflow

open Lean Elab Command Meta

run_cmd do
  let .inductInfo event ← getConstInfo `SourceV14.Workflow.Event
    | throwError "Direct workflow event type is missing"
  let .inductInfo directStep ← getConstInfo `SourceV14.Workflow.Step
    | throwError "Direct workflow step relation is missing"
  let .inductInfo recognisedStep ← getConstInfo `RecognisedV15.Workflow.Step
    | throwError "Recognised workflow step relation is missing"
  let labels (ctors : List Name) := ctors.map fun
    | .str _ label => label
    | name => toString name
  let kinds := labels event.ctors
  unless kinds.length == 17 && labels directStep.ctors == kinds &&
      labels recognisedStep.ctors == kinds do
    throwError "Workflow event coverage differs from the 17 root cases"
  logInfo m!"Both step relations cover the 17 root events: {kinds}"
  let proofs := [
    `RecognisedV15.Workflow.State.toDirect_fromDirect,
    `RecognisedV15.Workflow.State.fromDirect_toDirect,
    `RecognisedV15.Workflow.State.direct_recordCourse,
    `RecognisedV15.Workflow.State.direct_recordPayment,
    `RecognisedV15.Rescheduling.step_iff,
    `RecognisedV15.SeparateBooking.step_iff,
    `RecognisedV15.Settlement.step_iff,
    `RecognisedV15.Redress.step_iff,
    `RecognisedV15.PlaceConfirmation.step_iff,
    `RecognisedV15.MaterialPayments.step_iff,
    `RecognisedV15.Workflow.State.bookingStep_iff,
    `RecognisedV15.Workflow.step_to_direct,
    `RecognisedV15.Workflow.step_from_direct,
    `RecognisedV15.Workflow.step_iff,
    `RecognisedV15.Workflow.bisimulation,
    `RecognisedV15.Workflow.path_iff,
    `RecognisedV15.Workflow.startPermitted_iff,
    `RecognisedV15.Workflow.synchronised_iff,
    `RecognisedV15.Workflow.observation_equal
  ]
  let mut allAxioms : NameSet := {}
  for proof in proofs do
    for axiomName in ← liftTermElabM (collectAxioms proof) do
      unless [`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {proof}"
      allAxioms := allAxioms.insert axiomName
  logInfo m!"Checked {proofs.length} workflow theorems. Axioms: {allAxioms.toList}"

namespace WorkflowChecks

open SourceV14 SourceV14.Workflow

private def firstUse : CurrentLessonFunds :=
  ⟨1, 4, ⟨0, 1⟩, [⟨7, .providerFunds, .spendable, 100, 0, 100⟩]⟩

private def secondUse : CurrentLessonFunds :=
  ⟨2, 4, ⟨0, 2⟩, [⟨7, .providerFunds, .spendable, 100, 0, 100⟩]⟩

/-- Two courses cannot each omit the other's reservation of the same 100. -/
example : ¬Reserves.FundingContextMatches (Reserves.reserve [] firstUse) secondUse := by
  intro allowed
  have h := allowed ⟨7, .providerFunds, .spendable, 100, 0, 100⟩ (by simp [secondUse])
  have impossible : ¬Reserves.occupiedElsewhere (Reserves.reserve [] firstUse) secondUse 7 ≤ 0 := by
    decide +kernel
  exact impossible h

/-- A refund-return transition changes the common verified credit history seen by any later course. -/
example {s t : SourceV14.Workflow.State} {paid : PostedPayment} {ret : ReturnedPayment}
    {posting : SourceV14.Booking.CreditPosting} (step : Step s (.refundReturned paid ret posting) t) :
    (∀ lesson : LessonId, (t.course lesson).ledger = s.credit.ledger ++ [posting]) ∧
    t.synchronised := by
  cases step
  exact ⟨fun _ ↦ rfl, rfl⟩

/-- An overlapping actual receipt may be represented even if it is not a valid payment.
Booking in a different course reads the very same actual receipt history. -/
example {s t : SourceV14.Workflow.State} {paid : PostedPayment} (step : Step s (.payment (.post paid)) t) :
    paid ∈ t.holds.payments.posted ∧
    (∀ lesson : LessonId, (t.course lesson).creditRecords.payments = t.holds.payments) := by
  cases step with
  | payment _ approval =>
    cases approval
    constructor
    · change paid ∈ s.holds.payments.posted ++ [paid]
      simp
    · exact fun _ ↦ rfl

/-- A group majority or candidate tutor record does not by itself supply an account
that the tutor settlement can read. -/
example {ev : Course.StartEvidence} {holds : HoldHistory} {h : Settlement.History}
    {due : Settlement.TutorDue} (checked : due.established ev holds h)
    (line : Settlement.LessonSettlement) (listed : line ∈ due.basis.paymentsByPlace) :
    ∃ origin ∈ h.fees, origin.decision.amounts = line ∧
      origin.decision.form.lesson.id = due.form.lesson.id := by
  simp only [Settlement.TutorDue.established] at checked
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, operatives, _, _⟩ := checked
  obtain ⟨_, _, origin, present, lesson, _, amounts, _, _⟩ := operatives line listed
  exact ⟨origin, present, amounts, lesson⟩

/-- A correct partial transfer does not permit an incorrect recorded amount due. -/
example {book : CreditBook} {history : PaymentHistory} {posting : SourceV14.Booking.CreditPosting}
    {file : Course.VerifiedLessonRefund} {row : Review.CorrectedPayout} {scope : CorrectedMonetaryScope}
    (valid : book.mayFileCorrectedRefund history posting file row scope) :
    file.settlement.amount = scope.principal :=
  valid.2.2.2.2.1

/-- Recovery cannot elide an already established customer refund
in the same original tutor-fault history. -/
example {course : Course.StartEvidence} {redress : Redress.History} {before after : Debt.History}
    {loss : Debt.AssessedLoss} {facts : Debt.RecoveryEvidence} {receipt : TutorDebtRecovery}
    (step : Debt.Step course redress before (.collect loss facts receipt) after)
    (refund : Redress.AssessedRefund) (retained : refund ∈ redress.assessments)
    (same : loss.refundConcernsBreach refund) (prior : refund.amount.recordedAt.by receipt.madeAt) :
    facts.establishedRedress refund.amount.form.lesson.id refund.amount.form.place.id
      refund.amount.obligation := by
  cases step with
  | collect _ _ covered _ => exact covered.1 refund retained same prior

/-- Recording a separate booking leaves both lessons, refunds, cancellations
and the common balance alone, and keeps the exact original and new link. -/
example {s t : SourceV14.Workflow.State} {link : SeparateBooking.Link}
    (step : Step s (.separateBooking link) t) :
    link.original.lesson.id ≠ link.next.lesson.id ∧
    t.separateBookings = s.separateBookings ++ [link] ∧
    t.lessons = s.lessons ∧ t.cancelled = s.cancelled ∧
    t.redress = s.redress ∧ t.credit = s.credit := by
  cases step with
  | separateBooking rule =>
    rcases rule with ⟨_, _, _, _, _, _, confirmed, linked⟩
    exact ⟨confirmed.2.1, linked, rfl, rfl, rfl, rfl⟩

end WorkflowChecks
