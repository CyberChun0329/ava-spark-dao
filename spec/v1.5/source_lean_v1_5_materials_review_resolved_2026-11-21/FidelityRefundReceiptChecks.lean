import SourceV14.Workflow

/-! F2. Root workflow checks for §§4.3, 6.3 and 6.6, starting from an assessed refund. -/
namespace SourceV14.FidelityRefundReceiptChecks

open SourceV14.Booking SourceV14.Confirmation SourceV14.Course SourceV14.Operations
open SourceV14.Settlement SourceV14.Workflow.Redress
open SourceV14.CreditEvidence

private def day (n : Nat) : Moment := ⟨n * 86400, 0⟩

private def terms : PaymentTerms := ⟨.fixed (day 7), .fixed (day 8)⟩

private def form : PartOne where
  lesson := ⟨42, .oneToOne, 10, 20, 30, 60⟩
  place := ⟨1, 42, 101, 201, 301, 401, 100, 100⟩
  contacts := ⟨"Spark", "provider", "student", none, "coordinator", 50, "lead",
    none, none, 60, "reviewer", 70, "alternative", true, 80, "escalation"⟩
  rulesVersion := "1.5"
  confirmedAt := day 1
  customerRepresentatives := []
  schedule := ⟨42, day 6, day 7, "UTC", day 1, day 1⟩
  serviceTerms := "service"
  serviceItems := [1]
  discountBasis := none
  privateRoster := none
  rosterLock := none
  groupRescheduleCutoff := none
  oneToOneAdvanceCutoff := some (.fixed (day 3))
  cancelChangeTerms := "cancellation"
  noFaultTerms := "no-fault cancellation"
  applicableStartTerms := "start"
  tutorAgreementRef := "tutor terms"
  absentGroupPlacePay := none
  materialsOrBundle := none
  materialsTermsRef := none
  materialsPayer := none
  deadlines := ⟨.fixed (day 6), day 4, none, terms, terms, terms,
    terms, .fixed (day 12), day 15, day 13, day 14, .fixed (day 20)⟩

private def part : PaymentPart := ⟨⟨42, 12, 1, .lessonRefund 1⟩, .lessonRefund 401, 100⟩

private def assessment : AssessedRefund where
  amount := ⟨form, 12, .noFaultCancellation, "no-fault cancellation", day 5, day 6,
    ⟨day 7, day 8, none, .date (day 20)⟩, 0, 100, [part]⟩
  evidence := .noFault
    { schedule := form.schedule
      disruptionVerifiedAt := day 3
      cannotProceed := true
      anyPartyAtFault := false
      affected := [201]
      contacts := [⟨42, 30, 201, day 4⟩]
      newAcceptance := none
      cancellation := ⟨42, 1, 201, 30, day 5⟩
      refundObligation := 12
      underTerms := fun text ↦ text = form.noFaultTerms
      noneTaught := true
      undeliveredAgreedValue := 100
      undeliveredAt := fun lesson place atTime noneTaught amount ↦
        lesson = 42 ∧ place = 1 ∧ atTime = day 5 ∧ noneTaught = true ∧ amount = 100 }
  dueEvent := none
  executionEvent := none

private def facts : HoldFacts where
  terms := fun _ ↦ ⟨30, 70, 50, .exact (day 12), day 15, day 13, day 14, 80⟩
  termsApply := fun _ ↦ True
  acceptedPaymentConcern := fun _ _ _ _ ↦ False
  reviewerCannotActInTime := fun _ _ ↦ False
  temporaryAuthority := fun _ _ _ _ ↦ False
  allegedFactsWouldChangePayment := fun _ _ _ ↦ False
  separatelyIdentifiable := fun _ _ ↦ True
  establishedParts := fun lesson purpose ↦
    if lesson = part.ref.lesson ∧ purpose = part.ref.purpose then [part] else []
  paymentAffected := fun _ _ ↦ False
  decisionPending := fun _ _ _ ↦ False
  partFallsUnderDecision := fun _ _ _ ↦ False
  decisionConcernsWholeGroup := fun _ _ ↦ False
  isGroupLesson := fun _ ↦ False
  affectsWholeSettlement := fun _ ↦ False
  groupSettlementParts := fun _ ↦ []

private def authorities : ReviewAuthorities where
  corePartner := fun _ _ ↦ False
  initialFinding := fun _ _ _ ↦ False
  reviewer := fun _ _ _ ↦ False
  approvesPayment := fun ref actor atTime ↦ ref = part.ref ∧ actor = 10 ∧ atTime = day 6
  interest := fun _ _ _ ↦ ⟨false, false, false, false⟩
  originalDecisionMaker := fun _ ↦ none
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

private def approved : PaymentApproval :=
  ⟨10, 10, 30, day 6, some (day 30), none, [⟨part.ref, .account 401, 100, none⟩]⟩

private def debit : CreditPosting := ⟨90, 401, .lessonDebit 42 1, 100, day 2⟩

private def refundAt (atTime : Moment) (withApproval : Bool := true)
    (amount : Amount := 100) : RefundPosting where
  assessment
  posting := ⟨91, 401, .lessonRefund 42 1 12, amount, atTime⟩
  filing :=
    { form
      originalDebit := debit
      obligation := 12
      settlement := ⟨42, 1, 401, "no-fault cancellation", .noFaultCancellation,
        0, day 5, day 8, 100, amount, [atTime], false, false⟩
      payment := ⟨91, ⟨part.ref, .account 401, 30, amount, atTime⟩, some 92⟩
      approval := if withApproval then some approved else none }
  part
  route := if withApproval then some (.ordinary approved) else none
  postLift := none

private def returned : ReturnedPayment := ⟨93, 91, 25, ⟨9 * 86400, 1⟩, 94⟩
private def conditions : PaymentInstruction → Prop := fun _ ↦ True

private def start (base : Workflow.State) (withApproval : Bool := true) : Workflow.State :=
  let payments : PaymentHistory := ⟨[], [], []⟩
  let holds : HoldHistory := {
    payments
    temporary := []
    formal := []
    lifts := []
    approvals := if withApproval then [approved] else [] }
  { base with
    redress := { assessments := [assessment] }
    holds
    credit :=
      { base.credit with
        openingCredit := fun account ↦ if account = 401 then 100 else 0
        ledger := [debit]
        creditRecords := { base.credit.creditRecords with
          payments, verifiedRefunds := [], paymentAuthorities := authorities } } }

private def record (before : Workflow.State) (paid : PostedPayment) : Workflow.State :=
  let holds := { before.holds with payments :=
    { before.holds.payments with posted := before.holds.payments.posted ++ [paid] } }
  { before.withHolds holds with paymentRecords := before.paymentRecords ++ [.post paid] }

private def recordReturn (before : Workflow.State) (refund : ReturnedPayment) : Workflow.State :=
  let holds := { before.holds with payments :=
    { before.holds.payments with returned := before.holds.payments.returned ++ [refund] } }
  { before.withHolds holds with paymentRecords := before.paymentRecords ++ [.returnPayment refund] }

private def file (before : Workflow.State) (post : RefundPosting) : Workflow.State :=
  let lesson := post.assessment.amount.form.lesson.id
  let after := fileRefund (before.course lesson) post.posting post.filing
  (before.withCourse lesson after).withHolds before.holds

private def observe (post : RefundPosting) : Workflow.Event :=
  .redress (.fileObservedRefund post (day 10) facts authorities)

private theorem fileAtRoot {s : Workflow.State} {post : RefundPosting}
    (verified : post.observedFiling s.redress (s.course post.assessment.amount.form.lesson.id)
      s.holds (day 10) facts authorities) :
    Workflow.Step s (observe post) (file s post) :=
  Workflow.Step.redress trivial trivial (by simp [Workflow.Redress.Event.usesRecordedReviews,
    Event.assessmentDecisions]) trivial ⟨verified, rfl, rfl, rfl⟩

private theorem recordLate (base : Workflow.State) (withApproval : Bool := true) :
    let paid := (refundAt (day 9) withApproval).filing.payment
    Workflow.Step (start base withApproval) (.payment (.post paid))
      (record (start base withApproval) paid) := by
  refine Workflow.Step.payment trivial (.post _ ?_ (by simp [start]))
  change (0 : Amount) < 100
  decide +kernel

private theorem recordLateReturn (base : Workflow.State) :
    Workflow.Step (record (start base) (refundAt (day 9)).filing.payment)
      (.payment (.returnPayment returned))
      (recordReturn (record (start base) (refundAt (day 9)).filing.payment) returned) := by
  refine Workflow.Step.payment ?_ (.returnPayment (paid := (refundAt (day 9)).filing.payment)
    returned ?_ ?_ ?_ ?_ ?_ ?_)
  · simp [Workflow.Payment.Event.independentCreditChange, record, Workflow.State.withHolds, start]
  all_goals first
    | decide +kernel
    | (simp [record, start, Workflow.State.withHolds, sumAmounts] <;> decide +kernel)

private def beforeFiling (base : Workflow.State) (withReturn : Bool)
    (withApproval : Bool := true) : Workflow.State :=
  let received := record (start base withApproval) (refundAt (day 9) withApproval).filing.payment
  if withReturn then recordReturn received returned else received

private theorem formMatches : form.matches := by
  simp [PartOne.matches, form, terms, Place.matches, Place.validFees, Schedule.valid, Contacts.complete,
    PayAndReviewTerms.valid, PaymentTerms.valid, PaymentDeadline.valid, AdvanceWindow.validAt,
    day, Moment.by, Moment.before]
  all_goals decide +kernel

private theorem receiptTime (point : Moment) :
    ∀ time, time = point ↔ point = time ∧ time.by point := by
  intro time
  constructor
  · rintro rfl
    exact ⟨rfl, Or.inr rfl⟩
  · exact fun occurrence ↦ occurrence.1.symm

private theorem verifiesLateReceipt (base : Workflow.State) (withReturn : Bool)
    (withApproval : Bool := true) :
    let s := beforeFiling base withReturn withApproval
    (refundAt (day 9) withApproval).observedFiling s.redress (s.course form.lesson.id) s.holds
      (day 10) facts authorities := by
  cases withReturn <;> cases withApproval <;>
    simp [RefundPosting.observedFiling, RefundPosting.verifiedFiling, beforeFiling, record,
      recordReturn, start, Workflow.State.withHolds, Workflow.State.course,
      Workflow.LessonFile.evidence, refundAt, ledgerWithObservedRefund, observedRefundReturns,
      refundReturnPosting, returned, debit, assessment, RefundAssessment.partsMatch,
      VerifiedLessonRefund.matches, RefundRecord.matches, LessonRefundPostingMatches,
      HoldHistory.approvalRecorded,
      PaymentHistory.actualPaymentWithEvidence, PaymentHistory.validReturns,
      PaymentHistory.distinctReceipts, PaymentApproval.authorisedAtGrant,
      PaymentRecipient.accepts, facts, authorities, approved, part, form, refundDeadline]
  all_goals (repeat' first | exact formMatches | exact receiptTime _ | apply And.intro)
  all_goals decide +kernel

/-- The root filing credits a receipt after its original execution deadline. -/
theorem lateReceiptFiles (base : Workflow.State) :
    let before := beforeFiling base false
    let post := refundAt (day 9)
    Workflow.Step (start base) (.payment (.post post.filing.payment)) before ∧
    before.credit.ledger = [debit] ∧
    Workflow.Step before (observe post) (file before post) ∧
    (file before post).credit.ledger = [debit, post.posting] ∧
    (file before post).holds.payments = before.holds.payments ∧
    (file before post).credit.creditRecords.verifiedRefunds = [post.filing] ∧
    FeeRefundCompleted form.place (file before post).credit.ledger (day 10) 100 (some 12) ∧
    balanceBefore (file before post).credit.openingCredit (file before post).credit.ledger
      form.place.account (day 10) = 100 := by
  refine ⟨recordLate base, rfl, fileAtRoot (verifiesLateReceipt base false), rfl, rfl, rfl, ?_, ?_⟩
  · change FeeRefundCompleted form.place [debit, (refundAt (day 9)).posting] (day 10) 100 (some 12)
    exact ⟨by decide, by decide +kernel⟩
  · change balanceBefore (fun account ↦ if account = 401 then 100 else 0)
      [debit, (refundAt (day 9)).posting] 401 (day 10) = 100
    decide +kernel

/-- A same-second return with later order is filed once on the original account. -/
theorem lateReceiptFilesWithReturn (base : Workflow.State) :
    let before := beforeFiling base true
    let post := refundAt (day 9)
    Workflow.Step (beforeFiling base false) (.payment (.returnPayment returned)) before ∧
    Workflow.Step before (observe post) (file before post) ∧
    (file before post).credit.ledger = [debit, post.posting, refundReturnPosting post.posting returned] ∧
    refundBalanceDue form.place (file before post).credit.ledger (day 10) 100 (some 12) = 25 ∧
    balanceBefore (file before post).credit.openingCredit (file before post).credit.ledger
      form.place.account (day 10) = 75 := by
  let post := refundAt (day 9)
  let ledger := [debit, post.posting, refundReturnPosting post.posting returned]
  refine ⟨recordLateReturn base, fileAtRoot (verifiesLateReceipt base true), rfl, ?_, ?_⟩
  · change refundBalanceDue form.place ledger (day 10) 100 (some 12) = 25
    decide +kernel
  · change balanceBefore (fun account ↦ if account = 401 then 100 else 0)
      ledger 401 (day 10) = 75
    decide +kernel

/-- The verified receipt uses its established refund despite an empty approval history. -/
theorem actualReceiptFilesWithoutApproval (base : Workflow.State) :
    let before := beforeFiling base false false
    let post := refundAt (day 9) false
    Workflow.Step (start base false) (.payment (.post post.filing.payment)) before ∧
    before.holds.approvals = [] ∧ post.route = none ∧ post.filing.approval = none ∧
    Workflow.Step before (observe post) (file before post) ∧
    (file before post).holds = before.holds ∧
    (file before post).credit.creditRecords.verifiedRefunds = [post.filing] ∧
    FeeRefundCompleted form.place (file before post).credit.ledger (day 10) 100 (some 12) := by
  refine ⟨recordLate base false, rfl, rfl, rfl,
    fileAtRoot (verifiesLateReceipt base false false), rfl, rfl, ?_⟩
  change FeeRefundCompleted form.place [debit, (refundAt (day 9) false).posting]
    (day 10) 100 (some 12)
  exact ⟨by decide, by decide +kernel⟩

private def excessPosting : RefundPosting := refundAt (day 7) true 120

private theorem verifiesExcessReceipt (base : Workflow.State) :
    let before := record (start base) excessPosting.filing.payment
    excessPosting.observedFiling before.redress (before.course form.lesson.id) before.holds
      (day 10) facts authorities := by
  simp [RefundPosting.observedFiling, RefundPosting.verifiedFiling, excessPosting, refundAt,
    record, start, Workflow.State.withHolds, Workflow.State.course, Workflow.LessonFile.evidence,
    ledgerWithObservedRefund, observedRefundReturns, debit, assessment, RefundAssessment.partsMatch,
    VerifiedLessonRefund.matches, RefundRecord.matches, LessonRefundPostingMatches,
    HoldHistory.approvalRecorded, PaymentHistory.actualPaymentWithEvidence, PaymentHistory.validReturns,
    PaymentHistory.distinctReceipts, PaymentApproval.authorisedAtGrant, PaymentRecipient.accepts,
    facts, authorities, approved, part, form, refundDeadline]
  all_goals (repeat' first | exact formMatches | exact receiptTime _ | apply And.intro)
  all_goals decide +kernel

/-- Late assessment evidence can document an earlier restoration without authorising it. -/
theorem laterAssessmentFilesActualReceiptWithoutBackdatedApproval (base : Workflow.State) :
    let post := { excessPosting with assessment := { assessment with
      amount := { assessment.amount with recordedAt := day 8 } } }
    let initial := { start base with redress := { assessments := [post.assessment] } }
    let before := record initial post.filing.payment
    Workflow.Step before (observe post) (file before post) ∧
    ∀ next, ¬Workflow.Step initial (.redress (.postRefund post facts authorities conditions)) next := by
  dsimp only
  constructor
  · obtain ⟨occurred, ids, points, paymentBook, returns, ⟨_, _, details⟩, approval, rest⟩ :=
      verifiesExcessReceipt base
    exact fileAtRoot ⟨occurred, ids, points, paymentBook, returns,
      ⟨List.mem_cons_self, ⟨by decide, by decide⟩, details⟩, approval, rest⟩
  · intro next transitioned
    cases transitioned
    rename_i rule
    have required : (day 8).by (day 7) := rule.1.2.2.2.2.1.1.2.1.1
    exact (by decide : ¬(day 8).by (day 7)) required

#print axioms laterAssessmentFilesActualReceiptWithoutBackdatedApproval

/-- Retain the actual 120 against a principal of 100 and expose the excess of 20. -/
theorem actualExcessRefundFiles (base : Workflow.State) :
    let initial := start base
    let before := record initial excessPosting.filing.payment
    let after := file before excessPosting
    Workflow.Step initial (.payment (.post excessPosting.filing.payment)) before ∧
    Workflow.Step before (observe excessPosting) after ∧
    after.holds.payments.posted = [excessPosting.filing.payment] ∧
    after.credit.creditRecords.verifiedRefunds = [excessPosting.filing] ∧
    excessPosting.filing.settlement.amount = 100 ∧
    excessPosting.filing.settlement.returned = 120 ∧
    creditsRestoredFor form.place after.credit.ledger (day 10) (some 12) = 120 ∧
    refundBalanceDue form.place after.credit.ledger (day 10) 100 (some 12) = 0 ∧
    refundExcessRetained form.place after.credit.ledger (day 10) 100 12 = 20 ∧
    balanceBefore after.credit.openingCredit after.credit.ledger form.place.account (day 10) = 120 := by
  let ledger := [debit, excessPosting.posting]
  refine ⟨Workflow.Step.payment trivial (.post _ (by decide) (by simp [start])),
    fileAtRoot (verifiesExcessReceipt base), rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change creditsRestoredFor form.place ledger (day 10) (some 12) = 120
    decide +kernel
  · change refundBalanceDue form.place ledger (day 10) 100 (some 12) = 0
    decide +kernel
  · change refundExcessRetained form.place ledger (day 10) 100 12 = 20
    decide +kernel
  · change balanceBefore (fun account ↦ if account = 401 then 100 else 0)
      ledger 401 (day 10) = 120
    decide +kernel

/-- The same amount cannot be executed live even before the deadline with a recorded approval. -/
theorem excessRefundCannotExecute (base after : Workflow.State) :
    ¬Workflow.Step (start base)
      (.redress (.postRefund excessPosting facts authorities conditions)) after := by
  intro transitioned
  cases transitioned
  rename_i rule
  obtain ⟨⟨_, _, _, _, filed⟩, _, _⟩ := rule
  obtain ⟨_, _, withinRefund⟩ := filed.1.2
  have bound := withinRefund.2.1
  let prior := [debit, excessPosting.posting].filter
    (fun entry ↦ decide (entry.point.before (day 7)))
  change (120 : Amount) ≤ refundBalanceDue form.place prior (day 7) 100 (some 12) at bound
  have outstanding : refundBalanceDue form.place prior (day 7) 100 (some 12) = 100 :=
    by decide +kernel
  rw [outstanding] at bound
  exact (by decide : ¬(120 : Amount) ≤ 100) bound

private def excessReturn : ReturnedPayment := ⟨95, 91, 20, day 13, 96⟩

private def excessCorrection : PaymentCorrectionCase :=
  let matter : ReviewMatter := ⟨11, 42, [201]⟩
  ⟨part, ⟨matter, 60, day 11, "Overcredit recorded", 98, true⟩,
    ⟨42, 97, 98, 30, day 11, [201]⟩, ⟨part, day 11, [excessPosting.filing.payment]⟩⟩

private def excessRecovery : RecoveryRecord :=
  ⟨98, ⟨excessCorrection.finding.matter, 91, 20, 10, day 12⟩, excessReturn⟩

/-- Recover the 20 against the same receipt after a separately adopted review and decision. -/
theorem actualExcessRefundCanBeRecovered (base : Workflow.State)
    (external : Workflow.Review.Evidence) :
    let original : Workflow.Review.OriginalRecord :=
      ⟨⟨excessCorrection.finding.matter, 97, 50, day 6⟩, some part⟩
    let reviewed := { Workflow.Review.History.empty with
      originals := [original], corrections := [.monetary original excessCorrection] }
    let evidence := { external with
      recoveryUnderOriginalTerms := fun old decision ↦ old = part ∧ decision = excessRecovery.decision
      mayApproveRecovery := fun matter actor point ↦ matter = excessCorrection.finding.matter ∧
        actor = 10 ∧ point = day 12 }
    let before := record (start { base with review := reviewed }) excessPosting.filing.payment
    let filed := file before excessPosting
    let reversal := refundReturnPosting excessPosting.posting excessReturn
    let returned := { recordReturn filed excessReturn with
      credit := { (recordReturn filed excessReturn).credit with ledger := filed.credit.ledger ++
        [reversal] } }
    let final := { returned with review := { reviewed with
      recoveries := [(excessCorrection, excessRecovery)] } }
    Workflow.Step before (observe excessPosting) filed ∧
    Workflow.Step filed (.refundReturned excessPosting.filing.payment excessReturn reversal) returned ∧
    Workflow.Step returned (.review evidence (.fileRecovery form.lesson excessCorrection excessRecovery))
      final ∧
    final.holds.payments.posted = [excessPosting.filing.payment] ∧
    creditsRestoredFor form.place final.credit.ledger (day 14) (some 12) = 100 ∧
    refundBalanceDue form.place final.credit.ledger (day 14) 100 (some 12) = 0 ∧
    refundExcessRetained form.place final.credit.ledger (day 14) 100 12 = 0 := by
  let ledger := [debit, excessPosting.posting, refundReturnPosting excessPosting.posting excessReturn]
  refine ⟨fileAtRoot (verifiesExcessReceipt _), ?_, ?_, rfl, ?_, ?_, ?_⟩
  · refine Workflow.Step.refundReturned ?_
      (.returnPayment (paid := excessPosting.filing.payment) excessReturn ?_ rfl ?_ ?_ ?_ ?_)
    all_goals simp [refundReturnMatches, LessonRefundReceiptMatches,
      PaymentHistory.actualPaymentWithEvidence, file, record, start, Workflow.State.withCourse,
      Workflow.State.course, Workflow.State.withHolds, Workflow.CreditBook.fromEvidence,
      Workflow.LessonFile.evidence, fileRefund, ledgerWithObservedRefund, observedRefundReturns,
      refundReturnPosting, excessPosting, excessReturn, refundAt, debit, form]
    all_goals decide +kernel
  · apply Workflow.Step.review
    · trivial
    · trivial
    · intro _ impossible
      cases impossible
    apply Workflow.Review.Step.fileRecovery
    · change excessCorrection ∈ [excessCorrection]
      simp
    · rfl
    · refine ⟨rfl, rfl, excessPosting.filing.payment, ⟨rfl, rfl, rfl, by decide⟩, rfl,
        ⟨?_, rfl⟩, by decide, by decide, by decide, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl,
        ?_, ?_, ?_⟩
      all_goals simp [PaymentHistory.distinctReceipts, PaymentHistory.validReturns,
        recordReturn, file, record, start, Workflow.State.withHolds, excessPosting, excessReturn]
      all_goals decide +kernel
    · intro prior recorded
      exact (List.not_mem_nil recorded).elim
  · change creditsRestoredFor form.place ledger (day 14) (some 12) = 100
    decide +kernel
  · change refundBalanceDue form.place ledger (day 14) 100 (some 12) = 0
    decide +kernel
  · change refundExcessRetained form.place ledger (day 14) 100 12 = 0
    decide +kernel

private def priorPart : PaymentPart :=
  { part with ref := { part.ref with obligation := 11 }, amount := 80 }

private def priorAssessment : AssessedRefund :=
  { assessment with amount := { assessment.amount with
      obligation := 11, trigger := day 3, recordedAt := day 4, principal := 80, parts := [priorPart] } }

private def priorReview : Workflow.Review.History :=
  let priorCredit : PostedPayment := ⟨89, ⟨priorPart.ref, .account 401, 30, 80, day 7⟩, some 87⟩
  let matter : ReviewMatter := ⟨21, 42, [201]⟩
  let original : Workflow.Review.OriginalRecord := ⟨⟨matter, 101, 50, day 4⟩, some priorPart⟩
  let corrected : PaymentPart := { priorPart with amount := 60 }
  let correction : PaymentCorrectionCase :=
    ⟨priorPart, ⟨matter, 60, day 8, "Refund principal corrected", 102, true⟩,
      ⟨42, 101, 102, 30, day 8, [201]⟩, ⟨corrected, day 8, [priorCredit]⟩⟩
  { Workflow.Review.History.empty with
    originals := [original]
    corrections := [.monetary original correction] }

/-- A linked correction makes 20 of the earlier 80 a surplus. The distinct refund can use its 40. -/
theorem excessOnEarlierRefundDoesNotReduceAnotherRefund :
    let newPart : PaymentPart := { part with amount := 40 }
    let amount := { assessment.amount with
      trigger := day 9, recordedAt := day 10, principal := 40, parts := [newPart] }
    let refunds : History := { assessments := [priorAssessment, { assessment with amount }] }
    let prior := [debit, ⟨89, 401, .lessonRefund 42 1 11, 80, day 7⟩]
    let receipt : CreditPosting := ⟨91, 401, .lessonRefund 42 1 12, 40, day 11⟩
    creditsRestoredFor form.place prior (day 9) = 80 ∧
    refundBalanceDue form.place prior (day 9) 40 (some 12) = 40 ∧
    (∃ earlier ∈ refunds.earlierRefunds amount priorReview,
      feeAdjustmentRefundPrincipal form.place prior (day 9) 12 100 earlier = 40) ∧
    ∃ principals ∈ refunds.otherRefundPrincipals amount.form amount.obligation priorReview (day 11),
      ValidLessonRefund form.place (prior ++ [receipt]) receipt 12 40 false principals := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨[⟨11, 42, 1, day 3, day 7, day 8, none, 60⟩], ?_, by decide +kernel⟩
    cbv
  · exact ⟨[(11, 60)], by decide +kernel, ⟨⟨by simp, rfl, rfl, by decide⟩,
      by decide +kernel, by decide +kernel⟩⟩

/-- A retained original decision without a Redress assessment supplies the same prior principal. -/
theorem reviewOnlyPriorRefundPreservesCorrectedPayment :
    let newPart : PaymentPart := { part with amount := 40 }
    let oldPart : PaymentPart := { part with amount := 20 }
    let portion : CorrectedPortion := ⟨newPart, [oldPart]⟩
    let scope : CorrectedMonetaryScope := ⟨portion, [portion], 20, 40⟩
    let matter : ReviewMatter := ⟨22, 42, [201]⟩
    let correction : PaymentCorrectionCase :=
      ⟨oldPart, ⟨matter, 60, day 9, "Revised second refund", 104, true⟩,
        ⟨42, 103, 104, 30, day 9, [201]⟩, ⟨newPart, day 9, []⟩⟩
    let earlier : CreditPosting := ⟨89, 401, .lessonRefund 42 1 11, 80, day 7⟩
    let receipt : CreditPosting := ⟨91, 401, .lessonRefund 42 1 12, 40, day 11⟩
    let paid : PostedPayment := ⟨91, ⟨newPart.ref, .account 401, 30, 40, day 11⟩, some 92⟩
    let priorPaid : PostedPayment := ⟨89, ⟨priorPart.ref, .account 401, 30, 80, day 7⟩, some 87⟩
    let payment : CorrectionPaymentRecord := ⟨104, paid, some receipt⟩
    let history : PaymentHistory := ⟨[priorPaid, paid], [], []⟩
    let credits := [debit, earlier, receipt]
    let redress : History := {}
    ∃ principals ∈ redress.otherRefundPrincipals form 12 priorReview (day 11),
      feeAdjustmentRefundPrincipal form.place [debit, earlier] (day 9) 12 100 [] principals = 40 ∧
      correction.additionalPaymentPosted form.lesson history credits (some form.place) payment
        scope principals ∧
      ¬ correction.additionalPaymentPosted form.lesson history credits (some form.place) payment scope := by
  refine ⟨[(11, 60)], by decide +kernel, by decide +kernel, ?_, ?_⟩
  · let posting : CreditPosting := ⟨91, 401, .lessonRefund 42 1 12, 40, day 11⟩
    refine ⟨rfl, by decide, rfl, rfl, rfl, by decide, ⟨by simp, rfl⟩, rfl,
      ⟨40, ?_, by decide⟩, by decide +kernel, form.place, by simp, posting, rfl, rfl, rfl, rfl,
      ⟨⟨by simp [posting], rfl, rfl, by decide⟩, by decide +kernel, by decide +kernel⟩⟩
    exact ⟨form.place, by simp, rfl, rfl, rfl, by decide +kernel⟩
  · intro allowed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, place, debited, credit, retained, _, _, _, caps⟩ := allowed
    have samePlace : place = form.place := Option.some.inj debited.symm
    let earlier : CreditPosting := ⟨89, 401, .lessonRefund 42 1 11, 80, day 7⟩
    let posting : CreditPosting := ⟨91, 401, .lessonRefund 42 1 12, 40, day 11⟩
    have sameCredit : credit = posting := Option.some.inj retained.symm
    subst place
    subst credit
    let prior := [debit, earlier, posting].filter (fun entry ↦ decide (entry.point.before (day 11)))
    have amount := caps.2.2
    change (40 : Amount) ≤ debitTotal form.place prior (day 11) -
      creditsAppliedToLessonRefunds form.place prior (day 11) [] at amount
    have room : debitTotal form.place prior (day 11) -
        creditsAppliedToLessonRefunds form.place prior (day 11) [] = 20 := by decide +kernel
    rw [room] at amount
    exact (by decide +kernel : ¬(40 : Amount) ≤ 20) amount

private def directRequest : DirectRefundRequest :=
  ⟨42, 1, 201, ["teaching"], day 4, day 5, True⟩

private def failedService : OutstandingOriginalServices :=
  ⟨42, 1, ["teaching"], 100, fun service point ↦ service = "teaching" ∧ point = day 5⟩

private def faultRefund : AssessedRefund :=
  let fault : FaultFacts :=
    { form
      fault := .provider ⟨42, 1, 10, .arranging, True, True, True⟩
      authority := none
      disputed := false
      decisions := { authorities, terms := facts.terms ⟨1, 42, [201]⟩, appointments := []
                     faultOutcomes := [], faultMatterCovers := fun _ _ ↦ False
                     wasResponsibleTutor := fun _ _ ↦ False
                     originalAttendanceTime := fun _ _ _ ↦ False }
      teaching := .none }
  { assessment with
    amount := { assessment.amount with basis := .directRequest, reason := "Direct refund" }
    evidence := .faultRefund fault (.direct directRequest failedService) none }

private def closurePosting : RefundPosting :=
  { excessPosting with
    assessment := faultRefund
    filing := { excessPosting.filing with settlement := { excessPosting.filing.settlement with
      basis := .directRequest, reason := "Direct refund" } } }

private def closureInitial (base : Workflow.State) : Workflow.State :=
  let s := start base
  { s with
    redress := { assessments := [faultRefund], requests := [directRequest] }
    review := .empty
    credit := { s.credit with creditRecords := { s.credit.creditRecords with
      closed := [], lessonFees := {} } } }

private def coveredSettlement : LessonSettlement := ⟨42, 1, 0, 100, 100, 120, 0, 0⟩
private def fullClosure : FullRefundClosure := ⟨42, 1, day 11, [], [], []⟩

/-- Full restoration can close the case before the factual excess has been returned. -/
theorem fullRefundClosesBeforeRecoveringExcess (base : Workflow.State) :
    let initial := closureInitial base
    let before := record initial closurePosting.filing.payment
    let received := file before closurePosting
    let closing := received.withCourse 42 (closeRefund (received.course 42) fullClosure [])
    let closed := closing.withHolds received.holds
    Workflow.Step initial (.payment (.post closurePosting.filing.payment)) before ∧
    Workflow.Step before (observe closurePosting) received ∧
    Workflow.Step received (.redress (.closeFullRefund faultRefund coveredSettlement fullClosure [] True))
      closed ∧
    closed.credit.creditRecords.closed = [fullClosure] ∧
    closed.holds.payments.returned = [] ∧
    coveredSettlement.restored = 120 ∧
    refundExcessRetained form.place closed.credit.ledger (day 11) 100 12 = 20 := by
  refine ⟨Workflow.Step.payment trivial (.post _ (by decide) (by simp [closureInitial, start])),
    fileAtRoot ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp [RefundPosting.observedFiling, RefundPosting.verifiedFiling, closureInitial,
      closurePosting, faultRefund, excessPosting, refundAt, record, start, Workflow.State.withHolds,
      Workflow.State.course, Workflow.LessonFile.evidence, ledgerWithObservedRefund,
      observedRefundReturns, debit, assessment, RefundAssessment.partsMatch,
      VerifiedLessonRefund.matches, RefundRecord.matches, LessonRefundPostingMatches,
      HoldHistory.approvalRecorded, PaymentHistory.actualPaymentWithEvidence, PaymentHistory.validReturns,
      PaymentHistory.distinctReceipts, PaymentApproval.authorisedAtGrant, PaymentRecipient.accepts,
      facts, authorities, approved, part, form, refundDeadline]
    all_goals (repeat' first | exact formMatches | exact receiptTime _ | apply And.intro)
    all_goals decide +kernel
  · apply Workflow.Step.redress
    · trivial
    · trivial
    · simp [Workflow.Redress.Event.usesRecordedReviews, Event.assessmentDecisions]
    · trivial
    refine ⟨?_, rfl, rfl, rfl⟩
    let before := record (closureInitial base) closurePosting.filing.payment
    let ev := (file before closurePosting).course 42
    let ledger := [debit, closurePosting.posting]
    change faultRefund.closureConforms (closureInitial base).redress ev
      coveredSettlement fullClosure [] True .empty
    refine ⟨by simp [closureInitial], by decide, by decide +kernel, ?_, ?_, ?_,
      by simp [fullClosure], ?_⟩
    · change ¬fullRefundClosedBy form.place [] (day 11)
      simp [fullRefundClosedBy]
    · change coveredSettlement.matchesPaymentHistory form.place ledger (day 11)
      exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩
    · simp [closureRemovalsMatch]
    · refine ⟨100, by decide +kernel, [], by rfl, ?_, ?_, ?_⟩
      · simp +contextual [faultRefund, assessment, RefundCause.assess, closureInitial, directRefundTrigger,
          FaultBasis.lessonWithResponsibleTutor, FaultBasis.applies, ProviderFaultFacts.applies,
          directRequest, DirectRefundRequest.validFor, failedService, OutstandingOriginalServices.verifiedFor,
          History.remediesFor, FaultFacts.evidence, outstandingRefundFee, outstandingRefundNeedsFullWaiver,
          Place.matches, form, Moment.by]
        all_goals (repeat' first | decide +kernel | apply And.intro)
        refine ⟨100, ?_, by decide⟩
        change ({} : LessonFeeAmendments).feeAt form (day 5) 100
        simp [LessonFeeAmendments.feeAt, form]
      · change RefundPrincipalsRestored form.place ledger (day 11) [(12, 100)]
        refine ⟨by simp, ?_⟩
        intro liability present
        have recorded : liability = (12, 100) := by simpa using present
        subst liability
        exact ⟨by decide, by decide +kernel⟩
      · change closedByFullRefund form.place ledger [] [] 100
          (sumAmounts [(12, 100)] Prod.snd) 0 True fullClosure
        simp [closedByFullRefund, FullRefundClosure.dispositionsRecorded,
          FullRefundClosure.creditDispositionsRecorded, fullClosure, form, ledger, debit,
          closurePosting, excessPosting, refundAt]
        all_goals decide +kernel
  · change refundExcessRetained form.place [debit, closurePosting.posting] (day 11) 100 12 = 20
    decide +kernel

private def partialPart : PaymentPart := { part with amount := 50 }

private def partialAssessment : AssessedRefund :=
  { faultRefund with
    amount := { faultRefund.amount with finalFee := 50, principal := 50, parts := [partialPart] }
    evidence :=
      match faultRefund.evidence with
      | .faultRefund fault _ acceptance =>
        .faultRefund { fault with teaching := .some }
          (.direct directRequest { failedService with feeAttributable := 50 }) acceptance
      | other => other }

private def fullReview : ReviewFinding :=
  ⟨⟨12, 42, [201]⟩, 60, day 9, "The student received none of the lesson", 81, true⟩

private def priorDecision : Workflow.Review.OriginalRecord :=
  ⟨⟨fullReview.matter, 80, 50, day 6⟩, some partialPart⟩

private def actualFullReceipt : RefundPosting :=
  let receipt := refundAt (day 7) true
  { receipt with
    assessment := partialAssessment
    part := partialPart
    filing := { receipt.filing with settlement := { receipt.filing.settlement with
      basis := .directRequest, reason := "Direct refund", finalFee := 50, amount := 50 } } }

private def fullCorrection : PaymentCorrectionCase :=
  ⟨partialPart, fullReview, ⟨42, 80, 81, 30, day 10, [201]⟩,
    ⟨part, day 9, [actualFullReceipt.filing.payment]⟩⟩

private def fullReviewAuthorities : ReviewAuthorities :=
  { authorities with
    reviewer := fun matter actor point ↦ matter = fullReview.matter ∧ actor = 60 ∧ point = day 9
    corePartner := fun actor point ↦ actor = 61 ∧ point = day 8 }

private def reviewBeforeFull : Workflow.Review.History :=
  { Workflow.Review.History.empty with
    originals := [priorDecision]
    appointments := [⟨fullReview.matter, 61, 60, day 8⟩]
    reviewFindings := [fullReview] }

private def partialRefundReceived (base : Workflow.State) : Workflow.State :=
  let before := record (start base) actualFullReceipt.filing.payment
  let before := { before with
    redress := { assessments := [partialAssessment], requests := [directRequest] }
    review := reviewBeforeFull
    credit := { before.credit with creditRecords := { before.credit.creditRecords with
      closed := [], lessonFees := {} } } }
  file before actualFullReceipt

private noncomputable def reviewedAssessment (s : Workflow.State) : AssessedFaultRefund :=
  let facts : FaultFacts :=
    ⟨form, .provider ⟨42, 1, 10, .arranging, True, True, True⟩, none, false,
      { authorities := fullReviewAuthorities, terms := facts.terms fullReview.matter,
        appointments := [], faultOutcomes := [], faultMatterCovers := fun _ _ ↦ False,
        wasResponsibleTutor := fun _ _ ↦ False, originalAttendanceTime := fun _ _ _ ↦ False },
      .none⟩
  ⟨faultRefund.faultCase s.redress (s.course 42) facts
    (.direct directRequest failedService) none [], day 5, day 8, day 8, none, 0, 100⟩

private noncomputable def fullReviewResult (before : Workflow.State) : Workflow.State :=
  { before with
    review := { reviewBeforeFull with
      corrections := [.monetary priorDecision fullCorrection]
      refundAssessments := [(fullCorrection, reviewedAssessment before)] }
    holds := before.holds.withPartRevision priorDecision.outcome fullCorrection }

private def settleWithFullReceipt : LessonSettlement :=
  { coveredSettlement with restored := 100 }

private def closeAfterReview : Workflow.Event :=
  .redress (.closeFullRefund partialAssessment settleWithFullReceipt fullClosure [] True)

private theorem fullRefundCauseAssessesZero (ev : StartEvidence) (evidence : RemedyEvidence)
    (received : evidence.teaching = .none) (agreed : evidence.feeAt (day 5) 100) :
    (RefundCause.direct directRequest failedService).assess form
      (.provider ⟨42, 1, 10, .arranging, True, True, True⟩)
      ev none evidence [] [directRequest] (day 9) (day 5) 0 := by
  simp +contextual [RefundCause.assess, directRefundTrigger, DirectRefundRequest.validFor,
    directRequest, failedService, OutstandingOriginalServices.verifiedFor, outstandingRefundFee,
    outstandingRefundNeedsFullWaiver, Place.matches, Moment.by, FaultBasis.applies,
    FaultBasis.lessonWithResponsibleTutor, ProviderFaultFacts.applies, form, received]
  all_goals (repeat' first | decide +kernel | apply And.intro)
  exact ⟨100, agreed, by decide⟩

set_option maxHeartbeats 1000000 in
/-- A recorded partial assessment is immutable. Once a verified review makes it a full
refund, the same already-restored principal can close at the root without another receipt. -/
theorem revisedPartialRefundCloses (base : Workflow.State) (external : Workflow.Review.Evidence) :
    let before := partialRefundReceived base
    let after := fullReviewResult before
    let evidence := { external with
      authority := fullReviewAuthorities
      recordedAmount := fun matter outcome amount ↦
        matter = fullReview.matter ∧ outcome = fullReview.outcome ∧ amount = part
      reviewedFaultRefund := fun _ ↦ some (reviewedAssessment before) }
    Workflow.Step before (.review evidence (.recordCorrection form.lesson
      (.monetary priorDecision fullCorrection))) after ∧
    Workflow.Step after closeAfterReview
      ((after.withCourse 42 (closeRefund (after.course 42) fullClosure [])).withHolds after.holds) ∧
    (∀ next, ¬Workflow.Step before closeAfterReview next) ∧
    after.redress.assessments = [partialAssessment] ∧
    after.holds.payments.posted = [actualFullReceipt.filing.payment] := by
  dsimp only
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · apply Workflow.Step.review
    · trivial
    · trivial
    · intro row same
      cases same
    · apply Workflow.Review.Step.recordMonetary
      · exact List.mem_cons_self
      · exact List.mem_cons_self
      · exact ⟨rfl, rfl, rfl⟩
      · refine ⟨[], rfl, ?_⟩
        simp [PaymentCorrectionCase.recorded, PaymentCorrectionCase.outcomeConforms,
          correctionAfterReviewConforms, correctionRecordConforms, reviewFindingConforms,
          reviewFindingConformsWithContacts, independentReviewer,
          ReviewAuthorities.mayDecideDispute, ReviewAuthorities.disinterested, DirectInterest.affected,
          Workflow.Review.History.authorities, ReviewMatter.sameCase, ReviewAppointment.applies,
          correctionActualPaymentsRecorded,
          correctionActualPaymentsRetained, MonetaryCorrection.matchesReceipt,
          PaymentHistory.distinctReceipts, PaymentHistory.validReturns,
          partialRefundReceived, file, record, start, reviewBeforeFull,
          Workflow.State.withHolds, Workflow.State.withCourse, Workflow.State.reviewEvidence,
          fullCorrection, fullReview, priorDecision, part, partialPart, actualFullReceipt,
          refundAt, fullReviewAuthorities, authorities, form]
        all_goals (repeat' first | decide +kernel | apply And.intro)
        intro _ actor _ _ same _ _ _ _
        subst actor
        decide
      · change fullCorrection ∉ ([] : List PaymentCorrectionCase)
        simp
  · apply Workflow.Step.redress
    · trivial
    · trivial
    · simp [Workflow.Redress.Event.usesRecordedReviews, Event.assessmentDecisions]
    · trivial
    · refine ⟨?_, rfl, rfl, rfl⟩
      change partialAssessment.closureConforms _
        ((fullReviewResult (partialRefundReceived base)).course 42)
        settleWithFullReceipt fullClosure [] True _
      refine ⟨List.mem_cons_self, by decide,
        ?_, ?_, ?_, ?_, by simp [fullClosure], 100, ?_, [], ?_, ?_, ?_, ?_⟩
      · have selected : partialAssessment.amount.currentReviewAt
            (fullReviewResult (partialRefundReceived base)).review fullClosure.closedAt = [fullReview] := by
          change partialAssessment.amount.currentReviewAt
            { reviewBeforeFull with corrections := [.monetary priorDecision fullCorrection] }
            (day 11) = [fullReview]
          decide +kernel
        simp only [selected]
        rfl
      · change ¬fullRefundClosedBy form.place [] (day 11)
        simp [fullRefundClosedBy]
      · change settleWithFullReceipt.matchesPaymentHistory
          form.place [debit, actualFullReceipt.posting] (day 11)
        exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩
      · simp [closureRemovalsMatch]
      · change partialAssessment.amount.principalAt
            { reviewBeforeFull with corrections := [.monetary priorDecision fullCorrection] }
            (day 11) = some 100
        decide +kernel
      · rfl
      · have selected : partialAssessment.amount.currentReviewAt
            (fullReviewResult (partialRefundReceived base)).review fullClosure.closedAt =
            [fullReview] := by
          change partialAssessment.amount.currentReviewAt
            { reviewBeforeFull with corrections := [.monetary priorDecision fullCorrection] }
            (day 11) = [fullReview]
          decide +kernel
        simp only [selected]
        change partialAssessment.reviewedFeeConforms _ _
          (fullReviewResult (partialRefundReceived base)).review fullReview
          (reviewedAssessment (partialRefundReceived base)) (day 11) true
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, show (0 : Amount) ≤ 0 by decide,
          [], rfl, [], rfl, ?_, ?_, ?_⟩
        · change reviewFindingRecordedConforms
            (reviewBeforeFull.authorities fullReviewAuthorities) (some 60)
            reviewBeforeFull.appointments [] [fullReview] fullReview
          simp +contextual [reviewFindingRecordedConforms, reviewFindingConformsWithContacts,
            independentReviewer, didNotMakeOriginalFinding, Workflow.Review.History.authorities,
            ReviewAuthorities.mayDecideDispute, ReviewAuthorities.disinterested, DirectInterest.affected,
            fullReviewAuthorities, authorities, reviewBeforeFull, Workflow.Review.History.empty,
            priorDecision, fullReview, ReviewMatter.sameCase]
          all_goals decide +kernel
        · unfold FaultRefundCase.amountDue
          dsimp only [AssessedRefund.faultCase, reviewedAssessment]
          refine ⟨formMatches, ?_, ?_, ?_, ⟨0, 100, ?_, ?_, ?_⟩, ?_, rfl, ?_, ?_⟩
          · exact fun impossible ↦ (Bool.false_ne_true impossible).elim
          · change FaultMatchesEvidence form (.provider ⟨42, 1, 10, .arranging, True, True, True⟩)
              _ _ _ _ (day 5)
            simp [FaultMatchesEvidence, FaultBasis.applies, FaultBasis.lessonWithResponsibleTutor,
              ProviderFaultFacts.applies, Place.matches, form]
          · change ∀ progress ∈ ([] : List RemedyProgress), _
            simp
          · change ({} : LessonFeeAmendments).feeAt form (day 5) 100
            simp [LessonFeeAmendments.feeAt, form]
          · apply fullRefundCauseAssessesZero _ _ rfl
            change ({} : LessonFeeAmendments).feeAt form (day 5) 100
            simp [LessonFeeAmendments.feeAt, form]
          · left
            refine ⟨?_, by decide⟩
            simp [originalCompensationRelief, FaultBasis.standardCompensationOffered,
              FaultBasis.lessonWithResponsibleTutor, FaultBasis.applies, ProviderFaultFacts.applies,
              Place.matches, partialAssessment, faultRefund, assessment, form]
          · change PaymentDeadline.fromRefundTrigger (.fixed (day 8)) [] (day 5) (day 8)
            simp [PaymentDeadline.fromRefundTrigger, PaymentDeadline.applies]
          · change EarlierFeeRefundsFor form.place (day 5) []
            simp [EarlierFeeRefundsFor]
          · unfold FaultRefundCase.assessedAmount
            change (100 : Amount) = additionalRefundDue
              (grossLessonCreditRestoration
                (debitTotal form.place [debit, actualFullReceipt.posting] (day 5)) 0)
              (creditsAppliedToLessonRefunds form.place [debit, actualFullReceipt.posting] (day 5)
                ([] ++ []) - 0)
              (earlierOutstanding form.place [debit, actualFullReceipt.posting] [] (day 5) [])
            cbv
        · have nextPrincipal : partialAssessment.amount.principalAt
              { reviewBeforeFull with corrections := [.monetary priorDecision fullCorrection] }
              (day 11) = some 100 := by decide +kernel
          have principal : partialAssessment.amount.principalAt
              (fullReviewResult (partialRefundReceived base)).review (day 11) = some 100 :=
            nextPrincipal
          change partialAssessment.amount.principalAt
            (fullReviewResult (partialRefundReceived base)).review (day 11) = _
          rw [principal]
          congr 1
          unfold FaultRefundCase.assessedAmount
          change (100 : Amount) = additionalRefundDue
              (grossLessonCreditRestoration
                (debitTotal form.place [debit, actualFullReceipt.posting] (day 5)) 0)
              (creditsAppliedToLessonRefunds form.place [debit, actualFullReceipt.posting] (day 5) [] -
                creditsRestoredFor form.place [debit, actualFullReceipt.posting] (day 5) (some 12)) _
          cbv
        · intro _
          apply fullRefundCauseAssessesZero _ _ rfl
          change ({} : LessonFeeAmendments).feeAt form (day 5) 100
          simp [LessonFeeAmendments.feeAt, form]
      · change RefundPrincipalsRestored form.place [debit, actualFullReceipt.posting]
          (day 11) [(12, 100)]
        refine ⟨by simp, ?_⟩
        intro liability present
        have same : liability = (12, 100) := by simpa using present
        subst liability
        exact ⟨by decide, by decide +kernel⟩
      · change closedByFullRefund form.place ([debit, actualFullReceipt.posting] ++ [])
          [] [] 100 (sumAmounts [(12, 100)] Prod.snd) 0 True fullClosure
        simp [closedByFullRefund, FullRefundClosure.dispositionsRecorded,
          FullRefundClosure.creditDispositionsRecorded, fullClosure, form, debit,
          actualFullReceipt, refundAt]
        all_goals decide +kernel
  · intro next transitioned
    cases transitioned
    rename_i checked
    have stale : partialAssessment.feeAt (partialRefundReceived base).review (day 11) = some 0 :=
      checked.1.2.2.1
    exact (by decide +kernel :
      partialAssessment.feeAt reviewBeforeFull (day 11) ≠ some 0) stale

#print axioms revisedPartialRefundCloses

/-- Another obligation's credit cannot discharge the current refund at closure. -/
theorem unrelatedCreditDoesNotCloseThisRefund :
    let ledger := [debit, { excessPosting.posting with kind := .lessonRefund 42 1 11 }]
    ¬RefundPrincipalsRestored form.place ledger (day 11) [(12, 100)] := by
  dsimp only
  intro restored
  have settled := restored.2 (12, 100) (by simp)
  exact (by decide +kernel :
    refundBalanceDue form.place [debit, { excessPosting.posting with kind := .lessonRefund 42 1 11 }]
      (day 11) 100 (some 12) ≠ 0) settled.2

/-- An observed receipt with no approval cannot enter the live path with any supplied route. -/
theorem receiptWithoutApprovalCannotExecute (base after : Workflow.State)
    (route : Option PaymentApprovalRoute) :
    ¬Workflow.Step (start base false)
      (.redress (.postRefund { refundAt (day 9) false with route } facts authorities conditions))
      after := by
  intro step
  cases step with
  | redress _ _ _ _ rule =>
    obtain ⟨_, _, _, _, valid⟩ := rule.1
    obtain ⟨_, _, _, approval, _⟩ := valid
    cases approval

private def legalCutoff : Moment := ⟨7 * 86400, 1⟩

private def receiptAfterLegalCutoff : RefundPosting :=
  let post := refundAt (day 8)
  let amount := post.assessment.amount
  let schedule := { amount.schedule with legalDeadline := some legalCutoff }
  { post with
    assessment := { post.assessment with amount := { amount with schedule } }
    filing := { post.filing with settlement := { post.filing.settlement with due := legalCutoff } } }

/-- A receipt within the contractual window can still be late under the earlier legal cutoff. -/
theorem receiptAfterEarlierLegalDateFilesLate (base : Workflow.State) :
    let post := receiptAfterLegalCutoff
    let initial := { start base with redress := { assessments := [post.assessment] } }
    let before := record initial post.filing.payment
    let after := file before post
    let schedule := post.assessment.amount.schedule
    Workflow.Step initial (.payment (.post post.filing.payment)) before ∧
    Workflow.Step before (observe post) after ∧
    schedule.dueAt = day 7 ∧ schedule.legalDeadline = some legalCutoff ∧
    post.filing.payment.instruction.atTime.by schedule.originalExecutionDeadline ∧
    (after.credit.creditRecords.verifiedRefunds.map (·.settlement.due)) = [legalCutoff] ∧
    ¬FiledPaymentOnTime form authorities facts after.holds part schedule post.filing.payment [] := by
  refine ⟨Workflow.Step.payment trivial (.post _ (by decide) (by simp [start])),
    fileAtRoot ?_, rfl, rfl, by decide, rfl, ?_⟩
  · simp [RefundPosting.observedFiling, RefundPosting.verifiedFiling, receiptAfterLegalCutoff,
      record, start, Workflow.State.withHolds, Workflow.State.course, Workflow.LessonFile.evidence,
      refundAt, ledgerWithObservedRefund, observedRefundReturns, debit, assessment,
      RefundAssessment.partsMatch, VerifiedLessonRefund.matches, RefundRecord.matches,
      LessonRefundPostingMatches, HoldHistory.approvalRecorded,
      PaymentHistory.actualPaymentWithEvidence, PaymentHistory.validReturns,
      PaymentHistory.distinctReceipts, PaymentApproval.authorisedAtGrant,
      PaymentRecipient.accepts, facts, authorities, approved, part, form, refundDeadline]
    all_goals (repeat' first | exact formMatches | exact receiptTime _ | apply And.intro)
    all_goals decide +kernel
  · intro timely
    rcases timely.1 with ordinary | ⟨_, member, _⟩
    · exact (by decide : ¬(day 8).by legalCutoff) (ordinary.2.2.1 legalCutoff (by decide))
    · exact List.not_mem_nil member

private def filedLate (base : Workflow.State) : Workflow.State :=
  file (beforeFiling base false) (refundAt (day 9))

private def unrelatedTopUp : TopUpReceipt := ⟨100, 202, 30, 402, 40, day 12⟩

private def unrelatedPosting : CreditPosting := ⟨101, 402, .topUp 100, 40, day 12⟩

private def returnBase (base : Workflow.State) : Workflow.State :=
  let records := { base.credit.creditRecords with
      topUps := [], grants := [], topUpReturns := [], closed := []
      ownsAccount := fun actor account ↦ actor = 202 ∧ account = 402
      courseProviderAt := fun actor point ↦ actor = 30 ∧ point = day 12 }
  { base with credit := { base.credit with creditRecords := records } }

private def appendUnrelated (s : Workflow.State) : Workflow.State :=
  let records := { s.credit.creditRecords with
    topUps := s.credit.creditRecords.topUps ++ [unrelatedTopUp] }
  { s with credit := { s.credit with
      ledger := s.credit.ledger ++ [unrelatedPosting]
      creditRecords := records } }

private theorem postUnrelated (base : Workflow.State) :
    let s := filedLate (returnBase base)
    Workflow.Step s (.credit (.topUp unrelatedTopUp unrelatedPosting)) (appendUnrelated s) := by
  refine Workflow.Step.credit ⟨?_, ?_, rfl⟩
  · simp [topUpPostingMatches, unrelatedTopUp, unrelatedPosting, Moment.by] <;> decide +kernel
  simp [ValidCreditHistory, CreditOriginsValid, filedLate, returnBase, beforeFiling, file, record,
    start, Workflow.State.withCourse, Workflow.State.withHolds, Workflow.State.course,
    Workflow.LessonFile.evidence, Workflow.CreditBook.fromEvidence, fileRefund,
    ledgerWithObservedRefund, observedRefundReturns, unrelatedTopUp, unrelatedPosting,
    topUpPostingMatches, refundAt, debit, VerifiedLessonRefund.matches, RefundRecord.matches,
    LessonRefundPostingMatches, PaymentHistory.actualPaymentWithEvidence,
    PaymentHistory.distinctReceipts,
    PaymentApproval.authorisedAtGrant, returnedFrom, sumAmountsWhere,
    assessment, authorities, approved, part, form]
  all_goals (repeat' first | exact formMatches | exact receiptTime _ | apply And.intro)
  all_goals first | decide +kernel | (intro _; decide +kernel)

private def laterReturn : ReturnedPayment := ⟨93, 91, 25, day 11, 94⟩

private def reversal : CreditPosting := refundReturnPosting (refundAt (day 9)).posting laterReturn

private def applyReturn (s : Workflow.State) : Workflow.State :=
  let next := recordReturn s laterReturn
  { next with credit := { next.credit with ledger := s.credit.ledger ++ [reversal] } }

private theorem directReturn (base : Workflow.State) (unrelated : Bool) :
    let s := if unrelated then appendUnrelated (filedLate base) else filedLate base
    Workflow.Step s (.refundReturned (refundAt (day 9)).filing.payment laterReturn reversal)
      (applyReturn s) := by
  cases unrelated <;>
    refine Workflow.Step.refundReturned ?_ (.returnPayment
      (paid := (refundAt (day 9)).filing.payment) laterReturn ?_ ?_ ?_ ?_ ?_ ?_) <;>
    simp [refundReturnMatches, LessonRefundReceiptMatches, PaymentHistory.actualPaymentWithEvidence,
      filedLate, appendUnrelated, beforeFiling, file, record, start, Workflow.State.withCourse,
      Workflow.State.course, Workflow.State.withHolds, Workflow.CreditBook.fromEvidence,
      Workflow.LessonFile.evidence, fileRefund, ledgerWithObservedRefund, observedRefundReturns,
      reversal, laterReturn, refundReturnPosting, refundAt, debit, unrelatedPosting, form]
  all_goals decide +kernel

/-- An observed return can be entered immediately after the refund filing. -/
theorem directReturnAfterFiling (base : Workflow.State) :
    Workflow.Step (filedLate base)
      (.refundReturned (refundAt (day 9)).filing.payment laterReturn reversal)
      (applyReturn (filedLate base)) :=
  directReturn base false

/-- Filing the day-11 return after the unrelated day-12 entry preserves both actual dates. -/
theorem directReturnFiledAfterLaterPosting (base : Workflow.State) :
    let before := filedLate (returnBase base)
    let posted := appendUnrelated before
    let after := applyReturn posted
    Workflow.Step (beforeFiling (returnBase base) false) (observe (refundAt (day 9))) before ∧
    Workflow.Step before (.credit (.topUp unrelatedTopUp unrelatedPosting)) posted ∧
    Workflow.Step posted (.refundReturned (refundAt (day 9)).filing.payment laterReturn reversal)
      after ∧
    after.credit.ledger = [debit, (refundAt (day 9)).posting, unrelatedPosting, reversal] ∧
    after.holds.payments.posted = posted.holds.payments.posted ∧
    after.holds.payments.returned = [laterReturn] ∧
    balanceBefore after.credit.openingCredit after.credit.ledger 401 (day 10) = 100 ∧
    balanceBefore after.credit.openingCredit after.credit.ledger 401 (day 12) = 75 ∧
    refundBalanceDue form.place after.credit.ledger (day 12) 100 (some 12) = 25 ∧
    balanceBefore after.credit.openingCredit after.credit.ledger 402 (day 13) = 40 := by
  let ledger := [debit, (refundAt (day 9)).posting, unrelatedPosting, reversal]
  let opening : AccountId → Amount := fun account ↦ if account = 401 then 100 else 0
  refine ⟨fileAtRoot (verifiesLateReceipt (returnBase base) false), postUnrelated base,
    directReturn (returnBase base) true, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change balanceBefore opening ledger 401 (day 10) = 100
    decide +kernel
  · change balanceBefore opening ledger 401 (day 12) = 75
    decide +kernel
  · change refundBalanceDue form.place ledger (day 12) 100 (some 12) = 25
    decide +kernel
  · change balanceBefore opening ledger 402 (day 13) = 40
    decide +kernel

theorem duplicateDirectReturnCannotFile (base after : Workflow.State) :
    ¬Workflow.Step (applyReturn (filedLate base))
      (.refundReturned (refundAt (day 9)).filing.payment laterReturn reversal) after := by
  intro step
  cases step with
  | refundReturned matchCredit _ =>
    exact (matchCredit.1 reversal (by
      change reversal ∈ [debit, (refundAt (day 9)).posting, reversal]
      simp)).1 rfl

theorem directReturnCannotUseWrongReceipt {before after : Workflow.State}
    {paid : PostedPayment} {returned : ReturnedPayment} {posting : CreditPosting}
    (wrong : returned.paidReceipt ≠ paid.id) :
    ¬Workflow.Step before (.refundReturned paid returned posting) after := by
  intro step
  cases step with
  | refundReturned matchCredit _ => exact wrong matchCredit.2.1

/-- That same late receipt has no successor through the ordinary live execution route. -/
theorem lateReceiptCannotExecute (base after : Workflow.State) :
    ¬Workflow.Step (start base)
      (.redress (.postRefund (refundAt (day 9)) facts authorities conditions)) after := by
  intro transitioned
  cases transitioned
  rename_i rule
  obtain ⟨⟨_, _, _, _, filed⟩, _, _⟩ := rule
  obtain ⟨route, member, _, filed⟩ := filed.2
  have same : PaymentApprovalRoute.ordinary approved = route := by simpa [refundAt] using member
  subst route
  obtain ⟨_, _, _, _, _, _, _, _, allows, _⟩ := filed
  obtain ⟨_, _, _, _, _, _, _, _, onTime, _, _⟩ := allows
  exact (by decide : ¬(day 9).by (day 8)) onTime

private theorem observedForStep {before after : Workflow.State} {post : RefundPosting}
    (transitioned : Workflow.Step before (observe post) after) :
    post.observedFiling before.redress (before.course post.assessment.amount.form.lesson.id)
      before.holds (day 10) facts authorities := by
  unfold observe at transitioned
  cases transitioned
  rename_i rule
  exact rule.1

/-- The root filing requires the actual receipt's account, obligation and restored amount. -/
theorem filedReceiptMatches {before after : Workflow.State} {post : RefundPosting}
    (transitioned : Workflow.Step before (observe post) after) :
    post.filing.payment.instruction.destination = .account post.assessment.amount.form.place.account ∧
    post.filing.payment.instruction.part.obligation = post.assessment.amount.obligation ∧
    post.filing.payment.instruction.amount = post.posting.amount ∧
    before.holds.payments.actualPaymentWithEvidence post.filing.payment ∧
    ∀ approval ∈ post.filing.approval, before.holds.approvalRecorded approval := by
  obtain ⟨_, _, _, _, _, verified, recorded, _⟩ := observedForStep transitioned
  obtain ⟨_, _, sameForm, sameObligation, _, _, _, _, _, _, _, _, _, fileMatches⟩ := verified
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, evidence, _, _, _, obligation, account,
    amount, _, _⟩ := fileMatches
  exact ⟨account.trans (congrArg (fun row : PartOne ↦ PaymentDestination.account row.place.account)
      sameForm),
    obligation.trans sameObligation, amount, evidence, recorded⟩

theorem wrongAccountCannotFile {before after : Workflow.State} {post : RefundPosting}
    (wrong : post.filing.payment.instruction.destination ≠
      .account post.assessment.amount.form.place.account) :
    ¬Workflow.Step before (observe post) after :=
  fun transitioned ↦ wrong (filedReceiptMatches transitioned).1

theorem wrongObligationCannotFile {before after : Workflow.State} {post : RefundPosting}
    (wrong : post.filing.payment.instruction.part.obligation ≠ post.assessment.amount.obligation) :
    ¬Workflow.Step before (observe post) after :=
  fun transitioned ↦ wrong (filedReceiptMatches transitioned).2.1

theorem wrongAmountCannotFile {before after : Workflow.State} {post : RefundPosting}
    (wrong : post.filing.payment.instruction.amount ≠ post.posting.amount) :
    ¬Workflow.Step before (observe post) after :=
  fun transitioned ↦ wrong (filedReceiptMatches transitioned).2.2.1

theorem wrongPartCannotFile {before after : Workflow.State} {post : RefundPosting}
    (wrong : post.filing.payment.instruction.part ≠ post.part.ref) :
    ¬Workflow.Step before (observe post) after := by
  intro transitioned
  obtain ⟨_, _, _, _, _, _, _, samePart, _⟩ := observedForStep transitioned
  exact wrong samePart

theorem wrongReceiptIdCannotFile {before after : Workflow.State} {post : RefundPosting}
    (wrong : post.filing.payment.id ≠ post.posting.id) :
    ¬Workflow.Step before (observe post) after := by
  intro transitioned
  obtain ⟨_, _, _, _, _, verified, _⟩ := observedForStep transitioned
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, fileMatches⟩ := verified
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, sameId, _⟩ := fileMatches
  exact wrong sameId

theorem alreadyFiledReceiptCannotRefile {before after : Workflow.State} {post : RefundPosting}
    {old : VerifiedLessonRefund} (already : old ∈ before.credit.creditRecords.verifiedRefunds)
    (same : old.payment.id = post.filing.payment.id) :
    ¬Workflow.Step before (observe post) after := by
  intro transitioned
  obtain ⟨_, _, _, _, _, verified, _, _⟩ := observedForStep transitioned
  obtain ⟨_, _, _, _, _, _, _, fresh, _⟩ := verified
  exact fresh old already same

theorem excessRecordedReturnCannotFile {before after : Workflow.State} {post : RefundPosting}
    (tooMuch : ¬sumAmounts
      (before.holds.payments.returned.filter (fun row ↦ row.paidReceipt == post.filing.payment.id))
      ReturnedPayment.amount ≤ post.filing.payment.instruction.amount) :
    ¬Workflow.Step before (observe post) after := by
  intro transitioned
  obtain ⟨_, _, _, _, _, _, _, _, _, _, returns⟩ := observedForStep transitioned
  exact tooMuch (returns.2 post.filing.payment (filedReceiptMatches transitioned).2.2.2.1.1)

/-- The shared filing route accepts the late receipt without making the instruction timely. -/
theorem lateReceiptCanBeAccountedFor (base : Workflow.State) :
    let post := refundAt (day 9)
    let history := (beforeFiling base false).holds
    (PaymentApprovalRoute.ordinary approved).observedPayment authorities facts history part
      post.filing.payment ∧
    ¬(PaymentApprovalRoute.ordinary approved).allows authorities facts history part
      post.assessment.amount.schedule
      conditions post.filing.payment.instruction := by
  constructor
  · simp [PaymentApprovalRoute.observedPayment, refundAt, beforeFiling, record, start, 
      Workflow.State.withHolds, HoldFacts.isCanonicalPart, HoldHistory.approvalRecorded,
      PaymentApproval.authorisedAtGrant, PaymentApproval.originallyCovered,
      PaymentHistory.actualPaymentWithEvidence, PaymentHistory.recipientReceived,
      PaymentHistory.validOutstandingPayment, PaymentHistory.validReturns,
      PaymentHistory.distinctReceipts, PaymentRecipient.accepts, facts, authorities, approved, part]
    all_goals (repeat' apply And.intro)
    all_goals decide +kernel
  · intro execution
    obtain ⟨_, _, _, _, _, _, _, _, timely, _, _⟩ := execution
    exact (by decide : ¬(day 9).by (day 8)) timely

#print axioms lateReceiptCanBeAccountedFor
#print axioms lateReceiptFiles
#print axioms lateReceiptFilesWithReturn
#print axioms actualReceiptFilesWithoutApproval
#print axioms actualExcessRefundFiles
#print axioms actualExcessRefundCanBeRecovered
#print axioms excessRefundCannotExecute
#print axioms excessOnEarlierRefundDoesNotReduceAnotherRefund
#print axioms reviewOnlyPriorRefundPreservesCorrectedPayment
#print axioms fullRefundClosesBeforeRecoveringExcess
#print axioms unrelatedCreditDoesNotCloseThisRefund
#print axioms receiptWithoutApprovalCannotExecute
#print axioms receiptAfterEarlierLegalDateFilesLate
#print axioms directReturnAfterFiling
#print axioms directReturnFiledAfterLaterPosting
#print axioms duplicateDirectReturnCannotFile
#print axioms directReturnCannotUseWrongReceipt
#print axioms lateReceiptCannotExecute
#print axioms filedReceiptMatches
#print axioms wrongAccountCannotFile
#print axioms wrongObligationCannotFile
#print axioms wrongAmountCannotFile
#print axioms wrongPartCannotFile
#print axioms wrongReceiptIdCannotFile
#print axioms alreadyFiledReceiptCannotRefile
#print axioms excessRecordedReturnCannotFile

end SourceV14.FidelityRefundReceiptChecks
