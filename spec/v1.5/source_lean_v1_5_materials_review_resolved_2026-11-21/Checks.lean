import SourceV14

namespace SourceV14.Checks

open Booking Settlement Confirmation CreditEvidence Operations

def m (s n : Nat) : Moment := ⟨s, n⟩

def original : Place := ⟨8, 17, 11, 12, 13, 14, 100, 100⟩
def noDebitPlace : Place := ⟨9, 17, 21, 22, 23, 24, 50, 0⟩
def formDiscount : DiscountRecord :=
  ⟨17, 9, "original-lesson reduction", 50, m 10 1⟩

def debited : CreditPosting := ⟨1, 14, .lessonDebit 17 8, 100, m 10 2⟩
def refunded : CreditPosting := ⟨2, 14, .lessonRefund 17 8 1, 50, m 12 1⟩
def wrongAccount : CreditPosting := ⟨3, 99, .lessonRefund 17 8 1, 20, m 12 2⟩
def reversal : CreditPosting := ⟨4, 14, .creditReturned 2, 10, m 12 3⟩

theorem paidWithoutDebit : paidInFull noDebitPlace [] [formDiscount] (m 10 2) = true := by
  decide +kernel

theorem unknownDiscountDoesNotPay :
    paidInFull noDebitPlace [] [] (m 10 2) = false := by
  decide +kernel

theorem groupCountsDiscountedSeat :
    groupCount ⟨17, 3, [original, noDebitPlace], m 10 1⟩ [debited] [formDiscount]
      [8, 9] [] (m 10 3) = 2 := by
  decide +kernel

theorem sameSecondDebitHasOrder :
    paidInFull original [debited] [] (m 10 1) = false ∧
    paidInFull original [debited] [] (m 10 2) = true := by
  decide +kernel

theorem wrongAccountDoesNotDischargeRefund :
    refundBalanceDue original [debited, refunded, wrongAccount, reversal] (m 12 3) 100 = 60 := by
  decide +kernel

theorem lawfulHalfPaidAsOfReceipt :
    refundBalanceDue original [debited, refunded] (m 12 0) 50 = 50 ∧
    refundBalanceDue original [debited, refunded] (m 12 1) 50 = 0 := by
  decide +kernel

theorem canDistinguishThirtyDayCutWithinOneSecond :
    ¬ fallbackMature (m 10 0) (m (10 + thirtyDays) 2) (m (10 + thirtyDays) 1) ∧
    fallbackMature (m 10 0) (m (10 + thirtyDays) 2) (m (10 + thirtyDays) 3) := by
  simp [fallbackMature, m, Moment.by, Moment.before]

theorem unknownPeriodCannotSelectNewStart :
    ¬ LessonPeriodBase (m 100 1) (m 200 1) (m 20 2) .unknown (m 200 1) := by
  simp [LessonPeriodBase]

theorem changedCourseKeepsOriginalCustomerAmounts :
    halfPriceBenefit original = 50 ∧ compensationCourseCredit original = 100 ∧
    feeAfterHalfPriceBenefit original 160 = 110 ∧
    feeAfterHalfPriceBenefit original 20 = 0 ∧
    unappliedHalfPriceBenefit original 20 = 30 := by
  decide +kernel

def originalTutorLesson : Lesson := ⟨17, .oneToOne, 1, 2, 3, 80⟩
def tutorFault : TutorFaultCase :=
  ⟨originalTutorLesson, m 10 1,
    ⟨17, 2, True, True, True, .missedAgreedService "Teaching" True, .entireClass⟩⟩

def laterTutorLesson (fee : Amount) : TutorLessonRecord :=
  ⟨⟨18, .group, 1, 2, 3, fee⟩, some (m 20 1), true, fee⟩

theorem changedTutorFeeKeepsOriginalDeduction :
    originalTutorDeduction tutorFault = 80 ∧ nextTutorDeduction tutorFault = 40 ∧
    nextTutorPay tutorFault (laterTutorLesson 120) = 80 ∧
    nextTutorPay tutorFault (laterTutorLesson 60) = 20 ∧
    nextTutorPay tutorFault (laterTutorLesson 30) = 0 ∧
    unappliedTutorDeduction tutorFault (laterTutorLesson 30) = 10 := by
  decide +kernel

theorem refundIncreaseKeepsOriginalAmountDue :
    additionalRefundDue 70 0 50 = 20 ∧ additionalRefundDue 100 0 50 = 50 ∧
    additionalRefundDue 100 25 25 = 50 := by
  decide +kernel

theorem faultRefundCannotUseAnotherAccount (c : FaultRefundCase) (posting : CreditPosting)
    (obligation : Nat) (trigger agreedDue due : Moment) (legal : Option Moment)
    (fee amount : Amount)
    (h : c.restores posting obligation trigger agreedDue due legal fee amount) :
    posting.account = c.form.place.account := by
  rcases h with ⟨_, _, _, receipt⟩
  exact receipt.1.2.2.1

theorem faultDecisionUsesCoveredPlace (d : FaultDecision) (records : DecisionRecords)
    (lesson : LessonId) (place : PlaceId) (query : Moment)
    (h : d.effectiveFor records lesson place query) :
    match d with
    | .initial finding => records.faultMatterCovers finding.matter place
    | .review finding => records.faultMatterCovers finding.matter place := by
  cases d with
  | initial finding => exact h.2.2.2.1
  | review finding => exact h.2.2.1

theorem anEarlierLegalDeadlineDoesNotErasePaymentPermission
    (route : PaymentApprovalRoute) (a : ReviewAuthorities) (facts : HoldFacts)
    (h : HoldHistory) (part : PaymentPart) (schedule : PaymentSchedule)
    (conditions : PaymentInstruction → Prop) (entry : PaymentInstruction) (legal : Moment) :
    route.allows a facts h part { schedule with legalDeadline := some legal } conditions entry ↔
      route.allows a facts h part schedule conditions entry := by
  cases route <;> rfl

theorem anEarlierLegalDeadlineStillMarksLatePayment :
    ¬ (PaymentSchedule.mk (m 7 0) (m 9 0) (some (m 7 0))
      (.period 2 (m 16 0))).meetsLegalDeadline (m 15 0) := by
  simp [PaymentSchedule.meetsLegalDeadline, Moment.by, Moment.before, m]

theorem postLiftWindowCannotBeSubstituted :
    postLiftTermMatches (.after 2) ⟨m 7 0, m 9 0, none, .period 2 (m 16 0)⟩ ∧
    ¬ postLiftTermMatches (.after 2) ⟨m 7 0, m 9 0, none, .period 20 (m 34 0)⟩ := by
  simp [postLiftTermMatches]

#print axioms paidWithoutDebit
#print axioms sameSecondDebitHasOrder
#print axioms wrongAccountDoesNotDischargeRefund
#print axioms canDistinguishThirtyDayCutWithinOneSecond

#print axioms changedCourseKeepsOriginalCustomerAmounts
#print axioms changedTutorFeeKeepsOriginalDeduction
#print axioms faultRefundCannotUseAnotherAccount
#print axioms anEarlierLegalDeadlineDoesNotErasePaymentPermission

theorem scheduledRefundUsesAnActualNamedTrigger :
    ¬ PaymentDeadline.fromRefundTrigger (.after 10 "received")
      [⟨"recorded", m 3 1, [⟨m 3 1, .after, 10, m 13 1⟩]⟩]
      (m 3 1) (m 13 1) := by
  simp [PaymentDeadline.fromRefundTrigger, PaymentDeadline.applies]

theorem computedDeadlineUsesOneVerifiedBoundary :
    let event : PaymentTrigger := ⟨"received", m 100 9, [⟨m 100 9, .after, 60, m 160 0⟩]⟩
    PaymentDeadline.applies (.after 60 "received") (some event) (m 160 0) ∧
    ¬PaymentDeadline.applies (.after 60 "received") (some event) (m 160 1) := by
  simp [PaymentDeadline.applies, ClockBoundary.find, m]

theorem conflictingBoundariesAreUnresolved :
    ClockBoundary.find [⟨m 100 9, .after, 60, m 160 0⟩, ⟨m 100 9, .after, 60, m 160 1⟩]
      (m 100 9) .after 60 = none := by
  decide +kernel

#print axioms computedDeadlineUsesOneVerifiedBoundary
#print axioms conflictingBoundariesAreUnresolved

theorem recordedRefundHasStableObligation (c : FaultRefundCase) (posting : CreditPosting)
    (obligation : ObligationId) (trigger agreedDue due : Moment) (legal : Option Moment)
    (fee amount : Amount)
    (h : c.restores posting obligation trigger agreedDue due legal fee amount) :
    obligation = c.obligation :=
  h.2.1

theorem reviewExcludesTheRecordedOriginalDecider
    (a : ReviewAuthorities) (appointments : List ReviewAppointment) (finding : ReviewFinding)
    (oldMatter : ReviewMatter) (oldTime : Moment)
    (original : (oldMatter, finding.reviewer, oldTime) ∈ a.actualOriginalDecisions)
    (sameCase : oldMatter.sameCase finding.matter) (earlier : oldTime.by finding.decidedAt) :
    ¬ reviewFindingConforms a appointments finding := by
  intro valid
  exact valid.1.2.2.2 oldMatter finding.reviewer oldTime original sameCase earlier rfl

theorem originalApproverCannotImposeFormalHold
    (history : HoldHistory) (a : ReviewAuthorities) (facts : HoldFacts)
    (hold : FormalHold) (part : PaymentPart)
    (scope : part ∈ hold.portions)
    (original : history.originallyApprovedBy a part.ref hold.imposedBy hold.decidedAt) :
    ¬ history.validFormalHold a facts hold := by
  intro held
  exact held.2.2.1 part scope original

theorem sameTutorPayCannotBeResetByNewObligationNumber :
    let history : PaymentHistory := {
      posted := [⟨1, ⟨⟨17, 98, 1, .tutorPay 2⟩, .person 2, 4, 100, m 5 1⟩, some 1⟩]
      returned := [] }
    history.remainingPurposeBefore 17 (.tutorPay 2) (.person 2 none) 100 (m 5 2) = 0 ∧
      history.remainingObligationBefore 17 99 (.person 2 none) 100 (m 5 2) = 100 := by
  decide +kernel

theorem actualFiledPaymentRequiresRetainedRecipientEvidence (route : PaymentApprovalRoute)
    (a : ReviewAuthorities) (facts : HoldFacts) (history : HoldHistory) (part : PaymentPart)
    (schedule : PaymentSchedule) (conditions : PaymentInstruction → Prop)
    (paid : PostedPayment) (rows : List PostLiftPaymentRecord)
    (h : route.filedPayment a facts history part schedule conditions paid rows) :
    history.payments.recipientReceived part.recipient paid :=
  h.2.1

#print axioms scheduledRefundUsesAnActualNamedTrigger
#print axioms recordedRefundHasStableObligation
#print axioms reviewExcludesTheRecordedOriginalDecider
#print axioms originalApproverCannotImposeFormalHold
#print axioms sameTutorPayCannotBeResetByNewObligationNumber
#print axioms actualFiledPaymentRequiresRetainedRecipientEvidence

theorem tutorChangeKeepsOriginalLessonAndCustomerAmounts
    (lesson : Lesson) (place : Place) (finding : TutorFaultFinding) (facts : TutorFaultPlaceFacts) :
    let basis := FaultBasis.tutor finding facts
    (basis.lessonWithResponsibleTutor lesson).id = lesson.id ∧
      (basis.lessonWithResponsibleTutor lesson).tutor = finding.tutor ∧
      halfPriceBenefit place = place.normalFee / 2 ∧
      compensationCourseCredit place = place.normalFee := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem lateOldRefundAndTimelyNewRefund :
    let ledger : List CreditPosting :=
      [⟨11, 14, .lessonRefund 17 8 41, 20, m 13 1⟩,
       ⟨12, 14, .lessonRefund 17 8 41, 30, m 18 1⟩,
       ⟨13, 14, .lessonRefund 17 8 42, 50, m 22 1⟩]
    ¬ FeeRefundCompleted original ledger (m 14 0) 50 (some 41) ∧
      FeeRefundCompleted original ledger (m 23 0) 50 (some 41) ∧
      FeeRefundCompleted original ledger (m 22 2) 50 (some 42) := by
  dsimp only [FeeRefundCompleted]
  decide +kernel

theorem disputedAbsenceNeedsRecordedDecision (e : AbsenceReasonEvidence)
    (f : PartOne) (facts : AbsenceFacts) (query : Moment)
    (requiresDecision : e.decisionNeeded) (empty : e.recordedReasons = []) :
    ¬ e.applies f facts query := by
  intro accepted
  obtain ⟨_, row, inRecords, _⟩ := accepted requiresDecision
  rw [empty] at inRecords
  exact List.not_mem_nil inRecords

#print axioms tutorChangeKeepsOriginalLessonAndCustomerAmounts
#print axioms lateOldRefundAndTimelyNewRefund
#print axioms disputedAbsenceNeedsRecordedDecision

theorem groupAbsenceCorrectionFollowsRevisedFee
    (f : PartOne) (ev : Course.StartEvidence) (previous revised : LessonSettlement) (previousAt : Moment)
    (feeAt : EvidenceRef → PlaceId → Amount → Prop) (unavailable : ReviewFinding → PlaceId → Prop)
    (c : PaymentCorrectionCase) (records : DecisionRecords)
    (outcomes : List RecordedSettlementOutcome) (amounts : EvidenceRef → Option PaymentPart)
    (history : PaymentHistory) (earlier : List EarlierFeeRefund) (originalRefund : RefundRecord)
    (h : GroupAbsenceCorrectionRecorded f ev previous revised previousAt feeAt unavailable
      c records outcomes amounts history earlier originalRefund) :
    c.money.corrected.amount =
      feeAdjustmentRefundPrincipal f.place ev.ledger c.finding.decidedAt c.money.corrected.ref.obligation
        (grossLessonCreditRestoration revised.debited revised.feePayable) earlier := by
  rcases h with ⟨_, _, _, _, _, _, _, dueBack, _, _, _, _, _, _, _, _, _, _, amount, _⟩
  simpa only [dueBack] using amount

theorem groupAbsenceRevisedToZeroRestoresFullDebit :
    grossLessonCreditRestoration 100 0 = 100 ∧ grossLessonCreditRestoration 100 50 = 50 := by
  unfold grossLessonCreditRestoration
  decide +kernel

#print axioms groupAbsenceCorrectionFollowsRevisedFee
#print axioms groupAbsenceRevisedToZeroRestoresFullDebit

theorem newRefundCannotAlreadyAppearAtTrigger
    (c : FaultRefundCase) (entry : CreditPosting) (trigger : Moment)
    (onLedger : entry ∈ c.ledger)
    (sameRefund : entry.kind = .lessonRefund c.form.lesson.id c.form.place.id c.obligation)
    (sameMoment : entry.point = trigger) : ¬ c.newObligationAt trigger := by
  intro opened
  have tooEarly := opened.2 entry onLedger sameRefund
  rw [sameMoment] at tooEarly
  simp [Moment.before] at tooEarly

theorem sameSecondOrderedRefundIsLater :
    (m 5 1).before (m 5 2) := by
  decide +kernel

#print axioms newRefundCannotAlreadyAppearAtTrigger
#print axioms sameSecondOrderedRefundIsLater

end SourceV14.Checks
