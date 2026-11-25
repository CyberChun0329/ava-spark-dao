import SourceV14.Workflow

/-! Regression checks for applying §3.5 at confirmation and retained assent under §2.2. -/

namespace FidelityBookingEntitlementsChecks

open SourceV14 SourceV14.Booking SourceV14.Confirmation SourceV14.Course
open SourceV14.Operations SourceV14.Workflow

private theorem entitlementCannotBeReused (discount : Redress.DiscountBooking)
    (history : Redress.History) (original selected : StartEvidence) (used : List LaterBenefitUse)
    (valid : discount.appliesAtBooking history original selected used)
    (prior : LaterBenefitUse) (present : prior ∈ used) :
    ¬(prior.originalLesson = discount.remedy.facts.form.place.lesson ∧
      prior.originalPlace = discount.remedy.facts.form.place.id) := by
  obtain ⟨_, _, _, _, _, available⟩ := valid
  obtain ⟨_, _, _, _, _, _, priced⟩ := available
  obtain ⟨_, _, _, _, _, _, _, _, _, _, calculatedFee⟩ := priced
  obtain ⟨_, _, _, applied⟩ := calculatedFee
  obtain ⟨_, _, _, _, _, _, _, _, _, _, unspent, _, _, _, _⟩ := applied
  exact unspent prior present

theorem actualConfirmationConsumesDiscount (before after : State) (event : Workflow.Booking.Event)
    (discount : Redress.DiscountBooking)
    (confirmed : Step before (.booking event (some discount)) after) :
    after.redress.pendingDiscountUses = before.redress.pendingDiscountUses ++ [discount.use] := by
  cases confirmed
  rfl

/-- A booking can target another lesson with a different price. The earlier confirmation
    of the same entitlement is already sufficient to bar it before final filing. -/
theorem secondBookingCannotSpendPendingDiscount (before booked next : State)
    (firstEvent : Workflow.Booking.Event) (first second : Redress.DiscountBooking)
    (form : PartOne) (booking : BookingEvidence) (roster : Option SourceV14.Settlement.Roster)
    (payment : Workflow.Booking.ConfirmationPayment)
    (confirmed : Step before (.booking firstEvent (some first)) booked)
    (sameLesson : first.use.originalLesson = second.remedy.facts.form.place.lesson)
    (samePlace : first.use.originalPlace = second.remedy.facts.form.place.id) :
    ¬Step booked (.booking (.confirmPlace form booking roster payment) (some second)) next := by
  have consumed := actualConfirmationConsumesDiscount before booked firstEvent first confirmed
  have present : first.use ∈ booked.redress.usedDiscounts ++ booked.redress.pendingDiscountUses := by
    rw [consumed]
    simp
  intro step
  cases step with
  | booking _ _ _ _ price =>
    exact entitlementCannotBeReused second _ _ _ _ price.2.2.2 first.use present
      ⟨sameLesson, samePlace⟩

theorem reducedPriceNeedsItsActualBasis (before next : State) (form : PartOne)
    (booking : BookingEvidence) (roster : Option SourceV14.Settlement.Roster)
    (payment : Workflow.Booking.ConfirmationPayment)
    (reduced : form.place.feePayable ≠ form.place.normalFee)
    (noIndependentBasis : ¬before.verifiedContractualDiscount form form.confirmedAt) :
    ¬Step before (.booking (.confirmPlace form booking roster payment)) next := by
  intro step
  cases step with
  | booking _ _ _ _ price => exact price.elim reduced noIndependentBasis

theorem ordinaryOrContractualConfirmation (before : State) (form : PartOne)
    (booking : BookingEvidence) (roster : Option SourceV14.Settlement.Roster)
    (payment : Workflow.Booking.ConfirmationPayment) (after : StartEvidence)
    (check : Reserves.FundingContextMatches before.activeReserves booking.funding.funds)
    (rule : Workflow.Booking.Step (before.course form.lesson.id)
      (.confirmPlace form booking roster payment) after)
    (price : form.place.feePayable = form.place.normalFee ∨
      before.verifiedContractualDiscount form form.confirmedAt)
    (materials : (Workflow.Booking.Event.confirmPlace form booking roster payment)
      |>.securesPendingMaterials before)
    (receipts : (Workflow.Booking.Event.confirmPlace form booking roster payment)
      |>.readsFundingReceipts before.holds.payments) :
    Step before (.booking (.confirmPlace form booking roster payment))
      { before.withCourse form.lesson.id after with
        activeReserves := Reserves.reserve before.activeReserves booking.funding.funds } :=
  Step.booking check trivial trivial rule price trivial materials receipts

theorem finalFilingRequiresConfirmation (before next : State) (discount : Redress.DiscountBooking)
    (selected : StartEvidence) (unbooked : discount.use ∉ before.redress.pendingDiscountUses) :
    ¬Step before (.redress (.recordDiscountUse discount selected)) next := by
  intro step
  cases step with
  | redress _ _ _ _ rule =>
    obtain ⟨_, earlier, later, pending, _⟩ := rule
    exact unbooked (by rw [pending]; simp)

theorem linkedConfirmationCanBeFiled (before : State) (discount : Redress.DiscountBooking)
    (pending : before.redress.pendingDiscountUses = [discount.use])
    (conforms : discount.conforms before.redress (before.course discount.remedy.facts.form.lesson.id)
      (before.course discount.agreed.lesson.id)) :
    Step before (.redress (.recordDiscountUse discount (before.course discount.agreed.lesson.id)))
      { (before.withCourse discount.remedy.facts.form.lesson.id
          (before.course discount.remedy.facts.form.lesson.id)).withHolds before.holds with
        redress := { before.redress with
          usedDiscounts := before.redress.usedDiscounts ++ [discount.use]
          pendingDiscountUses := [] } } := by
  exact Step.redress trivial rfl (by simp [Redress.Event.usesRecordedReviews,
    Redress.Event.assessmentDecisions]) trivial ⟨conforms, [], [], pending, rfl, rfl, rfl⟩

theorem timelyScheduleAgreementBlocksNoFaultCancellation (before next : State)
    (form : PartOne) (record : NoFaultCancellationRecord) (change : AgreedScheduleChange)
    (retained : change ∈ (before.course form.lesson.id).changes)
    (oldSchedule : change.previous = record.schedule)
    (affects : change.record.originalLesson = form.lesson.id ∧ form.place.id ∈ change.record.scope)
    (valid : change.allowed form.lesson (before.course form.lesson.id))
    (timely : change.record.nextSchedule.agreedAt.by form.deadlines.noFaultAcceptance) :
    ¬Step before (.cancellation (.noFault form record)) next := by
  intro step
  cases step with
  | cancellation guard _ => exact guard.1 change retained oldSchedule affects valid timely

theorem timelyTutorAcceptanceBlocksNoFaultCancellation (before next : State)
    (form : PartOne) (record : NoFaultCancellationRecord) (change : TutorReplacement)
    (retained : change ∈ (before.course form.lesson.id).tutorReplacements)
    (oldSchedule : change.previous = record.schedule)
    (affects : change.record.originalLesson = form.lesson.id ∧ form.place.id ∈ change.record.scope)
    (valid : change.conforms form.lesson (before.course form.lesson.id))
    (newArrangement : record.disruptionVerifiedAt.before change.effectiveAt)
    (timely : change.agreedAt.by form.deadlines.noFaultAcceptance) :
    ¬Step before (.cancellation (.noFault form record)) next := by
  intro step
  cases step with
  | cancellation guard _ =>
    exact guard.2.1 change retained oldSchedule affects valid newArrangement timely

/-- The separately linked lesson may be paid for later than the actual acceptance. -/
theorem signedSeparateBookingBlocksNoFaultCancellation (before next : State)
    (form : PartOne) (record : NoFaultCancellationRecord) (link : SeparateBooking.Link)
    (retained : link ∈ before.separateBookings) (sameForm : link.original = form)
    (afterDisruption : record.disruptionVerifiedAt.by link.change.nextSchedule.agreedAt)
    (originalSchedule : EffectiveSchedule form.lesson (before.course form.lesson.id)
      record.schedule link.change.nextSchedule.agreedAt)
    (agreed : link.change.nextSchedule.agreedAt.by form.deadlines.noFaultAcceptance)
    (provider : link.nextBooking.signatures.providerAccepted.by form.deadlines.noFaultAcceptance)
    (tutor : link.nextBooking.signatures.tutorAccepted.by form.deadlines.noFaultAcceptance) :
    ¬Step before (.cancellation (.noFault form record)) next := by
  intro step
  cases step with
  | cancellation guard _ =>
    exact guard.2.2 link retained sameForm afterDisruption originalSchedule ⟨agreed, provider, tutor⟩

theorem noFaultCancellationWithOnlyLateAgreement (before : State)
    (form : PartOne) (record : NoFaultCancellationRecord) (change : AgreedScheduleChange)
    (onlyChange : (before.course form.lesson.id).changes = [change])
    (noReplacement : (before.course form.lesson.id).tutorReplacements = [])
    (noSeparate : before.separateBookings = [])
    (late : ¬change.record.nextSchedule.agreedAt.by form.deadlines.noFaultAcceptance)
    (valid : Cancellation.Step before.cancelled (before.course form.lesson.id) (.noFault form record)
      (before.cancelled ++ [.noFault form record])) :
    Step before (.cancellation (.noFault form record))
      { before with cancelled := before.cancelled ++ [.noFault form record] } := by
  apply Step.cancellation _ valid
  simp [BookingEntitlements.noTimelyRearrangement, Cancellation.Event.form,
    onlyChange, noReplacement, noSeparate, late]

private def tick (seconds : Nat) : Moment := ⟨seconds, 0⟩
private def deadline : PaymentTerms := ⟨.fixed (tick 90), .fixed (tick 100)⟩

private def bookingForm (id : LessonId) (booked start : Nat) (normal due : Amount)
    (basis : Option String) : PartOne where
  lesson := ⟨id, .oneToOne, 1, 2, 3, 60⟩
  place := ⟨1, id, 4, 5, 5, 6, normal, due⟩
  contacts := ⟨"Spark", "provider", "student", none, "coordinator", 7, "lead", none, none,
    8, "reviewer", 9, "alternative", false, 10, "escalation"⟩
  rulesVersion := "1.5"
  confirmedAt := tick booked
  customerRepresentatives := []
  schedule := ⟨id, tick start, tick (start + 1), "UTC", tick 1, tick 2⟩
  serviceTerms := "agreed lesson"
  serviceItems := [1]
  discountBasis := basis
  privateRoster := none
  rosterLock := none
  groupRescheduleCutoff := none
  oneToOneAdvanceCutoff := some (.fixed (tick 9))
  cancelChangeTerms := "agreed changes"
  noFaultTerms := "no-fault terms"
  applicableStartTerms := "start conditions"
  tutorAgreementRef := "teaching agreement"
  absentGroupPlacePay := none
  materialsOrBundle := none
  materialsTermsRef := none
  materialsPayer := none
  deadlines := ⟨.fixed (tick 70), tick 19, none, deadline, deadline, deadline,
    deadline, .fixed (tick 120), tick 130, tick 110, tick 115, .fixed (tick 150)⟩

private def origin := bookingForm 17 10 30 100 100 none
private def otherwiseDue (full : Bool) : Amount := if full then 40 else 90
private def quote (full : Bool) := bookingForm 18 50 60 (otherwiseDue full) (otherwiseDue full) none
private def debitDue (full : Bool) : Amount := if full then 0 else 40
private def charged (full : Bool) :=
  bookingForm 18 50 60 (otherwiseDue full) (debitDue full) (some "recorded standard compensation")

private def compensationFormChecks (f : PartOne) : Prop := f.matches ∧ f.schedule.valid

private theorem originMatches : compensationFormChecks origin := by
  simp [compensationFormChecks, origin, bookingForm, PartOne.matches, Place.matches, Place.validFees,
    Contacts.complete, PayAndReviewTerms.valid, PaymentTerms.valid, PaymentDeadline.valid,
    AdvanceWindow.validAt, Schedule.valid, deadline, tick, Moment.by, Moment.before]
  all_goals decide +kernel

private theorem quoteMatches (full : Bool) : compensationFormChecks (quote full) := by
  cases full <;> simp [compensationFormChecks, quote, otherwiseDue, bookingForm, PartOne.matches,
    Place.matches, Place.validFees, Contacts.complete, PayAndReviewTerms.valid, PaymentTerms.valid,
    PaymentDeadline.valid, AdvanceWindow.validAt, Schedule.valid, deadline, tick, Moment.by,
    Moment.before] <;> decide +kernel

private theorem chargedMatches (full : Bool) : compensationFormChecks (charged full) := by
  cases full <;> simp [compensationFormChecks, charged, otherwiseDue, debitDue, bookingForm,
    PartOne.matches, Place.matches, Place.validFees, Contacts.complete, PayAndReviewTerms.valid,
    PaymentTerms.valid, PaymentDeadline.valid, AdvanceWindow.validAt, Schedule.valid, deadline,
    tick, Moment.by, Moment.before] <;> decide +kernel

private def singleBooked (base : StartEvidence) (f : PartOne)
    (bookings : List (PartOne × BookingEvidence) := []) : StartEvidence :=
  { base with
    effectiveForms := [f]
    scheduleHistory := [f.schedule]
    groupRoster := none
    bookedRosters := []
    changes := []
    bookings := bookings
    teachingBegan := none
    creditRecords := { base.creditRecords with closed := [], lessonFees := {} } }

private theorem onlySchedule (base : StartEvidence) (f : PartOne)
    (bookings : List (PartOne × BookingEvidence)) (queried : Moment)
    (oneToOne : f.lesson.kind = .oneToOne) (same : f.schedule.lesson = f.lesson.id)
    (valid : compensationFormChecks f) (effective : f.schedule.effectiveAt.by queried) :
    EffectiveSchedule f.lesson (singleBooked base f bookings) f.schedule queried := by
  refine ⟨same, ⟨by simp [singleBooked], valid.2, effective, ?_⟩, ?_, ?_⟩
  · simp [singleBooked, Moment.by]
  · simp [singleBooked, same]
  · intro row present _ _
    have eq : row = f.schedule := List.mem_singleton.mp present
    subst row
    refine ⟨same, valid.2, Or.inl ⟨oneToOne, ?_, ?_⟩⟩
    · simp [StartEvidence.rosterMatchesForms, StartEvidence.formsMatch, oneToOne, singleBooked,
        valid.1]
    · simp [singleBooked]

private def remedy (base : StartEvidence) : Redress.AcceptedRemedy where
  id := 12
  facts := ⟨origin, .provider ⟨17, 1, 1, .notifying, True, True, True⟩,
    none, false, base.studentFaults.decisions, .none⟩
  agreement := ⟨17, 1, 5, .standardCompensation, ["missed teaching"], tick 35, tick 70⟩
  dates := none

private def availability : LaterBenefitAvailability := ⟨17, 1, 50, tick 40, True⟩

private def choice (full : Bool) (base : StartEvidence) (booking : BookingEvidence) :
    Redress.DiscountBooking where
  remedy := remedy base
  selected := quote full
  agreed := charged full
  originalStart := tick 30
  selectedStart := tick 60
  selectedIsSparkCourse := True
  booking := booking
  use := ⟨17, 1, 18, 1, 5, tick 50, otherwiseDue full,
    if full then 40 else 50, if full then 10 else 0⟩
  remainderHandledUnderTerms := fun _ ↦ False

private def prices (base : StartEvidence) : Redress.History :=
  { remedies := [remedy base], availableDiscounts := [(12, availability)] }

private def selectedBooking (full : Bool) (base : StartEvidence) (booking : BookingEvidence) :=
  singleBooked base (charged full) [(charged full, booking)]

/-- A £100 original place carries a £50 entitlement. For a £90 selected place the
    correct debit is £40. For a £40 place it is fully discounted, with £10 unapplied.
    The ordinary confirmation check supplies the transaction and funding facts. -/
theorem fixedBenefitAppliesAtActualConfirmation (full : Bool) (base : StartEvidence)
    (booking : BookingEvidence) (payment : Workflow.Booking.ConfirmationPayment)
    (actual : CanConfirmPlace (charged full) booking none base.openingCredit base.ledger
      (selectedBooking full base booking).creditRecords base.discounts none) :
    BookingEntitlements.confirmationAllowed
      (fun _ ↦ singleBooked base origin) (fun _ _ ↦ False) (prices base)
      (.confirmPlace (charged full) booking none payment) (some (choice full base booking))
      (selectedBooking full base booking) := by
  refine ⟨rfl, rfl, Or.inl rfl, ?_⟩
  refine ⟨by simp [choice, prices], by simp [choice, selectedBooking, singleBooked], rfl, ?_, ?_, ?_⟩
  · exact ⟨origin.schedule, onlySchedule base origin [] (tick 50) rfl rfl originMatches
      (by decide), rfl⟩
  · exact ⟨(charged full).schedule, onlySchedule base (charged full) _ (tick 50) rfl rfl
      (chargedMatches full) (by change (tick 2).by (tick 50); decide), rfl⟩
  · refine ⟨(12, availability), by simp [prices], rfl, ?_, none, ?_, ?_⟩
    · simp [LaterBenefitAvailability.deliveredBy, availability, choice, remedy, origin,
        bookingForm, laterBenefitDeliveredBy, RemedyAgreement.acceptedStandardFor,
        RemedyAgreement.forPlace, halfPriceBenefit, tick, Moment.by, Moment.before] <;> decide +kernel
    · exact Or.inr ⟨by simp [selectedBooking, singleBooked], Or.inl rfl⟩
    · refine ⟨originMatches.1, (quoteMatches full).1, (chargedMatches full).1, rfl, actual,
        ?_, ?_, ?_, ?_, rfl, otherwiseDue full, ?_, ?_, ?_⟩
      · exact ⟨⟨rfl, rfl, rfl, rfl, trivial, trivial⟩, trivial⟩
      · exact ⟨⟨rfl, rfl, rfl, rfl, trivial, trivial⟩, trivial⟩
      · simp [SourceV14.CreditEvidence.FaultDecisionWhenRequired, choice, remedy]
      · simp [singleBooked]
      · exact Or.inl ⟨by simp [selectedBooking, singleBooked], rfl⟩
      · cases full <;> simp [choice, quote, charged, remedy, origin, bookingForm, otherwiseDue,
          debitDue, feeAfterHalfPriceBenefit, appliedHalfPriceBenefit, halfPriceBenefit] <;>
          decide +kernel
      · cases full <;> simp [laterBenefitApplied, laterBenefitDeliveredBy, choice, origin, remedy,
          quote, charged, otherwiseDue, debitDue, bookingForm, tick, Moment.by, Moment.before,
          RemedyAgreement.acceptedStandardFor, RemedyAgreement.forPlace, prices,
          feeAfterHalfPriceBenefit, unappliedHalfPriceBenefit, appliedHalfPriceBenefit,
          halfPriceBenefit] <;> decide +kernel

/-- A booking cannot offset a verified expense using a receipt missing from the
shared account history, even when its local funding check accepts the evidence. -/
theorem confirmationUsesRecordedFundingReceipt
    {before next : State} {form : PartOne} {booking : BookingEvidence}
    {roster : Option SourceV14.Settlement.Roster}
    {payment : Workflow.Booking.ConfirmationPayment} {receipt : PostedPayment}
    (confirmed : Step before (.booking (.confirmPlace form booking roster payment)) next)
    (supplied : receipt ∈ booking.funding.terms.payments.posted)
    (ownLesson : receipt.instruction.part.lesson = form.lesson.id)
    (evidenced : receipt.evidence.isSome = true)
    (prior : receipt.instruction.atTime.before booking.funding.checkedAt) :
    receipt ∈ before.holds.payments.posted := by
  cases confirmed with
  | booking _ _ _ _ _ _ _ recorded =>
    change List.Perm
        (booking.funding.terms.payments.posted.filter fun row ↦
          row.instruction.part.lesson == form.lesson.id && row.evidence.isSome &&
          decide (row.instruction.atTime.before booking.funding.checkedAt))
        (before.holds.payments.posted.filter fun row ↦
          row.instruction.part.lesson == form.lesson.id && row.evidence.isSome &&
          decide (row.instruction.atTime.before booking.funding.checkedAt)) ∧ _ at recorded
    have retained := recorded.1.mem_iff.mp (show receipt ∈ _ from List.mem_filter.mpr
      ⟨supplied, by simp [ownLesson, evidenced, prior]⟩)
    exact (List.mem_filter.mp retained).1

/-- Another booking cannot consume the funds protecting a known same-lesson provision
just because the booking passed its original funding check. -/
theorem knownMaterialsBudgetProtectsConfirmation
    (before next : State) (form : PartOne) (booking : BookingEvidence)
    (roster : Option SourceV14.Settlement.Roster) (payment : Workflow.Booking.ConfirmationPayment)
    (pending : before.materials.liveMaterialBudgetsAt before.holds.payments
      form.lesson.id form.confirmedAt before.materialsPrincipalContext ≠ [])
    (insufficient : ¬booking.funding.funds.secures
      (sumAmounts (before.materials.liveMaterialBudgetsAt before.holds.payments
        form.lesson.id form.confirmedAt before.materialsPrincipalContext) Prod.snd)) :
    ¬Step before (.booking (.confirmPlace form booking roster payment)) next := by
  intro accepted
  cases accepted with
  | booking _ _ _ _ _ _ materials _ =>
    exact insufficient (materials pending).1

#print axioms confirmationUsesRecordedFundingReceipt
#print axioms knownMaterialsBudgetProtectsConfirmation

end FidelityBookingEntitlementsChecks
