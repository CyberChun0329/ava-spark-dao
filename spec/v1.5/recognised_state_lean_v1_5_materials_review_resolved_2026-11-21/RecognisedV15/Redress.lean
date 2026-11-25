import RecognisedV15.Evidence
import SourceV14.Workflow.Redress

namespace RecognisedV15.Redress

open SourceV14 SourceV14.Booking SourceV14.Course SourceV14.Operations SourceV14.CreditEvidence
open SourceV14.Workflow
open SourceV14.Workflow.Redress (AcceptedRemedy DiscountBooking Event History FreshPosting
  RefundTriggerEvidence ledgerWithObservedRefund)

private def fixedDiscountAvailableBy (remedy : AcceptedRemedy) (discount : LaterBenefitAvailability)
    (atTime : Moment) : Prop :=
  let original := remedy.facts.form.place
  discount.originalLesson = original.lesson ∧ discount.originalPlace = original.id ∧
  discount.amount = halfPriceBenefit original ∧ discount.verifiedAvailableForBooking ∧
  remedy.facts.teaching = .none ∧ remedy.agreement.acceptedStandardFor original ∧
  remedy.agreement.acceptedAt.by discount.availableAt ∧ discount.availableAt.by atTime

private def recordVerifiedRefund (course : LessonEvidence) (ledger : List CreditPosting)
    (filing : VerifiedLessonRefund) (payments : PaymentHistory) : LessonEvidence :=
  let credit := course.creditFee
  { course with creditFee := { credit with
      ledger
      creditRecords := { credit.creditRecords with
        payments
        verifiedRefunds := credit.creditRecords.verifiedRefunds ++ [filing] } } }

/-- Record the customer's agreement, make compensation available, or establish a refund.
A refund assessment records what is due. Posting or filing the actual receipt updates the ledger
and verified refund record. Full closure reads the actual restoration and records the treatment
of unused benefits. -/
def Step (before : History) (course : LessonEvidence) (holds : HoldHistory) (event : Event)
    (next : History) (after : LessonEvidence) (followingHolds : HoldHistory)
    (clockEvidence : RefundTriggerEvidence) (reviews : Review.History) : Prop :=
  let recordOnly := fun updated ↦ next = updated ∧ after = course ∧ followingHolds = holds
  match event with
  | .acceptRemedy entry =>
    let original := entry.facts.form
    let agreement := entry.agreement
    entry.facts.established course.toDirect agreement.acceptedAt ∧
    agreement.validForFault (entry.facts.fault.lessonWithResponsibleTutor original.lesson)
      original.place entry.facts.fault ∧
    agreement.acceptedAt.by agreement.deliveryDeadline ∧
    (∀ other ∈ before.remedies, other.id ≠ entry.id ∧ other.agreement ≠ agreement) ∧
    ¬fullRefundClosedBy original.place course.creditFee.creditRecords.closed
      agreement.acceptedAt ∧
    (agreement.kind = .standardCompensation → ∃ dates ∈ entry.dates,
      dates.matches agreement original course.toDirect agreement.acceptedAt) ∧
    recordOnly { before with remedies := before.remedies ++ [entry] }
  | .extendRemedy entry extension agreedAt =>
    let progress := before.progress course.toDirect entry
    let provider := entry.facts.form.lesson.provider
    entry ∈ before.remedies ∧ progress.stillOwedAt agreedAt ∧
    (∃ deadline, progress.deadlineBy provider agreedAt deadline ∧
      extension.applies entry.agreement provider deadline agreedAt) ∧
    recordOnly { before with extensions := before.extensions ++ [(entry.id, extension)] }
  | .confirmUnable entry provider atTime =>
    entry ∈ before.remedies ∧ provider = entry.facts.form.lesson.provider ∧
    (before.progress course.toDirect entry).stillOwedAt atTime ∧
    (∀ prior ∈ before.unable, prior.1 ≠ entry.id) ∧
    recordOnly { before with unable := before.unable ++ [(entry.id, atTime)] }
  | .deliverRemedy entry record =>
    entry ∈ before.remedies ∧ record.conforms before course.toDirect entry ∧
    (∀ prior ∈ before.deliveries, prior.remedy ≠ entry.id) ∧
    recordOnly { before with deliveries := before.deliveries ++ [record] }
  | .requestRefund form request =>
    (∃ roster forms,
      course.toDirect.rosterFormsAt form.lesson request.receivedAt roster forms ∧
      form ∈ forms) ∧
    request.validFor form.place ∧ request ∉ before.requests ∧
    recordOnly { before with requests := before.requests ++ [request] }
  | .makeDiscountUsable entry discount =>
    let original := entry.facts.form.place
    entry ∈ before.remedies ∧
    (before.progress course.toDirect entry).stillOwedAt discount.availableAt ∧
    fixedDiscountAvailableBy entry discount discount.availableAt ∧
    (∀ row ∈ before.availableDiscounts, row.2.originalLesson = original.lesson →
      row.2.originalPlace ≠ original.id) ∧
    recordOnly { before with
      availableDiscounts := before.availableDiscounts ++ [(entry.id, discount)] }
  | .recordDiscountUse discount selectedCourse =>
    let remedy := discount.remedy
    let facts := remedy.facts
    let original := facts.form
    let credit := course.creditFee
    let bookedAt := discount.use.bookedAt
    remedy ∈ before.remedies ∧
    (discount.agreed, discount.booking) ∈ selectedCourse.bookings ∧
    credit.ledger = selectedCourse.ledger ∧
    (∃ schedule, EffectiveSchedule original.lesson course.toDirect schedule bookedAt ∧
      schedule.start = discount.originalStart) ∧
    (∃ schedule, EffectiveSchedule discount.agreed.lesson selectedCourse schedule bookedAt ∧
      schedule.start = discount.selectedStart) ∧
    (∃ recorded ∈ before.availableDiscounts, recorded.1 = remedy.id ∧
      fixedDiscountAvailableBy remedy recorded.2 bookedAt ∧
      ∃ roster, selectedCourse.readsBookedRoster discount.agreed selectedCourse.groupRoster
          bookedAt roster ∧
        -- Apply the fixed benefit from the original place to the selected course's ordinary fee.
        LaterCompensationBooking original facts.fault facts.authority facts.disputed
          facts.decisions credit.ledger credit.discounts credit.creditRecords.closed
          discount.selected discount.agreed discount.originalStart discount.selectedStart
          recorded.2.availableAt facts.teaching remedy.agreement discount.selectedIsSparkCourse
          before.usedDiscounts discount.use discount.booking { selectedCourse with
            groupRoster := roster }) ∧
    LaterBenefitRemainderHandled original.place discount.selected selectedCourse
      discount.use discount.remainderHandledUnderTerms ∧
    ∃ earlier later, before.pendingDiscountUses = earlier ++ discount.use :: later ∧
      recordOnly { before with
        usedDiscounts := before.usedDiscounts ++ [discount.use]
        pendingDiscountUses := earlier ++ later }
  | .issueCourseCredit entry issue posting =>
    let grant := entry.creditOrigin issue course.toDirect
    let credit := course.creditFee
    entry ∈ before.remedies ∧
    (before.progress course.toDirect entry).stillOwedAt posting.point ∧
    FreshPosting course.toDirect posting ∧
    -- The original normal fee fixes the amount credited to the customer's usable account.
    grant.matchesPosting credit.ledger credit.creditRecords.closed credit.creditRecords.ownsAccount
      posting credit.creditRecords.lessonFees ∧
    (∀ prior ∈ credit.creditRecords.grants, prior.original.lesson = grant.original.lesson →
      prior.original.id ≠ grant.original.id) ∧
    (∀ prior ∈ credit.ledger,
      prior.kind ≠ .compensation grant.original.lesson grant.original.id) ∧
    next = before ∧ followingHolds = holds ∧
    after = { course with creditFee := { credit with
      ledger := credit.ledger ++ [posting]
      creditRecords := { credit.creditRecords with
        grants := credit.creditRecords.grants ++ [grant] } } }
  | .assessRefund assessment facts =>
    assessment.conforms before course.toDirect holds facts clockEvidence reviews ∧
    recordOnly { before with assessments := before.assessments ++ [assessment] }
  | .postRefund post facts authorities conditions =>
    post.conforms before course.toDirect holds followingHolds facts authorities conditions reviews ∧
    next = before ∧
    after = recordVerifiedRefund course (course.creditFee.ledger ++ [post.posting])
      post.filing followingHolds.payments
  | .fileObservedRefund post recordedAt facts authorities =>
    let payments := course.creditFee.creditRecords.payments
    post.observedFiling before course.toDirect holds recordedAt facts authorities ∧
    next = before ∧ followingHolds = holds ∧
    after = recordVerifiedRefund course
      (ledgerWithObservedRefund course.toDirect post.posting payments) post.filing payments
  | .closeFullRefund assessment settlement closure removals permitted =>
    let credit := course.creditFee
    assessment.closureConforms before course.toDirect settlement closure removals
      permitted reviews ∧
    next = before ∧ followingHolds = holds ∧
    after = { course with creditFee := { credit with
      ledger := credit.ledger ++ removals
      creditRecords := { credit.creditRecords with
        closed := credit.creditRecords.closed ++ [closure] } } }

private theorem toDirect_eq_iff (left right : LessonEvidence) :
    left.toDirect = right.toDirect ↔ left = right := by
  constructor
  · intro same
    simpa only [LessonEvidence.fromDirect_toDirect] using congrArg LessonEvidence.fromDirect same
  · exact congrArg LessonEvidence.toDirect

/-- The local rule admits the same events and exact successors as the frozen redress relation. -/
theorem step_iff (before : History) (course : LessonEvidence) (holds : HoldHistory) (event : Event)
    (next : History) (after : LessonEvidence) (followingHolds : HoldHistory)
    (clockEvidence : RefundTriggerEvidence) (reviews : Review.History) :
    Step before course holds event next after followingHolds clockEvidence reviews ↔
      SourceV14.Workflow.Redress.Step before course.toDirect holds event next after.toDirect
        followingHolds clockEvidence reviews := by
  cases event <;>
    simp only [Step, SourceV14.Workflow.Redress.Step, AcceptedRemedy.conforms,
      DiscountBooking.conforms, DiscountBooking.appliesAtBooking, fixedDiscountAvailableBy,
      LaterBenefitAvailability.deliveredBy, laterBenefitDeliveredBy, ← toDirect_eq_iff,
      and_assoc] <;>
    rfl

end RecognisedV15.Redress
