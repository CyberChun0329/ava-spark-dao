import SourceV14.Settlement

/-! Spark DAO teaching and research rules v1.4, English clauses 3.1–3.6. -/

namespace SourceV14

open Booking Settlement

-- §3.1. Facts verified for the particular place and lesson.
structure AbsenceFacts where
  startRequirementsMet : Prop
  studentNotifiedAsAgreed : Prop
  teachingAvailableAsAgreed : Prop
  studentDidNotAttend : Prop
  providerErrorCausedMissedService : Prop
  cancelledOrRescheduledUnderTerms : Prop
  lessonWentAhead : Prop
  couldNotProceedSolelyForNonattendance : Prop
  studentWasNotReady : Prop
  verifiedGoodReason : Option Bool

def verifiedStudentAbsence (lesson : Lesson) (place : Place) (facts : AbsenceFacts) : Prop :=
  place.matches lesson ∧ facts.startRequirementsMet ∧ facts.studentNotifiedAsAgreed ∧
    facts.teachingAvailableAsAgreed ∧ facts.studentDidNotAttend ∧
    ¬ facts.providerErrorCausedMissedService ∧ ¬ facts.cancelledOrRescheduledUnderTerms

def groupAbsenceHalfFee (lesson : Lesson) (place : Place) (facts : AbsenceFacts) : Prop :=
  lesson.kind = .group ∧ verifiedStudentAbsence lesson place facts ∧ facts.lessonWentAhead

def oneToOneAbsenceHalfFee (lesson : Lesson) (place : Place) (facts : AbsenceFacts) : Prop :=
  lesson.kind = .oneToOne ∧ verifiedStudentAbsence lesson place facts ∧
    facts.couldNotProceedSolelyForNonattendance ∧ facts.studentWasNotReady ∧
    facts.verifiedGoodReason = some false

def oneToOneAbsenceUsesChangeTerms (lesson : Lesson) (place : Place)
    (facts : AbsenceFacts) : Prop :=
  lesson.kind = .oneToOne ∧ verifiedStudentAbsence lesson place facts ∧
    facts.couldNotProceedSolelyForNonattendance ∧ facts.verifiedGoodReason = some true

def absenceCustomerFee (feePayable : Amount) : Amount := feePayable / 2

def oneToOneAbsenceTutorPay (lesson : Lesson) : Amount := lesson.normalTutorFee / 2

/-- The group absence fee for the tutor is the amount agreed in advance for that place. -/
def groupAbsenceAmounts (lesson : Lesson) (place : Place) (facts : AbsenceFacts)
    (feePayable agreedAbsenceTutorPay customerFee tutorPay : Amount) : Prop :=
  groupAbsenceHalfFee lesson place facts ∧
    customerFee = absenceCustomerFee feePayable ∧ tutorPay = agreedAbsenceTutorPay

def oneToOneAbsenceAmounts (lesson : Lesson) (place : Place) (facts : AbsenceFacts)
    (customerFee tutorPay : Amount) : Prop :=
  oneToOneAbsenceHalfFee lesson place facts ∧
    customerFee = absenceCustomerFee place.feePayable ∧ tutorPay = oneToOneAbsenceTutorPay lesson

/-- The §4.3 gross credit to restore before deducting valid prior restorations. -/
def grossLessonCreditRestoration (creditDebited finalFee : Amount) : Amount :=
  max 0 (creditDebited - finalFee)

-- §3.2. The ground states which service was missed or what serious incident occurred.
inductive TutorFaultGround where
  | missedAgreedService (service : String) (agreedAndNotProvided : Prop)
  | seriousIncident (description : String) (affectedPeople : List ActorId)
      (occurredAndWasSerious : Prop)

def TutorFaultGround.established : TutorFaultGround → Prop
  | .missedAgreedService service agreedAndNotProvided =>
      service ≠ "" ∧ agreedAndNotProvided
  | .seriousIncident description affectedPeople occurredAndWasSerious =>
      description ≠ "" ∧ affectedPeople ≠ [] ∧ occurredAndWasSerious

inductive TutorFaultScope where
  | particularPlaces (places : List PlaceId)
  | entireClass

def TutorFaultScope.affects : TutorFaultScope → PlaceId → Prop
  | .particularPlaces places, place => place ∈ places
  | .entireClass, _ => True

structure TutorFaultFinding where
  lesson : LessonId
  tutor : ActorId
  coordinatorCheckedWithTutor : Prop
  coordinatorCheckedWithAffectedStudents : Prop
  tutorGivenOpportunityToRespond : Prop
  ground : TutorFaultGround
  scope : TutorFaultScope

def tutorFaultInvestigationRequired (failedAgreedTeaching seriousTeachingProblem : Prop) : Prop :=
  failedAgreedTeaching ∨ seriousTeachingProblem

def TutorFaultFinding.establishedFor (finding : TutorFaultFinding) (lesson : Lesson) : Prop :=
  finding.lesson = lesson.id ∧ finding.tutor = lesson.tutor ∧
    finding.coordinatorCheckedWithTutor ∧ finding.coordinatorCheckedWithAffectedStudents ∧
    finding.tutorGivenOpportunityToRespond ∧ finding.ground.established

structure TutorFaultPlaceFacts where
  feePaidInFull : Prop
  studentAttendedAsAgreed : Prop
  studentReadyToAttendAsAgreed : Prop

def tutorFaultCompensationEligible (lesson : Lesson) (place : Place)
    (finding : TutorFaultFinding) (facts : TutorFaultPlaceFacts) : Prop :=
  place.matches lesson ∧ finding.establishedFor lesson ∧ finding.scope.affects place.id ∧
    facts.feePaidInFull ∧ (facts.studentAttendedAsAgreed ∨ facts.studentReadyToAttendAsAgreed)

structure TutorFaultCase where
  originalLesson : Lesson
  originalLessonAt : Moment
  finding : TutorFaultFinding

def originalTutorDeduction (fault : TutorFaultCase) : Amount := fault.originalLesson.normalTutorFee

/-- The zero pay also covers any otherwise payable absence fee for the original lesson. -/
def originalFaultTutorSettlement (fault : TutorFaultCase) (deduction tutorPay : Amount) : Prop :=
  fault.finding.establishedFor fault.originalLesson ∧
    deduction = originalTutorDeduction fault ∧ tutorPay = 0

-- §3.3. Compensation for each affected group place uses the §3.2 eligibility test.
def groupTutorFaultOtherPlace (lesson : Lesson) (place : Place)
    (finding : TutorFaultFinding) : Prop :=
  lesson.kind = .group ∧ place.matches lesson ∧ finding.establishedFor lesson ∧
    ¬ finding.scope.affects place.id

def groupPreviousAbsenceCorrectionRequired (lesson : Lesson) (place : Place)
    (previousAbsenceSettlement tutorCouldNotProvideAgreedService : Prop) : Prop :=
  lesson.kind = .group ∧ place.matches lesson ∧
    previousAbsenceSettlement ∧ tutorCouldNotProvideAgreedService

-- §3.4. Time and pay in these rows come from the verified teaching and fee records.
structure TutorLessonRecord where
  lesson : Lesson
  completedAt : Option Moment
  completedForSparkDAO : Bool
  feeOtherwisePayable : Amount
  deriving DecidableEq, Repr

def laterPayableTutorCompletion (fault : TutorFaultCase) (candidate : TutorLessonRecord)
    (atTime : Moment) : Prop :=
  candidate.lesson.id ≠ fault.originalLesson.id ∧
    candidate.lesson.tutor = fault.originalLesson.tutor ∧
    candidate.completedForSparkDAO = true ∧ candidate.completedAt = some atTime ∧
    fault.originalLessonAt.before atTime ∧ 0 < candidate.feeOtherwisePayable

/-- The supplied verified history covers actual completions after the original lesson. -/
def firstPayableLessonAfterFault (fault : TutorFaultCase) (history : List TutorLessonRecord)
    (next : TutorLessonRecord) : Prop :=
  fault.finding.establishedFor fault.originalLesson ∧ next ∈ history ∧
    ∃ completedAt, laterPayableTutorCompletion fault next completedAt ∧
      ∀ row ∈ history, ∀ otherTime, laterPayableTutorCompletion fault row otherTime →
        row = next ∨ completedAt.before otherTime

abbrev TutorDeductionKey := ActorId × LessonId

def TutorFaultCase.deductionKey (fault : TutorFaultCase) : TutorDeductionKey :=
  (fault.originalLesson.tutor, fault.originalLesson.id)

def nextTutorDeduction (fault : TutorFaultCase) : Amount := originalTutorDeduction fault / 2

def appliedTutorDeduction (fault : TutorFaultCase) (next : TutorLessonRecord) : Amount :=
  min (nextTutorDeduction fault) next.feeOtherwisePayable

def unappliedTutorDeduction (fault : TutorFaultCase) (next : TutorLessonRecord) : Amount :=
  nextTutorDeduction fault - appliedTutorDeduction fault next

def nextTutorPay (fault : TutorFaultCase) (next : TutorLessonRecord) : Amount :=
  next.feeOtherwisePayable - appliedTutorDeduction fault next

/-- The deduction record refers to the tutor and original lesson, and to the next lesson total. -/
structure NextTutorDeductionRecord where
  key : TutorDeductionKey
  nextLesson : LessonId
  payableBeforeDeductions : Amount
  fixedAmount : Amount
  appliedAmount : Amount
  unappliedAmount : Amount
  shortfallTerms : Option String

def NextTutorDeductionRecord.matches (record : NextTutorDeductionRecord) (fault : TutorFaultCase)
    (next : TutorLessonRecord) : Prop :=
  record.key = fault.deductionKey ∧ record.nextLesson = next.lesson.id ∧
    record.payableBeforeDeductions = next.feeOtherwisePayable ∧
    record.fixedAmount = nextTutorDeduction fault ∧
    0 ≤ record.appliedAmount ∧ record.appliedAmount ≤ record.fixedAmount ∧
    record.unappliedAmount = record.fixedAmount - record.appliedAmount ∧
    (0 < record.unappliedAmount →
      ∃ terms, record.shortfallTerms = some terms ∧ terms ≠ "")

/-- Each applicable original in the verified fault history is recorded once. -/
def nextTutorDeductionsSettled (verifiedHistory : List TutorLessonRecord)
    (next : TutorLessonRecord) (priorApplications : List TutorDeductionKey)
    (verifiedFaults : List TutorFaultCase) (records : List NextTutorDeductionRecord)
    (tutorPay : Amount) : Prop :=
  0 ≤ next.feeOtherwisePayable ∧
    (records.map NextTutorDeductionRecord.key).Nodup ∧
    (∀ fault ∈ verifiedFaults, firstPayableLessonAfterFault fault verifiedHistory next →
      fault.deductionKey ∉ priorApplications →
      ∃ record ∈ records, record.matches fault next) ∧
    (∀ record ∈ records, ∃ fault ∈ verifiedFaults,
      firstPayableLessonAfterFault fault verifiedHistory next ∧
      fault.deductionKey ∉ priorApplications ∧ record.matches fault next) ∧
    sumAmounts records NextTutorDeductionRecord.appliedAmount =
      min (sumAmounts records NextTutorDeductionRecord.fixedAmount) next.feeOtherwisePayable ∧
    tutorPay = next.feeOtherwisePayable - sumAmounts records NextTutorDeductionRecord.appliedAmount

/-- Actual payment is checked separately from the deduction calculation and customer remedies. -/
structure ActualTutorPayment where
  lesson : LessonId
  tutor : ActorId
  amount : Amount
  paidAt : Moment

def nextTutorPaymentMatches (next : TutorLessonRecord) (settledAt : Moment)
    (agreedPaymentConditionsAt : Moment → Prop) (tutorPay : Amount)
    (payment : Option ActualTutorPayment) : Prop :=
  match payment with
  | none => tutorPay = 0
  | some entry =>
      entry.lesson = next.lesson.id ∧ entry.tutor = next.lesson.tutor ∧
        entry.amount = tutorPay ∧ 0 < entry.amount ∧
        settledAt.by entry.paidAt ∧ agreedPaymentConditionsAt entry.paidAt

-- §§3.5–3.6. Provider error has to cause the loss of an agreed service.
inductive ProviderErrorKind where
  | arranging
  | administering
  | notifying
  deriving DecidableEq, Repr

structure ProviderFaultFacts where
  lesson : LessonId
  place : PlaceId
  provider : ActorId
  kind : ProviderErrorKind
  errorOccurred : Prop
  missedAgreedServiceAsResult : Prop
  missedAgreedTeachingAsResult : Prop

def ProviderFaultFacts.applies (facts : ProviderFaultFacts) (lesson : Lesson)
    (place : Place) : Prop :=
  place.matches lesson ∧ facts.lesson = lesson.id ∧ facts.place = place.id ∧
    facts.provider = lesson.provider ∧ facts.errorOccurred ∧ facts.missedAgreedServiceAsResult

inductive FaultBasis where
  | tutor (finding : TutorFaultFinding) (facts : TutorFaultPlaceFacts)
  | provider (facts : ProviderFaultFacts)

/-- The finding concerns the tutor responsible for this lesson, including an agreed replacement. -/
def FaultBasis.lessonWithResponsibleTutor (basis : FaultBasis) (lesson : Lesson) : Lesson :=
  match basis with
  | .tutor finding _ => { lesson with tutor := finding.tutor }
  | .provider _ => lesson

def FaultBasis.applies (basis : FaultBasis) (lesson : Lesson) (place : Place) : Prop :=
  match basis with
  | .tutor finding facts => tutorFaultCompensationEligible lesson place finding facts
  | .provider facts => facts.applies lesson place

def FaultBasis.standardCompensationOffered (basis : FaultBasis) (lesson : Lesson)
    (place : Place) : Prop :=
  basis.applies lesson place ∧
    match basis with
    | .tutor _ _ => True
    | .provider facts => facts.missedAgreedTeachingAsResult

inductive TeachingReceived where
  | none
  | some
  | all
  deriving DecidableEq, Repr

def halfPriceBenefit (original : Place) : Amount := original.normalFee / 2

def compensationCourseCredit (original : Place) : Amount := original.normalFee

def appliedHalfPriceBenefit (original : Place) (feeOtherwiseDue : Amount) : Amount :=
  min (halfPriceBenefit original) feeOtherwiseDue

def unappliedHalfPriceBenefit (original : Place) (feeOtherwiseDue : Amount) : Amount :=
  halfPriceBenefit original - appliedHalfPriceBenefit original feeOtherwiseDue

def feeAfterHalfPriceBenefit (original : Place) (feeOtherwiseDue : Amount) : Amount :=
  feeOtherwiseDue - appliedHalfPriceBenefit original feeOtherwiseDue

def feeAfterOriginalCompensation (original : Place) (teaching : TeachingReceived)
    (otherwiseDue : Amount := original.feePayable) : Amount :=
  match teaching with
  | .none => 0
  | .some | .all => feeAfterHalfPriceBenefit original otherwiseDue

structure RemedialTeachingArrangement where
  specificTime : Option Moment
  confirmedBy : ActorId
  otherNecessaryConsents : Prop
  academicTeamNotifiedStudentAsAgreed : Prop
  noticeRecorded : Prop

def remedialTeachingAgreed (place : Place) (arrangement : RemedialTeachingArrangement) : Prop :=
  (∃ time, arrangement.specificTime = some time) ∧
    arrangement.confirmedBy = place.payer ∧ arrangement.otherNecessaryConsents

def remedialTeachingArranged (place : Place) (arrangement : RemedialTeachingArrangement) : Prop :=
  remedialTeachingAgreed place arrangement ∧
    arrangement.academicTeamNotifiedStudentAsAgreed ∧ arrangement.noticeRecorded

inductive RemedyKind where
  | standardCompensation
  | remedialTeaching (arrangement : RemedialTeachingArrangement)
  | otherRemedy

/-- The services, acceptance and delivery deadline actually agreed and recorded on the form. -/
structure RemedyAgreement where
  lesson : LessonId
  place : PlaceId
  customer : ActorId
  kind : RemedyKind
  scope : List String
  acceptedAt : Moment
  deliveryDeadline : Moment

def RemedyAgreement.forPlace (agreement : RemedyAgreement) (place : Place) : Prop :=
  agreement.lesson = place.lesson ∧ agreement.place = place.id ∧
    agreement.customer = place.customer ∧ agreement.scope ≠ [] ∧
    match agreement.kind with
    | .remedialTeaching arrangement => remedialTeachingAgreed place arrangement
    | .standardCompensation | .otherRemedy => True

def RemedyAgreement.acceptedStandardFor (agreement : RemedyAgreement) (place : Place) : Prop :=
  agreement.forPlace place ∧ agreement.kind = .standardCompensation

def RemedyAgreement.validForFault (agreement : RemedyAgreement) (lesson : Lesson) (place : Place)
    (fault : FaultBasis) : Prop :=
  agreement.forPlace place ∧
    match agreement.kind with
    | .standardCompensation => fault.standardCompensationOffered lesson place
    | .remedialTeaching _ | .otherRemedy => fault.applies lesson place

/-- With tutor fault the original partial-teaching relief need not wait for package acceptance. -/
def originalCompensationRelief (lesson : Lesson) (original : Place) (basis : FaultBasis)
    (teaching : TeachingReceived) (agreements : List RemedyAgreement) (atTime : Moment)
    (otherwiseDue feeDue : Amount) : Prop :=
  basis.standardCompensationOffered lesson original ∧
    (teaching = .none ∨
      (match basis with
       | .tutor _ _ => True
       | .provider _ =>
           ∃ agreement ∈ agreements, agreement.acceptedStandardFor original ∧
             agreement.acceptedAt.by atTime)) ∧
    feeDue = feeAfterOriginalCompensation original teaching otherwiseDue

/-- A later discount is delivered when this benefit becomes available for booking. -/
def laterBenefitDeliveredBy (original : Place) (teaching : TeachingReceived)
    (agreement : RemedyAgreement) (availableAt query : Moment) : Prop :=
  teaching = .none ∧ agreement.acceptedStandardFor original ∧
    agreement.acceptedAt.by availableAt ∧ availableAt.by query

structure LaterBenefitUse where
  originalLesson : LessonId
  originalPlace : PlaceId
  lesson : LessonId
  place : PlaceId
  selectedBy : ActorId
  bookedAt : Moment
  feeOtherwiseDue : Amount
  applied : Amount
  unapplied : Amount

/-- The earlier teaching and the booking records determine which lesson uses the single benefit. -/
def laterBenefitApplied (original selected : Place) (originalAt selectedLessonAt : Moment)
    (teaching : TeachingReceived) (agreement : RemedyAgreement) (availableAt : Moment)
    (selectedSparkDAOLesson : Prop) (priorUses : List LaterBenefitUse)
    (entry : LaterBenefitUse) (newFeeDue : Amount) : Prop :=
  laterBenefitDeliveredBy original teaching agreement availableAt entry.bookedAt ∧
    selectedSparkDAOLesson ∧ selected.lesson ≠ original.lesson ∧
    originalAt.before selectedLessonAt ∧
    entry.originalLesson = original.lesson ∧ entry.originalPlace = original.id ∧
    entry.lesson = selected.lesson ∧ entry.place = selected.id ∧
    entry.selectedBy = original.customer ∧ selected.customer = original.customer ∧
    (∀ prior ∈ priorUses, ¬ (prior.originalLesson = original.lesson ∧
      prior.originalPlace = original.id)) ∧ entry.feeOtherwiseDue = selected.feePayable ∧
    entry.applied = appliedHalfPriceBenefit original entry.feeOtherwiseDue ∧
    entry.unapplied = unappliedHalfPriceBenefit original entry.feeOtherwiseDue ∧
    newFeeDue = feeAfterHalfPriceBenefit original entry.feeOtherwiseDue

structure CourseCreditIssue where
  originalLesson : LessonId
  originalPlace : PlaceId
  account : AccountId
  amount : Amount
  postedAt : Moment
  usableForBookingAt : Option Moment

/-- The customer's compensation account is distinct in role from the lesson's debit account. -/
def courseCreditIssuedBy (original : Place) (customerAccount : AccountId)
    (agreement : RemedyAgreement) (entry : CourseCreditIssue) (query : Moment) : Prop :=
  agreement.acceptedStandardFor original ∧
    entry.originalLesson = original.lesson ∧ entry.originalPlace = original.id ∧
    entry.account = customerAccount ∧
    entry.amount = compensationCourseCredit original ∧ agreement.acceptedAt.by entry.postedAt ∧
    ∃ usableAt, entry.usableForBookingAt = some usableAt ∧
      entry.postedAt.by usableAt ∧ usableAt.by query

def courseCreditPostingMatches (original : Place) (agreement : RemedyAgreement)
    (issue : CourseCreditIssue) (ownsAccount : ActorId → AccountId → Prop)
    (posting : CreditPosting) : Prop :=
  ownsAccount original.customer issue.account ∧
    courseCreditIssuedBy original issue.account agreement issue posting.point ∧
    posting.kind = .compensation original.lesson original.id ∧
    posting.account = issue.account ∧ posting.amount = issue.amount ∧ 0 < posting.amount ∧
    issue.usableForBookingAt = some posting.point

inductive CompensationCreditUse where
  | sparkDAOLesson (lesson : LessonId)
  | cashWithdrawal

def CompensationCreditUse.allowed : CompensationCreditUse → Prop
  | .sparkDAOLesson _ => True
  | .cashWithdrawal => False

structure DeadlineConsent where
  party : ActorId
  signer : ActorId
  newDeadline : Moment
  agreedAt : Moment

/-- Extension is a separate agreement on a specific new deadline. -/
def remedyDeadlineExtended (acceptedAt oldDeadline newDeadline query : Moment) (affected : List ActorId)
    (consents : List DeadlineConsent)
    (authorisedRepresentativeAt : ActorId → ActorId → Moment → Prop)
    (recordedOnForm : Prop) : Prop :=
  oldDeadline.before newDeadline ∧ recordedOnForm ∧
    ∀ party ∈ affected, ∃ consent ∈ consents,
      consent.party = party ∧ consent.newDeadline = newDeadline ∧
      acceptedAt.by consent.agreedAt ∧ consent.agreedAt.before oldDeadline ∧
      consent.agreedAt.by query ∧
      (consent.signer = party ∨ authorisedRepresentativeAt party consent.signer consent.agreedAt)

structure RemedyExtension where
  agreement : RemedyAgreement
  oldDeadline : Moment
  newDeadline : Moment
  /-- Verified parties affected by this extension. -/
  affected : List ActorId
  consents : List DeadlineConsent
  authorisedRepresentativeAt : ActorId → ActorId → Moment → Prop
  separatelyAgreedAndRecordedOnForm : Prop

def RemedyExtension.applies (extension : RemedyExtension) (agreement : RemedyAgreement)
    (provider : ActorId) (current query : Moment) : Prop :=
  extension.agreement = agreement ∧ extension.oldDeadline = current ∧
    agreement.customer ∈ extension.affected ∧ provider ∈ extension.affected ∧
    remedyDeadlineExtended agreement.acceptedAt current extension.newDeadline query
      extension.affected extension.consents extension.authorisedRepresentativeAt
      extension.separatelyAgreedAndRecordedOnForm

/-- Read the form's extension records in order. An inapplicable record leaves the deadline intact. -/
def effectiveRemedyDeadline (agreement : RemedyAgreement) (provider : ActorId) (query : Moment)
    (extensions : List RemedyExtension) (current effective : Moment) : Prop :=
  match extensions with
  | [] => effective = current
  | extension :: rest =>
    (extension.applies agreement provider current query ∧
      effectiveRemedyDeadline agreement provider query rest extension.newDeadline effective) ∨
    (¬ extension.applies agreement provider current query ∧
      effectiveRemedyDeadline agreement provider query rest current effective)

structure LaterBenefitAvailability where
  originalLesson : LessonId
  originalPlace : PlaceId
  amount : Amount
  availableAt : Moment
  verifiedAvailableForBooking : Prop

def LaterBenefitAvailability.deliveredBy (record : LaterBenefitAvailability) (original : Place)
    (teaching : TeachingReceived) (agreement : RemedyAgreement) (query : Moment) : Prop :=
  record.originalLesson = original.lesson ∧ record.originalPlace = original.id ∧
    record.amount = halfPriceBenefit original ∧ record.verifiedAvailableForBooking ∧
    laterBenefitDeliveredBy original teaching agreement record.availableAt query

structure ClosureTreatment where
  termsOrLawRef : String
  actionRecorded : String
  settledAt : Moment
  verifiedAsAppliedUnderTermsAndLaw : Prop

def ClosureTreatment.recordedBy (treatment : ClosureTreatment) (closedAt : Moment) : Prop :=
  treatment.termsOrLawRef ≠ "" ∧ treatment.actionRecorded ≠ "" ∧
    treatment.verifiedAsAppliedUnderTermsAndLaw ∧ treatment.settledAt.by closedAt

structure RemedyClosureDisposition where
  agreement : RemedyAgreement
  treatment : ClosureTreatment

structure DiscountClosureDisposition where
  agreement : RemedyAgreement
  benefit : LaterBenefitAvailability
  unusedAmount : Amount
  verifiedUnusedAmount : Prop
  treatment : ClosureTreatment

structure CreditClosureDisposition where
  issue : CreditPosting
  checkedAt : Moment
  unusedAmount : Amount
  /-- Verified balance attributable to this issue before the recorded treatment. -/
  verifiedUnusedAmount : Prop
  /-- The amount the applicable terms and law require removing from this account. -/
  removalRequired : Amount
  treatment : ClosureTreatment

def CreditClosureDisposition.applicable (row : CreditClosureDisposition) (ledger : List CreditPosting)
    (lesson : LessonId) (place : PlaceId) (closedAt : Moment) : Prop :=
  row.issue ∈ ledger ∧ row.issue.kind = .compensation lesson place ∧ 0 < row.issue.amount ∧
    row.issue.point.by row.checkedAt ∧ row.checkedAt.by row.treatment.settledAt ∧
    row.treatment.recordedBy closedAt ∧ row.verifiedUnusedAmount ∧
    0 ≤ row.removalRequired ∧ row.removalRequired ≤ row.unusedAmount ∧
    row.unusedAmount ≤ row.issue.amount - returnedFrom ledger row.issue row.checkedAt

def CreditClosureDisposition.matches (row : CreditClosureDisposition) (ledger : List CreditPosting)
    (lesson : LessonId) (place : PlaceId) (closedAt : Moment) : Prop :=
  row.applicable ledger lesson place closedAt ∧
    returnedFrom ledger row.issue row.treatment.settledAt =
      returnedFrom ledger row.issue row.checkedAt + row.removalRequired

structure FullRefundClosure where
  lesson : LessonId
  place : PlaceId
  closedAt : Moment
  remedies : List RemedyClosureDisposition
  discounts : List DiscountClosureDisposition
  credits : List CreditClosureDisposition

def FullRefundClosure.creditDispositionsRecorded (closure : FullRefundClosure)
    (ledger : List CreditPosting) : Prop :=
  (closure.credits.map (·.issue.id)).Nodup ∧
  (∀ issue ∈ ledger, issue.kind = .compensation closure.lesson closure.place →
    issue.point.by closure.closedAt → ∃ row ∈ closure.credits, row.issue = issue) ∧
  ∀ row ∈ closure.credits, row.matches ledger closure.lesson closure.place closure.closedAt

/-- The negative ledger posting removes only credit from the identified, actually issued credit. -/
def compensationClosureRemovalPosting (ledger : List CreditPosting)
    (closed : List FullRefundClosure) (posting : CreditPosting) : Prop :=
  posting ∈ ledger ∧ 0 < posting.amount ∧
    ∃ closure ∈ closed, ∃ row ∈ closure.credits,
      row.applicable ledger closure.lesson closure.place closure.closedAt ∧
      0 < row.removalRequired ∧ posting.kind = .creditReturned row.issue.id ∧
      posting.account = row.issue.account ∧ row.checkedAt.before posting.point ∧
      posting.point.by row.treatment.settledAt ∧
      returnedFrom ledger row.issue posting.point ≤
        returnedFrom ledger row.issue row.checkedAt + row.removalRequired

/-- The history consists of verified, actual closures. -/
def fullRefundClosedBy (place : Place) (closed : List FullRefundClosure) (query : Moment) : Prop :=
  ∃ entry ∈ closed, entry.lesson = place.lesson ∧ entry.place = place.id ∧ entry.closedAt.by query

structure RemedyEvidence where
  ledger : List CreditPosting
  ownsAccount : ActorId → AccountId → Prop
  closed : List FullRefundClosure
  teaching : TeachingReceived
  lesson : Lesson
  fault : FaultBasis
  feeAt : Moment → Amount → Prop

structure OriginalCompensationSettlement where
  settlement : LessonSettlement
  settledAt : Moment
  appliedToOriginal : Amount
  unappliedFromOriginalUse : Amount
  unappliedAmountHandledUnderTerms : Amount → Prop

def OriginalCompensationSettlement.amountsRecorded (record : OriginalCompensationSettlement)
    (original : Place) (teaching : TeachingReceived) (ledger : List CreditPosting)
    (query : Moment) (otherwiseDue : Amount) : Prop :=
  record.settledAt.by query ∧ record.settlement.matchesPaymentHistory original ledger record.settledAt ∧
  record.settlement.feePayable = feeAfterOriginalCompensation original teaching otherwiseDue ∧
  record.settlement.creditDueBack =
    grossLessonCreditRestoration record.settlement.debited record.settlement.feePayable ∧
  match teaching with
  | .none => record.appliedToOriginal = 0 ∧ record.unappliedFromOriginalUse = 0
  | .some | .all =>
    record.appliedToOriginal = appliedHalfPriceBenefit original otherwiseDue ∧
    record.unappliedFromOriginalUse = unappliedHalfPriceBenefit original otherwiseDue

def OriginalCompensationSettlement.completedBy (record : OriginalCompensationSettlement)
    (original : Place) (teaching : TeachingReceived) (ledger : List CreditPosting)
    (query : Moment) (otherwiseDue : Amount) : Prop :=
  record.amountsRecorded original teaching ledger query otherwiseDue ∧
  FeeRefundCompleted original ledger query
    (grossLessonCreditRestoration (debitTotal original ledger query) record.settlement.feePayable) ∧
  (0 < record.unappliedFromOriginalUse →
    record.unappliedAmountHandledUnderTerms record.unappliedFromOriginalUse)

inductive RemedyDelivery where
  | standardCompensation (originalRelief : Option OriginalCompensationSettlement)
      (laterBenefit : Option LaterBenefitAvailability) (credit : CourseCreditIssue)
  | remedialTeaching (completedAt : Moment) (verifiedTeachingAsAgreed : String → Prop)
  | otherRemedy (completedAt : Moment) (verifiedServiceAsAgreed : String → Prop)

def RemedyDelivery.completedBy (delivery : RemedyDelivery) (agreement : RemedyAgreement)
    (original : Place) (evidence : RemedyEvidence) (query : Moment) : Prop :=
  match agreement.kind, delivery with
  | .standardCompensation, .standardCompensation originalRelief laterBenefit credit =>
    (∃ relief fee, originalRelief = some relief ∧ evidence.feeAt relief.settledAt fee ∧
      relief.completedBy original evidence.teaching evidence.ledger query fee) ∧
    (match evidence.teaching with
    | .none => ∃ benefit, laterBenefit = some benefit ∧
        benefit.deliveredBy original evidence.teaching agreement query
    | .some | .all => True) ∧
    ∃ posting ∈ evidence.ledger, posting.point.by query ∧
      courseCreditPostingMatches original agreement credit evidence.ownsAccount posting
  | .remedialTeaching arrangement, .remedialTeaching completedAt verifiedTeachingAsAgreed =>
    remedialTeachingArranged original arrangement ∧
    agreement.acceptedAt.by completedAt ∧ completedAt.by query ∧
    ∀ service ∈ agreement.scope, verifiedTeachingAsAgreed service
  | .otherRemedy, .otherRemedy completedAt verifiedServiceAsAgreed =>
    agreement.acceptedAt.by completedAt ∧ completedAt.by query ∧
    ∀ service ∈ agreement.scope, verifiedServiceAsAgreed service
  | _, _ => False

-- §3.6. Refunds use verified choice, coverage, delivery and timing facts.
structure RemedyProgress where
  agreement : RemedyAgreement
  extensions : List RemedyExtension
  delivery : Option RemedyDelivery
  providerConfirmedUnableAt : Option Moment
  stillOwedAt : Moment → Prop

def RemedyProgress.deadlineBy (progress : RemedyProgress) (provider : ActorId)
    (query effective : Moment) : Prop :=
  effectiveRemedyDeadline progress.agreement provider query progress.extensions
    progress.agreement.deliveryDeadline effective

def RemedyProgress.deliveredBy (progress : RemedyProgress) (place : Place)
    (evidence : RemedyEvidence) (query : Moment) : Prop :=
  progress.agreement.validForFault evidence.lesson place evidence.fault ∧
  ∃ delivery deliveredAt deadline, progress.delivery = some delivery ∧
    progress.deadlineBy evidence.lesson.provider deliveredAt deadline ∧
    deliveredAt.by deadline ∧ deliveredAt.by query ∧
    progress.agreement.acceptedAt.by deliveredAt ∧
    (∀ unableAt, progress.providerConfirmedUnableAt = some unableAt →
      progress.agreement.acceptedAt.by unableAt → deliveredAt.by unableAt) ∧
    ¬ fullRefundClosedBy place evidence.closed deliveredAt ∧
    delivery.completedBy progress.agreement place evidence deliveredAt

def serviceSettledByRemedy (place : Place) (progress : RemedyProgress)
    (evidence : RemedyEvidence) (service : String) (query : Moment) : Prop :=
  service ∈ progress.agreement.scope ∧ progress.deliveredBy place evidence query

/-- Amount attributable under the applicable terms, for the identified original services. -/
structure OutstandingOriginalServices where
  lesson : LessonId
  place : PlaceId
  services : List String
  feeAttributable : Amount
  verifiedOutstandingAt : String → Moment → Prop

def OutstandingOriginalServices.verifiedFor (outstanding : OutstandingOriginalServices)
    (place : Place) (remedies : List RemedyProgress) (evidence : RemedyEvidence)
    (trigger : Moment) : Prop :=
  outstanding.lesson = place.lesson ∧ outstanding.place = place.id ∧
    outstanding.services ≠ [] ∧ 0 ≤ outstanding.feeAttributable ∧
    (∃ fee, evidence.feeAt trigger fee ∧ outstanding.feeAttributable ≤ fee) ∧
    ∀ service ∈ outstanding.services, outstanding.verifiedOutstandingAt service trigger ∧
      ¬ ∃ remedy ∈ remedies, serviceSettledByRemedy place remedy evidence service trigger

structure DirectRefundRequest where
  lesson : LessonId
  place : PlaceId
  customer : ActorId
  scope : List String
  electedAt : Moment
  receivedAt : Moment
  validUnderApplicableTermsAndLaw : Prop

def DirectRefundRequest.validFor (request : DirectRefundRequest) (place : Place) : Prop :=
  request.lesson = place.lesson ∧ request.place = place.id ∧
    request.customer = place.customer ∧
    request.electedAt.by request.receivedAt ∧ request.validUnderApplicableTermsAndLaw

/-- A switch to a refund after acceptance requires a valid choice under the terms and law. -/
def remedyRefundSwitch (place : Place) (agreement : RemedyAgreement)
    (request : DirectRefundRequest) (service : String) : Prop :=
  request.validFor place ∧ agreement.forPlace place ∧
    agreement.acceptedAt.by request.electedAt ∧
    service ∈ agreement.scope ∧ service ∈ request.scope

/-- A separate refund of service already made good depends on the applicable terms and law. -/
def refundOfServiceMadeGood (place : Place) (progress : RemedyProgress)
    (evidence : RemedyEvidence) (service : String) (query : Moment)
    (separateRefundOwedUnderTermsAndLaw : Prop) : Prop :=
  serviceSettledByRemedy place progress evidence service query ∧ separateRefundOwedUnderTermsAndLaw

structure SeparateMadeGoodRefund where
  lesson : LessonId
  place : PlaceId
  services : List String
  trigger : Moment
  finalFee : Amount
  verifiedRefundDueUnderTermsAndLaw : Prop

def separateMadeGoodRefund (lesson : Lesson) (place : Place) (fault : FaultBasis)
    (separate : SeparateMadeGoodRefund) (remedies : List RemedyProgress) (evidence : RemedyEvidence)
    (query trigger : Moment) (fee : Amount) : Prop :=
  fault.applies lesson place ∧ separate.lesson = place.lesson ∧ separate.place = place.id ∧
    separate.services ≠ [] ∧ trigger = separate.trigger ∧ trigger.by query ∧
    fee = separate.finalFee ∧ 0 ≤ fee ∧ (∃ agreed, evidence.feeAt trigger agreed ∧ fee ≤ agreed) ∧
    ∀ service ∈ separate.services, ∃ remedy ∈ remedies,
      refundOfServiceMadeGood place remedy evidence service trigger
        separate.verifiedRefundDueUnderTermsAndLaw

/-- A valid refund election starts handling when the provider receives it. -/
def directRefundTrigger (lesson : Lesson) (place : Place) (fault : FaultBasis)
    (outstanding : OutstandingOriginalServices) (remedies : List RemedyProgress)
    (evidence : RemedyEvidence) (request : DirectRefundRequest) (query trigger : Moment) : Prop :=
  fault.applies lesson place ∧ request.validFor place ∧ trigger = request.receivedAt ∧
    trigger.by query ∧ outstanding.verifiedFor place remedies evidence trigger ∧
    ∀ service ∈ outstanding.services, service ∈ request.scope

/-- For services still outstanding, the lapse is assessed at the form's acceptance deadline. -/
def noRemedyAgreedRefundTrigger (lesson : Lesson) (place : Place) (fault : FaultBasis)
    (outstanding : OutstandingOriginalServices) (remedies : List RemedyProgress)
    (evidence : RemedyEvidence) (requests : List DirectRefundRequest)
    (acceptanceDeadline query trigger : Moment) : Prop :=
  fault.applies lesson place ∧ trigger = acceptanceDeadline ∧ trigger.by query ∧
    outstanding.verifiedFor place remedies evidence trigger ∧
    ∀ service ∈ outstanding.services,
      (¬ ∃ request ∈ requests, request.validFor place ∧
        service ∈ request.scope ∧ request.electedAt.by trigger) ∧
      ¬ ∃ remedy ∈ remedies, remedy.agreement.validForFault lesson place fault ∧
        service ∈ remedy.agreement.scope ∧ remedy.agreement.acceptedAt.by trigger

def outstandingRefundNeedsFullWaiver (place : Place) (teaching : TeachingReceived)
    (remedies : List RemedyProgress) (evidence : RemedyEvidence) (trigger : Moment) : Prop :=
  teaching = .none ∧
    ¬ ∃ remedy ∈ remedies, ∃ service, serviceSettledByRemedy place remedy evidence service trigger

/-- Apply after a direct or acceptance-deadline refund trigger is established. -/
def outstandingRefundFee (place : Place) (teaching : TeachingReceived)
    (outstanding : OutstandingOriginalServices) (remedies : List RemedyProgress)
    (evidence : RemedyEvidence) (trigger : Moment) (feeDue : Amount) : Prop :=
  (outstandingRefundNeedsFullWaiver place teaching remedies evidence trigger ∧ feeDue = 0) ∨
    (¬ outstandingRefundNeedsFullWaiver place teaching remedies evidence trigger ∧
      ∃ agreed, evidence.feeAt trigger agreed ∧ feeDue = agreed - outstanding.feeAttributable)

def RemedyProgress.cannotDeliverEvent (progress : RemedyProgress) (provider : ActorId)
    (query atTime : Moment) : Prop :=
  progress.agreement.acceptedAt.by atTime ∧
    (progress.providerConfirmedUnableAt = some atTime ∨ progress.deadlineBy provider query atTime)

def failedAcceptedRemedyRefundTrigger (lesson : Lesson) (place : Place) (fault : FaultBasis)
    (progress : RemedyProgress) (evidence : RemedyEvidence) (query trigger : Moment) : Prop :=
  progress.agreement.validForFault lesson place fault ∧ trigger.by query ∧
    progress.cannotDeliverEvent lesson.provider query trigger ∧ progress.stillOwedAt trigger ∧
    ¬ fullRefundClosedBy place evidence.closed trigger ∧
    ¬ progress.deliveredBy place evidence trigger ∧
    ∀ event, progress.cannotDeliverEvent lesson.provider query event → trigger.by event

/-- This route waives the fee even when some original teaching or some remedy was provided. -/
def failedAcceptedRemedyRefund (lesson : Lesson) (place : Place) (fault : FaultBasis)
    (progress : RemedyProgress) (evidence : RemedyEvidence) (query trigger : Moment)
    (feeDue : Amount) : Prop :=
  failedAcceptedRemedyRefundTrigger lesson place fault progress evidence query trigger ∧ feeDue = 0

/-- The agreed date uses the trigger for this refund. An earlier legal date takes precedence. -/
def refundDeadline (agreedDeadline : Moment) (legalDeadline : Option Moment) : Moment :=
  match legalDeadline with
  | none => agreedDeadline
  | some legal => if legal.before agreedDeadline then legal else agreedDeadline

/-- Previously established unpaid refunds retain their own deadlines when a new amount falls due. -/
def additionalRefundDue (grossRefund validPriorRestorations alreadyDueAndUnpaid : Amount) :
    Amount :=
  max 0 (grossRefund - validPriorRestorations - alreadyDueAndUnpaid)

/-- The pre-closure history supplies the actual open remedies, discounts and credit issues. -/
def FullRefundClosure.dispositionsRecorded (closure : FullRefundClosure) (original : Place)
    (ledger : List CreditPosting) (remedies : List RemedyProgress)
    (benefits : List LaterBenefitAvailability) : Prop :=
  (∀ remedy ∈ remedies, remedy.agreement.forPlace original →
    remedy.agreement.acceptedAt.by closure.closedAt → remedy.stillOwedAt closure.closedAt →
    ∃ row ∈ closure.remedies, row.agreement = remedy.agreement) ∧
  (∀ row ∈ closure.remedies, row.agreement.forPlace original ∧
    row.agreement.acceptedAt.by row.treatment.settledAt ∧ row.treatment.recordedBy closure.closedAt ∧
    ∃ remedy ∈ remedies, remedy.agreement = row.agreement) ∧
  (∀ benefit ∈ benefits, benefit.originalLesson = original.lesson →
    benefit.originalPlace = original.id → benefit.verifiedAvailableForBooking →
    benefit.availableAt.by closure.closedAt →
    ∃ row ∈ closure.discounts, row.benefit = benefit) ∧
  (∀ row ∈ closure.discounts, row.benefit ∈ benefits ∧
    row.benefit.deliveredBy original .none row.agreement row.treatment.settledAt ∧
    0 ≤ row.unusedAmount ∧ row.unusedAmount ≤ row.benefit.amount ∧ row.verifiedUnusedAmount ∧
    row.treatment.recordedBy closure.closedAt ∧
    ∃ remedy ∈ remedies, remedy.agreement = row.agreement) ∧
  closure.creditDispositionsRecorded ledger

/-- The retained restoration amount comes from §4.3 for the actual debit account. -/
def closedByFullRefund (original : Place) (ledger : List CreditPosting)
    (remedies : List RemedyProgress) (benefits : List LaterBenefitAvailability)
    (creditDebited validCreditRestored feeDue : Amount) (termsAndLawPermitClosure : Prop)
    (closure : FullRefundClosure) : Prop :=
  closure.lesson = original.lesson ∧ closure.place = original.id ∧ termsAndLawPermitClosure ∧
    feeDue = 0 ∧ validCreditRestored = creditDebited ∧
    closure.dispositionsRecorded original ledger remedies benefits

end SourceV14
