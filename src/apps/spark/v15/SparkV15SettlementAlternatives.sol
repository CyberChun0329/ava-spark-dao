// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {ISparkV15BookingChanges, SparkV15Booking} from "./SparkV15Booking.sol";
import {SparkV15Payments} from "./SparkV15Payments.sol";
import {SparkV15ReviewCases, SparkV15ReviewContext} from "./SparkV15ReviewCases.sol";
import {SparkV15SettlementOccurrences} from "./SparkV15SettlementOccurrences.sol";

interface ISparkV15SettlementActors {
    function isSettlementActor(bytes32 lessonId, address actor) external view returns (bool);
    function hasAdoptedOneToOneCompletion(bytes32 lessonId, bytes32 formId) external view returns (bool);
    function retainedPayment(SparkV15Payments.PaymentTerms calldata expected, uint256 packageId)
        external view returns (bytes32 id, uint256 alreadyReceived);
}

/// @notice Case-scoped fee holds and the occurrence records required for one-to-one settlement.
contract SparkV15SettlementAlternatives {
    enum AbsenceReason {
        Unverified,
        NoGoodReason,
        GoodReason
    }

    struct FeeHoldTerms {
        bytes32 formId;
        bytes32 caseId;
        SparkV15ReviewContext.Notice notice;
        uint64 reviewAt;
    }

    struct FeeHold {
        FeeHoldTerms terms;
        address reviewer;
        bytes32 authorityId;
        uint256 evidenceId;
        uint64 imposedAt;
        uint64 liftedAt;
        address liftedBy;
        uint256 liftEvidenceId;
    }

    struct AbsenceFacts {
        bytes32 formId;
        uint64 occurredAt;
        bytes32 factsRef;
        bytes32 reasonCaseId;
        AbsenceReason reason;
    }

    struct AbsenceRecord {
        AbsenceFacts facts;
        uint256 evidenceId;
        address verifiedBy;
        uint64 verifiedAt;
    }

    bytes32 public constant ACTION_CONFIRM_ONE_TO_ONE = keccak256("spark.action.confirm-one-to-one-completion.v1.5");
    bytes32 public constant ACTION_VERIFY_ONE_TO_ONE_ABSENCE = keccak256("spark.action.verify-one-to-one-absence.v1.5");
    bytes32 public constant ACTION_IMPOSE_FEE_HOLD = keccak256("spark.action.impose-fee-hold.v1.5");
    bytes32 public constant ACTION_LIFT_FEE_HOLD = keccak256("spark.action.lift-fee-hold.v1.5");

    error InvalidFeeHold();
    error InvalidCompletion();
    error InvalidAbsence();
    error InvalidEvidence();

    event FeeHoldImposed(bytes32 indexed caseId, bytes32 indexed formId, address indexed reviewer, uint256 evidenceId);
    event FeeHoldLifted(bytes32 indexed caseId, bytes32 indexed formId, address indexed reviewer, uint256 evidenceId);
    event OneToOneCompletionRecorded(bytes32 indexed formId, address indexed actor, uint256 evidenceId);
    event OneToOneAbsenceRecorded(bytes32 indexed formId, uint64 occurredAt, AbsenceReason reason, uint256 evidenceId);
    event TutorWageAllocationAgreed(bytes32 indexed lessonId, bytes32 indexed commitment, address indexed signer);

    SparkV15Booking public immutable BOOKING;
    SparkV15Payments public immutable PAYMENTS;
    ISparkV15SettlementActors public immutable SETTLEMENT;
    SparkV15SettlementOccurrences public immutable OCCURRENCES;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;

    mapping(bytes32 => uint256) public activeFeeHolds;
    mapping(bytes32 => FeeHold) private feeHolds;
    mapping(bytes32 => AbsenceRecord[]) private absences;
    mapping(bytes32 => uint256) public studentCompletion;
    mapping(bytes32 => uint256) public coordinatorCompletion;
    mapping(bytes32 => mapping(address => bool)) private wageAllocationAssents;

    constructor(SparkV15Booking booking, SparkV15Payments payments, ISparkV15SettlementActors settlement) {
        BOOKING = booking;
        PAYMENTS = payments;
        SETTLEMENT = settlement;
        EVIDENCE_REGISTRY = payments.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        OCCURRENCES = new SparkV15SettlementOccurrences(booking, payments.VERIFIER_ROLE());
    }

    function feeHoldCommitment(FeeHoldTerms calldata terms, address reviewer) public view returns (bytes32) {
        return keccak256(abi.encode(ACTION_IMPOSE_FEE_HOLD, block.chainid, address(this), terms, reviewer));
    }

    function imposeFeeHold(FeeHoldTerms calldata terms, uint256 evidenceId, bytes32 authorityId) external {
        (uint256 packageId, uint64 receivedAt) =
            _requireReviewer(terms.caseId, terms.formId, ACTION_IMPOSE_FEE_HOLD, authorityId);
        if (
            feeHolds[terms.caseId].evidenceId != 0 || terms.reviewAt < block.timestamp
                || terms.notice.referenceHash == bytes32(0) || terms.notice.sentAt < receivedAt
                || terms.notice.sentAt > block.timestamp
        ) revert InvalidFeeHold();
        _requireEvidence(evidenceId, packageId, feeHoldCommitment(terms, msg.sender));
        FeeHold storage hold = feeHolds[terms.caseId];
        hold.terms = terms;
        hold.reviewer = msg.sender;
        hold.authorityId = authorityId;
        hold.evidenceId = evidenceId;
        hold.imposedAt = uint64(block.timestamp);
        ++activeFeeHolds[terms.formId];
        emit FeeHoldImposed(terms.caseId, terms.formId, msg.sender, evidenceId);
    }

    function feeLiftCommitment(
        bytes32 caseId,
        bytes32 disposition,
        SparkV15ReviewContext.Notice calldata notice,
        address reviewer
    ) public view returns (bytes32) {
        return keccak256(
            abi.encode(
                ACTION_LIFT_FEE_HOLD,
                block.chainid,
                address(this),
                caseId,
                feeHolds[caseId].evidenceId,
                disposition,
                notice,
                reviewer
            )
        );
    }

    function liftFeeHold(
        bytes32 caseId,
        bytes32 disposition,
        SparkV15ReviewContext.Notice calldata notice,
        uint256 evidenceId,
        bytes32 authorityId
    ) external {
        FeeHold storage hold = feeHolds[caseId];
        bytes32 formId = hold.terms.formId;
        if (
            hold.imposedAt == 0 || hold.liftedAt != 0 || disposition == bytes32(0) || notice.referenceHash == bytes32(0)
                || notice.sentAt <= hold.imposedAt || notice.sentAt > block.timestamp
        ) revert InvalidFeeHold();
        (uint256 packageId,) = _requireReviewer(caseId, formId, ACTION_LIFT_FEE_HOLD, authorityId);
        _requireEvidence(evidenceId, packageId, feeLiftCommitment(caseId, disposition, notice, msg.sender));
        hold.liftedAt = uint64(block.timestamp);
        hold.liftedBy = msg.sender;
        hold.liftEvidenceId = evidenceId;
        --activeFeeHolds[formId];
        emit FeeHoldLifted(caseId, formId, msg.sender, evidenceId);
    }

    function getFeeHold(bytes32 caseId) external view returns (FeeHold memory) {
        return feeHolds[caseId];
    }

    function feeHoldEvidence(bytes32 caseId, bytes32 formId) external view returns (uint256) {
        FeeHold storage hold = feeHolds[caseId];
        return hold.terms.formId == formId && hold.liftedAt == 0 ? hold.evidenceId : 0;
    }

    function heldSeatWitness(
        bytes32 lessonId,
        bytes32 formId,
        bytes32 feeCaseId,
        bytes32 tutorPart,
        address tutorRecipient,
        uint256 packageId
    ) external view returns (bytes32) {
        if (feeCaseId != bytes32(0)) {
            FeeHold storage hold = feeHolds[feeCaseId];
            if (hold.terms.formId != formId || hold.liftedAt != 0) return bytes32(0);
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(hold.evidenceId, packageId);
            return keccak256(abi.encode(feeCaseId, hold.evidenceId));
        }
        bytes32 id = keccak256(abi.encode(lessonId, tutorPart));
        SparkV15Payments.Obligation memory wage = PAYMENTS.getObligation(id);
        if (
            wage.packageId != packageId || wage.terms.originalDebitAccount != bytes32(0)
                || wage.terms.recipient != tutorRecipient || wage.terms.amount <= wage.paid
                || !PAYMENTS.HOLDS().getStatus(id).active
        ) return bytes32(0);
        return keccak256(abi.encode(id, wage.version));
    }

    function feeConditionsPermitWage(bytes32 lessonId, bytes32 formId, bool independent, AbsenceReason absence)
        external
        view
        returns (bool)
    {
        if (absence != AbsenceReason.Unverified && getOneToOneAbsence(formId).facts.reason != absence) {
            return false;
        }
        if (activeFeeHolds[formId] != 0) return false;
        if (!independent) {
            bytes32[] memory forms = BOOKING.getLockedForms(lessonId);
            for (uint256 i; i < forms.length; ++i) {
                if (activeFeeHolds[forms[i]] != 0) return false;
            }
        }
        return true;
    }

    function fallbackClockCommitment(bytes32 lessonId, uint64 anchor, bytes32 boundaryRef)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                "spark.v1.5.settlement-clock",
                block.chainid,
                address(SETTLEMENT),
                lessonId,
                anchor,
                uint256(anchor) + 30 days,
                boundaryRef
            )
        );
    }

    function fallbackMature(bytes32 lessonId, uint64 anchor, bytes32 boundaryRef, uint256 evidenceId)
        external
        view
        returns (bool)
    {
        uint256 expiry = uint256(anchor) + 30 days;
        if (block.timestamp < expiry) return false;
        if (evidenceId == 0) return block.timestamp > expiry;
        if (boundaryRef == bytes32(0)) return false;
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, BOOKING.getLesson(lessonId).packageId);
        AVACoreTypes.EvidenceRecord memory evidence = EVIDENCE_REGISTRY.getEvidence(evidenceId);
        if (
            evidence.commitment != fallbackClockCommitment(lessonId, anchor, boundaryRef)
                || evidence.registeredAt < expiry
        ) {
            revert InvalidEvidence();
        }
        return true;
    }

    function agreedAbsenceCommitment(
        bytes32 lessonId,
        bytes32 placeId,
        bytes32 documentsRef,
        bytes32 changeTermsRef,
        uint128 fee,
        uint128 tutorPay
    ) external view returns (bytes32) {
        return keccak256(
            abi.encode(
                "spark.v1.5.agreed-absence",
                block.chainid,
                address(SETTLEMENT),
                lessonId,
                placeId,
                documentsRef,
                changeTermsRef,
                fee,
                tutorPay
            )
        );
    }

    function wageAllocationCommitment(
        bytes32 lessonId,
        bytes32 payTerms,
        uint128 gross,
        uint128 net,
        uint128[] calldata seatAmounts
    ) public view returns (bytes32) {
        return keccak256(
            abi.encode(
                "spark.v1.5.tutor-wage-allocation",
                block.chainid,
                address(this),
                lessonId,
                payTerms,
                gross,
                net,
                seatAmounts
            )
        );
    }

    function agreeTutorWageAllocation(bytes32 lessonId, bytes32 commitment) external {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        address tutor = BOOKING.getEffectiveArrangement(lessonId, teaching.startedAt).tutor;
        if (
            commitment == bytes32(0) || (msg.sender != tutor && msg.sender != lesson.terms.provider)
                || teaching.endedAt == 0
        ) revert InvalidCompletion();
        wageAllocationAssents[commitment][msg.sender] = true;
        emit TutorWageAllocationAgreed(lessonId, commitment, msg.sender);
    }

    function wageAllocationAgreed(bytes32 lessonId, uint128 gross, uint128 net, uint128[] calldata seatAmounts)
        external
        view
        returns (bool)
    {
        SparkV15Booking.LessonTerms memory terms = BOOKING.getLesson(lessonId).terms;
        ISparkV15BookingChanges.Arrangement memory effective =
            BOOKING.getEffectiveArrangement(lessonId, BOOKING.getTeaching(lessonId).startedAt);
        bytes32 commitment = wageAllocationCommitment(lessonId, effective.tutorPayTermsRef, gross, net, seatAmounts);
        return wageAllocationAssents[commitment][terms.provider] && wageAllocationAssents[commitment][effective.tutor];
    }

    function completionCommitment(bytes32 formId, bytes32 reportRef, address actor) public view returns (bytes32) {
        bytes32 lessonId = BOOKING.getForm(formId).lessonId;
        return keccak256(
            abi.encode(
                ACTION_CONFIRM_ONE_TO_ONE,
                block.chainid,
                address(this),
                formId,
                BOOKING.getTeaching(lessonId).endEvidenceId,
                actor,
                reportRef
            )
        );
    }

    function recordOneToOneCompletion(bytes32 formId, bytes32 reportRef, uint256 evidenceId) external {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        if (
            form.confirmation.confirmedAt == 0 || lesson.terms.rosterRef != bytes32(0) || reportRef == bytes32(0)
                || BOOKING.getTeaching(form.lessonId).endEvidenceId == 0
                || SETTLEMENT.hasAdoptedOneToOneCompletion(form.lessonId, formId)
        ) revert InvalidCompletion();
        if (msg.sender == form.terms.student) {
            if (studentCompletion[formId] != 0) revert InvalidCompletion();
            studentCompletion[formId] = evidenceId;
        } else {
            if (msg.sender != lesson.terms.coordinator || coordinatorCompletion[formId] != 0) {
                revert InvalidCompletion();
            }
            _requireAuthority(BOOKING.COORDINATOR_ROLE(), ACTION_CONFIRM_ONE_TO_ONE);
            coordinatorCompletion[formId] = evidenceId;
        }
        _requireEvidence(evidenceId, lesson.packageId, completionCommitment(formId, reportRef, msg.sender));
        emit OneToOneCompletionRecorded(formId, msg.sender, evidenceId);
    }

    function absenceCommitment(AbsenceFacts calldata facts, address verifier) public view returns (bytes32) {
        bytes32 lessonId = BOOKING.getForm(facts.formId).lessonId;
        bytes32 changeId = BOOKING.getEffectiveArrangement(lessonId, facts.occurredAt).changeId;
        return _absenceCommitment(facts, verifier, changeId);
    }

    function _absenceCommitment(AbsenceFacts calldata facts, address verifier, bytes32 changeId)
        private
        view
        returns (bytes32)
    {
        bytes32 commitment =
            keccak256(abi.encode(ACTION_VERIFY_ONE_TO_ONE_ABSENCE, block.chainid, address(this), facts, verifier));
        return changeId == bytes32(0) ? commitment : keccak256(abi.encode(commitment, changeId));
    }

    function absenceReasonOutcome(bytes32 formId, AbsenceReason reason) public pure returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.one-to-one-absence-reason"), formId, reason));
    }

    /// @dev The source verifies available teaching, an unready and absent student, and nonoccurrence solely due
    /// to the absence. It identifies any recorded decision required for the reason.
    function recordOneToOneAbsence(AbsenceFacts calldata facts, uint256 evidenceId) external {
        _requireAuthority(PAYMENTS.VERIFIER_ROLE(), ACTION_VERIFY_ONE_TO_ONE_ABSENCE);
        SparkV15Booking.Form memory form = BOOKING.getForm(facts.formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        if (
            lesson.terms.rosterRef != bytes32(0) || form.confirmation.confirmedAt == 0
                || form.confirmation.confirmedAt >= facts.occurredAt || lesson.terms.startsAt > facts.occurredAt
                || block.timestamp < lesson.terms.endsAt || facts.occurredAt > lesson.terms.endsAt
                || BOOKING.getTeaching(form.lessonId).startedAt != 0
                || BOOKING.isCancelledAt(facts.formId, uint64(block.timestamp)) || facts.factsRef == bytes32(0)
                || facts.reason == AbsenceReason.Unverified || msg.sender == lesson.terms.coordinator
                || msg.sender == lesson.terms.tutor || msg.sender == lesson.terms.provider || _isSeatParty(form.terms)
        ) revert InvalidAbsence();
        AbsenceRecord[] storage history = absences[facts.formId];
        if (history.length != 0) _requireAbsenceRevision(facts, history[history.length - 1]);
        (bytes32 changeId, address tutor) =
            OCCURRENCES.requireAbsenceArrangement(form.lessonId, facts.formId, facts.occurredAt, lesson.packageId);
        if (msg.sender == tutor) revert InvalidAbsence();
        _requireEvidence(evidenceId, lesson.packageId, _absenceCommitment(facts, msg.sender, changeId));
        _requireReason(facts, form, lesson.packageId);
        history.push(AbsenceRecord(facts, evidenceId, msg.sender, uint64(block.timestamp)));
        emit OneToOneAbsenceRecorded(facts.formId, facts.occurredAt, facts.reason, evidenceId);
    }

    function getOneToOneAbsence(bytes32 formId) public view returns (AbsenceRecord memory record) {
        AbsenceRecord[] storage history = absences[formId];
        if (history.length != 0) {
            record = history[history.length - 1];
            SparkV15Booking.Form memory form = BOOKING.getForm(formId);
            uint256 packageId = BOOKING.getLesson(form.lessonId).packageId;
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(record.evidenceId, packageId);
            _requireReason(record.facts, form, packageId);
        }
    }

    function getOneToOneAbsenceRecord(bytes32 formId, uint256 index) external view returns (AbsenceRecord memory) {
        return absences[formId][index];
    }

    function absenceForSettlement(bytes32 formId)
        external
        view
        returns (uint64 occurredAt, uint8 reason, uint256 evidenceId)
    {
        AbsenceRecord memory record = getOneToOneAbsence(formId);
        return (record.facts.occurredAt, uint8(record.facts.reason), record.evidenceId);
    }

    function _requireAbsenceRevision(AbsenceFacts calldata facts, AbsenceRecord storage previous) private view {
        SparkV15ReviewCases review = SparkV15ReviewCases(address(PAYMENTS.reviewCases()));
        if (
            address(review) == address(0) || facts.reasonCaseId == bytes32(0)
                || previous.facts.occurredAt != facts.occurredAt || previous.facts.reason == facts.reason
        ) revert InvalidAbsence();
        SparkV15ReviewCases.AdoptedDisposition memory adopted = review.getAdoptedDisposition(facts.reasonCaseId);
        if (
            adopted.adoptedAt < previous.verifiedAt
                || adopted.originalOutcome != absenceReasonOutcome(facts.formId, previous.facts.reason)
                || adopted.outcome != absenceReasonOutcome(facts.formId, facts.reason)
        ) revert InvalidAbsence();
    }

    function retainedPayment(SparkV15Payments.PaymentTerms calldata expected, uint256 packageId)
        external
        view
        returns (bytes32 id, uint256 alreadyReceived)
    {
        return SETTLEMENT.retainedPayment(expected, packageId);
    }

    function _requireReviewer(bytes32 caseId, bytes32 formId, bytes32 action, bytes32 authorityId)
        private
        view
        returns (uint256, uint64)
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        if (_requireAuthority(PAYMENTS.VERIFIER_ROLE(), action) != authorityId) {
            revert InvalidFeeHold();
        }
        SparkV15ReviewCases review = SparkV15ReviewCases(address(PAYMENTS.reviewCases()));
        if (address(review) == address(0)) revert InvalidFeeHold();
        SparkV15ReviewContext.ConcernRecord memory concern = review.INTAKE().getConcern(caseId);
        SparkV15ReviewContext.PublishedContacts memory publication =
            review.INTAKE().getPublishedContacts(concern.termsId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        if (
            concern.lessonId != form.lessonId || concern.obligationId != bytes32(0)
                || concern.intake.subject != SparkV15ReviewContext.ConcernSubject.CustomerFee
                || concern.intake.subjectRef != form.terms.placeId || publication.terms.governingForm != formId
                || publication.packageId != lesson.packageId || publication.terms.provider != lesson.terms.provider
                || publication.terms.coordinator != lesson.terms.coordinator || concern.intake.evidenceId == 0
                || msg.sender == lesson.terms.coordinator || SETTLEMENT.isSettlementActor(form.lessonId, msg.sender)
                || msg.sender == lesson.terms.provider || msg.sender == lesson.terms.tutor || _isSeatParty(form.terms)
                || msg.sender == BOOKING.getEffectiveArrangement(form.lessonId, uint64(block.timestamp)).tutor
                || ((concern.appointmentRequiredAt != 0 || msg.sender != publication.terms.namedReviewer)
                    && !review.isAppointedForCase(
                        caseId,
                        SparkV15ReviewContext.AppointmentPurpose.IndependentReview,
                        msg.sender,
                        uint64(block.timestamp),
                        concern.appointmentRequiredAt != 0
                    ))
        ) revert InvalidFeeHold();
        if (action == ACTION_IMPOSE_FEE_HOLD) {
            if (form.confirmation.confirmedAt == 0) OCCURRENCES.requireUnconfirmedProviderStartForm(formId);
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(concern.intake.evidenceId, publication.packageId);
        }
        review.requireIndependentReviewer(caseId, msg.sender);
        return (publication.packageId, concern.intake.receivedAt);
    }

    function _requireReason(AbsenceFacts memory facts, SparkV15Booking.Form memory form, uint256 packageId)
        private
        view
    {
        bytes32 caseId = facts.reasonCaseId;
        if (caseId == bytes32(0)) return;
        SparkV15ReviewCases review = SparkV15ReviewCases(address(PAYMENTS.reviewCases()));
        if (address(review) == address(0)) revert InvalidAbsence();
        SparkV15ReviewContext.ConcernRecord memory concern = review.INTAKE().getConcern(caseId);
        SparkV15ReviewContext.PublishedContacts memory publication =
            review.INTAKE().getPublishedContacts(concern.termsId);
        SparkV15ReviewContext.CaseRecord memory outcome = review.getCase(caseId);
        if (
            concern.lessonId != form.lessonId
                || concern.intake.subject != SparkV15ReviewContext.ConcernSubject.StudentAttendance
                || concern.intake.subjectRef != form.terms.placeId || publication.terms.governingForm != facts.formId
                || publication.packageId != packageId
                || outcome.initial.input.issue != SparkV15ReviewContext.DisputedFinding.AbsenceReason
        ) revert InvalidAbsence();
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(outcome.initial.evidenceId, packageId);
        bytes32 expected = absenceReasonOutcome(facts.formId, facts.reason);
        if (outcome.review.input.disposition == SparkV15ReviewContext.ReviewDisposition.CorrectionRequired) {
            SparkV15ReviewCases.AdoptedDisposition memory adopted = review.getAdoptedDisposition(caseId);
            if (adopted.outcome != expected || adopted.adoptedAt == 0) revert InvalidAbsence();
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(adopted.adoptionEvidenceId, packageId);
        } else if (outcome.review.input.disposition == SparkV15ReviewContext.ReviewDisposition.Affirmed) {
            if (outcome.review.input.outcome != expected) revert InvalidAbsence();
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(outcome.review.evidenceId, packageId);
        } else if (
            outcome.review.decidedAt != 0 || concern.reviewRequestedAt != 0 || outcome.initial.input.outcome != expected
        ) {
            revert InvalidAbsence();
        }
    }

    function _isSeatParty(SparkV15Booking.PlaceTerms memory terms) private view returns (bool) {
        return msg.sender == terms.customer || msg.sender == terms.payer || msg.sender == terms.student
            || msg.sender == terms.customerRepresentative;
    }

    function _requireAuthority(bytes32 role, bytes32 action) private view returns (bytes32) {
        return EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(msg.sender, SparkV15.APP_ID, role, action);
    }

    function _requireEvidence(uint256 evidenceId, uint256 packageId, bytes32 commitment) private view {
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        if (EVIDENCE_REGISTRY.getEvidenceReference(evidenceId).commitment != commitment) revert InvalidEvidence();
    }
}
