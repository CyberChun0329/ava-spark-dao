// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {ISparkV15BookingChanges, SparkV15Booking, SparkV15BookingOpening} from "./SparkV15Booking.sol";
import {SparkV15CustomerRedress, SparkV15LessonRemedies} from "./SparkV15LessonRemedies.sol";
import {SparkV15Settlement} from "./SparkV15Settlement.sol";

interface ISparkV15SettlementOccurrenceRecords {
    function SETTLEMENT() external view returns (address);
    function ACTION_CONFIRM_ONE_TO_ONE() external view returns (bytes32);
    function studentCompletion(bytes32 formId) external view returns (uint256);
    function coordinatorCompletion(bytes32 formId) external view returns (uint256);
    function absenceForSettlement(bytes32 formId)
        external
        view
        returns (uint64 occurredAt, uint8 reason, uint256 evidenceId);
}

interface ISparkV15SettlementChangeNotices {
    function getAgreement(bytes32 changeId)
        external
        view
        returns (
            uint64 contactedAt,
            uint64 agreedAt,
            uint64 effectiveAt,
            uint64 finalizedAt,
            uint256 proposalEvidenceId,
            uint256 fundingEvidenceId
        );
    function tutorChangeNotices(bytes32 changeId)
        external
        view
        returns (uint64 deliveredAt, uint256 evidenceId, address sender);
    function getStudentNoticeEvidence(bytes32 changeId, bytes32 formId)
        external
        view
        returns (uint256 scheduleEvidenceId, uint256 replacementEvidenceId);
    function usesInitialStudentNotice(bytes32 changeId) external view returns (bool);
}

/// @notice Reads the accepted booking, arrangement, occurrence and reporting evidence for assessment.
contract SparkV15SettlementOccurrences {
    struct LocalOneToOneRecords {
        bytes32 formId;
        bytes32 studentReportRef;
        bytes32 coordinatorReportRef;
        uint64 validThrough;
        bytes32 studentR;
        bytes32 studentVS;
        bytes32 coordinatorR;
        bytes32 coordinatorVS;
    }

    struct SignedAttendance {
        bytes32 reportRef;
        uint64 validThrough;
        bytes32 r;
        bytes32 vs;
    }

    struct Basis {
        uint64 startedAt;
        uint64 endedAt;
        uint64 deadlineAnchor;
        bool tutorCompleted;
        bool allOneToOneConfirmed;
        bytes32 evidenceRoot;
        ISparkV15BookingChanges.Arrangement arrangement;
        uint64 legalDeadline;
        bool legalDeadlineExact;
        uint256 legalDeadlineEvidenceId;
    }

    struct TutorLegalScope {
        bytes32 lessonId;
        bytes32 arrangementId;
        address tutor;
        bytes32 tutorAgreementRef;
        bytes32 tutorPayTermsRef;
        uint64 agreedStartAnchor;
    }

    struct StatutoryTutorDeadline {
        TutorLegalScope scope;
        uint64 deadline;
        bool deadlineExact;
        bytes32 jurisdictionRef;
        bytes32 ruleRef;
        bytes32 applicabilityRef;
    }

    struct VerifiedStatutoryTutorDeadline {
        StatutoryTutorDeadline terms;
        uint256 evidenceId;
        address verifier;
        bytes32 authorityId;
        uint64 verifiedAt;
    }

    bytes32 public constant ACTION_VERIFY_EARLIER_TUTOR_DEADLINE =
        keccak256("spark.action.verify-earlier-tutor-deadline.v1.5");
    bytes32 public constant STATUTORY_TUTOR_DEADLINE_EVIDENCE_TYPE =
        keccak256("spark.evidence.statutory-tutor-deadline.v1.5");

    bytes32 private constant DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant STUDENT_COMPLETION_TYPEHASH = keccak256(
        "StudentCompletion(bytes32 lessonId,bytes32 formId,uint64 endedAt,uint256 endEvidenceId,bytes32 reportRef,uint64 validThrough)"
    );
    bytes32 private constant COORDINATOR_COMPLETION_TYPEHASH = keccak256(
        "CoordinatorCompletionAndProposal(bytes32 lessonId,bytes32 formId,uint64 endedAt,uint256 endEvidenceId,bytes32 reportRef,uint64 validThrough,bytes32 proposalCommitment,bytes32 authorityId)"
    );
    bytes32 private constant STUDENT_ATTENDANCE_TYPEHASH = keccak256(
        "StudentAttendance(bytes32 lessonId,bytes32 formId,uint64 endedAt,uint256 endEvidenceId,bool attended,bytes32 reportRef,uint64 validThrough)"
    );
    uint256 private constant SIGNATURE_S_MASK = type(uint256).max >> 1;
    uint256 private constant MAX_CANONICAL_S = 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0;

    error OrdinaryGroupConditionsNotMet();
    error InvalidLocalOneToOneRecords();
    error ApplicableArrangementChanged();
    error InvalidAbsence();
    error InvalidStatutoryTutorDeadline();

    event EarlierTutorDeadlineVerified(
        bytes32 indexed lessonId,
        bytes32 indexed arrangementId,
        address indexed tutor,
        uint64 deadline,
        uint256 evidenceId
    );

    SparkV15Booking private immutable BOOKING;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;
    ISparkV15SettlementOccurrenceRecords private immutable RECORDS;
    bytes32 private immutable VERIFIER_ROLE;
    mapping(bytes32 => VerifiedStatutoryTutorDeadline) private tutorDeadlines;

    constructor(SparkV15Booking booking, bytes32 verifierRole) {
        BOOKING = booking;
        EVIDENCE_REGISTRY = booking.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        RECORDS = ISparkV15SettlementOccurrenceRecords(msg.sender);
        VERIFIER_ROLE = verifierRole;
    }

    function earlierTutorDeadlineCommitment(StatutoryTutorDeadline calldata terms, address verifier)
        public
        view
        returns (bytes32)
    {
        return
            keccak256(abi.encode(ACTION_VERIFY_EARLIER_TUTOR_DEADLINE, block.chainid, address(this), terms, verifier));
    }

    /// @notice Verify an earlier statutory cutoff for the named tutor and signed pay terms.
    /// @dev The independent source attests the applicable rule and its computation for this exact scope.
    function verifyEarlierTutorDeadline(StatutoryTutorDeadline calldata terms, uint256 evidenceId, bytes32 authorityId)
        external
    {
        EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, VERIFIER_ROLE, ACTION_VERIFY_EARLIER_TUTOR_DEADLINE, authorityId
            );
        TutorLegalScope calldata scope = terms.scope;
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(scope.lessonId);
        uint64 nowAt = uint64(block.timestamp);
        uint64 actualStart = BOOKING.getTeaching(scope.lessonId).startedAt;
        ISparkV15BookingChanges.Arrangement memory arrangement =
            BOOKING.getEffectiveArrangement(scope.lessonId, actualStart == 0 ? nowAt : actualStart);
        bytes32 key = keccak256(abi.encode(scope));
        if (
            lesson.packageId == 0 || arrangement.changeId != scope.arrangementId || arrangement.tutor != scope.tutor
                || arrangement.tutorAgreementRef != scope.tutorAgreementRef
                || arrangement.tutorPayTermsRef != scope.tutorPayTermsRef
                || BOOKING.getLessonDeadlineAnchor(scope.lessonId, nowAt) != scope.agreedStartAnchor
                || terms.deadline == 0 || terms.deadline >= uint256(scope.agreedStartAnchor) + 30 days
                || terms.jurisdictionRef == bytes32(0) || terms.ruleRef == bytes32(0)
                || terms.applicabilityRef == bytes32(0) || tutorDeadlines[key].evidenceId != 0
                || _interestedInTutorDeadline(msg.sender, lesson.terms, scope.tutor)
        ) revert InvalidStatutoryTutorDeadline();
        _requireAvailable(evidenceId, lesson.packageId);
        AVACoreTypes.EvidenceRecord memory proof = EVIDENCE_REGISTRY.getEvidence(evidenceId);
        if (
            proof.commitment != earlierTutorDeadlineCommitment(terms, msg.sender)
                || proof.evidenceTypeHash != STATUTORY_TUTOR_DEADLINE_EVIDENCE_TYPE || proof.registeredBy == msg.sender
                || _interestedInTutorDeadline(proof.registeredBy, lesson.terms, scope.tutor)
        ) revert InvalidStatutoryTutorDeadline();
        tutorDeadlines[key] = VerifiedStatutoryTutorDeadline(terms, evidenceId, msg.sender, authorityId, nowAt);
        emit EarlierTutorDeadlineVerified(scope.lessonId, scope.arrangementId, scope.tutor, terms.deadline, evidenceId);
    }

    function getEarlierTutorDeadline(TutorLegalScope calldata scope)
        external
        view
        returns (VerifiedStatutoryTutorDeadline memory)
    {
        return tutorDeadlines[keccak256(abi.encode(scope))];
    }

    /// @notice Read the late-verified opening basis for the normal settlement of the original lesson.
    function hasUsableLateOpeningNotices(bytes32 lessonId) public view returns (bool) {
        SparkV15BookingOpening opening = BOOKING.OPENING();
        return address(opening) != address(0) && opening.TEACHING_END().hasUsableLateOpeningNotices(lessonId);
    }

    function readBasis(bytes32 lessonId, bytes32 firstForm, bytes32 changeId, bool group, uint8 absenceReason)
        external
        view
        returns (Basis memory basis)
    {
        uint64 nowAt = uint64(block.timestamp);
        if (BOOKING.getEffectiveArrangement(lessonId, nowAt).changeId != changeId) {
            revert ApplicableArrangementChanged();
        }
        basis.deadlineAnchor = BOOKING.getLessonDeadlineAnchor(lessonId, nowAt);
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        uint256 packageId = BOOKING.getLesson(lessonId).packageId;
        if (absenceReason != 0) {
            (uint64 occurredAt, uint8 reason, uint256 evidenceId) = RECORDS.absenceForSettlement(firstForm);
            if (teaching.startedAt != 0 || evidenceId == 0 || reason != absenceReason) {
                revert OrdinaryGroupConditionsNotMet();
            }
            basis.startedAt = occurredAt;
            basis.endedAt = occurredAt;
            basis.arrangement = BOOKING.getEffectiveArrangement(lessonId, occurredAt);
            if (basis.arrangement.changeId != changeId) revert ApplicableArrangementChanged();
            bytes32 absenceArrangement = _absenceArrangementEvidence(lessonId, changeId, occurredAt, packageId);
            basis.evidenceRoot = keccak256(abi.encode(evidenceId, occurredAt, reason, absenceArrangement));
            return basis;
        }
        if (
            teaching.endedAt == 0
                || (teaching.startPermission != SparkV15Booking.StartPermission.Permitted
                    && !hasUsableLateOpeningNotices(lessonId))
        ) {
            revert OrdinaryGroupConditionsNotMet();
        }
        basis.arrangement = BOOKING.getEffectiveArrangement(lessonId, teaching.startedAt);
        if (basis.arrangement.changeId != changeId) revert ApplicableArrangementChanged();
        _readTutorDeadline(lessonId, packageId, basis);
        basis.startedAt = teaching.startedAt;
        basis.endedAt = teaching.endedAt;
        BOOKING.OPENING().requireTeachingStartEvidence(lessonId, teaching.startEvidenceId, packageId);
        BOOKING.OPENING().requireTeachingEndEvidence(lessonId, teaching.endEvidenceId, packageId);
        bytes32 arrangementEvidence = _arrangementEvidence(lessonId, changeId, teaching.startedAt, packageId);
        uint256 deliveryId = _readTutorDelivery(lessonId, packageId, basis);
        uint256 rosterId;
        uint256 studentId;
        uint256 coordinatorId;
        if (group) {
            SparkV15Booking.RosterLock memory roster = BOOKING.getRosterLock(lessonId);
            if (roster.lockedAt > basis.arrangement.startsAt) revert OrdinaryGroupConditionsNotMet();
            rosterId = roster.evidenceId;
            _requireAvailable(rosterId, packageId);
        } else {
            studentId = RECORDS.studentCompletion(firstForm);
            coordinatorId = RECORDS.coordinatorCompletion(firstForm);
            if (studentId != 0) _requireAvailable(studentId, packageId);
            if (coordinatorId != 0) _requireAvailable(coordinatorId, packageId);
            basis.allOneToOneConfirmed = basis.tutorCompleted && studentId != 0 && coordinatorId != 0;
        }
        basis.evidenceRoot = keccak256(
            abi.encode(
                teaching.startEvidenceId,
                teaching.endEvidenceId,
                deliveryId,
                arrangementEvidence,
                rosterId,
                studentId,
                coordinatorId,
                basis.legalDeadlineEvidenceId
            )
        );
    }

    function requireAbsenceArrangement(bytes32 lessonId, bytes32 formId, uint64 occurredAt, uint256 packageId)
        external
        view
        returns (bytes32 changeId, address tutor)
    {
        ISparkV15BookingChanges.Arrangement memory arrangement =
            BOOKING.getEffectiveArrangement(lessonId, uint64(block.timestamp));
        changeId = arrangement.changeId;
        studentNoticeEvidence(formId, changeId, occurredAt, packageId);
        _absenceArrangementEvidence(lessonId, changeId, occurredAt, packageId);
        if (
            BOOKING.OPENING().startPermission(lessonId, false, occurredAt, new address[](0))
                != SparkV15Booking.StartPermission.Permitted
        ) revert InvalidAbsence();
        return (changeId, arrangement.tutor);
    }

    /// @notice Encode the verified customer service value and tutor amount in GroupAssessment.verificationRef.
    function encodeProviderStartedEarlyAmounts(uint128 serviceValue, uint128 tutorAmount)
        external
        pure
        returns (bytes32)
    {
        return bytes32((uint256(serviceValue) << 128) | uint256(tutorAmount));
    }

    /// @notice Read the actual unpermitted occurrence under the original arrangement, using its existing evidence.
    function readProviderStartBasis(bytes32 lessonId) external view returns (Basis memory basis) {
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        if (teaching.endedAt == 0) revert OrdinaryGroupConditionsNotMet();
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        uint256 packageId = lesson.packageId;
        basis.arrangement = _requireOriginalProviderStart(lessonId, teaching, packageId);

        basis.startedAt = teaching.startedAt;
        basis.endedAt = teaching.endedAt;
        basis.deadlineAnchor = BOOKING.getLessonDeadlineAnchor(lessonId, uint64(block.timestamp));
        _readTutorDeadline(lessonId, packageId, basis);
        BOOKING.OPENING().requireTeachingEndEvidence(lessonId, teaching.endEvidenceId, packageId);
        uint256 deliveryId = _readTutorDelivery(lessonId, packageId, basis);
        basis.evidenceRoot = keccak256(
            abi.encode(
                teaching.startEvidenceId,
                teaching.endEvidenceId,
                teaching.startedAt,
                teaching.endedAt,
                teaching.unmetConditionRef,
                deliveryId,
                basis.legalDeadlineEvidenceId
            )
        );

        bytes32[] memory plan = BOOKING.getPlannedForms(lessonId);
        if (plan.length == 1) {
            SparkV15Booking.Form memory form = BOOKING.getForm(plan[0]);
            if (form.confirmation.confirmedAt == 0) {
                bytes32 agreement = _unconfirmedProviderStartAgreement(plan[0], form, lesson, teaching.startedAt);
                basis.evidenceRoot = keccak256(abi.encode(basis.evidenceRoot, agreement));
            }
        }
    }

    /// @notice Verify the exact effective form when imposing a fee hold for an unconfirmed provider start.
    function requireUnconfirmedProviderStartForm(bytes32 formId) external view {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        bytes32 lessonId = form.lessonId;
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        bytes32[] memory plan = BOOKING.getPlannedForms(lessonId);
        if (plan.length != 1 || plan[0] != formId) revert OrdinaryGroupConditionsNotMet();
        _requireOriginalProviderStart(lessonId, teaching, lesson.packageId);
        _unconfirmedProviderStartAgreement(formId, form, lesson, teaching.startedAt);
    }

    function _requireOriginalProviderStart(
        bytes32 lessonId,
        SparkV15Booking.Teaching memory teaching,
        uint256 packageId
    ) private view returns (ISparkV15BookingChanges.Arrangement memory arrangement) {
        if (
            teaching.startPermission != SparkV15Booking.StartPermission.RequirementsNotMet
                || !teaching.providerWentAhead || teaching.unmetConditionRef == bytes32(0)
        ) revert OrdinaryGroupConditionsNotMet();
        arrangement = BOOKING.getEffectiveArrangement(lessonId, teaching.startedAt);
        if (
            arrangement.changeId != bytes32(0)
                || BOOKING.getEffectiveArrangement(lessonId, uint64(block.timestamp)).changeId != bytes32(0)
        ) revert ApplicableArrangementChanged();
        BOOKING.OPENING().requireTeachingStartEvidence(lessonId, teaching.startEvidenceId, packageId);
    }

    function _unconfirmedProviderStartAgreement(
        bytes32 formId,
        SparkV15Booking.Form memory form,
        SparkV15Booking.Lesson memory lesson,
        uint64 startedAt
    ) private view returns (bytes32) {
        SparkV15Booking.PlaceTerms memory place = form.terms;
        if (
            lesson.terms.rosterRef != bytes32(0) || lesson.terms.materialsTermsRef != bytes32(0)
                || form.confirmation.confirmedAt != 0 || form.confirmation.debitedUnits != 0
                || place.customerRepresentative != address(0) || place.payableFee == 0
                || BOOKING.currentForm(form.lessonId, place.placeId) != formId
                || BOOKING.isCancelledAt(formId, startedAt)
        ) revert OrdinaryGroupConditionsNotMet();

        address[4] memory actors = [lesson.terms.provider, lesson.terms.tutor, place.customer, place.payer];
        uint64[4] memory acceptedAt;
        uint256 count = place.payer == place.customer ? 3 : 4;
        for (uint256 role; role < count; ++role) {
            (address signer, uint64 time) = BOOKING.acceptances(formId, SparkV15Booking.Acceptance(role));
            if (signer != actors[role] || time == 0 || time >= startedAt) revert OrdinaryGroupConditionsNotMet();
            acceptedAt[role] = time;
        }
        // Both draft adoption routes require delivery before either teaching signature. Separate publication
        // and prefunding do not establish when delivery happened relative to those signatures.
        uint64 providerSignedAt = BOOKING.teachingAgreementSignedAt(form.lessonId, actors[0]);
        uint64 tutorSignedAt = BOOKING.teachingAgreementSignedAt(form.lessonId, actors[1]);
        SparkV15BookingOpening opening = BOOKING.OPENING();
        if (
            !BOOKING.wasDraftAdopted(form.lessonId)
                || providerSignedAt == 0 || providerSignedAt > acceptedAt[1]
                || tutorSignedAt == 0 || tutorSignedAt > acceptedAt[1]
                || !opening.hasUsableTermsProvision(formId, actors[1], lesson.packageId)
                || !opening.hasUsableTermsProvision(formId, actors[2], lesson.packageId)
        ) revert OrdinaryGroupConditionsNotMet();
        return keccak256(abi.encode(formId, acceptedAt, providerSignedAt, tutorSignedAt, lesson.prefunding.evidenceId));
    }

    function _readTutorDelivery(bytes32 lessonId, uint256 packageId, Basis memory basis)
        private
        view
        returns (uint256 evidenceId)
    {
        SparkV15Booking.TutorDelivery memory delivery = BOOKING.getTutorDelivery(lessonId);
        basis.tutorCompleted = delivery.completed;
        evidenceId = delivery.evidenceId;
        if (evidenceId != 0) {
            BOOKING.OPENING().SERVICE_REPORTS().requireUsableTutorDeliveryEvidence(lessonId, evidenceId, packageId);
        }
    }

    /// @notice Verify two completion statements prepared for first adoption and the coordinator's exact proposal.
    function requireLocalOneToOneRecords(
        bytes32 lessonId,
        bytes32 proposalCommitment,
        LocalOneToOneRecords calldata records
    ) external view returns (bytes32 completionRoot, address coordinator, bytes32 authorityId) {
        SparkV15Booking.Form memory form = BOOKING.getForm(records.formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        if (
            form.lessonId != lessonId || form.confirmation.confirmedAt == 0 || lesson.terms.rosterRef != bytes32(0)
                || lesson.terms.materialsTermsRef != bytes32(0) || form.terms.materialsBundleRef != bytes32(0)
                || teaching.endedAt == 0 || teaching.endEvidenceId == 0 || block.timestamp > records.validThrough
                || records.studentReportRef == bytes32(0) || records.coordinatorReportRef == bytes32(0)
                || RECORDS.studentCompletion(records.formId) != 0 || RECORDS.coordinatorCompletion(records.formId) != 0
        ) revert InvalidLocalOneToOneRecords();

        coordinator = lesson.terms.coordinator;
        bytes32 coordinatorRole = BOOKING.COORDINATOR_ROLE();
        authorityId = EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                coordinator, SparkV15.APP_ID, coordinatorRole, RECORDS.ACTION_CONFIRM_ONE_TO_ONE()
            );
        SparkV15Settlement settlement = SparkV15Settlement(RECORDS.SETTLEMENT());
        EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                coordinator, SparkV15.APP_ID, coordinatorRole, settlement.ACTION_PROPOSE_GROUP_SETTLEMENT(), authorityId
            );
        bytes32 domain = _localRecordsDomain(address(settlement));
        bytes32 studentMessage = keccak256(
            abi.encode(
                STUDENT_COMPLETION_TYPEHASH,
                lessonId,
                records.formId,
                teaching.endedAt,
                teaching.endEvidenceId,
                records.studentReportRef,
                records.validThrough
            )
        );
        bytes32 coordinatorMessage = keccak256(
            abi.encode(
                COORDINATOR_COMPLETION_TYPEHASH,
                lessonId,
                records.formId,
                teaching.endedAt,
                teaching.endEvidenceId,
                records.coordinatorReportRef,
                records.validThrough,
                proposalCommitment,
                authorityId
            )
        );
        if (
            _recover(domain, studentMessage, records.studentR, records.studentVS) != form.terms.student
                || _recover(domain, coordinatorMessage, records.coordinatorR, records.coordinatorVS) != coordinator
        ) revert InvalidLocalOneToOneRecords();
        completionRoot = keccak256(abi.encode(studentMessage, coordinatorMessage));
    }

    /// @notice Verify the student's positive attendance for first use in independent settlement.
    function requireLocalAttendance(bytes32 lessonId, bytes32 formId, SignedAttendance calldata signedAttendance)
        external
        view
        returns (bytes32 message)
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        if (
            form.lessonId != lessonId || form.confirmation.confirmedAt == 0 || teaching.endedAt == 0
                || teaching.endEvidenceId == 0 || BOOKING.getAttendance(formId).reportedAt != 0
                || signedAttendance.reportRef == bytes32(0) || block.timestamp > signedAttendance.validThrough
        ) revert InvalidLocalOneToOneRecords();
        message = keccak256(
            abi.encode(
                STUDENT_ATTENDANCE_TYPEHASH,
                lessonId,
                formId,
                teaching.endedAt,
                teaching.endEvidenceId,
                true,
                signedAttendance.reportRef,
                signedAttendance.validThrough
            )
        );
        if (
            _recover(_localRecordsDomain(RECORDS.SETTLEMENT()), message, signedAttendance.r, signedAttendance.vs)
                != form.terms.student
        ) revert InvalidLocalOneToOneRecords();
    }

    function _localRecordsDomain(address settlement) private view returns (bytes32) {
        return keccak256(
            abi.encode(
                DOMAIN_TYPEHASH,
                keccak256("Spark DAO One-to-One Settlement Records"),
                keccak256("1"),
                block.chainid,
                settlement
            )
        );
    }

    function _recover(bytes32 domain, bytes32 message, bytes32 r, bytes32 vs) private pure returns (address signer) {
        uint256 s = uint256(vs) & SIGNATURE_S_MASK;
        if (s > MAX_CANONICAL_S) revert InvalidLocalOneToOneRecords();
        signer = ecrecover(
            keccak256(abi.encodePacked(hex"1901", domain, message)), uint8(27 + (uint256(vs) >> 255)), r, bytes32(s)
        );
        if (signer == address(0)) revert InvalidLocalOneToOneRecords();
    }

    function _readTutorDeadline(bytes32 lessonId, uint256 packageId, Basis memory basis) private view {
        ISparkV15BookingChanges.Arrangement memory arrangement = basis.arrangement;
        TutorLegalScope memory scope = TutorLegalScope(
            lessonId,
            arrangement.changeId,
            arrangement.tutor,
            arrangement.tutorAgreementRef,
            arrangement.tutorPayTermsRef,
            basis.deadlineAnchor
        );
        VerifiedStatutoryTutorDeadline storage record = tutorDeadlines[keccak256(abi.encode(scope))];
        if (record.evidenceId == 0 || !EVIDENCE_REGISTRY.isEvidenceAvailableForPackage(record.evidenceId, packageId)) {
            return;
        }
        basis.legalDeadline = record.terms.deadline;
        basis.legalDeadlineExact = record.terms.deadlineExact;
        basis.legalDeadlineEvidenceId = record.evidenceId;
    }

    function _interestedInTutorDeadline(address actor, SparkV15Booking.LessonTerms memory terms, address tutor)
        private
        pure
        returns (bool)
    {
        return actor == terms.provider || actor == terms.coordinator || actor == tutor;
    }

    function studentNoticeEvidence(bytes32 formId, bytes32 changeId, uint64 at, uint256 packageId)
        public
        view
        returns (uint256 noticeId, uint256 replacementNoticeId)
    {
        bool initial = changeId == bytes32(0);
        if (initial) {
            noticeId = BOOKING.getStudentNotice(formId).evidenceId;
        } else {
            ISparkV15BookingChanges changes = BOOKING.bookingChanges();
            if (!changes.hasStudentNotice(changeId, formId, at)) revert ApplicableArrangementChanged();
            ISparkV15SettlementChangeNotices source = ISparkV15SettlementChangeNotices(address(changes));
            (noticeId, replacementNoticeId) = source.getStudentNoticeEvidence(changeId, formId);
            if (replacementNoticeId != 0 && replacementNoticeId != noticeId) {
                _requireAvailable(replacementNoticeId, packageId);
            }
            initial = source.usesInitialStudentNotice(changeId);
        }
        if (initial) {
            BOOKING.OPENING().COURSE_NOTICES().requireStudentNoticeEvidence(formId, noticeId, packageId);
        } else {
            _requireAvailable(noticeId, packageId);
        }
    }

    function _absenceArrangementEvidence(bytes32 lessonId, bytes32 changeId, uint64 at, uint256 packageId)
        private
        view
        returns (bytes32)
    {
        if (changeId == bytes32(0)) return bytes32(_originalTutorNotice(lessonId, packageId));
        ISparkV15SettlementChangeNotices changes = ISparkV15SettlementChangeNotices(address(BOOKING.bookingChanges()));
        if (!changes.usesInitialStudentNotice(changeId)) revert ApplicableArrangementChanged();
        return _arrangementEvidence(lessonId, changeId, at, packageId);
    }

    function _arrangementEvidence(bytes32 lessonId, bytes32 changeId, uint64 at, uint256 packageId)
        private
        view
        returns (bytes32)
    {
        if (changeId == bytes32(0)) {
            return keccak256(abi.encode(_originalTutorNotice(lessonId, packageId)));
        }
        ISparkV15BookingChanges changes = BOOKING.bookingChanges();
        if (!changes.hasTutorNotice(changeId, at)) revert ApplicableArrangementChanged();
        ISparkV15SettlementChangeNotices source = ISparkV15SettlementChangeNotices(address(changes));
        (,, uint64 effectiveAt, uint64 finalizedAt, uint256 proposalEvidenceId, uint256 fundingEvidenceId) =
            source.getAgreement(changeId);
        if (effectiveAt > at || finalizedAt == 0 || finalizedAt > at) revert ApplicableArrangementChanged();
        (, uint256 tutorNoticeId,) = source.tutorChangeNotices(changeId);
        _requireAvailable(tutorNoticeId, packageId);
        _requireAvailable(proposalEvidenceId, packageId);
        if (fundingEvidenceId != 0) _requireAvailable(fundingEvidenceId, packageId);
        return
            keccak256(
                abi.encode(changeId, effectiveAt, finalizedAt, proposalEvidenceId, fundingEvidenceId, tutorNoticeId)
            );
    }

    function _originalTutorNotice(bytes32 lessonId, uint256 packageId) private view returns (uint256 evidenceId) {
        evidenceId = BOOKING.getTutorNotice(lessonId).evidenceId;
        BOOKING.OPENING().COURSE_NOTICES().requireTutorNoticeEvidence(lessonId, evidenceId, packageId);
    }

    function _requireAvailable(uint256 evidenceId, uint256 packageId) private view {
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
    }

    function requireNoExistingRedress(address policy, bytes32 formId, bool includeRefundHistory) external view {
        if (policy == address(0)) return;
        SparkV15LessonRemedies remedies = SparkV15LessonRemedies(policy);
        bytes32 caseId = remedies.placeFaultCase(formId);
        if (caseId != bytes32(0) && remedies.isOperative(caseId, remedies.latestFaultRevision(caseId))) {
            revert OrdinaryGroupConditionsNotMet();
        }
        SparkV15CustomerRedress redress = remedies.customerRedress();
        if (address(redress) == address(0)) return;
        SparkV15CustomerRedress.RedressRecord memory choice = redress.getRedress(formId);
        if (choice.directRefundAt != 0 || choice.acceptedAt != 0) revert OrdinaryGroupConditionsNotMet();
        if (includeRefundHistory) {
            (uint256 assessments,,) = redress.refundStatus(formId);
            if (assessments != 0) revert OrdinaryGroupConditionsNotMet();
        }
    }

    /// @notice Read a current provider-fault assessment and the actual refund history of the original debit.
    function readProviderRedress(address policy, bytes32 formId, uint256 packageId)
        external
        view
        returns (bytes32 basis, uint128 finalFee, bytes32 refundObligationId, uint256 received, bool missedNotice)
    {
        if (policy == address(0)) return (bytes32(0), 0, bytes32(0), 0, false);
        SparkV15LessonRemedies remedies = SparkV15LessonRemedies(policy);
        SparkV15CustomerRedress redress = remedies.customerRedress();
        bytes32 caseId = remedies.placeFaultCase(formId);
        if (caseId == bytes32(0)) {
            if (address(redress) != address(0)) (,, received) = redress.refundStatus(formId);
            return (bytes32(0), 0, bytes32(0), received, false);
        }

        uint256 revision = remedies.latestFaultRevision(caseId);
        SparkV15LessonRemedies.FaultKind kind = remedies.getFault(caseId, revision).kind;
        if (
            kind < SparkV15LessonRemedies.FaultKind.ProviderArrangementError
                || kind > SparkV15LessonRemedies.FaultKind.ProviderAdministrationError
        ) return (bytes32(0), 0, bytes32(0), 0, false);
        if (address(redress) == address(0) || !remedies.isOperative(caseId, revision)) {
            revert OrdinaryGroupConditionsNotMet();
        }
        uint256 count;
        (count,, received) = redress.refundStatus(formId);
        if (count == 0) revert OrdinaryGroupConditionsNotMet();
        SparkV15CustomerRedress.RefundAssessment memory assessment = redress.getRefund(formId, count - 1);
        if (assessment.caseId != caseId || assessment.faultRevision != revision) {
            revert OrdinaryGroupConditionsNotMet();
        }
        if (assessment.cause == SparkV15CustomerRedress.RefundBasis.OriginalRelief && assessment.finalFee != 0) {
            SparkV15CustomerRedress.RedressRecord memory choice = redress.getRedress(formId);
            if (
                choice.directRefundAt != 0 || choice.unableAt != 0
                    || (block.timestamp > redress.deliveryDeadline(formId) && redress.remedyOutstanding(formId))
            ) revert OrdinaryGroupConditionsNotMet();
        }
        _requireAvailable(assessment.evidenceId, packageId);
        // The redress route owns every refund. Link the obligation only when it covers the entire principal.
        if (assessment.principal == assessment.grossCreditRestoration) {
            refundObligationId = assessment.obligationId;
        }
        if (kind == SparkV15LessonRemedies.FaultKind.ProviderNoticeError) {
            SparkV15LessonRemedies.AffectedPlace memory place = remedies.getPlaceFinding(caseId, revision, formId);
            missedNotice = place.missedAgreedTeaching && place.teaching == SparkV15LessonRemedies.TeachingReceived.NoneDelivered;
        }
        return (assessment.basis, assessment.finalFee, refundObligationId, received, missedNotice);
    }
}
