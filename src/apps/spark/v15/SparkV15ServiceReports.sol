// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACapabilityKeys} from "@ava-protocol/contracts/src/core/AVACapabilityKeys.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {ECDSA} from "@ava-protocol/contracts/src/vendor/openzeppelin-v4.9.6/utils/cryptography/ECDSA.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {ISparkV15BookingChanges, SparkV15Booking, SparkV15BookingOpening} from "./SparkV15Booking.sol";

/// @notice Separate student and tutor reports and the availability of their supporting evidence.
contract SparkV15ServiceReports {
    bytes32 private constant DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant FEEDBACK_TYPEHASH = keccak256(
        "FullServiceFeedback(bytes32 commitment,uint256 packageId,address student,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"
    );
    bytes32 private constant FEEDBACK_EVIDENCE_TYPE = keccak256("spark.v1.5.booking.service-feedback");
    bytes32 private constant TUTOR_DELIVERY_TYPEHASH = keccak256(
        "CompletedTutorDelivery(bytes32 commitment,uint256 packageId,address tutor,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"
    );
    bytes32 private constant TUTOR_DELIVERY_EVIDENCE_TYPE = keccak256("spark.v1.5.booking.tutor-delivery");

    struct SourceProof {
        bytes32 sourceRole;
        bytes32 sourceAuthorityId;
        uint256 disclosurePolicyId;
        uint64 validThrough;
        bytes32 r;
        bytes32 vs;
    }

    struct AdoptedEvidence {
        // The subject and policy are published on adoption. Only their commitment is needed for replacement checks.
        bytes32 subjectAndPolicy;
        AVACoreTypes.EvidenceStatus invalidatedStatus;
        uint256 replacementEvidenceId;
    }

    SparkV15Booking public immutable BOOKING;
    SparkV15BookingOpening private immutable OPENING;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;

    mapping(bytes32 => SparkV15Booking.ServiceFeedback) private feedback;
    mapping(bytes32 => AdoptedEvidence) private feedbackEvidence;
    mapping(bytes32 => SparkV15Booking.TutorDelivery) private tutorDelivery;
    mapping(address => bytes32[]) private completedLessons;
    mapping(bytes32 => AdoptedEvidence) private tutorDeliveryEvidence;

    event FullServiceFeedbackAdopted(
        bytes32 indexed formId,
        uint256 indexed evidenceId,
        address indexed student,
        bytes32 receivedRef,
        address source,
        bytes32 sourceAuthorityId,
        uint256 disclosurePolicyId,
        uint64 reportedAt
    );
    event FeedbackEvidenceInvalidated(
        bytes32 indexed formId,
        uint256 indexed evidenceId,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementEvidenceId,
        bytes32 reasonHash,
        bytes32 authorityId,
        address actor
    );
    event CompletedTutorDeliveryAdopted(
        bytes32 indexed lessonId,
        uint256 indexed evidenceId,
        address indexed tutor,
        bytes32 detailsRef,
        address source,
        bytes32 sourceAuthorityId,
        uint256 disclosurePolicyId,
        uint64 reportedAt
    );
    event TutorDeliveryEvidenceInvalidated(
        bytes32 indexed lessonId,
        uint256 indexed evidenceId,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementEvidenceId,
        bytes32 reasonHash,
        bytes32 authorityId,
        address actor
    );

    constructor(SparkV15Booking booking, SparkV15BookingOpening opening) {
        BOOKING = booking;
        OPENING = opening;
        EVIDENCE_REGISTRY = booking.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
    }

    function getServiceFeedback(bytes32 formId) external view returns (SparkV15Booking.ServiceFeedback memory) {
        return feedback[formId];
    }

    function recordRegisteredFeedback(
        address student,
        bytes32 formId,
        SparkV15Booking.ServiceStatus status,
        bytes32 receivedRef,
        bytes32 notReceivedRef,
        uint256 evidenceId
    ) external {
        if (msg.sender != address(BOOKING)) revert SparkV15Booking.UnauthorisedBookingActor();
        (SparkV15Booking.Form memory form,) = _studentReport(formId, student);
        bool received = status >= SparkV15Booking.ServiceStatus.PartiallyDelivered;
        bool missed = status == SparkV15Booking.ServiceStatus.PartiallyDelivered
            || status == SparkV15Booking.ServiceStatus.NoneDelivered;
        if (
            feedback[formId].reportedAt != 0 || status == SparkV15Booking.ServiceStatus.Unreported
                || (receivedRef != bytes32(0)) != received || (notReceivedRef != bytes32(0)) != missed
        ) revert SparkV15Booking.InvalidReport();
        OPENING.requireEvidence(
            BOOKING.getLesson(form.lessonId).packageId,
            evidenceId,
            BOOKING.serviceFeedbackCommitment(formId, status, receivedRef, notReceivedRef)
        );
        feedback[formId] =
            SparkV15Booking.ServiceFeedback(status, uint64(block.timestamp), evidenceId, receivedRef, notReceivedRef);
    }

    function fullServiceFeedbackDigest(bytes32 formId, bytes32 receivedRef, SourceProof calldata proof)
        external
        view
        returns (bytes32)
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        return
            _feedbackDigest(formId, receivedRef, BOOKING.getLesson(form.lessonId).packageId, form.terms.student, proof);
    }

    /// @notice A student reports full delivery before any later settlement uses the report.
    /// @dev The Source authorises first use here. The proof does not establish earlier evidence availability.
    function recordFullServiceFeedback(bytes32 formId, bytes32 receivedRef, SourceProof calldata proof)
        external
        returns (uint256 evidenceId)
    {
        (SparkV15Booking.Form memory form, SparkV15Booking.Teaching memory teaching) =
            _studentReport(formId, msg.sender);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        if (
            receivedRef == bytes32(0) || feedback[formId].reportedAt != 0 || lesson.terms.rosterRef != bytes32(0)
                || lesson.terms.materialsTermsRef != bytes32(0) || form.terms.payableFee == 0
                || BOOKING.getEffectiveArrangement(form.lessonId, teaching.startedAt).changeId != bytes32(0)
        ) revert SparkV15Booking.InvalidReport();
        bytes32 digest = _feedbackDigest(formId, receivedRef, lesson.packageId, msg.sender, proof);
        address source = _requireSource(digest, lesson.packageId, FEEDBACK_EVIDENCE_TYPE, proof);
        evidenceId = uint256(digest);
        uint64 reportedAt = uint64(block.timestamp);
        feedback[formId] = SparkV15Booking.ServiceFeedback(
            SparkV15Booking.ServiceStatus.FullyDelivered, reportedAt, evidenceId, receivedRef, bytes32(0)
        );
        feedbackEvidence[formId].subjectAndPolicy =
            keccak256(abi.encode(proof.sourceAuthorityId, proof.disclosurePolicyId));
        emit FullServiceFeedbackAdopted(
            formId,
            evidenceId,
            msg.sender,
            receivedRef,
            source,
            proof.sourceAuthorityId,
            proof.disclosurePolicyId,
            reportedAt
        );
    }

    function getAdoptedFeedbackEvidence(bytes32 formId)
        external
        view
        returns (uint256 evidenceId, AVACoreTypes.EvidenceStatus status, uint256 replacementEvidenceId)
    {
        AdoptedEvidence storage evidence = feedbackEvidence[formId];
        if (evidence.subjectAndPolicy == bytes32(0)) return (0, AVACoreTypes.EvidenceStatus.None, 0);
        status = evidence.invalidatedStatus;
        if (status == AVACoreTypes.EvidenceStatus.None) status = AVACoreTypes.EvidenceStatus.Active;
        return (feedback[formId].evidenceId, status, evidence.replacementEvidenceId);
    }

    /// @notice Require the exact current evidence of this report. An adopted reference is scoped to this form.
    function requireUsableFeedbackEvidence(bytes32 formId, uint256 evidenceId, uint256 packageId) external view {
        if (feedback[formId].evidenceId != evidenceId) revert SparkV15Booking.InvalidEvidence();
        AdoptedEvidence storage evidence = feedbackEvidence[formId];
        if (evidence.subjectAndPolicy != bytes32(0) && _packageId(formId) != packageId) {
            revert SparkV15Booking.InvalidEvidence();
        }
        _requireUsableEvidence(evidence, evidenceId, packageId);
    }

    function getTutorDelivery(bytes32 lessonId) external view returns (SparkV15Booking.TutorDelivery memory) {
        return tutorDelivery[lessonId];
    }

    function getTutorCompletedLessons(address tutor) external view returns (bytes32[] memory) {
        return completedLessons[tutor];
    }

    function recordRegisteredTutorDelivery(
        address tutor,
        bytes32 lessonId,
        bool completed,
        bytes32 detailsRef,
        uint256 evidenceId
    ) external {
        if (msg.sender != address(BOOKING)) revert SparkV15Booking.UnauthorisedBookingActor();
        _tutorReport(lessonId, tutor, detailsRef);
        OPENING.requireEvidence(
            BOOKING.getLesson(lessonId).packageId,
            evidenceId,
            BOOKING.tutorDeliveryCommitment(lessonId, completed, detailsRef)
        );
        _recordTutorDelivery(lessonId, tutor, completed, detailsRef, evidenceId);
    }

    function tutorDeliveryDigest(bytes32 lessonId, bytes32 detailsRef, SourceProof calldata proof)
        external
        view
        returns (bytes32)
    {
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        address tutor = OPENING.arrangementAt(lessonId, teaching.startedAt).tutor;
        return _tutorDeliveryDigest(lessonId, detailsRef, BOOKING.getLesson(lessonId).packageId, tutor, proof);
    }

    /// @notice The effective tutor records completed delivery when the Source proof is first adopted.
    /// @dev Settlement and remedy use may later reject the proof without changing that the tutor reported.
    function recordCompletedTutorDelivery(bytes32 lessonId, bytes32 detailsRef, SourceProof calldata proof)
        external
        returns (uint256 evidenceId)
    {
        (SparkV15Booking.Teaching memory teaching, ISparkV15BookingChanges.Arrangement memory arrangement) =
            _tutorReport(lessonId, msg.sender, detailsRef);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        if (
            arrangement.changeId != bytes32(0) || lesson.terms.rosterRef != bytes32(0)
                || lesson.terms.materialsTermsRef != bytes32(0) || arrangement.tutorFee == 0
                || (teaching.startPermission != SparkV15Booking.StartPermission.Permitted
                    && !OPENING.TEACHING_END().hasUsableLateOpeningNotices(lessonId))
        ) revert SparkV15Booking.InvalidReport();
        bytes32[] memory forms = BOOKING.getConfirmedForms(lessonId);
        if (forms.length != 1 || BOOKING.getForm(forms[0]).confirmation.debitedUnits == 0) {
            revert SparkV15Booking.InvalidReport();
        }

        bytes32 digest = _tutorDeliveryDigest(lessonId, detailsRef, lesson.packageId, msg.sender, proof);
        address source = _requireSource(digest, lesson.packageId, TUTOR_DELIVERY_EVIDENCE_TYPE, proof);
        evidenceId = uint256(digest);
        _recordTutorDelivery(lessonId, msg.sender, true, detailsRef, evidenceId);
        tutorDeliveryEvidence[lessonId].subjectAndPolicy =
            keccak256(abi.encode(proof.sourceAuthorityId, proof.disclosurePolicyId));
        emit CompletedTutorDeliveryAdopted(
            lessonId,
            evidenceId,
            msg.sender,
            detailsRef,
            source,
            proof.sourceAuthorityId,
            proof.disclosurePolicyId,
            uint64(block.timestamp)
        );
    }

    function getAdoptedTutorDeliveryEvidence(bytes32 lessonId)
        external
        view
        returns (uint256 evidenceId, AVACoreTypes.EvidenceStatus status, uint256 replacementEvidenceId)
    {
        AdoptedEvidence storage evidence = tutorDeliveryEvidence[lessonId];
        if (evidence.subjectAndPolicy == bytes32(0)) return (0, AVACoreTypes.EvidenceStatus.None, 0);
        status = evidence.invalidatedStatus;
        if (status == AVACoreTypes.EvidenceStatus.None) status = AVACoreTypes.EvidenceStatus.Active;
        return (tutorDelivery[lessonId].evidenceId, status, evidence.replacementEvidenceId);
    }

    /// @notice Check the original report's exact evidence where a live basis is required.
    function requireUsableTutorDeliveryEvidence(bytes32 lessonId, uint256 evidenceId, uint256 packageId) external view {
        if (tutorDelivery[lessonId].evidenceId != evidenceId) revert SparkV15Booking.InvalidEvidence();
        AdoptedEvidence storage evidence = tutorDeliveryEvidence[lessonId];
        if (evidence.subjectAndPolicy != bytes32(0) && BOOKING.getLesson(lessonId).packageId != packageId) {
            revert SparkV15Booking.InvalidEvidence();
        }
        _requireUsableEvidence(evidence, evidenceId, packageId);
    }

    function _requireUsableEvidence(AdoptedEvidence storage evidence, uint256 evidenceId, uint256 packageId)
        private
        view
    {
        if (evidence.subjectAndPolicy == bytes32(0)) {
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
            return;
        }
        if (evidence.invalidatedStatus != AVACoreTypes.EvidenceStatus.None) {
            revert SparkV15Booking.InvalidEvidence();
        }
        // Admission only accepts the installed default policy. Check the module identity again at use.
        EVIDENCE_REGISTRY.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_POLICY);
    }

    /// @notice Apply the installed evidence lifecycle authority without changing the student's reported history.
    function recordFeedbackEvidenceLifecycle(
        bytes32 formId,
        bytes32 role,
        bytes32 authority,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementEvidenceId,
        bytes32 reasonHash
    ) external {
        _recordEvidenceLifecycle(
            feedbackEvidence[formId],
            _packageId(formId),
            FEEDBACK_EVIDENCE_TYPE,
            role,
            authority,
            kind,
            replacementEvidenceId,
            reasonHash
        );
        emit FeedbackEvidenceInvalidated(
            formId, feedback[formId].evidenceId, kind, replacementEvidenceId, reasonHash, authority, msg.sender
        );
    }

    /// @notice Apply the existing lifecycle authority while retaining the tutor's historical report and order.
    function recordTutorDeliveryEvidenceLifecycle(
        bytes32 lessonId,
        bytes32 role,
        bytes32 authority,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementEvidenceId,
        bytes32 reasonHash
    ) external {
        _recordEvidenceLifecycle(
            tutorDeliveryEvidence[lessonId],
            BOOKING.getLesson(lessonId).packageId,
            TUTOR_DELIVERY_EVIDENCE_TYPE,
            role,
            authority,
            kind,
            replacementEvidenceId,
            reasonHash
        );
        emit TutorDeliveryEvidenceInvalidated(
            lessonId, tutorDelivery[lessonId].evidenceId, kind, replacementEvidenceId, reasonHash, authority, msg.sender
        );
    }

    function _recordEvidenceLifecycle(
        AdoptedEvidence storage evidence,
        uint256 packageId,
        bytes32 evidenceType,
        bytes32 role,
        bytes32 authority,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementEvidenceId,
        bytes32 reasonHash
    ) private {
        if (
            evidence.subjectAndPolicy == bytes32(0) || evidence.invalidatedStatus != AVACoreTypes.EvidenceStatus.None
                || reasonHash == bytes32(0) || kind == AVACoreTypes.EvidenceLifecycleKind.None
        ) revert SparkV15Booking.InvalidEvidence();
        EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, role, AVACoreTypes.ACTION_RECORD_EVIDENCE_LIFECYCLE, authority
            );
        // Admission already checked the default lifecycle policy, which has no additional predicates.
        EVIDENCE_REGISTRY.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_LIFECYCLE);
        AVACoreTypes.EvidenceStatus status;
        if (kind == AVACoreTypes.EvidenceLifecycleKind.Supersede) {
            AVAEvidenceRegistry.EvidenceReference memory replacement =
                EVIDENCE_REGISTRY.getEvidenceReference(replacementEvidenceId);
            if (
                replacement.status != AVACoreTypes.EvidenceStatus.Active || replacement.packageId != packageId
                    || replacement.appId != SparkV15.APP_ID || replacement.evidenceTypeHash != evidenceType
                    || keccak256(abi.encode(replacement.subjectId, replacement.disclosurePolicyId))
                        != evidence.subjectAndPolicy
            ) revert SparkV15Booking.InvalidEvidence();
            status = AVACoreTypes.EvidenceStatus.Superseded;
            evidence.replacementEvidenceId = replacementEvidenceId;
        } else {
            if (replacementEvidenceId != 0) revert SparkV15Booking.InvalidEvidence();
            status = kind == AVACoreTypes.EvidenceLifecycleKind.Revoke
                ? AVACoreTypes.EvidenceStatus.Revoked
                : AVACoreTypes.EvidenceStatus.Expired;
        }
        evidence.invalidatedStatus = status;
    }

    function _requireSource(bytes32 digest, uint256 packageId, bytes32 evidenceType, SourceProof calldata proof)
        private
        view
        returns (address source)
    {
        ECDSA.RecoverError recovery;
        (source, recovery) = ECDSA.tryRecover(digest, proof.r, proof.vs);
        if (
            block.timestamp > proof.validThrough || recovery != ECDSA.RecoverError.NoError || source == msg.sender
                || digest == bytes32(0)
        ) revert SparkV15Booking.InvalidEvidence();
        OPENING.requireFirstUseEvidenceSource(
            packageId, source, proof.sourceRole, proof.sourceAuthorityId, proof.disclosurePolicyId, evidenceType, true
        );
    }

    function _feedbackDigest(
        bytes32 formId,
        bytes32 receivedRef,
        uint256 packageId,
        address student,
        SourceProof calldata proof
    ) private view returns (bytes32) {
        bytes32 commitment = BOOKING.serviceFeedbackCommitment(
            formId, SparkV15Booking.ServiceStatus.FullyDelivered, receivedRef, bytes32(0)
        );
        return _firstUseDigest(
            keccak256("Spark DAO Full Service Feedback"), FEEDBACK_TYPEHASH, commitment, packageId, student, proof
        );
    }

    function _tutorDeliveryDigest(
        bytes32 lessonId,
        bytes32 detailsRef,
        uint256 packageId,
        address tutor,
        SourceProof calldata proof
    ) private view returns (bytes32) {
        return _firstUseDigest(
            keccak256("Spark DAO Completed Tutor Delivery"),
            TUTOR_DELIVERY_TYPEHASH,
            BOOKING.tutorDeliveryCommitment(lessonId, true, detailsRef),
            packageId,
            tutor,
            proof
        );
    }

    function _firstUseDigest(
        bytes32 domainName,
        bytes32 typeHash,
        bytes32 commitment,
        uint256 packageId,
        address reporter,
        SourceProof calldata proof
    ) private view returns (bytes32) {
        bytes32 domain = keccak256(
            abi.encode(DOMAIN_TYPEHASH, domainName, keccak256("1"), block.chainid, address(this))
        );
        bytes32 message = keccak256(
            abi.encode(
                typeHash,
                commitment,
                packageId,
                reporter,
                proof.sourceRole,
                proof.sourceAuthorityId,
                proof.disclosurePolicyId,
                proof.validThrough
            )
        );
        return ECDSA.toTypedDataHash(domain, message);
    }

    function _tutorReport(bytes32 lessonId, address tutor, bytes32 detailsRef)
        private
        view
        returns (SparkV15Booking.Teaching memory teaching, ISparkV15BookingChanges.Arrangement memory arrangement)
    {
        teaching = BOOKING.getTeaching(lessonId);
        arrangement = OPENING.arrangementAt(lessonId, teaching.startedAt);
        if (tutor != arrangement.tutor) revert SparkV15Booking.UnauthorisedBookingActor();
        if (teaching.endedAt == 0 || tutorDelivery[lessonId].evidenceId != 0 || detailsRef == bytes32(0)) {
            revert SparkV15Booking.InvalidReport();
        }
    }

    function _recordTutorDelivery(
        bytes32 lessonId,
        address tutor,
        bool completed,
        bytes32 detailsRef,
        uint256 evidenceId
    ) private {
        tutorDelivery[lessonId] = SparkV15Booking.TutorDelivery(
            completed, uint64(block.timestamp), evidenceId, detailsRef
        );
        if (completed) completedLessons[tutor].push(lessonId);
    }

    function _studentReport(bytes32 formId, address student)
        private
        view
        returns (SparkV15Booking.Form memory form, SparkV15Booking.Teaching memory teaching)
    {
        form = BOOKING.getForm(formId);
        if (form.version == 0 || BOOKING.currentForm(form.lessonId, form.terms.placeId) != formId) {
            revert SparkV15Booking.InvalidForm();
        }
        if (student != form.terms.student) revert SparkV15Booking.UnauthorisedBookingActor();
        teaching = BOOKING.getTeaching(form.lessonId);
        if (form.confirmation.confirmedAt == 0 || teaching.endedAt == 0) revert SparkV15Booking.InvalidReport();
    }

    function _packageId(bytes32 formId) private view returns (uint256) {
        return BOOKING.getLesson(BOOKING.getForm(formId).lessonId).packageId;
    }
}
