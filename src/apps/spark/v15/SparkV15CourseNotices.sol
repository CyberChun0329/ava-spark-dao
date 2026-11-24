// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACapabilityKeys} from "@ava-protocol/contracts/src/core/AVACapabilityKeys.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {ECDSA} from "@ava-protocol/contracts/src/vendor/openzeppelin-v4.9.6/utils/cryptography/ECDSA.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {COORDINATE_BOOKING_ACTION, SparkV15Booking} from "./SparkV15Booking.sol";

/// @notice The original agreed course notices and their evidence provenance.
contract SparkV15CourseNotices {
    bytes32 private constant DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant STUDENT_PROOF_TYPEHASH = keccak256(
        "StudentNoticeEvidence(bytes32 commitment,uint256 packageId,address actor,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"
    );
    bytes32 private constant TUTOR_PROOF_TYPEHASH = keccak256(
        "TutorNoticeEvidence(bytes32 commitment,uint256 packageId,address actor,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"
    );
    bytes32 private constant STUDENT_NOTICE_TYPE = keccak256("spark.v1.5.booking.student-notice");
    bytes32 private constant TUTOR_NOTICE_TYPE = keccak256("spark.v1.5.booking.tutor-notice");

    enum NoticeKind {
        Student,
        Tutor
    }

    struct SourceProof {
        bytes32 sourceRole;
        bytes32 sourceAuthorityId;
        uint256 disclosurePolicyId;
        uint64 validThrough;
        bytes32 r;
        bytes32 vs;
    }

    struct Adoption {
        bytes32 subjectAndPolicy;
        AVACoreTypes.EvidenceStatus invalidatedStatus;
        uint256 replacementEvidenceId;
    }

    SparkV15Booking public immutable BOOKING;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;
    mapping(bytes32 => SparkV15Booking.StudentNotice) private studentNotices;
    mapping(bytes32 => SparkV15Booking.TutorNotice) private tutorNotices;
    mapping(NoticeKind => mapping(bytes32 => Adoption)) private adoptedEvidence;
    mapping(NoticeKind => mapping(bytes32 => bool)) private recordedAfterOpeningInSameSecond;

    event NoticeEvidenceAdopted(
        NoticeKind indexed kind,
        bytes32 indexed target,
        uint256 indexed evidenceId,
        address actor,
        address source,
        bytes32 sourceAuthorityId,
        uint256 disclosurePolicyId,
        bytes32 deliveryRef,
        uint64 deliveredAt,
        uint64 recordedAt
    );
    event NoticeEvidenceInvalidated(
        NoticeKind indexed kind,
        bytes32 indexed target,
        uint256 indexed evidenceId,
        AVACoreTypes.EvidenceLifecycleKind transition,
        uint256 replacementEvidenceId,
        bytes32 reasonHash,
        bytes32 authorityId,
        address actor
    );

    constructor(SparkV15Booking booking) {
        BOOKING = booking;
        EVIDENCE_REGISTRY = booking.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
    }

    function getStudentNotice(bytes32 formId) external view returns (SparkV15Booking.StudentNotice memory) {
        return studentNotices[formId];
    }

    function getTutorNotice(bytes32 lessonId) external view returns (SparkV15Booking.TutorNotice memory) {
        return tutorNotices[lessonId];
    }

    function recordRegisteredStudentNotice(
        address actor,
        bytes32 formId,
        uint64 deliveredAt,
        bytes32 deliveryRef,
        uint256 evidenceId
    ) external {
        if (msg.sender != address(BOOKING)) revert SparkV15Booking.UnauthorisedBookingActor();
        (SparkV15Booking.Lesson memory lesson, bytes32 authorityId) =
            _studentNoticeScope(actor, formId, deliveredAt, deliveryRef);
        BOOKING.OPENING()
            .requireEvidence(
                lesson.packageId, evidenceId, BOOKING.studentNoticeCommitment(formId, deliveredAt, deliveryRef)
            );
        uint64 recordedAt = _recordNoticeTime(NoticeKind.Student, formId, lesson.terms);
        studentNotices[formId] = SparkV15Booking.StudentNotice(actor, authorityId, deliveredAt, recordedAt, evidenceId);
    }

    function recordRegisteredTutorNotice(
        address actor,
        bytes32 lessonId,
        bytes32 channelRef,
        uint64 deliveredAt,
        bytes32 deliveryRef,
        uint256 evidenceId
    ) external {
        if (msg.sender != address(BOOKING)) revert SparkV15Booking.UnauthorisedBookingActor();
        (SparkV15Booking.Lesson memory lesson,) =
            _tutorNoticeScope(actor, lessonId, channelRef, deliveredAt, deliveryRef);
        BOOKING.OPENING()
            .requireEvidence(
                lesson.packageId,
                evidenceId,
                BOOKING.tutorNoticeCommitment(lessonId, channelRef, deliveredAt, deliveryRef)
            );
        uint64 recordedAt = _recordNoticeTime(NoticeKind.Tutor, lessonId, lesson.terms);
        tutorNotices[lessonId] = SparkV15Booking.TutorNotice(actor, deliveredAt, recordedAt, channelRef, evidenceId);
    }

    function studentNoticeAdoptionDigest(
        bytes32 formId,
        uint64 deliveredAt,
        bytes32 deliveryRef,
        address actor,
        SourceProof calldata proof
    ) external view returns (bytes32) {
        return _adoptionDigest(
            NoticeKind.Student,
            BOOKING.studentNoticeCommitment(formId, deliveredAt, deliveryRef),
            BOOKING.getLesson(BOOKING.getForm(formId).lessonId).packageId,
            actor,
            proof
        );
    }

    function tutorNoticeAdoptionDigest(
        bytes32 lessonId,
        bytes32 channelRef,
        uint64 deliveredAt,
        bytes32 deliveryRef,
        address actor,
        SourceProof calldata proof
    ) external view returns (bytes32) {
        return _adoptionDigest(
            NoticeKind.Tutor,
            BOOKING.tutorNoticeCommitment(lessonId, channelRef, deliveredAt, deliveryRef),
            BOOKING.getLesson(lessonId).packageId,
            actor,
            proof
        );
    }

    /// @notice Confirm actual delivery to the student using a Source proof first made available here.
    function recordStudentNoticeWithConsent(
        bytes32 formId,
        uint64 deliveredAt,
        bytes32 deliveryRef,
        SourceProof calldata proof
    ) external returns (uint256 evidenceId) {
        (SparkV15Booking.Lesson memory lesson, bytes32 authorityId) =
            _studentNoticeScope(msg.sender, formId, deliveredAt, deliveryRef);
        _requireOrdinaryInitialNotice(lesson, formId);
        bytes32 commitment = BOOKING.studentNoticeCommitment(formId, deliveredAt, deliveryRef);
        evidenceId = _adopt(NoticeKind.Student, formId, commitment, lesson.packageId, deliveredAt, deliveryRef, proof);
        uint64 recordedAt = _recordNoticeTime(NoticeKind.Student, formId, lesson.terms);
        studentNotices[formId] =
            SparkV15Booking.StudentNotice(msg.sender, authorityId, deliveredAt, recordedAt, evidenceId);
    }

    /// @notice The provider or the coordinator independently confirms actual delivery to the tutor.
    function recordTutorNoticeWithConsent(
        bytes32 lessonId,
        bytes32 channelRef,
        uint64 deliveredAt,
        bytes32 deliveryRef,
        SourceProof calldata proof
    ) external returns (uint256 evidenceId) {
        (SparkV15Booking.Lesson memory lesson, bytes32 firstForm) =
            _tutorNoticeScope(msg.sender, lessonId, channelRef, deliveredAt, deliveryRef);
        _requireOrdinaryInitialNotice(lesson, firstForm);
        bytes32 commitment = BOOKING.tutorNoticeCommitment(lessonId, channelRef, deliveredAt, deliveryRef);
        evidenceId = _adopt(NoticeKind.Tutor, lessonId, commitment, lesson.packageId, deliveredAt, deliveryRef, proof);
        uint64 recordedAt = _recordNoticeTime(NoticeKind.Tutor, lessonId, lesson.terms);
        tutorNotices[lessonId] = SparkV15Booking.TutorNotice(msg.sender, deliveredAt, recordedAt, channelRef, evidenceId);
    }

    function _recordNoticeTime(NoticeKind kind, bytes32 target, SparkV15Booking.LessonTerms memory terms)
        private
        returns (uint64 recordedAt)
    {
        recordedAt = uint64(block.timestamp);
        // The late-verification route only uses an original one-to-one starting at or after its agreed time.
        if (recordedAt < terms.startsAt || terms.rosterRef != bytes32(0) || terms.materialsTermsRef != bytes32(0)) {
            return recordedAt;
        }
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(terms.lessonId);
        if (
            teaching.startRecordedAt == recordedAt && teaching.startPermission == SparkV15Booking.StartPermission.Unverified
                && teaching.unmetConditionRef == bytes32(0)
        ) recordedAfterOpeningInSameSecond[kind][target] = true;
    }

    function getAdoptedNoticeEvidence(NoticeKind kind, bytes32 target)
        external
        view
        returns (uint256 evidenceId, AVACoreTypes.EvidenceStatus status, uint256 replacementEvidenceId)
    {
        evidenceId = _noticeEvidenceId(kind, target);
        Adoption storage adoption = adoptedEvidence[kind][target];
        if (adoption.subjectAndPolicy == bytes32(0)) return (0, AVACoreTypes.EvidenceStatus.None, 0);
        status = adoption.invalidatedStatus;
        if (status == AVACoreTypes.EvidenceStatus.None) status = AVACoreTypes.EvidenceStatus.Active;
        return (evidenceId, status, adoption.replacementEvidenceId);
    }

    function requireStudentNoticeEvidence(bytes32 formId, uint256 evidenceId, uint256 packageId) external view {
        _requireAvailable(NoticeKind.Student, formId, evidenceId, packageId);
    }

    function requireTutorNoticeEvidence(bytes32 lessonId, uint256 evidenceId, uint256 packageId) external view {
        _requireAvailable(NoticeKind.Tutor, lessonId, evidenceId, packageId);
    }

    /// @notice Require both live notice proofs, including independent verification when recorded after the opening judgement.
    function requireLateOpeningNotices(bytes32 lessonId, bytes32 formId, uint64 openingRecordedAt, uint256 packageId)
        external
        view
    {
        SparkV15Booking.StudentNotice storage student = studentNotices[formId];
        SparkV15Booking.TutorNotice storage tutor = tutorNotices[lessonId];
        bool studentLate = _recordedAfterOpening(NoticeKind.Student, formId, student.recordedAt, openingRecordedAt);
        bool tutorLate = _recordedAfterOpening(NoticeKind.Tutor, lessonId, tutor.recordedAt, openingRecordedAt);
        if (!studentLate && !tutorLate) revert SparkV15Booking.InvalidNotice();
        _requireAvailable(NoticeKind.Student, formId, student.evidenceId, packageId);
        _requireAvailable(NoticeKind.Tutor, lessonId, tutor.evidenceId, packageId);
        if (studentLate) _requireIndependentProof(NoticeKind.Student, formId, student.evidenceId, student.sender);
        if (tutorLate) _requireIndependentProof(NoticeKind.Tutor, lessonId, tutor.evidenceId, tutor.sender);
    }

    function _recordedAfterOpening(NoticeKind kind, bytes32 target, uint64 recordedAt, uint64 openingRecordedAt)
        private
        view
        returns (bool)
    {
        return recordedAt > openingRecordedAt
            || (recordedAt == openingRecordedAt && recordedAfterOpeningInSameSecond[kind][target]);
    }

    function _requireIndependentProof(NoticeKind kind, bytes32 target, uint256 evidenceId, address sender) private view {
        // A first-use proof already required a Source distinct from the actor confirming delivery.
        if (
            adoptedEvidence[kind][target].subjectAndPolicy == bytes32(0)
                && EVIDENCE_REGISTRY.getEvidence(evidenceId).registeredBy == sender
        ) revert SparkV15Booking.InvalidEvidence();
    }

    /// @notice Withdraw, expire, or link a compatible Core replacement under the existing lifecycle authority.
    /// @dev History of actual notice delivery and recognition remains available by the original reference.
    function recordNoticeEvidenceLifecycle(
        NoticeKind kind,
        bytes32 target,
        bytes32 role,
        bytes32 authorityId,
        AVACoreTypes.EvidenceLifecycleKind transition,
        uint256 replacementEvidenceId,
        bytes32 reasonHash
    ) external {
        uint256 evidenceId = _noticeEvidenceId(kind, target);
        Adoption storage adoption = adoptedEvidence[kind][target];
        if (
            adoption.subjectAndPolicy == bytes32(0) || adoption.invalidatedStatus != AVACoreTypes.EvidenceStatus.None
                || reasonHash == bytes32(0) || transition == AVACoreTypes.EvidenceLifecycleKind.None
        ) revert SparkV15Booking.InvalidEvidence();
        EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, role, AVACoreTypes.ACTION_RECORD_EVIDENCE_LIFECYCLE, authorityId
            );
        uint256 packageId = _noticePackageId(kind, target);
        EVIDENCE_REGISTRY.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_LIFECYCLE);
        AVACoreTypes.EvidenceStatus status;
        if (transition == AVACoreTypes.EvidenceLifecycleKind.Supersede) {
            AVAEvidenceRegistry.EvidenceReference memory replacement =
                EVIDENCE_REGISTRY.getEvidenceReference(replacementEvidenceId);
            if (
                replacement.status != AVACoreTypes.EvidenceStatus.Active || replacement.packageId != packageId
                    || replacement.appId != SparkV15.APP_ID || replacement.evidenceTypeHash != _evidenceType(kind)
                    || keccak256(abi.encode(replacement.subjectId, replacement.disclosurePolicyId))
                        != adoption.subjectAndPolicy
            ) revert SparkV15Booking.InvalidEvidence();
            status = AVACoreTypes.EvidenceStatus.Superseded;
            adoption.replacementEvidenceId = replacementEvidenceId;
        } else {
            if (replacementEvidenceId != 0) revert SparkV15Booking.InvalidEvidence();
            status = transition == AVACoreTypes.EvidenceLifecycleKind.Revoke
                ? AVACoreTypes.EvidenceStatus.Revoked
                : AVACoreTypes.EvidenceStatus.Expired;
        }
        adoption.invalidatedStatus = status;
        emit NoticeEvidenceInvalidated(
            kind, target, evidenceId, transition, replacementEvidenceId, reasonHash, authorityId, msg.sender
        );
    }

    function _requireAvailable(NoticeKind kind, bytes32 target, uint256 evidenceId, uint256 packageId) private view {
        if (_noticeEvidenceId(kind, target) != evidenceId) revert SparkV15Booking.InvalidEvidence();
        Adoption storage adoption = adoptedEvidence[kind][target];
        if (adoption.subjectAndPolicy == bytes32(0)) {
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
            return;
        }
        if (
            adoption.invalidatedStatus != AVACoreTypes.EvidenceStatus.None
                || _noticePackageId(kind, target) != packageId
        ) {
            revert SparkV15Booking.InvalidEvidence();
        }
        // First use requires the default evidence and lifecycle policies, with these module identities pinned.
        EVIDENCE_REGISTRY.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_POLICY);
    }

    function _noticeEvidenceId(NoticeKind kind, bytes32 target) private view returns (uint256) {
        return kind == NoticeKind.Student ? studentNotices[target].evidenceId : tutorNotices[target].evidenceId;
    }

    function _noticePackageId(NoticeKind kind, bytes32 target) private view returns (uint256) {
        bytes32 lessonId = kind == NoticeKind.Student ? BOOKING.getForm(target).lessonId : target;
        return BOOKING.getLesson(lessonId).packageId;
    }

    function _studentNoticeScope(address actor, bytes32 formId, uint64 deliveredAt, bytes32 deliveryRef)
        private
        view
        returns (SparkV15Booking.Lesson memory lesson, bytes32 authorityId)
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        if (form.version == 0 || BOOKING.currentForm(form.lessonId, form.terms.placeId) != formId) {
            revert SparkV15Booking.InvalidForm();
        }
        lesson = BOOKING.getLesson(form.lessonId);
        authorityId = _requireCoordinator(lesson.terms.coordinator, actor);
        if (
            form.confirmation.confirmedAt == 0 || studentNotices[formId].evidenceId != 0 || deliveredAt == 0
                || deliveredAt > block.timestamp || deliveryRef == bytes32(0)
        ) revert SparkV15Booking.InvalidNotice();
    }

    function _tutorNoticeScope(
        address actor,
        bytes32 lessonId,
        bytes32 channelRef,
        uint64 deliveredAt,
        bytes32 deliveryRef
    ) private view returns (SparkV15Booking.Lesson memory lesson, bytes32 firstForm) {
        lesson = BOOKING.getLesson(lessonId);
        if (actor != lesson.terms.provider) _requireCoordinator(lesson.terms.coordinator, actor);
        bytes32[] memory forms = BOOKING.getConfirmedForms(lessonId);
        bytes32 agreedChannel = lesson.terms.tutorNoticeChannelRef;
        if (
            forms.length == 0 || tutorNotices[lessonId].evidenceId != 0 || deliveredAt == 0
                || deliveredAt > block.timestamp || channelRef == bytes32(0) || deliveryRef == bytes32(0)
                || (agreedChannel != bytes32(0) && channelRef != agreedChannel)
        ) revert SparkV15Booking.InvalidNotice();
        firstForm = forms[0];
    }

    function _requireCoordinator(address coordinator, address actor) private view returns (bytes32) {
        if (actor != coordinator) revert SparkV15Booking.UnauthorisedBookingActor();
        return BOOKING.OPENING().requireBookingActor(actor, BOOKING.COORDINATOR_ROLE(), COORDINATE_BOOKING_ACTION);
    }

    function _requireOrdinaryInitialNotice(SparkV15Booking.Lesson memory lesson, bytes32 formId) private view {
        if (
            lesson.terms.rosterRef != bytes32(0) || lesson.terms.materialsTermsRef != bytes32(0)
                || BOOKING.getForm(formId).terms.payableFee == 0
                || BOOKING.getEffectiveArrangement(lesson.terms.lessonId, uint64(block.timestamp)).changeId
                    != bytes32(0)
        ) revert SparkV15Booking.InvalidNotice();
    }

    function _adopt(
        NoticeKind kind,
        bytes32 target,
        bytes32 commitment,
        uint256 packageId,
        uint64 deliveredAt,
        bytes32 deliveryRef,
        SourceProof calldata proof
    ) private returns (uint256 evidenceId) {
        if (block.timestamp > proof.validThrough) revert SparkV15Booking.InvalidEvidence();
        bytes32 digest = _adoptionDigest(kind, commitment, packageId, msg.sender, proof);
        (address source, ECDSA.RecoverError recovery) = ECDSA.tryRecover(digest, proof.r, proof.vs);
        if (recovery != ECDSA.RecoverError.NoError || source == msg.sender || digest == bytes32(0)) {
            revert SparkV15Booking.InvalidEvidence();
        }
        BOOKING.OPENING()
            .requireFirstUseEvidenceSource(
                packageId,
                source,
                proof.sourceRole,
                proof.sourceAuthorityId,
                proof.disclosurePolicyId,
                _evidenceType(kind),
                true
            );
        evidenceId = uint256(digest);
        adoptedEvidence[kind][target].subjectAndPolicy =
            keccak256(abi.encode(proof.sourceAuthorityId, proof.disclosurePolicyId));
        emit NoticeEvidenceAdopted(
            kind,
            target,
            evidenceId,
            msg.sender,
            source,
            proof.sourceAuthorityId,
            proof.disclosurePolicyId,
            deliveryRef,
            deliveredAt,
            uint64(block.timestamp)
        );
    }

    function _adoptionDigest(
        NoticeKind kind,
        bytes32 commitment,
        uint256 packageId,
        address actor,
        SourceProof calldata proof
    ) private view returns (bytes32) {
        bytes32 domain = keccak256(
            abi.encode(
                DOMAIN_TYPEHASH,
                keccak256("Spark DAO Course Notice Evidence"),
                keccak256("1"),
                block.chainid,
                address(this)
            )
        );
        bytes32 typehash = kind == NoticeKind.Student ? STUDENT_PROOF_TYPEHASH : TUTOR_PROOF_TYPEHASH;
        bytes32 message = keccak256(
            abi.encode(
                typehash,
                commitment,
                packageId,
                actor,
                proof.sourceRole,
                proof.sourceAuthorityId,
                proof.disclosurePolicyId,
                proof.validThrough
            )
        );
        return ECDSA.toTypedDataHash(domain, message);
    }

    function _evidenceType(NoticeKind kind) private pure returns (bytes32) {
        return kind == NoticeKind.Student ? STUDENT_NOTICE_TYPE : TUTOR_NOTICE_TYPE;
    }
}
