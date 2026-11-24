// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACapabilityKeys} from "@ava-protocol/contracts/src/core/AVACapabilityKeys.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {SparkV15Booking, SparkV15BookingOpening} from "./SparkV15Booking.sol";

/// @notice First adoption and subsequent eligibility of signed evidence for actual ordinary teaching occurrences.
contract SparkV15TeachingEnd {
    error InterestedSettlementActor();

    bytes32 private constant END_DOMAIN_NAME = keccak256("Spark DAO Teaching End Evidence");
    bytes32 private constant START_DOMAIN_NAME = keccak256("Spark DAO Teaching Start Evidence");
    bytes32 private constant END_PROOF_TYPEHASH = keccak256(
        "TeachingEndEvidence(uint256 packageId,bytes32 lessonId,bytes32 commitment,address verifier,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"
    );
    bytes32 private constant START_PROOF_TYPEHASH = keccak256(
        "TeachingStartEvidence(uint256 packageId,bytes32 lessonId,bytes32 commitment,address verifier,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"
    );
    bytes32 public constant EVIDENCE_TYPE = keccak256("spark.v1.5.booking.teaching-end");
    bytes32 public constant START_EVIDENCE_TYPE = keccak256("spark.v1.5.booking.teaching-start");

    struct Proof {
        bytes32 sourceRole;
        bytes32 sourceAuthorityId;
        uint256 disclosurePolicyId;
        uint64 validThrough;
        bytes32 r;
        bytes32 vs;
    }

    struct AdoptedEvidence {
        bytes32 sourceAuthorityId;
        uint256 disclosurePolicyId;
        AVACoreTypes.EvidenceStatus lifecycleStatus;
        uint256 replacementCoreEvidenceId;
    }

    SparkV15Booking public immutable BOOKING;
    AVAEvidenceRegistry private immutable EVIDENCE;
    mapping(bytes32 => AdoptedEvidence) private adopted;
    mapping(bytes32 => AdoptedEvidence) private adoptedStart;

    event TeachingStartEvidenceAdopted(
        bytes32 indexed lessonId,
        uint256 indexed evidenceId,
        address indexed source,
        address verifier,
        bytes32 sourceAuthorityId,
        uint256 disclosurePolicyId,
        bytes32 commitment
    );
    event TeachingEndEvidenceAdopted(
        bytes32 indexed lessonId,
        uint256 indexed evidenceId,
        address indexed source,
        address verifier,
        bytes32 sourceAuthorityId,
        uint256 disclosurePolicyId,
        bytes32 commitment
    );
    event TeachingEndEvidenceLifecycleRecorded(
        bytes32 indexed lessonId,
        uint256 indexed evidenceId,
        AVACoreTypes.EvidenceLifecycleKind indexed kind,
        uint256 replacementCoreEvidenceId,
        bytes32 reasonHash,
        bytes32 authorityId,
        address actor
    );
    event TeachingStartEvidenceLifecycleRecorded(
        bytes32 indexed lessonId,
        uint256 indexed evidenceId,
        AVACoreTypes.EvidenceLifecycleKind indexed kind,
        uint256 replacementCoreEvidenceId,
        bytes32 reasonHash,
        bytes32 authorityId,
        address actor
    );

    constructor(SparkV15Booking booking) {
        BOOKING = booking;
        EVIDENCE = booking.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
    }

    /// @notice The verifier adopts independent Source evidence while recording the actual start.
    function recordOrdinaryTeachingStarted(
        bytes32 lessonId,
        SparkV15Booking.StartObservation calldata observation,
        Proof calldata proof
    ) external {
        SparkV15BookingOpening opening = BOOKING.OPENING();
        _requireTeachingVerifier(opening, msg.sender);
        uint256 packageId = _ordinaryLessonPackage(lessonId);
        bytes32 commitment = BOOKING.teachingStartCommitment(lessonId, observation);
        (address source, uint256 evidenceId) = _firstUseProof(opening, lessonId, packageId, commitment, proof, true);
        BOOKING.recordTeachingStarted(lessonId, observation, evidenceId);
        _retain(adoptedStart[lessonId], proof);
        emit TeachingStartEvidenceAdopted(
            lessonId, evidenceId, source, msg.sender, proof.sourceAuthorityId, proof.disclosurePolicyId, commitment
        );
    }

    /// @dev The proof is available for App use for the first time in this transaction.
    function recordOrdinaryTeachingEnded(
        bytes32 lessonId,
        uint64 occurredAt,
        bytes32 occurrenceRef,
        Proof calldata proof
    ) external {
        SparkV15BookingOpening opening = BOOKING.OPENING();
        _requireTeachingVerifier(opening, msg.sender);
        uint256 packageId = _ordinaryLessonPackage(lessonId);
        if (
            BOOKING.getTeaching(lessonId).startPermission != SparkV15Booking.StartPermission.Permitted
                && !hasUsableLateOpeningNotices(lessonId)
        ) {
            revert SparkV15Booking.InvalidTeaching();
        }
        bytes32 commitment = BOOKING.teachingEndCommitment(lessonId, occurredAt, occurrenceRef);
        (address source, uint256 evidenceId) = _firstUseProof(opening, lessonId, packageId, commitment, proof, false);
        BOOKING.recordTeachingEnded(lessonId, occurredAt, occurrenceRef, evidenceId);
        _retain(adopted[lessonId], proof);
        emit TeachingEndEvidenceAdopted(
            lessonId, evidenceId, source, msg.sender, proof.sourceAuthorityId, proof.disclosurePolicyId, commitment
        );
    }

    /// @notice A later consumer can rely on independently verified timely notices for the original paid one-to-one.
    /// @dev This leaves both the observed start and the judgement at its original recording intact.
    function hasUsableLateOpeningNotices(bytes32 lessonId) public view returns (bool) {
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        if (
            teaching.startPermission != SparkV15Booking.StartPermission.Unverified
                || teaching.unmetConditionRef != bytes32(0)
        ) return false;

        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        if (lesson.terms.rosterRef != bytes32(0) || lesson.terms.materialsTermsRef != bytes32(0)) return false;
        SparkV15BookingOpening opening = BOOKING.OPENING();
        if (opening.arrangementAt(lessonId, teaching.startedAt).changeId != bytes32(0)) return false;
        bytes32[] memory forms = BOOKING.getConfirmedForms(lessonId);
        if (forms.length != 1 || BOOKING.getForm(forms[0]).confirmation.debitedUnits == 0) return false;
        if (
            opening.startPermission(lessonId, false, teaching.startedAt, BOOKING.getStudentsTakingLesson(lessonId))
                != SparkV15Booking.StartPermission.Permitted
        ) return false;

        try this.requireStartAvailable(lessonId, teaching.startEvidenceId, lesson.packageId) {}
        catch { return false; }
        try opening.COURSE_NOTICES().requireLateOpeningNotices(lessonId, forms[0], teaching.startRecordedAt, lesson.packageId) {
            return true;
        } catch {
            return false;
        }
    }

    /// @notice Check the registered Source for settlement of teaching started without permission.
    function requireIndependentProviderStartSource(uint256 evidenceId, bytes32 lessonId, bytes32 formId, address paidTo)
        external
        view
    {
        address source = EVIDENCE.getEvidence(evidenceId).registeredBy;
        SparkV15Booking.LessonTerms memory lesson = BOOKING.getLesson(lessonId).terms;
        if (source == lesson.provider || source == lesson.tutor || source == paidTo) {
            revert InterestedSettlementActor();
        }
        // The compiler verifies the confirmed group roster. An unconfirmed single place uses its exact effective form.
        bytes32[] memory forms = BOOKING.getConfirmedForms(lessonId);
        if (forms.length == 0) _requireDisinterestedSettlementSeat(formId, source);
        for (uint256 i; i < forms.length; ++i) {
            _requireDisinterestedSettlementSeat(forms[i], source);
        }
    }

    function _requireDisinterestedSettlementSeat(bytes32 formId, address source) private view {
        SparkV15Booking.PlaceTerms memory place = BOOKING.getForm(formId).terms;
        if (
            source == place.customer || source == place.customerRepresentative || source == place.payer
                || source == place.student
        ) revert InterestedSettlementActor();
    }

    /// @notice Validate the canonical writer's original occurrence and permission checks.
    function requireTeachingStart(
        address actor,
        bytes32 lessonId,
        SparkV15Booking.StartObservation calldata observation,
        uint256 evidenceId
    ) external view returns (SparkV15Booking.StartPermission permission) {
        SparkV15BookingOpening opening = BOOKING.OPENING();
        bool firstUse = actor == address(this);
        if (!firstUse) _requireTeachingVerifier(opening, actor);
        if (
            BOOKING.getTeaching(lessonId).startedAt != 0
                || observation.occurredAt == 0 || observation.occurredAt > block.timestamp
                || observation.occurrenceRef == bytes32(0)
        ) revert SparkV15Booking.InvalidTeaching();
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        if (!firstUse) {
            opening.requireEvidence(
                lesson.packageId, evidenceId, BOOKING.teachingStartCommitment(lessonId, observation)
            );
        }
        if (BOOKING.getConfirmedForms(lessonId).length == 0) {
            if (
                firstUse || lesson.packageId == 0 || !observation.providerWentAhead
                    || observation.unmetConditionRef == bytes32(0)
            ) revert SparkV15Booking.InvalidTeaching();
            return SparkV15Booking.StartPermission.RequirementsNotMet;
        }
        permission = opening.startPermission(
            lessonId, lesson.terms.rosterLockAt != 0, observation.occurredAt, observation.studentsTakingLesson
        );
        if (observation.unmetConditionRef != bytes32(0)) {
            // Preserve the actual occurrence with its conflicting evidence.
            permission = permission == SparkV15Booking.StartPermission.Permitted
                ? SparkV15Booking.StartPermission.Unverified
                : SparkV15Booking.StartPermission.RequirementsNotMet;
        }
    }

    function _requireTeachingVerifier(SparkV15BookingOpening opening, address actor) private view {
        opening.requireBookingActor(actor, BOOKING.VERIFIER_ROLE(), BOOKING.ACTION_VERIFY_TEACHING());
    }

    function _firstUseProof(
        SparkV15BookingOpening opening,
        bytes32 lessonId,
        uint256 packageId,
        bytes32 commitment,
        Proof calldata proof,
        bool forStart
    ) private view returns (address source, uint256 evidenceId) {
        if (block.timestamp > proof.validThrough) revert SparkV15Booking.InvalidEvidence();
        bytes32 message = keccak256(
            abi.encode(
                forStart ? START_PROOF_TYPEHASH : END_PROOF_TYPEHASH,
                packageId,
                lessonId,
                commitment,
                msg.sender,
                proof.sourceRole,
                proof.sourceAuthorityId,
                proof.disclosurePolicyId,
                proof.validThrough
            )
        );
        source = opening.recoverSource(
            forStart ? START_DOMAIN_NAME : END_DOMAIN_NAME, address(this), message, proof.r, proof.vs
        );
        if (source == msg.sender || message == bytes32(0)) revert SparkV15Booking.InvalidEvidence();
        opening.requireFirstUseEvidenceSource(
            packageId,
            source,
            proof.sourceRole,
            proof.sourceAuthorityId,
            proof.disclosurePolicyId,
            forStart ? START_EVIDENCE_TYPE : EVIDENCE_TYPE,
            true
        );
        evidenceId = uint256(message);
    }

    // Booking retains the exact reference and both times. The source distinguishes
    // the adopted reference for this occurrence from a Core evidence ID.
    function _retain(AdoptedEvidence storage evidence, Proof calldata proof) private {
        evidence.sourceAuthorityId = proof.sourceAuthorityId;
        evidence.disclosurePolicyId = proof.disclosurePolicyId;
    }

    function _ordinaryLessonPackage(bytes32 lessonId) private view returns (uint256) {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        if (lesson.terms.rosterRef != bytes32(0) || lesson.terms.materialsTermsRef != bytes32(0)) {
            revert SparkV15Booking.InvalidTeaching();
        }
        bytes32[] memory forms = BOOKING.getConfirmedForms(lessonId);
        if (
            forms.length != 1 || BOOKING.getForm(forms[0]).confirmation.debitedUnits == 0
                || BOOKING.isCancelledAt(forms[0], uint64(block.timestamp))
                || BOOKING.bookingChanges().hasFinalizedArrangement(lessonId)
        ) revert SparkV15Booking.InvalidTeaching();
        return lesson.packageId;
    }

    function getAdoptedEvidence(bytes32 lessonId)
        external
        view
        returns (
            uint256 evidenceId,
            bytes32 sourceAuthorityId,
            uint256 disclosurePolicyId,
            AVACoreTypes.EvidenceStatus status,
            uint256 replacementCoreEvidenceId
        )
    {
        return _getAdoptedEvidence(lessonId, false);
    }

    function getAdoptedStartEvidence(bytes32 lessonId)
        external
        view
        returns (
            uint256 evidenceId,
            bytes32 sourceAuthorityId,
            uint256 disclosurePolicyId,
            AVACoreTypes.EvidenceStatus status,
            uint256 replacementCoreEvidenceId
        )
    {
        return _getAdoptedEvidence(lessonId, true);
    }

    function _getAdoptedEvidence(bytes32 lessonId, bool forStart)
        private
        view
        returns (uint256, bytes32, uint256, AVACoreTypes.EvidenceStatus status, uint256)
    {
        AdoptedEvidence storage evidence = forStart ? adoptedStart[lessonId] : adopted[lessonId];
        if (evidence.sourceAuthorityId == bytes32(0)) return (0, bytes32(0), 0, AVACoreTypes.EvidenceStatus.None, 0);
        status = evidence.lifecycleStatus;
        if (status == AVACoreTypes.EvidenceStatus.None) status = AVACoreTypes.EvidenceStatus.Active;
        return (
            _occurrenceEvidenceId(lessonId, forStart),
            evidence.sourceAuthorityId,
            evidence.disclosurePolicyId,
            status,
            evidence.replacementCoreEvidenceId
        );
    }

    /// @notice Require the original ending basis. Supersession does not substitute a new basis.
    function requireAvailable(bytes32 lessonId, uint256 evidenceId, uint256 packageId) external view {
        _requireAvailable(lessonId, evidenceId, packageId, false);
    }

    /// @notice Require the original starting basis, using the Core registry for its existing receipts.
    function requireStartAvailable(bytes32 lessonId, uint256 evidenceId, uint256 packageId) external view {
        _requireAvailable(lessonId, evidenceId, packageId, true);
    }

    function _requireAvailable(bytes32 lessonId, uint256 evidenceId, uint256 packageId, bool forStart) private view {
        if (evidenceId == 0 || _occurrenceEvidenceId(lessonId, forStart) != evidenceId) {
            revert AVACoreTypes.InvalidState(evidenceId);
        }
        AdoptedEvidence storage evidence = forStart ? adoptedStart[lessonId] : adopted[lessonId];
        if (evidence.sourceAuthorityId == bytes32(0)) {
            EVIDENCE.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
            return;
        }
        if (
            evidence.lifecycleStatus != AVACoreTypes.EvidenceStatus.None
                || BOOKING.getLesson(lessonId).packageId != packageId
        ) revert AVACoreTypes.InvalidState(evidenceId);
        // First adoption required the default evidence policy. Keep Core's package identity check.
        EVIDENCE.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_POLICY);
    }

    function _occurrenceEvidenceId(bytes32 lessonId, bool forStart) private view returns (uint256) {
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        return forStart ? teaching.startEvidenceId : teaching.endEvidenceId;
    }

    /// @notice Apply the existing evidence lifecycle action to the original adopted ending basis.
    function recordEvidenceLifecycle(
        bytes32 lessonId,
        bytes32 role,
        bytes32 authorityId,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementCoreEvidenceId,
        bytes32 reasonHash
    ) external {
        uint256 evidenceId = _recordLifecycle(
            lessonId, role, authorityId, kind, replacementCoreEvidenceId, reasonHash, false
        );
        emit TeachingEndEvidenceLifecycleRecorded(
            lessonId, evidenceId, kind, replacementCoreEvidenceId, reasonHash, authorityId, msg.sender
        );
    }

    /// @notice Apply the existing evidence lifecycle action to the adopted starting basis.
    function recordStartEvidenceLifecycle(
        bytes32 lessonId,
        bytes32 role,
        bytes32 authorityId,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementCoreEvidenceId,
        bytes32 reasonHash
    ) external {
        uint256 evidenceId = _recordLifecycle(
            lessonId, role, authorityId, kind, replacementCoreEvidenceId, reasonHash, true
        );
        emit TeachingStartEvidenceLifecycleRecorded(
            lessonId, evidenceId, kind, replacementCoreEvidenceId, reasonHash, authorityId, msg.sender
        );
    }

    function _recordLifecycle(
        bytes32 lessonId,
        bytes32 role,
        bytes32 authorityId,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementCoreEvidenceId,
        bytes32 reasonHash,
        bool forStart
    ) private returns (uint256 evidenceId) {
        AdoptedEvidence storage evidence = forStart ? adoptedStart[lessonId] : adopted[lessonId];
        evidenceId = _occurrenceEvidenceId(lessonId, forStart);
        if (
            evidence.sourceAuthorityId == bytes32(0) || evidence.lifecycleStatus != AVACoreTypes.EvidenceStatus.None
                || reasonHash == bytes32(0) || kind == AVACoreTypes.EvidenceLifecycleKind.None
        ) revert AVACoreTypes.InvalidState(evidenceId);
        EVIDENCE.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, role, AVACoreTypes.ACTION_RECORD_EVIDENCE_LIFECYCLE, authorityId
            );
        uint256 packageId = BOOKING.getLesson(lessonId).packageId;
        EVIDENCE.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_LIFECYCLE);
        if (kind == AVACoreTypes.EvidenceLifecycleKind.Supersede) {
            _requireCompatibleReplacement(
                packageId, evidence, replacementCoreEvidenceId, forStart ? START_EVIDENCE_TYPE : EVIDENCE_TYPE
            );
            evidence.replacementCoreEvidenceId = replacementCoreEvidenceId;
            evidence.lifecycleStatus = AVACoreTypes.EvidenceStatus.Superseded;
        } else {
            if (replacementCoreEvidenceId != 0) revert AVACoreTypes.InvalidState(replacementCoreEvidenceId);
            evidence.lifecycleStatus = kind == AVACoreTypes.EvidenceLifecycleKind.Revoke
                ? AVACoreTypes.EvidenceStatus.Revoked
                : AVACoreTypes.EvidenceStatus.Expired;
        }
    }

    function _requireCompatibleReplacement(
        uint256 packageId,
        AdoptedEvidence storage evidence,
        uint256 replacementCoreEvidenceId,
        bytes32 evidenceType
    ) private view {
        AVAEvidenceRegistry.EvidenceReference memory replacement =
            EVIDENCE.getEvidenceReference(replacementCoreEvidenceId);
        if (
            replacement.status != AVACoreTypes.EvidenceStatus.Active || replacement.appId != SparkV15.APP_ID
                || replacement.packageId != packageId || replacement.subjectId != evidence.sourceAuthorityId
                || replacement.disclosurePolicyId != evidence.disclosurePolicyId
                || replacement.evidenceTypeHash != evidenceType
        ) revert AVACoreTypes.InvalidState(replacementCoreEvidenceId);
    }
}
