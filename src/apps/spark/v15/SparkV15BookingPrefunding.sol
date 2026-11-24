// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACapabilityKeys} from "@ava-protocol/contracts/src/core/AVACapabilityKeys.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {IAVAEvidenceLifecycleModule} from "@ava-protocol/contracts/src/core/interfaces/IAVACoreRuleModules.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {COORDINATE_BOOKING_ACTION, SparkV15Booking, SparkV15BookingOpening} from "./SparkV15Booking.sol";
import {SparkV15Funds} from "./SparkV15Funds.sol";

/// @notice Adopts a draft when its actual verifier reserves its backing in Booking's existing funds.
contract SparkV15BookingPrefunding {
    bytes32 private constant DRAFT_TYPEHASH = keccak256(
        "AdoptOrdinaryBookingDraft(bytes32 formId,uint128 requiredUnits,bytes32 fundingRef,uint256 fundingEvidenceId,address verifier,uint64 validThrough)"
    );
    bytes32 private constant PROOF_TYPEHASH = keccak256(
        "PrefundingEvidence(uint256 packageId,bytes32 lessonId,bytes32 commitment,address verifier,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"
    );
    bytes32 public constant EVIDENCE_TYPE = keccak256("spark.v1.5.booking.verified-prefunding");
    bytes32 private constant TERMS_RECEIPT_TYPE = keccak256("spark.v1.5.booking.receipt");

    struct Proof {
        bytes32 sourceRole;
        bytes32 sourceAuthorityId;
        uint256 disclosurePolicyId;
        uint64 validThrough;
        bytes32 r;
        bytes32 vs;
    }

    struct AdoptedEvidence {
        bytes32 commitment;
        bytes32 sourceAuthorityId;
        uint256 disclosurePolicyId;
        AVACoreTypes.EvidenceStatus lifecycleStatus;
        uint256 replacementCoreEvidenceId;
    }

    enum CommitmentUse {
        AtomicAdoption,
        Acceptance,
        TutorAcceptance,
        Confirmation
    }

    SparkV15Booking public immutable BOOKING;
    AVAEvidenceRegistry private immutable EVIDENCE;
    mapping(bytes32 => AdoptedEvidence) private adopted;

    event PrefundingEvidenceAdopted(
        bytes32 indexed lessonId,
        uint256 indexed evidenceId,
        address indexed source,
        address verifier,
        bytes32 sourceAuthorityId,
        uint256 disclosurePolicyId,
        bytes32 commitment
    );
    event PrefundingEvidenceLifecycleRecorded(
        bytes32 indexed lessonId,
        uint256 indexed evidenceId,
        AVACoreTypes.EvidenceLifecycleKind indexed kind,
        uint256 replacementCoreEvidenceId,
        bytes32 reasonHash,
        bytes32 authorityId,
        address actor
    );

    mapping(bytes32 => mapping(address => AdoptedEvidence)) private standaloneTerms;

    event TermsEvidenceLifecycleRecorded(
        bytes32 indexed formId,
        address indexed recipient,
        AVACoreTypes.EvidenceLifecycleKind indexed kind,
        bytes32 commitment,
        uint256 replacementCoreEvidenceId,
        bytes32 reasonHash,
        bytes32 authorityId,
        address actor
    );

    constructor(SparkV15Booking booking) {
        BOOKING = booking;
        EVIDENCE = booking.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
    }

    /// @dev The old Opening entry forwards the actual verifier. The Core evidence remains authoritative.
    function adoptRegisteredDraft(
        SparkV15Booking.LessonTerms calldata lesson,
        SparkV15Booking.PlaceTerms calldata place,
        uint128 requiredUnits,
        bytes32 fundingRef,
        uint256 evidenceId,
        uint64 validThrough,
        bytes32 r,
        bytes32 vs,
        address verifier
    ) external returns (bytes32 formId) {
        SparkV15BookingOpening opening = BOOKING.OPENING();
        if (msg.sender != address(opening)) revert SparkV15Booking.UnauthorisedBookingActor();
        formId = _publishDraft(opening, lesson, place, verifier, validThrough);
        _requireDraftConsent(
            opening, lesson.coordinator, formId, requiredUnits, fundingRef, evidenceId, verifier, validThrough, r, vs
        );
        BOOKING.verifyDraftPrefunding(
            lesson.lessonId, _singleForm(formId), requiredUnits, fundingRef, evidenceId, verifier
        );
    }

    /// @notice First use of the signed funding proof, together with publication and actual vault reservation.
    /// @dev Both signers authorise this specific action. Neither signature records an earlier available proof.
    function adoptOrdinaryBookingDraftWithPrefundingProof(
        SparkV15Booking.LessonTerms calldata lesson,
        SparkV15Booking.PlaceTerms calldata place,
        uint128 requiredUnits,
        bytes32 fundingRef,
        uint64 draftValidThrough,
        bytes32 draftR,
        bytes32 draftVs,
        Proof calldata proof
    ) external returns (bytes32 formId) {
        SparkV15BookingOpening opening = BOOKING.OPENING();
        formId = _publishDraft(opening, lesson, place, msg.sender, draftValidThrough);
        bytes32[] memory forms = _singleForm(formId);
        bytes32 commitment = BOOKING.prefundingCommitment(lesson.lessonId, forms, requiredUnits, fundingRef);
        uint256 evidenceId = _adoptProof(opening, lesson, commitment, proof);
        _requireDraftConsent(
            opening,
            lesson.coordinator,
            formId,
            requiredUnits,
            fundingRef,
            evidenceId,
            msg.sender,
            draftValidThrough,
            draftR,
            draftVs
        );
        BOOKING.verifyDraftPrefunding(lesson.lessonId, forms, requiredUnits, fundingRef, evidenceId, msg.sender);
    }

    function _publishDraft(
        SparkV15BookingOpening opening,
        SparkV15Booking.LessonTerms calldata lesson,
        SparkV15Booking.PlaceTerms calldata place,
        address verifier,
        uint64 validThrough
    ) private returns (bytes32 formId) {
        if (lesson.coordinator == verifier) revert SparkV15Booking.UnauthorisedBookingActor();
        if (block.timestamp > validThrough || validThrough >= lesson.startsAt) {
            revert SparkV15Booking.InvalidEvidence();
        }
        if (
            lesson.rosterRef != bytes32(0) || lesson.materialsTermsRef != bytes32(0) || place.payableFee == 0
                || place.payableFee != place.normalFee || place.customerRepresentative != address(0)
        ) revert SparkV15Booking.InvalidForm();
        opening.requireBookingActor(lesson.coordinator, BOOKING.COORDINATOR_ROLE(), COORDINATE_BOOKING_ACTION);
        BOOKING.publishLesson(lesson);
        return BOOKING.publishForm(lesson.lessonId, place);
    }

    function _requireDraftConsent(
        SparkV15BookingOpening opening,
        address coordinator,
        bytes32 formId,
        uint128 requiredUnits,
        bytes32 fundingRef,
        uint256 evidenceId,
        address verifier,
        uint64 validThrough,
        bytes32 r,
        bytes32 vs
    ) private view {
        bytes32 message = keccak256(
            abi.encode(DRAFT_TYPEHASH, formId, requiredUnits, fundingRef, evidenceId, verifier, validThrough)
        );
        if (
            opening.recoverSource(keccak256("Spark DAO Booking Draft"), address(BOOKING), message, r, vs) != coordinator
        ) {
            revert SparkV15Booking.InvalidEvidence();
        }
    }

    function _adoptProof(
        SparkV15BookingOpening opening,
        SparkV15Booking.LessonTerms calldata lesson,
        bytes32 commitment,
        Proof calldata proof
    ) private returns (uint256 evidenceId) {
        if (block.timestamp > proof.validThrough) revert SparkV15Booking.InvalidEvidence();
        uint256 packageId = BOOKING.getLesson(lesson.lessonId).packageId;
        bytes32 message = keccak256(
            abi.encode(
                PROOF_TYPEHASH,
                packageId,
                lesson.lessonId,
                commitment,
                msg.sender,
                proof.sourceRole,
                proof.sourceAuthorityId,
                proof.disclosurePolicyId,
                proof.validThrough
            )
        );
        address source = opening.recoverSource(
            keccak256("Spark DAO Prefunding Evidence"), address(this), message, proof.r, proof.vs
        );
        if (source == msg.sender || source == lesson.coordinator || message == bytes32(0)) {
            revert SparkV15Booking.InvalidEvidence();
        }
        opening.requireFirstUseEvidenceSource(
            packageId, source, proof.sourceRole, proof.sourceAuthorityId, proof.disclosurePolicyId, EVIDENCE_TYPE, true
        );

        // Booking stores the exact reference and time. This record identifies its evidence
        // origin and supplies the commitment and metadata needed by the later consumers.
        evidenceId = uint256(message);
        AdoptedEvidence storage evidence = adopted[lesson.lessonId];
        evidence.commitment = commitment;
        evidence.sourceAuthorityId = proof.sourceAuthorityId;
        evidence.disclosurePolicyId = proof.disclosurePolicyId;
        emit PrefundingEvidenceAdopted(
            lesson.lessonId,
            evidenceId,
            source,
            msg.sender,
            proof.sourceAuthorityId,
            proof.disclosurePolicyId,
            commitment
        );
    }

    function _singleForm(bytes32 formId) private pure returns (bytes32[] memory forms) {
        forms = new bytes32[](1);
        forms[0] = formId;
    }

    /// @dev Initial Booking write. A local proof is staged by this module in the same transaction.
    function validateInitialCheck(
        bytes32 lessonId,
        bytes32[] calldata formIds,
        uint128 requiredUnits,
        bytes32 fundingRef,
        uint256 evidenceId,
        address verifier
    ) external view returns (bytes32 authorityId) {
        if (msg.sender != address(BOOKING)) revert SparkV15Booking.UnauthorisedBookingActor();
        SparkV15BookingOpening opening = BOOKING.OPENING();
        authorityId = opening.requireBookingActor(verifier, BOOKING.VERIFIER_ROLE(), BOOKING.ACTION_VERIFY_PREFUNDING());
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        uint64 cutoff = lesson.terms.rosterLockAt == 0 ? lesson.terms.startsAt : lesson.terms.rosterLockAt;
        if (
            lesson.packageId == 0 || lesson.prefunding.evidenceId != 0 || formIds.length == 0
                || (lesson.terms.rosterRef == bytes32(0) && formIds.length != 1) || requiredUnits == 0
                || fundingRef == bytes32(0) || block.timestamp >= cutoff
        ) revert SparkV15Booking.InvalidPrefunding();
        bytes32 commitment = BOOKING.prefundingCommitment(lessonId, formIds, requiredUnits, fundingRef);
        AdoptedEvidence storage evidence = adopted[lessonId];
        if (evidence.sourceAuthorityId == bytes32(0)) {
            opening.requireEvidence(lesson.packageId, evidenceId, commitment);
        } else if (evidence.commitment != commitment) {
            revert SparkV15Booking.InvalidEvidence();
        }
    }

    /// @notice Read the original proof. A later replacement does not change the binding of an assent.
    function requireAvailable(bytes32 lessonId, uint256 evidenceId, uint256 packageId) public view {
        AdoptedEvidence storage evidence = adopted[lessonId];
        if (evidence.sourceAuthorityId != bytes32(0)) {
            SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
            if (lesson.prefunding.evidenceId != evidenceId || lesson.packageId != packageId) {
                revert AVACoreTypes.InvalidState(evidenceId);
            }
        }
        _requireUsableProof(evidence, evidenceId, packageId);
    }

    function matchesRetainedBasis(bytes32 lessonId, uint256 evidenceId, uint256 packageId, bytes32 commitment)
        external
        view
        returns (bool)
    {
        requireAvailable(lessonId, evidenceId, packageId);
        AdoptedEvidence storage evidence = adopted[lessonId];
        bytes32 retainedCommitment = evidence.sourceAuthorityId == bytes32(0)
            ? EVIDENCE.getEvidenceReference(evidenceId).commitment
            : evidence.commitment;
        return retainedCommitment == commitment;
    }

    /// @dev Applies to separate agreement, assent and charge entries as well as signed ordinary confirmation.
    function requireCommitmentFunding(bytes32 lessonId, bytes32 formId) public view {
        _requireCommitmentFunding(lessonId, formId, BOOKING.getLesson(lessonId));
    }

    function _requireCommitmentFunding(bytes32 lessonId, bytes32 formId, SparkV15Booking.Lesson memory lesson)
        private
        view
    {
        SparkV15Funds funds = SparkV15Funds(address(BOOKING.FUNDS()));
        if (lesson.terms.materialsTermsRef != bytes32(0) && funds.materialBookingCoverage() != address(0)) {
            funds.requireCommitmentFunding(lessonId, formId);
            return;
        }
        uint256 evidenceId = lesson.prefunding.evidenceId;
        if (evidenceId == 0 || funds.lessonReserved(lessonId) < lesson.prefunding.reservedUnits) {
            revert SparkV15Booking.InvalidPrefunding();
        }
        _requireUsableProof(adopted[lessonId], evidenceId, lesson.packageId);
    }

    function requireFormCommitmentFunding(bytes32 lessonId, bytes32 formId, CommitmentUse use) external view {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        // Opening already checks both deliveries before the atomic adoption of signatures and funding use.
        if (use != CommitmentUse.AtomicAdoption) {
            SparkV15Booking.Form memory form = BOOKING.getForm(formId);
            address tutor = use == CommitmentUse.Acceptance ? address(0) : lesson.terms.tutor;
            _requireFormDelivery(formId, form.terms, lesson.packageId, tutor, use == CommitmentUse.Confirmation);
            // Booking has already rejected unfunded customer assents. The provider and payer can
            // still assent to a legacy non-material draft before its first funding check.
            if (
                use == CommitmentUse.Acceptance && lesson.prefunding.evidenceId == 0
                    && lesson.terms.materialsTermsRef == bytes32(0)
            ) return;
        }
        _requireCommitmentFunding(lessonId, formId, lesson);
    }

    function requireTeachingAgreementFunding(bytes32 lessonId, bool draftAdopted) external view {
        if (draftAdopted) {
            requireDraftAgreementDelivery(BOOKING.getPlannedForms(lessonId)[0], BOOKING.getLesson(lessonId).terms.tutor);
        }
        // A separate teaching agreement does not record the tutor's assent to the form.
        // Preserve its existing checks for adopted signed drafts and material lessons.
        if (adopted[lessonId].sourceAuthorityId != bytes32(0)) {
            requireCommitmentFunding(lessonId, bytes32(0));
        } else {
            BOOKING.FUNDS().requireCommitmentFunding(lessonId, bytes32(0));
        }
    }

    function requireDraftAgreementDelivery(bytes32 formId, address tutor) public view {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        uint256 packageId = BOOKING.getLesson(form.lessonId).packageId;
        _requireFormDelivery(formId, form.terms, packageId, tutor, false);
    }

    function _requireFormDelivery(
        bytes32 formId, SparkV15Booking.PlaceTerms memory place, uint256 packageId, address tutor, bool confirming
    ) private view {
        if (
            !hasUsableCustomerTerms(formId, place.customer, place.customerRepresentative, packageId)
                || (tutor != address(0) && !hasUsableTermsProvision(formId, tutor, packageId))
        ) {
            if (confirming) revert SparkV15Booking.InvalidConfirmation();
            revert SparkV15Booking.InvalidAcceptance();
        }
    }

    function hasUsableCustomerTerms(bytes32 formId, address customer, address representative, uint256 packageId)
        public
        view
        returns (bool)
    {
        return hasUsableTermsProvision(formId, customer, packageId)
            || (representative != address(0) && hasUsableTermsProvision(formId, representative, packageId));
    }

    /// @dev Booking checks the recorded coordinator, current form, recipient, and absence of an earlier delivery.
    function adoptStandaloneTermsProvision(
        uint256 packageId,
        bytes32 formId,
        address recipient,
        bytes32 deliveryRef,
        address coordinator,
        SparkV15Booking.TermsProvisionConsent calldata consent
    ) external returns (address source) {
        if (msg.sender != address(BOOKING)) revert SparkV15Booking.UnauthorisedBookingActor();
        source = BOOKING.OPENING().requireTermsProvisionConsent(packageId, formId, recipient, deliveryRef, coordinator, consent);
        AdoptedEvidence storage evidence = standaloneTerms[formId][recipient];
        evidence.commitment = BOOKING.provisionCommitment(formId, recipient, deliveryRef);
        evidence.sourceAuthorityId = consent.sourceAuthorityId;
        evidence.disclosurePolicyId = consent.disclosurePolicyId;
    }

    function hasStandaloneTermsProvision(bytes32 formId, address recipient) external view returns (bool) {
        return standaloneTerms[formId][recipient].sourceAuthorityId != bytes32(0);
    }

    function getStandaloneTermsEvidence(bytes32 formId, address recipient)
        external
        view
        returns (AdoptedEvidence memory evidence)
    {
        evidence = standaloneTerms[formId][recipient];
        if (evidence.sourceAuthorityId != bytes32(0) && evidence.lifecycleStatus == AVACoreTypes.EvidenceStatus.None) {
            evidence.lifecycleStatus = AVACoreTypes.EvidenceStatus.Active;
        }
    }

    /// @notice Retain the original signed delivery and record which evidence can be used in later decisions.
    function recordTermsEvidenceLifecycle(
        bytes32 formId,
        address recipient,
        bytes32 role,
        bytes32 authorityId,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementCoreEvidenceId,
        bytes32 reasonHash
    ) external {
        AdoptedEvidence storage evidence = standaloneTerms[formId][recipient];
        if (
            evidence.sourceAuthorityId == bytes32(0) || evidence.lifecycleStatus != AVACoreTypes.EvidenceStatus.None
                || reasonHash == bytes32(0) || kind == AVACoreTypes.EvidenceLifecycleKind.None
        ) revert SparkV15Booking.InvalidEvidence();
        EVIDENCE.AUTHORITY_MATRIX().requireAuthorisedSubject(
            msg.sender, SparkV15.APP_ID, role, AVACoreTypes.ACTION_RECORD_EVIDENCE_LIFECYCLE, authorityId
        );
        uint256 packageId = _termsPackage(formId);
        AVACoreTypes.EvidenceStatus status;
        if (kind == AVACoreTypes.EvidenceLifecycleKind.Supersede) {
            AVAEvidenceRegistry.EvidenceReference memory replacement = EVIDENCE.getEvidenceReference(replacementCoreEvidenceId);
            if (
                replacement.status != AVACoreTypes.EvidenceStatus.Active || replacement.packageId != packageId
                    || replacement.appId != SparkV15.APP_ID || replacement.evidenceTypeHash != TERMS_RECEIPT_TYPE
                    || replacement.subjectId != evidence.sourceAuthorityId
                    || replacement.disclosurePolicyId != evidence.disclosurePolicyId
                    || replacement.commitment != evidence.commitment || EVIDENCE.isCorrectionEvidence(replacementCoreEvidenceId)
            ) revert SparkV15Booking.InvalidEvidence();
            status = AVACoreTypes.EvidenceStatus.Superseded;
        } else {
            if (replacementCoreEvidenceId != 0) revert SparkV15Booking.InvalidEvidence();
            status = kind == AVACoreTypes.EvidenceLifecycleKind.Revoke
                ? AVACoreTypes.EvidenceStatus.Revoked
                : AVACoreTypes.EvidenceStatus.Expired;
        }
        IAVAEvidenceLifecycleModule(EVIDENCE.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_LIFECYCLE))
            .validateEvidenceLifecycle(IAVAEvidenceLifecycleModule.EvidenceLifecycleContext({
                appId: SparkV15.APP_ID,
                workflowKey: BOOKING.WORKFLOW(),
                packageId: packageId,
                evidenceId: uint256(evidence.commitment),
                evidenceTypeHash: TERMS_RECEIPT_TYPE,
                subjectId: evidence.sourceAuthorityId,
                disclosurePolicyId: evidence.disclosurePolicyId,
                fromStatus: AVACoreTypes.EvidenceStatus.Active,
                toStatus: status,
                kind: kind,
                replacementEvidenceId: replacementCoreEvidenceId,
                roleKey: role,
                authorityId: authorityId,
                reasonHash: reasonHash,
                actor: msg.sender
            }));
        evidence.lifecycleStatus = status;
        evidence.replacementCoreEvidenceId = replacementCoreEvidenceId;
        emit TermsEvidenceLifecycleRecorded(
            formId, recipient, kind, evidence.commitment, replacementCoreEvidenceId, reasonHash, authorityId, msg.sender
        );
    }

    function hasUsableTermsProvision(bytes32 formId, address recipient, uint256 packageId) public view returns (bool) {
        uint256 evidenceId = BOOKING.termsProvisionEvidence(formId, recipient);
        if (evidenceId != 0) return _hasUsableCoreTermsProvision(evidenceId, packageId);
        // The paired receipts were adopted in the same transaction as the binding agreements and debit.
        if (BOOKING.OPENING().adoptedTermsProvision(formId, recipient)) return true;
        AdoptedEvidence storage evidence = standaloneTerms[formId][recipient];
        if (evidence.sourceAuthorityId == bytes32(0) || packageId != _termsPackage(formId)) return false;
        if (evidence.lifecycleStatus == AVACoreTypes.EvidenceStatus.None) {
            EVIDENCE.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_POLICY);
            return EVIDENCE.IDENTITY_REGISTRY().getSubjectContext(evidence.sourceAuthorityId).active;
        }
        evidenceId = evidence.replacementCoreEvidenceId;
        return evidenceId != 0 && _hasUsableCoreTermsProvision(evidenceId, packageId);
    }

    function _termsPackage(bytes32 formId) private view returns (uint256) {
        return BOOKING.getLesson(BOOKING.getForm(formId).lessonId).packageId;
    }

    function _hasUsableCoreTermsProvision(uint256 evidenceId, uint256 packageId) private view returns (bool) {
        if (EVIDENCE.isEvidenceAvailableForPackage(evidenceId, packageId)) return true;

        AVAEvidenceRegistry.EvidenceReference memory delivery = EVIDENCE.getEvidenceReference(evidenceId);
        bytes32 commitment = delivery.commitment;
        while (delivery.replacementEvidenceId != 0) {
            evidenceId = delivery.replacementEvidenceId;
            delivery = EVIDENCE.getEvidenceReference(evidenceId);
            // Core links require an active successor and leave each predecessor inactive.
            if (delivery.commitment != commitment || EVIDENCE.isCorrectionEvidence(evidenceId)) return false;
            if (EVIDENCE.isEvidenceAvailableForPackage(evidenceId, packageId)) return true;
        }
        return false;
    }

    function _requireUsableProof(AdoptedEvidence storage evidence, uint256 evidenceId, uint256 packageId) private view {
        if (evidence.sourceAuthorityId == bytes32(0)) {
            EVIDENCE.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
            return;
        }
        if (evidenceId == 0 || evidence.lifecycleStatus != AVACoreTypes.EvidenceStatus.None) {
            revert AVACoreTypes.InvalidState(evidenceId);
        }
        // Admission checked the default evidence policy. Keep the Core package identity check on use.
        EVIDENCE.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_POLICY);
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
        AdoptedEvidence storage evidence = adopted[lessonId];
        if (evidence.sourceAuthorityId == bytes32(0)) return (0, bytes32(0), 0, AVACoreTypes.EvidenceStatus.None, 0);
        status = evidence.lifecycleStatus;
        if (status == AVACoreTypes.EvidenceStatus.None) status = AVACoreTypes.EvidenceStatus.Active;
        return (
            BOOKING.getLesson(lessonId).prefunding.evidenceId,
            evidence.sourceAuthorityId,
            evidence.disclosurePolicyId,
            status,
            evidence.replacementCoreEvidenceId
        );
    }

    /// @notice Uses the existing evidence lifecycle authority for the app's adopted funding proof.
    function recordEvidenceLifecycle(
        bytes32 lessonId,
        bytes32 role,
        bytes32 authorityId,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementCoreEvidenceId,
        bytes32 reasonHash
    ) external {
        AdoptedEvidence storage evidence = adopted[lessonId];
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        uint256 evidenceId = lesson.prefunding.evidenceId;
        if (
            evidence.sourceAuthorityId == bytes32(0) || evidence.lifecycleStatus != AVACoreTypes.EvidenceStatus.None
                || reasonHash == bytes32(0) || kind == AVACoreTypes.EvidenceLifecycleKind.None
        ) revert AVACoreTypes.InvalidState(evidenceId);
        EVIDENCE.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, role, AVACoreTypes.ACTION_RECORD_EVIDENCE_LIFECYCLE, authorityId
            );
        EVIDENCE.RULE_PACKAGE_REGISTRY().getModule(lesson.packageId, AVACapabilityKeys.EVIDENCE_LIFECYCLE);
        if (kind == AVACoreTypes.EvidenceLifecycleKind.Supersede) {
            AVAEvidenceRegistry.EvidenceReference memory replacement =
                EVIDENCE.getEvidenceReference(replacementCoreEvidenceId);
            if (
                replacementCoreEvidenceId == evidenceId || replacement.status != AVACoreTypes.EvidenceStatus.Active
                    || replacement.appId != SparkV15.APP_ID || replacement.packageId != lesson.packageId
                    || replacement.subjectId != evidence.sourceAuthorityId
                    || replacement.disclosurePolicyId != evidence.disclosurePolicyId
                    || replacement.evidenceTypeHash != EVIDENCE_TYPE
            ) revert AVACoreTypes.InvalidState(replacementCoreEvidenceId);
            evidence.replacementCoreEvidenceId = replacementCoreEvidenceId;
            evidence.lifecycleStatus = AVACoreTypes.EvidenceStatus.Superseded;
        } else {
            if (replacementCoreEvidenceId != 0) revert AVACoreTypes.InvalidState(replacementCoreEvidenceId);
            evidence.lifecycleStatus = kind == AVACoreTypes.EvidenceLifecycleKind.Revoke
                ? AVACoreTypes.EvidenceStatus.Revoked
                : AVACoreTypes.EvidenceStatus.Expired;
        }
        emit PrefundingEvidenceLifecycleRecorded(
            lessonId, evidenceId, kind, replacementCoreEvidenceId, reasonHash, authorityId, msg.sender
        );
    }
}
