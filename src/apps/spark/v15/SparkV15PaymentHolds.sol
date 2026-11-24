// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {SparkV15Funds} from "./SparkV15Funds.sol";
import {SparkV15PaymentApprovalChecks} from "./SparkV15PaymentApprovalChecks.sol";
import {SparkV15Payments} from "./SparkV15Payments.sol";
import {SparkV15ConcernIntake, SparkV15ReviewContext} from "./SparkV15ReviewCases.sol";
import {SparkV15TemporaryHolds} from "./SparkV15TemporaryHolds.sol";

interface ISparkV15PaymentHoldsHost {
    function paymentHoldBasis(bytes32 obligationId) external view returns (SparkV15PaymentHolds.HoldBasis memory);
    function getObligation(bytes32 obligationId) external view returns (SparkV15Payments.Obligation memory);
    function FUNDS() external view returns (SparkV15Funds);
    function reviewCases() external view returns (address);
    function recordHoldMutation(bytes32 obligationId) external;
}

interface ISparkV15PaymentConcern {
    function isPaymentConcern(bytes32 caseId, bytes32 lessonId, bytes32 obligationId) external view returns (bool);
    function requireDisinterested(bytes32 caseId, address actor, uint64 atTime) external view;
    function INTAKE() external view returns (SparkV15ConcernIntake);
}

/// @notice Hold history and post-lift clocks for one Spark payment installation.
contract SparkV15PaymentHolds {
    struct HoldBasis {
        bytes32 lessonId;
        uint256 packageId;
        uint128 outstanding;
        uint64 executionDeadline;
        bool executionDeadlineExact;
        uint64 postLiftDeadline;
        uint64 postLiftPeriod;
        address settlementProposer;
        address settlementApprover;
        address originalApprover;
        uint256 version;
    }

    struct HoldTerms {
        bytes32 obligationId;
        bytes32 caseId;
        bytes32 noticeHash;
        uint64 reviewAt;
        uint256 expectedVersion;
    }

    struct FormalHold {
        HoldTerms terms;
        address reviewer;
        bytes32 authorityId;
        uint256 evidenceId;
        uint128 amount;
        uint64 imposedAt;
        uint64 liftedAt;
        address liftedBy;
        bytes32 liftAuthorityId;
        uint256 liftEvidenceId;
        bytes32 liftDisposition;
        bool completelyReleased;
    }

    struct Status {
        uint64 formalCoverageStartedAt;
        uint64 firstFullReleaseAt;
        uint64 postLiftCutoff;
        uint64 lastFullReleaseAt;
        uint256 postLiftClockEvidenceId;
        uint256 activeFormalHolds;
        bool active;
    }

    struct HoldHistory {
        uint64 formalCoverageStartedAt;
        uint64 firstFullReleaseAt;
        uint64 postLiftCutoff;
        uint64 lastFullReleaseAt;
        uint256 postLiftClockEvidenceId;
        uint256 activeFormalHolds;
        uint64 lastFormalLift;
        bool coveredOriginalDeadline;
        bool unresolvedOriginalBoundary;
    }

    struct TemporaryHoldDeadlines {
        uint64 expiresAt;
        uint64 handoffDeadline;
        uint256 evidenceId;
    }

    error NotPayments();
    error InvalidFormalHold();
    error InvalidTemporaryHold();
    error InvalidClockEvidence();

    event TemporaryHoldDeadlinesRecorded(bytes32 indexed termsId, uint256 indexed evidenceId);

    ISparkV15PaymentHoldsHost public immutable PAYMENTS;
    SparkV15TemporaryHolds public immutable TEMPORARY_HOLDS;
    SparkV15PaymentApprovalChecks public immutable APPROVAL_CHECKS;
    AVARequestAllocation public immutable REQUEST_ALLOCATION;
    bytes32 public immutable WORKFLOW;
    bytes32 public immutable VERIFIER_ROLE;

    mapping(bytes32 => FormalHold) private formalHolds;
    mapping(bytes32 => HoldHistory) private holdHistories;
    mapping(bytes32 => TemporaryHoldDeadlines) public temporaryHoldDeadlines;

    constructor(address payments, AVARequestAllocation requests, bytes32 workflow, bytes32 verifierRole) {
        PAYMENTS = ISparkV15PaymentHoldsHost(payments);
        REQUEST_ALLOCATION = requests;
        WORKFLOW = workflow;
        VERIFIER_ROLE = verifierRole;
        TEMPORARY_HOLDS = new SparkV15TemporaryHolds(address(this));
        APPROVAL_CHECKS = new SparkV15PaymentApprovalChecks(requests, workflow);
    }

    modifier onlyPayments() {
        if (msg.sender != address(PAYMENTS)) revert NotPayments();
        _;
    }

    function formalHoldCommitment(HoldTerms calldata terms, address reviewer) public view returns (bytes32) {
        return
            keccak256(
                abi.encode(keccak256("spark.v1.5.formal-hold"), block.chainid, address(PAYMENTS), terms, reviewer)
            );
    }

    /// @notice Commitment to the two dates verified from the original form in the published terms.
    function temporaryHoldDeadlinesCommitment(bytes32 termsId, uint64 expiresAt, uint64 handoffDeadline)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.temporary-hold-deadlines"),
                block.chainid,
                address(PAYMENTS),
                termsId,
                expiresAt,
                handoffDeadline
            )
        );
    }

    /// @notice Publish verified dates for these immutable terms. Submission does not confer authority to set them.
    function recordTemporaryHoldDeadlines(bytes32 termsId, uint64 expiresAt, uint64 handoffDeadline, uint256 evidenceId)
        external
    {
        ISparkV15PaymentConcern source = ISparkV15PaymentConcern(PAYMENTS.reviewCases());
        if (address(source) == address(0)) revert InvalidTemporaryHold();
        SparkV15ReviewContext.PublishedContacts memory publication = source.INTAKE().getPublishedContacts(termsId);
        if (
            publication.terms.governingForm == bytes32(0) || expiresAt == 0 || handoffDeadline == 0
                || !_matchesEvidence(
                    evidenceId,
                    publication.packageId,
                    temporaryHoldDeadlinesCommitment(termsId, expiresAt, handoffDeadline)
                )
        ) revert InvalidTemporaryHold();

        AVAEvidenceRegistry registry = REQUEST_ALLOCATION.EVIDENCE_REGISTRY();
        TemporaryHoldDeadlines storage recorded = temporaryHoldDeadlines[termsId];
        if (
            recorded.evidenceId != 0
                && (recorded.expiresAt != expiresAt || recorded.handoffDeadline != handoffDeadline
                    || registry.isEvidenceAvailableForPackage(recorded.evidenceId, publication.packageId))
        ) revert InvalidTemporaryHold();
        bytes32 publicationAuthority = registry.getEvidenceReference(publication.evidenceId).authorityId;
        bytes32 sourceAuthority = registry.getEvidenceReference(evidenceId).authorityId;
        if (
            registry.IDENTITY_REGISTRY().getSubjectContext(sourceAuthority).roleKey
                != registry.IDENTITY_REGISTRY().getSubjectContext(publicationAuthority).roleKey
        ) revert InvalidTemporaryHold();
        if (recorded.evidenceId == 0) {
            recorded.expiresAt = expiresAt;
            recorded.handoffDeadline = handoffDeadline;
        }
        recorded.evidenceId = evidenceId;
        emit TemporaryHoldDeadlinesRecorded(termsId, evidenceId);
    }

    /// @notice Evidence binds the named contact, prior case authority, immediate notice and hold scope.
    function temporaryHoldCommitment(SparkV15TemporaryHolds.Terms calldata terms, address contact)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(keccak256("spark.v1.5.temporary-hold"), block.chainid, address(PAYMENTS), terms, contact)
        );
    }

    function imposeTemporaryHold(
        SparkV15TemporaryHolds.Terms calldata terms,
        uint256 evidenceId,
        bytes32 authorityId,
        address actor
    ) external onlyPayments returns (bytes32 holdId) {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                actor, SparkV15.APP_ID, SparkV15.ALTERNATIVE_CONTACT_ROLE, SparkV15.ACTION_TEMPORARY_HOLD, authorityId
            );
        bytes32 obligationId = terms.obligationId;
        HoldBasis memory basis = PAYMENTS.paymentHoldBasis(obligationId);
        ISparkV15PaymentConcern source = _paymentConcern(terms.caseId, basis.lessonId, obligationId, true);
        if (address(source) != address(0)) {
            SparkV15ConcernIntake intake = source.INTAKE();
            bytes32 termsId = intake.caseContext(terms.caseId).termsId;
            SparkV15ReviewContext.PublishedContacts memory publication = intake.getPublishedContacts(termsId);
            TemporaryHoldDeadlines storage deadlines = temporaryHoldDeadlines[termsId];
            if (
                publication.terms.alternativeContact != actor || deadlines.expiresAt != terms.expiresAt
                    || !REQUEST_ALLOCATION.EVIDENCE_REGISTRY()
                        .isEvidenceAvailableForPackage(deadlines.evidenceId, publication.packageId)
            ) revert InvalidTemporaryHold();
        }
        holdId = keccak256(abi.encode("temporary", obligationId, terms.caseId, terms.expectedVersion));
        if (
            basis.packageId == 0 || basis.version != terms.expectedVersion || terms.caseId == bytes32(0)
                || terms.noticeHash == bytes32(0) || terms.authorisedAt == 0 || terms.authorisedAt >= block.timestamp
                || terms.expiresAt <= block.timestamp || basis.outstanding == 0
                || !_matchesEvidence(evidenceId, basis.packageId, temporaryHoldCommitment(terms, actor))
        ) revert InvalidTemporaryHold();
        _requirePaymentDisinterest(source, terms.caseId, obligationId, basis.outstanding, actor);

        _recordReleaseIfUnheld(obligationId, holdHistories[obligationId], basis);
        TEMPORARY_HOLDS.record(
            holdId,
            basis.lessonId,
            SparkV15TemporaryHolds.Hold(
                terms, actor, authorityId, evidenceId, basis.outstanding, uint64(block.timestamp), bytes32(0)
            )
        );
        PAYMENTS.recordHoldMutation(obligationId);
    }

    function imposeFormalHold(HoldTerms calldata terms, uint256 evidenceId, bytes32 authorityId, address actor)
        external
        onlyPayments
        returns (bytes32 holdId)
    {
        bytes32 obligationId = terms.obligationId;
        HoldBasis memory basis = PAYMENTS.paymentHoldBasis(obligationId);
        ISparkV15PaymentConcern source = _paymentConcern(terms.caseId, basis.lessonId, obligationId, true);
        _requireIndependentReviewer(basis, terms.caseId, SparkV15.ACTION_FORMAL_HOLD, authorityId, actor);
        holdId = keccak256(abi.encode("formal", obligationId, terms.caseId, terms.expectedVersion));
        if (
            basis.version != terms.expectedVersion || terms.caseId == bytes32(0) || terms.noticeHash == bytes32(0)
                || terms.reviewAt < block.timestamp || basis.outstanding == 0
                || !_matchesEvidence(evidenceId, basis.packageId, formalHoldCommitment(terms, actor))
        ) revert InvalidFormalHold();
        _requirePaymentDisinterest(source, terms.caseId, obligationId, basis.outstanding, actor);

        HoldHistory storage history = holdHistories[obligationId];
        _recordReleaseIfUnheld(obligationId, history, basis);
        uint64 nowAt = uint64(block.timestamp);
        if (history.activeFormalHolds == 0) history.formalCoverageStartedAt = nowAt;
        ++history.activeFormalHolds;
        PAYMENTS.recordHoldMutation(obligationId);
        TEMPORARY_HOLDS.replace(obligationId, terms.caseId, holdId);
        formalHolds[holdId] = FormalHold({
            terms: terms,
            reviewer: actor,
            authorityId: authorityId,
            evidenceId: evidenceId,
            amount: basis.outstanding,
            imposedAt: nowAt,
            liftedAt: 0,
            liftedBy: address(0),
            liftAuthorityId: bytes32(0),
            liftEvidenceId: 0,
            liftDisposition: bytes32(0),
            completelyReleased: false
        });
    }

    function formalLiftCommitment(bytes32 holdId, bytes32 disposition, uint256 expectedVersion, address reviewer)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.formal-lift"),
                block.chainid,
                address(PAYMENTS),
                holdId,
                disposition,
                expectedVersion,
                reviewer
            )
        );
    }

    function liftFormalHold(
        bytes32 holdId,
        bytes32 disposition,
        uint256 expectedVersion,
        uint256 evidenceId,
        bytes32 authorityId,
        address actor
    ) external onlyPayments returns (bytes32 obligationId) {
        FormalHold storage hold = formalHolds[holdId];
        obligationId = hold.terms.obligationId;
        HoldBasis memory basis = PAYMENTS.paymentHoldBasis(obligationId);
        _requireIndependentReviewer(basis, hold.terms.caseId, SparkV15.ACTION_LIFT_HOLD, authorityId, actor);
        if (
            hold.reviewer == address(0) || hold.liftedBy != address(0) || basis.version != expectedVersion
                || block.timestamp <= hold.imposedAt || disposition == bytes32(0)
                || !_matchesEvidence(
                    evidenceId, basis.packageId, formalLiftCommitment(holdId, disposition, expectedVersion, actor)
                )
        ) revert InvalidFormalHold();
        // Holds recorded without ReviewCases can still be lifted after it is bound.
        ISparkV15PaymentConcern source = _paymentConcern(hold.terms.caseId, basis.lessonId, obligationId, false);
        _requirePaymentDisinterest(source, hold.terms.caseId, obligationId, basis.outstanding, actor);

        uint64 nowAt = uint64(block.timestamp);
        hold.liftedAt = nowAt;
        hold.liftedBy = actor;
        hold.liftAuthorityId = authorityId;
        hold.liftEvidenceId = evidenceId;
        hold.liftDisposition = disposition;
        HoldHistory storage history = holdHistories[obligationId];
        --history.activeFormalHolds;
        PAYMENTS.recordHoldMutation(obligationId);
        if (history.activeFormalHolds == 0) {
            history.lastFormalLift = nowAt;
            uint64 deadline = basis.executionDeadline;
            if (
                !basis.executionDeadlineExact && history.formalCoverageStartedAt <= deadline
                    && (history.formalCoverageStartedAt == deadline || nowAt == deadline)
            ) history.unresolvedOriginalBoundary = true;
            if (
                nowAt > deadline
                    && (history.formalCoverageStartedAt < deadline
                        || (history.formalCoverageStartedAt == deadline && basis.executionDeadlineExact))
            ) {
                history.coveredOriginalDeadline = true;
            }
            hold.completelyReleased = _recordReleaseIfUnheld(obligationId, history, basis);
            history.formalCoverageStartedAt = 0;
        }
    }

    /// @notice The release anchors the verified elapsed deadline. Without evidence, its boundary second is uncertain.
    function postLiftClockCommitment(bytes32 obligationId) external view returns (bytes32) {
        HoldBasis memory basis = PAYMENTS.paymentHoldBasis(obligationId);
        HoldHistory storage history = holdHistories[obligationId];
        uint64 releasedAt = _elapsedRelease(history, TEMPORARY_HOLDS.latestExpiry(obligationId));
        (uint64 firstReleaseAt, uint64 cutoff) = _firstReleaseClock(history, releasedAt, basis);
        return _clockCommitment(obligationId, firstReleaseAt, basis.postLiftPeriod, cutoff);
    }

    function verifyPostLiftClock(bytes32 obligationId, uint256 evidenceId, bytes32 authorityId, address actor)
        external
        onlyPayments
        returns (uint64 releaseAt, uint64 cutoff)
    {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                actor, SparkV15.APP_ID, VERIFIER_ROLE, SparkV15.ACTION_VERIFY_POST_LIFT_CLOCK, authorityId
            );
        HoldBasis memory basis = PAYMENTS.paymentHoldBasis(obligationId);
        HoldHistory storage history = holdHistories[obligationId];
        _recordReleaseIfUnheld(obligationId, history, basis);
        releaseAt = history.firstFullReleaseAt;
        cutoff = history.postLiftCutoff;
        if (
            releaseAt == 0 || basis.postLiftPeriod == 0 || history.postLiftClockEvidenceId != 0
                || !_matchesEvidence(
                    evidenceId, basis.packageId, _clockCommitment(obligationId, releaseAt, basis.postLiftPeriod, cutoff)
                )
        ) revert InvalidClockEvidence();

        history.postLiftClockEvidenceId = evidenceId;
        PAYMENTS.recordHoldMutation(obligationId);
    }

    function getFormalHold(bytes32 id) external view returns (FormalHold memory) {
        return formalHolds[id];
    }

    function heldReviewStartedAt(bytes32 caseId, bytes32 obligationId, bytes32 holdId, uint64 observedAt)
        external
        view
        returns (uint64)
    {
        FormalHold storage hold = formalHolds[holdId];
        if (
            hold.terms.caseId != caseId || hold.terms.obligationId != obligationId
                || (hold.liftedAt != 0 && hold.liftedAt <= observedAt)
        ) revert SparkV15ReviewContext.InvalidCase();
        return hold.imposedAt;
    }

    function getTemporaryHold(bytes32 id) external view returns (SparkV15TemporaryHolds.Hold memory) {
        return TEMPORARY_HOLDS.get(id);
    }

    function temporarySetterFor(bytes32 lessonId, bytes32 caseId, address actor) public view returns (bool) {
        return TEMPORARY_HOLDS.setterFor(lessonId, caseId, actor);
    }

    function getStatus(bytes32 obligationId) public view returns (Status memory status) {
        HoldHistory storage history = holdHistories[obligationId];
        uint64 expiry = TEMPORARY_HOLDS.latestExpiry(obligationId);
        status = _storedStatus(history, expiry);
        uint64 releasedAt = _elapsedRelease(history, expiry);
        if (releasedAt != 0) {
            status.lastFullReleaseAt = releasedAt;
            HoldBasis memory basis = PAYMENTS.paymentHoldBasis(obligationId);
            (status.firstFullReleaseAt, status.postLiftCutoff) = _firstReleaseClock(history, releasedAt, basis);
        }
    }

    /// @notice Distinguish original deadline coverage from a hold first imposed after that deadline.
    function takeoverClock(bytes32 obligationId) external view returns (Status memory status, bool ordinaryBlocked) {
        status = getStatus(obligationId);
        HoldHistory storage history = holdHistories[obligationId];
        ordinaryBlocked = history.unresolvedOriginalBoundary || history.coveredOriginalDeadline
            || (history.activeFormalHolds != 0
                && history.formalCoverageStartedAt <= PAYMENTS.paymentHoldBasis(obligationId).executionDeadline);
    }

    /// @dev Expiry may establish a release between transactions. Record it without changing the obligation version.
    function syncStatus(bytes32 obligationId) external onlyPayments returns (Status memory) {
        HoldHistory storage history = holdHistories[obligationId];
        uint64 expiry = TEMPORARY_HOLDS.latestExpiry(obligationId);
        uint64 releasedAt = _elapsedRelease(history, expiry);
        if (releasedAt != 0) _recordRelease(history, releasedAt, PAYMENTS.paymentHoldBasis(obligationId));
        return _storedStatus(history, expiry);
    }

    function _matchesEvidence(uint256 evidenceId, uint256 packageId, bytes32 commitment) private view returns (bool) {
        AVAEvidenceRegistry registry = REQUEST_ALLOCATION.EVIDENCE_REGISTRY();
        (bytes32 appId, bytes32 workflowKey,,,) =
            registry.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        return appId == SparkV15.APP_ID && workflowKey == WORKFLOW
            && registry.getEvidenceReference(evidenceId).commitment == commitment;
    }

    function _requireIndependentReviewer(
        HoldBasis memory basis,
        bytes32 caseId,
        bytes32 action,
        bytes32 authorityId,
        address actor
    ) private view {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(actor, SparkV15.APP_ID, VERIFIER_ROLE, action, authorityId);
        if (
            basis.packageId == 0 || actor == basis.settlementProposer || actor == basis.settlementApprover
                || actor == basis.originalApprover || temporarySetterFor(basis.lessonId, caseId, actor)
        ) revert InvalidFormalHold();
    }

    function _paymentConcern(bytes32 caseId, bytes32 lessonId, bytes32 obligationId, bool newHold)
        private
        view
        returns (ISparkV15PaymentConcern source)
    {
        source = ISparkV15PaymentConcern(PAYMENTS.reviewCases());
        if (address(source) != address(0) && !source.isPaymentConcern(caseId, lessonId, obligationId)) {
            if (newHold) revert InvalidFormalHold();
            SparkV15ReviewContext.ConcernContext memory retained = source.INTAKE().caseContext(caseId);
            if (retained.termsId == bytes32(0) || retained.lessonId != lessonId || retained.obligationId != obligationId) {
                return ISparkV15PaymentConcern(address(0));
            }
        }
    }

    function _requirePaymentDisinterest(
        ISparkV15PaymentConcern source,
        bytes32 caseId,
        bytes32 obligationId,
        uint128 outstanding,
        address actor
    ) private view {
        if (address(source) != address(0)) {
            source.requireDisinterested(caseId, actor, uint64(block.timestamp));
        }

        SparkV15Payments.Obligation memory payment = PAYMENTS.getObligation(obligationId);
        bytes32 debitAccount = payment.terms.originalDebitAccount;
        if (
            outstanding != 0
                && (debitAccount == bytes32(0)
                        ? payment.beneficiary == actor
                        : PAYMENTS.FUNDS().creditAccount(actor) == debitAccount)
        ) {
            revert SparkV15ReviewContext.ConflictedCaseActor();
        }
        // A predecessor hold can still delay an assigned share after the original amount is rebased.
        if (debitAccount == bytes32(0) && payment.terms.agreedStart == 0 && address(source) != address(0)) {
            source.INTAKE().requireMaterialCaseDisinterest(caseId, actor);
        }
    }

    function _storedStatus(HoldHistory storage history, uint64 expiry) private view returns (Status memory) {
        return Status(
            history.formalCoverageStartedAt,
            history.firstFullReleaseAt,
            history.postLiftCutoff,
            history.lastFullReleaseAt,
            history.postLiftClockEvidenceId,
            history.activeFormalHolds,
            history.activeFormalHolds != 0 || expiry > block.timestamp
        );
    }

    function _elapsedRelease(HoldHistory storage history, uint64 expiry) private view returns (uint64) {
        if (history.activeFormalHolds != 0 || history.lastFormalLift == 0) return 0;
        uint64 releasedAt = expiry > history.lastFormalLift ? expiry : history.lastFormalLift;
        return releasedAt <= block.timestamp ? releasedAt : 0;
    }

    function _recordReleaseIfUnheld(bytes32 obligationId, HoldHistory storage history, HoldBasis memory basis)
        private
        returns (bool)
    {
        uint64 releasedAt = _elapsedRelease(history, TEMPORARY_HOLDS.latestExpiry(obligationId));
        if (releasedAt == 0) return false;
        _recordRelease(history, releasedAt, basis);
        return true;
    }

    function _recordRelease(HoldHistory storage history, uint64 releasedAt, HoldBasis memory basis) private {
        history.lastFullReleaseAt = releasedAt;
        (history.firstFullReleaseAt, history.postLiftCutoff) = _firstReleaseClock(history, releasedAt, basis);
        delete history.lastFormalLift;
        delete history.coveredOriginalDeadline;
    }

    function _firstReleaseClock(HoldHistory storage history, uint64 releasedAt, HoldBasis memory basis)
        private
        view
        returns (uint64 releaseAt, uint64 cutoff)
    {
        if (history.firstFullReleaseAt == 0 && releasedAt != 0 && history.coveredOriginalDeadline) {
            return (releasedAt, basis.postLiftPeriod == 0 ? basis.postLiftDeadline : releasedAt + basis.postLiftPeriod);
        }
        return (history.firstFullReleaseAt, history.postLiftCutoff);
    }

    function _clockCommitment(bytes32 obligationId, uint64 releaseAt, uint64 period, uint64 cutoff)
        private
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.post-lift-clock"),
                block.chainid,
                address(PAYMENTS),
                obligationId,
                releaseAt,
                period,
                cutoff
            )
        );
    }
}
