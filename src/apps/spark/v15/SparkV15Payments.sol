// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {IERC20} from "../legacy/interfaces/IERC20.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {SparkV15Funds} from "./SparkV15Funds.sol";
import {SparkV15Returns} from "./SparkV15Returns.sol";
import {SparkV15TemporaryHolds} from "./SparkV15TemporaryHolds.sol";
import {SparkV15PaymentHolds} from "./SparkV15PaymentHolds.sol";
import {SparkV15Settlement} from "./SparkV15Settlement.sol";

interface ISparkV15AdoptedDispositions {
    function adoptedPaymentEffect(bytes32 caseId)
        external
        view
        returns (bytes32 obligationId, bytes32 outcome, uint64 adoptedAt);

    function isPaymentConcern(bytes32 caseId, bytes32 lessonId, bytes32 obligationId) external view returns (bool);
}

interface ISparkV15SettlementPaymentPolicy {
    function mayPaySettlementPart(bytes32 obligationId) external view returns (bool);
}

/// @notice Scoped approvals and actual payments for established Spark teaching obligations.
/// @dev Establishment and hold decisions accept verified evidence of the assessment, notice and case findings.
contract SparkV15Payments {
    struct PaymentTerms {
        bytes32 lessonId;
        bytes32 paymentPart;
        address recipient;
        bytes32 originalDebitAccount;
        uint128 originalDebitAmount;
        uint128 amount;
        uint64 agreedStart;
        uint64 dueAt;
        uint64 executionDeadline;
        uint64 legalDeadline;
        uint64 postLiftDeadline;
        uint64 postLiftPeriod;
        bool dueAtExact;
        bool executionDeadlineExact;
        bool legalDeadlineExact;
        bool postLiftDeadlineExact;
        address settlementProposer;
        address settlementApprover;
    }

    struct Obligation {
        PaymentTerms terms;
        uint256 packageId;
        uint256 evidenceId;
        bytes32 commitment;
        uint256 paid;
        uint256 version;
        uint256 firstApprovalRequestId;
        uint64 eligibleFrom;
        bool eligibilityExact;
        uint128 correctAmount;
        address beneficiary;
        address destination;
        uint64 beneficiaryVersion;
    }

    struct PaymentAdmission {
        uint256 evidenceId;
        uint256 packageId;
        uint64 eligibleFrom;
        bool eligibilityExact;
        address materialHolder;
    }

    struct ApprovalTerms {
        bytes32 obligationId;
        address executor;
        uint128 ceiling;
        uint64 validThrough;
        uint256 replacesRequestId;
    }

    struct Approval {
        ApprovalTerms terms;
        address approver;
        bytes32 authorityId;
        uint64 grantedAt;
        uint128 paid;
        uint64 stoppedAt;
        bytes32 stoppedByCase;
        uint64 beneficiaryVersion;
    }

    struct PaymentRevision {
        bytes32 obligationId;
        uint128 correctAmount;
        address beneficiary;
        address destination;
        uint256 expectedVersion;
    }

    struct PaymentReceipt {
        bytes32 obligationId;
        uint256 approvalRequestId;
        address executor;
        address recipient;
        bytes32 creditAccount;
        uint128 amount;
        uint128 approvedOutstandingBefore;
        uint64 paidAt;
        uint64 promptCutoff;
        bool promptCutoffMet;
    }

    struct ApprovalArrangement {
        uint256 originalRequestId;
        address arrangedBy;
        bytes32 authorityId;
        uint64 releasedAt;
        uint64 arrangedAt;
    }

    error InvalidObligation();
    error InsufficientFunds();
    error InvalidApproval();
    error InvalidFormalHold();
    error InvalidTemporaryHold();
    error InvalidClockEvidence();
    error InvalidReturn();
    error InvalidObservation();
    error PaymentNotAllowed();
    error TransferMismatch();

    event PaymentEstablished(bytes32 indexed obligationId, uint256 indexed evidenceId, uint128 amount);
    event PaymentApprovalRecorded(bytes32 indexed obligationId, uint256 indexed requestId, address indexed approver);
    event PaymentApprovalStopped(bytes32 indexed obligationId, uint256 indexed requestId, bytes32 indexed caseId);
    event PaymentRevised(bytes32 indexed obligationId, bytes32 indexed decisionRef, uint256 version, uint128 amount);
    event ReplacementArranged(
        bytes32 indexed obligationId, uint256 indexed requestId, uint256 indexed originalRequestId
    );
    event FormalHoldImposed(bytes32 indexed obligationId, bytes32 indexed holdId, uint256 indexed evidenceId);
    event FormalHoldLifted(bytes32 indexed obligationId, bytes32 indexed holdId, uint256 indexed evidenceId);
    event TemporaryHoldImposed(bytes32 indexed obligationId, bytes32 indexed holdId, uint256 indexed evidenceId);
    event PostLiftClockVerified(bytes32 indexed obligationId, uint64 releaseAt, uint64 cutoff, uint256 evidenceId);
    event PaymentReceived(
        bytes32 indexed obligationId,
        uint256 indexed requestId,
        uint256 indexed receiptId,
        address executor,
        address recipient,
        bytes32 creditAccount,
        uint128 amount
    );
    AVARequestAllocation public immutable REQUEST_ALLOCATION;
    IERC20 public immutable TOKEN;
    SparkV15Funds public immutable FUNDS;
    SparkV15Returns public immutable RETURNS;
    SparkV15PaymentHolds public HOLDS;
    bytes32 public immutable WORKFLOW;
    bytes32 public immutable VERIFIER_ROLE;
    bytes32 public constant ACTION_APPLY_CASE_EFFECT = keccak256("spark.action.apply-case-effect.v1.5");
    bytes32 public constant ACTION_RECORD_SETTLEMENT_OBLIGATION =
        keccak256("spark.action.record-settlement-obligation.v1.5");
    uint256 private constant ORDINARY_APPROVAL_ID_MASK = 1 << 255;
    ISparkV15AdoptedDispositions public reviewCases;
    address public paymentObservations;
    ISparkV15SettlementPaymentPolicy public settlementPolicy;

    uint256 private nextReceiptId = 1;
    mapping(bytes32 => Obligation) private obligations;
    mapping(uint256 => Approval) private approvals;
    mapping(uint256 => ApprovalArrangement) public approvalArrangements;
    mapping(uint256 => PaymentReceipt) private receipts;
    mapping(bytes32 => mapping(address => bool)) public recognisedBeneficiary;
    mapping(bytes32 => mapping(address => uint256)) private previousNetReceipts;
    mapping(bytes32 => bytes32[]) private lessonObligations;

    constructor(AVARequestAllocation requests, IERC20 token, bytes32 workflow, bytes32 verifierRole) {
        if (
            address(requests).code.length == 0 || address(token).code.length == 0 || workflow == bytes32(0)
                || verifierRole == bytes32(0)
        ) revert InvalidObligation();
        REQUEST_ALLOCATION = requests;
        TOKEN = token;
        WORKFLOW = workflow;
        VERIFIER_ROLE = verifierRole;
        FUNDS = new SparkV15Funds(requests, token, workflow, address(this));
        RETURNS = new SparkV15Returns(address(this), requests, verifierRole);
    }

    function paymentEvidenceCommitment(PaymentTerms calldata terms, bytes32 basis) public view returns (bytes32) {
        return
            keccak256(abi.encode(keccak256("spark.v1.5.payment.evidence"), block.chainid, address(this), terms, basis));
    }

    function establishPayment(PaymentTerms calldata terms, bytes32 basis, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 obligationId)
    {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, VERIFIER_ROLE, SparkV15.ACTION_ESTABLISH_PAYMENT, authorityId
            );
        uint256 packageId = REQUEST_ALLOCATION.RULE_PACKAGE_REGISTRY().getActivePackageId(SparkV15.APP_ID, WORKFLOW);
        return this.establishFromEntry(
            terms, basis, PaymentAdmission(evidenceId, packageId, terms.dueAt, terms.dueAtExact, address(0)), false
        );
    }

    function settlementRole() public view returns (bytes32) {
        return keccak256(abi.encode(keccak256("ava.spark.role.settlement-obligations.v1.5"), address(this)));
    }

    function establishSettledPayment(PaymentTerms calldata terms, bytes32 basis, uint256 evidenceId, uint256 packageId)
        external
        returns (bytes32)
    {
        _requireSettlementObligationAuthority();
        return this.establishFromEntry(
            terms, basis, PaymentAdmission(evidenceId, packageId, terms.dueAt, terms.dueAtExact, address(0)), false
        );
    }

    /// @notice The installed Settlement has verified explicit first-use evidence for this ordinary wage.
    function establishAdoptedWage(PaymentTerms calldata terms, bytes32 basis, uint256 packageId)
        external
        returns (bytes32)
    {
        if (msg.sender != address(settlementPolicy)) revert InvalidObligation();
        _requireSettlementObligationAuthority();
        return this.establishFromEntry(
            terms, basis, PaymentAdmission(0, packageId, terms.dueAt, terms.dueAtExact, address(0)), true
        );
    }

    function _requireSettlementObligationAuthority() private view {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                msg.sender, SparkV15.APP_ID, settlementRole(), ACTION_RECORD_SETTLEMENT_OBLIGATION
            );
    }

    function establishMaterialPayment(
        PaymentTerms calldata terms,
        bytes32 basis,
        uint256 evidenceId,
        uint256 packageId,
        uint64 eligibleFrom,
        address beneficiary
    ) external returns (bytes32) {
        if (msg.sender != FUNDS.materialProvisions() || beneficiary == address(0)) {
            revert InvalidObligation();
        }
        return this.establishFromEntry(
            terms, basis, PaymentAdmission(evidenceId, packageId, eligibleFrom, true, beneficiary), false
        );
    }

    /// @dev Keep one establishment body for the independently authorised entry points.
    function establishFromEntry(
        PaymentTerms calldata terms, bytes32 basis, PaymentAdmission calldata admission, bool adoptedWage
    ) external returns (bytes32 obligationId) {
        if (msg.sender != address(this)) revert InvalidObligation();
        obligationId = keccak256(abi.encode(terms.lessonId, terms.paymentPart));
        if (
            terms.lessonId == bytes32(0) || terms.paymentPart == bytes32(0) || terms.recipient == address(0)
                || terms.recipient == address(this) || terms.recipient == address(FUNDS) || terms.amount == 0
                || terms.dueAt > terms.executionDeadline || terms.settlementProposer == address(0)
                || terms.settlementApprover == address(0) || admission.eligibleFrom > terms.executionDeadline
                || (terms.legalDeadline != 0 && terms.legalDeadline < admission.eligibleFrom)
                || (terms.postLiftDeadline != 0 && terms.postLiftPeriod != 0)
                || (terms.postLiftDeadlineExact && terms.postLiftDeadline == 0)
                || (terms.legalDeadlineExact && terms.legalDeadline == 0) || basis == bytes32(0)
                || obligations[obligationId].packageId != 0
        ) revert InvalidObligation();
        if (admission.materialHolder != address(0)) {
            if (
                terms.originalDebitAccount != bytes32(0) || terms.originalDebitAmount != 0 || terms.agreedStart != 0
                    || admission.eligibleFrom == 0
            ) revert InvalidObligation();
        } else if (terms.originalDebitAccount == bytes32(0)) {
            uint256 ordinaryEarliest = uint256(terms.agreedStart) + 30 days;
            if (
                terms.originalDebitAmount != 0 || terms.agreedStart == 0
                    || (terms.dueAt < ordinaryEarliest
                        && (terms.legalDeadline == 0 || terms.legalDeadline >= ordinaryEarliest))
            ) revert InvalidObligation();
        } else if (terms.amount > terms.originalDebitAmount || terms.agreedStart != 0) {
            revert InvalidObligation();
        }
        if (admission.materialHolder != address(0)) {
            basis = keccak256(
                abi.encode(
                    keccak256("spark.v1.5.material-schedule"), basis, admission.eligibleFrom, admission.eligibilityExact
                )
            );
        }
        bytes32 commitment = paymentEvidenceCommitment(terms, basis);
        if (!adoptedWage && !RETURNS.matchesPaymentEvidence(admission.evidenceId, admission.packageId, commitment)) {
            revert InvalidObligation();
        }
        FUNDS.reservePayment(obligationId, terms.lessonId, terms.amount);

        Obligation storage item = obligations[obligationId];
        item.terms = terms;
        item.packageId = admission.packageId;
        item.evidenceId = admission.evidenceId;
        item.commitment = commitment;
        item.version = 1;
        item.eligibleFrom = admission.eligibleFrom;
        item.eligibilityExact = admission.eligibilityExact;
        item.correctAmount = terms.amount;
        address holder = admission.materialHolder == address(0) ? terms.recipient : admission.materialHolder;
        item.beneficiary = holder;
        item.destination = terms.recipient;
        recognisedBeneficiary[obligationId][holder] = true;
        lessonObligations[terms.lessonId].push(obligationId);
        emit PaymentEstablished(obligationId, admission.evidenceId, terms.amount);
    }

    function approvalParameters(ApprovalTerms calldata terms) public view returns (bytes32) {
        Obligation storage item = obligations[terms.obligationId];
        if (item.packageId == 0) revert InvalidObligation();
        return keccak256(
            abi.encode(keccak256("spark.v1.5.payment-approval"), terms, item.commitment, item.beneficiaryVersion)
        );
    }

    function recordReplacementArrangement(uint256 requestId, ApprovalTerms calldata terms) external {
        Obligation storage item = obligations[terms.obligationId];
        SparkV15PaymentHolds.Status memory hold = HOLDS.syncStatus(terms.obligationId);
        (bytes32 allocatorRole, bytes32 authorityId) = _allocatedFor(requestId, terms, item);
        Approval storage original = approvals[terms.replacesRequestId];
        if (
            !_inReleasedWindow(item, hold) || original.approver == address(0)
                || original.terms.obligationId != terms.obligationId
                || original.grantedAt > item.terms.executionDeadline
                || approvalArrangements[requestId].arrangedBy != address(0)
        ) revert InvalidApproval();
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, allocatorRole, AVACoreTypes.ACTION_RECORD_ALLOCATION, authorityId
            );
        REQUEST_ALLOCATION.validateExecution(
            requestId, SparkV15.RESPONSE_APPROVE_PAYMENT, approvalParameters(terms), address(this)
        );
        approvalArrangements[requestId] = ApprovalArrangement(
            terms.replacesRequestId, msg.sender, authorityId, hold.firstFullReleaseAt, uint64(block.timestamp)
        );
        emit ReplacementArranged(terms.obligationId, requestId, terms.replacesRequestId);
    }

    function recordApproval(uint256 requestId, ApprovalTerms calldata terms) external {
        Obligation storage item = obligations[terms.obligationId];
        SparkV15PaymentHolds.Status memory hold = HOLDS.syncStatus(terms.obligationId);
        (, bytes32 authorityId) = _allocatedFor(requestId, terms, item);
        if (_withinCutoff(item.terms.executionDeadline, item.terms.executionDeadlineExact)) {
            if (terms.replacesRequestId != 0) revert InvalidApproval();
        } else {
            if (hold.active || !_inReleasedWindow(item, hold)) revert InvalidApproval();
            if (terms.replacesRequestId == 0) {
                if (item.firstApprovalRequestId != 0) revert InvalidApproval();
            } else {
                ApprovalArrangement storage arrangement = approvalArrangements[requestId];
                if (
                    arrangement.originalRequestId != terms.replacesRequestId
                        || arrangement.releasedAt != hold.firstFullReleaseAt
                ) {
                    revert InvalidApproval();
                }
            }
        }
        REQUEST_ALLOCATION.consume(requestId, SparkV15.RESPONSE_APPROVE_PAYMENT, approvalParameters(terms), msg.sender);
        Approval memory approval = _newApproval(terms, item, authorityId);
        bytes32 effectHash = keccak256(abi.encode(address(this), requestId, approval));
        // Core holds the allocator authority for the lifetime of this request.
        approval.authorityId = bytes32(0);
        _saveApproval(requestId, item, approval);
        REQUEST_ALLOCATION.complete(requestId, effectHash);
        emit PaymentApprovalRecorded(terms.obligationId, requestId, msg.sender);
    }

    /// @notice Give a first payment approval for a straightforward, independently settled one-to-one wage.
    /// @dev The approved executor still pays through pay(), with the same funding, clocks and case effects.
    function grantOrdinaryWageApproval(ApprovalTerms calldata terms) external returns (uint256 approvalId) {
        Obligation storage item = obligations[terms.obligationId];
        // The original version still binds the original beneficiary and destination with no hold, revision, or grant.
        if (
            item.version != 1 || item.terms.legalDeadline != 0 || terms.replacesRequestId != 0
                || !_withinCutoff(item.terms.executionDeadline, item.terms.executionDeadlineExact)
                || !_validApprovalTerms(terms, item)
        ) revert InvalidApproval();
        approvalId = uint256(terms.obligationId) | ORDINARY_APPROVAL_ID_MASK;
        if (approvalId < REQUEST_ALLOCATION.nextRequestId() || approvals[approvalId].approver != address(0)) {
            revert InvalidApproval();
        }
        bytes32 authorityId = HOLDS.APPROVAL_CHECKS()
            .requireOrdinaryWageAuthority(
                SparkV15Settlement(address(settlementPolicy)),
                item.terms.lessonId,
                terms.obligationId,
                item.packageId,
                msg.sender
            );
        _saveApproval(approvalId, item, _newApproval(terms, item, authorityId));
        emit PaymentApprovalRecorded(terms.obligationId, approvalId, msg.sender);
    }

    function _newApproval(ApprovalTerms calldata terms, Obligation storage item, bytes32 authorityId)
        private
        view
        returns (Approval memory)
    {
        return Approval(
            terms, msg.sender, authorityId, uint64(block.timestamp), 0, 0, bytes32(0), item.beneficiaryVersion
        );
    }

    function _saveApproval(uint256 id, Obligation storage item, Approval memory approval) private {
        approvals[id] = approval;
        if (item.firstApprovalRequestId == 0) item.firstApprovalRequestId = id;
        ++item.version;
    }

    function caseEffectRole() public view returns (bytes32) {
        return keccak256(abi.encode(keccak256("ava.spark.role.case-effects.v1.5"), address(this)));
    }

    function bindReviewCases(ISparkV15AdoptedDispositions source) external {
        _requireApplicationAdmin();
        if (address(reviewCases) != address(0) || address(source).code.length == 0) revert InvalidApproval();
        reviewCases = source;
    }

    function bindHolds(SparkV15PaymentHolds holds) external {
        _requireApplicationAdmin();
        if (
            address(HOLDS) != address(0) || address(holds.PAYMENTS()) != address(this)
                || address(holds.REQUEST_ALLOCATION()) != address(REQUEST_ALLOCATION) || holds.WORKFLOW() != WORKFLOW
                || holds.VERIFIER_ROLE() != VERIFIER_ROLE
        ) revert InvalidFormalHold();
        HOLDS = holds;
    }

    function bindPaymentObservations(address observer) external {
        _requireApplicationAdmin();
        if (paymentObservations != address(0) || observer.code.length == 0) revert InvalidObservation();
        paymentObservations = observer;
    }

    function bindSettlementPolicy(ISparkV15SettlementPaymentPolicy policy) external {
        _requireApplicationAdmin();
        if (address(settlementPolicy) != address(0) || address(policy).code.length == 0) revert InvalidApproval();
        settlementPolicy = policy;
    }

    function _requireApplicationAdmin() private view {
        REQUEST_ALLOCATION.IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
    }

    function stopApprovalOutcome(bytes32 caseId, uint256 requestId) public view returns (bytes32) {
        Approval storage approval = approvals[requestId];
        if (approval.approver == address(0)) revert InvalidApproval();
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.stop-payment-approval"),
                block.chainid,
                address(this),
                caseId,
                requestId,
                approval.terms.obligationId,
                obligations[approval.terms.obligationId].commitment
            )
        );
    }

    function stopApproval(bytes32 caseId, uint256 requestId) external {
        Approval storage approval = approvals[requestId];
        bytes32 obligationId = approval.terms.obligationId;
        Obligation storage item = obligations[obligationId];
        if (approval.stoppedAt != 0) revert InvalidApproval();
        _requireAdoptedEffect(caseId, obligationId, stopApprovalOutcome(caseId, requestId));
        approval.stoppedAt = uint64(block.timestamp);
        approval.stoppedByCase = caseId;
        ++item.version;
        emit PaymentApprovalStopped(obligationId, requestId, caseId);
    }

    function applyPaymentRevision(bytes32 decisionRef, PaymentRevision calldata revision) external {
        bytes32 id = revision.obligationId;
        Obligation storage item = obligations[id];
        if (
            item.packageId == 0 || item.version != revision.expectedVersion || revision.beneficiary == address(0)
                || revision.destination == address(0) || revision.destination == address(this)
                || revision.destination == address(FUNDS)
                || (item.terms.originalDebitAccount != bytes32(0)
                    && (revision.beneficiary != item.beneficiary || revision.destination != item.destination))
        ) {
            revert InvalidObligation();
        }
        if (msg.sender == FUNDS.materialProvisions()) {
            if (
                !_isMaterial(item) || revision.beneficiary != item.beneficiary
                    || revision.destination != item.destination || decisionRef == bytes32(0)
            ) revert InvalidObligation();
        } else {
            _requireAdoptedEffect(
                decisionRef,
                id,
                SparkV15PaymentRevisionCommitment.hash(address(this), decisionRef, revision, item.commitment)
            );
        }
        if (revision.beneficiary != item.beneficiary || revision.destination != item.destination) {
            ++item.beneficiaryVersion;
        }
        if (revision.beneficiary != item.beneficiary) {
            previousNetReceipts[id][item.beneficiary] = item.paid;
            item.paid = previousNetReceipts[id][revision.beneficiary];
            item.beneficiary = revision.beneficiary;
            recognisedBeneficiary[id][revision.beneficiary] = true;
        }
        item.destination = revision.destination;
        item.correctAmount = revision.correctAmount;
        ++item.version;
        uint128 backing = FUNDS.paymentReserved(id);
        uint128 unpaid = _outstanding(item);
        if (backing > unpaid) FUNDS.releasePaymentBacking(id, backing - unpaid);
        emit PaymentRevised(id, decisionRef, item.version, revision.correctAmount);
    }

    function _requireAdoptedEffect(bytes32 caseId, bytes32 obligationId, bytes32 expectedOutcome) private view {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(msg.sender, SparkV15.APP_ID, caseEffectRole(), ACTION_APPLY_CASE_EFFECT);
        (bytes32 correctedObligation, bytes32 outcome, uint64 adoptedAt) =
            ISparkV15AdoptedDispositions(msg.sender).adoptedPaymentEffect(caseId);
        if (adoptedAt != block.timestamp || correctedObligation != obligationId || outcome != expectedOutcome) {
            revert InvalidApproval();
        }
    }

    function _allocatedFor(uint256 requestId, ApprovalTerms calldata terms, Obligation storage item)
        private
        view
        returns (bytes32 role, bytes32 authorityId)
    {
        (role, authorityId) = HOLDS.APPROVAL_CHECKS().requireAllocation(requestId, item.packageId, msg.sender);
        if (
            approvals[requestId].authorityId != bytes32(0) || !_validApprovalTerms(terms, item)
                || (_isMaterial(item) && msg.sender != item.terms.settlementApprover)
        ) revert InvalidApproval();
    }

    function _validApprovalTerms(ApprovalTerms calldata terms, Obligation storage item) private view returns (bool) {
        return terms.executor != address(0) && terms.ceiling > item.paid && terms.ceiling <= item.correctAmount
            && terms.validThrough >= block.timestamp;
    }

    function _inReleasedWindow(Obligation storage item, SparkV15PaymentHolds.Status memory hold)
        private
        view
        returns (bool)
    {
        return hold.firstFullReleaseAt != 0 && _withinCutoff(hold.postLiftCutoff, _postLiftCutoffIsExact(item, hold));
    }

    function imposeTemporaryHold(SparkV15TemporaryHolds.Terms calldata terms, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 holdId)
    {
        holdId = HOLDS.imposeTemporaryHold(terms, evidenceId, authorityId, msg.sender);
        emit TemporaryHoldImposed(terms.obligationId, holdId, evidenceId);
    }

    function imposeFormalHold(SparkV15PaymentHolds.HoldTerms calldata terms, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 holdId)
    {
        holdId = HOLDS.imposeFormalHold(terms, evidenceId, authorityId, msg.sender);
        emit FormalHoldImposed(terms.obligationId, holdId, evidenceId);
    }

    function liftFormalHold(
        bytes32 holdId,
        bytes32 disposition,
        uint256 expectedVersion,
        uint256 evidenceId,
        bytes32 authorityId
    ) external {
        bytes32 obligationId = HOLDS.liftFormalHold(
            holdId, disposition, expectedVersion, evidenceId, authorityId, msg.sender
        );
        emit FormalHoldLifted(obligationId, holdId, evidenceId);
    }

    function verifyPostLiftClock(bytes32 obligationId, uint256 evidenceId, bytes32 authorityId) external {
        (uint64 releaseAt, uint64 cutoff) = HOLDS.verifyPostLiftClock(obligationId, evidenceId, authorityId, msg.sender);
        emit PostLiftClockVerified(obligationId, releaseAt, cutoff, evidenceId);
    }

    function paymentHoldBasis(bytes32 obligationId) external view returns (SparkV15PaymentHolds.HoldBasis memory) {
        Obligation storage item = obligations[obligationId];
        PaymentTerms storage terms = item.terms;
        return SparkV15PaymentHolds.HoldBasis(
            terms.lessonId,
            item.packageId,
            _outstanding(item),
            terms.executionDeadline,
            terms.executionDeadlineExact,
            terms.postLiftDeadline,
            terms.postLiftPeriod,
            terms.settlementProposer,
            terms.settlementApprover,
            approvals[item.firstApprovalRequestId].approver,
            item.version
        );
    }

    function recordHoldMutation(bytes32 obligationId) external {
        if (msg.sender != address(HOLDS)) revert InvalidFormalHold();
        ++obligations[obligationId].version;
    }

    function temporarySetterFor(bytes32 lessonId, bytes32 caseId, address actor) external view returns (bool) {
        return HOLDS.temporarySetterFor(lessonId, caseId, actor);
    }

    function pay(uint256 requestId, uint128 amount) external returns (uint256 receiptId) {
        Approval storage approval = approvals[requestId];
        bytes32 obligationId = approval.terms.obligationId;
        Obligation storage item = obligations[obligationId];
        SparkV15PaymentHolds.Status memory hold = HOLDS.syncStatus(obligationId);
        PaymentTerms storage terms = item.terms;
        uint64 deadline = hold.firstFullReleaseAt == 0 ? terms.executionDeadline : hold.postLiftCutoff;
        bool deadlineExact =
            hold.firstFullReleaseAt == 0 ? terms.executionDeadlineExact : _postLiftCutoffIsExact(item, hold);
        uint128 remaining = _outstanding(item);
        uint128 remainingApproved = _scopeRemaining(approval, item.paid);
        if (
            approval.approver == address(0) || approval.stoppedAt != 0 || msg.sender != approval.terms.executor
                || approval.beneficiaryVersion != item.beneficiaryVersion || amount == 0 || hold.active
                || block.timestamp < item.eligibleFrom
                || (block.timestamp == item.eligibleFrom && !item.eligibilityExact)
                || !_withinCutoff(deadline, deadlineExact)
                || (terms.legalDeadline != 0 && !_withinCutoff(terms.legalDeadline, terms.legalDeadlineExact))
                || block.timestamp > approval.terms.validThrough || amount > remaining || amount > remainingApproved
        ) revert PaymentNotAllowed();
        ISparkV15SettlementPaymentPolicy policy = settlementPolicy;
        if (address(policy) != address(0) && !policy.mayPaySettlementPart(obligationId)) revert PaymentNotAllowed();
        if (approval.terms.replacesRequestId != 0) {
            Approval storage original = approvals[approval.terms.replacesRequestId];
            if (
                original.stoppedAt == 0 && original.beneficiaryVersion == item.beneficiaryVersion
                    && block.timestamp <= original.terms.validThrough && amount <= _scopeRemaining(original, item.paid)
            ) {
                revert PaymentNotAllowed();
            }
        }

        (uint64 promptCutoff, bool promptCutoffMet) = _promptCutoff(item, hold);
        item.paid += amount;
        approval.paid += amount;
        ++item.version;
        receiptId = nextReceiptId++;
        RETURNS.recordPayment(obligationId, receiptId, item.beneficiary);
        receipts[receiptId] = PaymentReceipt(
            obligationId,
            requestId,
            msg.sender,
            item.destination,
            terms.originalDebitAccount,
            amount,
            remaining < remainingApproved ? remaining : remainingApproved,
            uint64(block.timestamp),
            promptCutoff,
            promptCutoffMet
        );
        FUNDS.disbursePayment(obligationId, item.destination, terms.originalDebitAccount, amount);
        emit PaymentReceived(
            obligationId, requestId, receiptId, msg.sender, item.destination, terms.originalDebitAccount, amount
        );
    }

    function getObligation(bytes32 id) external view returns (Obligation memory) {
        return obligations[id];
    }

    function _postLiftCutoffIsExact(Obligation storage item, SparkV15PaymentHolds.Status memory hold)
        private
        view
        returns (bool)
    {
        return item.terms.postLiftDeadlineExact || hold.postLiftClockEvidenceId != 0;
    }

    function _withinCutoff(uint64 time, bool exact) private view returns (bool) {
        return block.timestamp < time || (exact && block.timestamp == time);
    }

    function _scopeRemaining(Approval storage approval, uint256 received) private view returns (uint128) {
        return approval.terms.ceiling > received ? uint128(approval.terms.ceiling - received) : 0;
    }

    function _isMaterial(Obligation storage item) private view returns (bool) {
        return item.terms.originalDebitAccount == bytes32(0) && item.terms.agreedStart == 0;
    }

    function _outstanding(Obligation storage item) private view returns (uint128) {
        return item.correctAmount > item.paid ? uint128(item.correctAmount - item.paid) : 0;
    }

    function _promptCutoff(Obligation storage item, SparkV15PaymentHolds.Status memory hold)
        private
        view
        returns (uint64, bool)
    {
        uint64 release = hold.lastFullReleaseAt;
        if (release == 0 || release <= item.terms.dueAt) return (0, false);
        uint64 cutoff = item.terms.postLiftDeadline;
        bool exact = item.terms.postLiftDeadlineExact;
        if (item.terms.postLiftPeriod != 0) {
            cutoff = release + item.terms.postLiftPeriod;
            exact = release == hold.firstFullReleaseAt && hold.postLiftClockEvidenceId != 0;
        }
        return (cutoff, _withinCutoff(cutoff, exact));
    }

    function getApproval(uint256 requestId) external view returns (Approval memory approval) {
        approval = approvals[requestId];
        if (approval.approver != address(0) && approval.authorityId == bytes32(0)) {
            approval.authorityId = HOLDS.APPROVAL_CHECKS().legacyAuthority(requestId);
        }
    }

    function getReceipt(uint256 receiptId) external view returns (PaymentReceipt memory) {
        return receipts[receiptId];
    }

    function paymentReturnBasis(uint256 receiptId)
        external
        view
        returns (
            bytes32 obligationId,
            address recipient,
            bytes32 creditAccount,
            uint128 amount,
            uint64 paidAt,
            uint256 packageId
        )
    {
        PaymentReceipt storage receipt = receipts[receiptId];
        return (
            receipt.obligationId,
            receipt.recipient,
            receipt.creditAccount,
            receipt.amount,
            receipt.paidAt,
            obligations[receipt.obligationId].packageId
        );
    }

    function applyPaymentReturn(uint256 receiptId, address returningActor, uint128 amount) external {
        if (msg.sender != address(RETURNS)) revert InvalidReturn();
        PaymentReceipt storage receipt = receipts[receiptId];
        Obligation storage item = obligations[receipt.obligationId];
        uint128 beforeReturn = _outstanding(item);
        address payee = RETURNS.receiptBeneficiary(receiptId);
        if (payee == item.beneficiary) item.paid -= amount;
        else previousNetReceipts[receipt.obligationId][payee] -= amount;
        approvals[receipt.approvalRequestId].paid -= amount;
        ++item.version;
        FUNDS.takePaymentReturn(receipt.obligationId, returningActor, receipt.creditAccount, amount);
        uint128 newlyOutstanding = _outstanding(item) - beforeReturn;
        if (newlyOutstanding < amount) FUNDS.releasePaymentBacking(receipt.obligationId, amount - newlyOutstanding);
    }

    function paymentObservationBasis(bytes32 obligationId)
        external
        view
        returns (
            address recipient,
            bytes32 creditAccount,
            uint256 packageId,
            uint64 executionDeadline,
            uint64 legalDeadline,
            address beneficiary
        )
    {
        Obligation storage item = obligations[obligationId];
        return (
            item.destination,
            item.terms.originalDebitAccount,
            item.packageId,
            item.terms.executionDeadline,
            item.terms.legalDeadline,
            item.beneficiary
        );
    }

    function applyObservedPayment(bytes32 obligationId, address beneficiary, uint128 amount, bool isReturn) external {
        if (msg.sender != paymentObservations || amount == 0) revert InvalidObservation();
        Obligation storage item = obligations[obligationId];
        if (
            item.packageId == 0 || item.terms.originalDebitAccount != bytes32(0)
                || !recognisedBeneficiary[obligationId][beneficiary]
        ) revert InvalidObservation();
        if (beneficiary != item.beneficiary) {
            uint256 retained = previousNetReceipts[obligationId][beneficiary];
            previousNetReceipts[obligationId][beneficiary] = isReturn ? retained - amount : retained + amount;
        } else if (isReturn) {
            item.paid -= amount;
        } else {
            uint128 beforeReceipt = _outstanding(item);
            item.paid += amount;
            uint128 reduction = beforeReceipt - _outstanding(item);
            if (reduction != 0) FUNDS.releasePaymentBacking(obligationId, reduction);
        }
        ++item.version;
    }

    function retainedByBeneficiary(bytes32 id, address payee) external view returns (uint256) {
        Obligation storage item = obligations[id];
        return item.beneficiary == payee ? item.paid : previousNetReceipts[id][payee];
    }

    function getLessonObligations(bytes32 lessonId) external view returns (bytes32[] memory) {
        return lessonObligations[lessonId];
    }

}

library SparkV15PaymentRevisionCommitment {
    function hash(
        address payments,
        bytes32 caseId,
        SparkV15Payments.PaymentRevision calldata revision,
        bytes32 originalCommitment
    ) internal view returns (bytes32) {
        return hashAtVersion(payments, caseId, revision, originalCommitment, revision.expectedVersion);
    }

    function hashAtVersion(
        address payments,
        bytes32 caseId,
        SparkV15Payments.PaymentRevision calldata revision,
        bytes32 originalCommitment,
        uint256 version
    ) internal view returns (bytes32) {
        // PaymentRevision is a static ABI tuple. Substitute only the version at application.
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.revise-payment"),
                block.chainid,
                payments,
                caseId,
                revision.obligationId,
                revision.correctAmount,
                revision.beneficiary,
                revision.destination,
                version,
                originalCommitment
            )
        );
    }
}
