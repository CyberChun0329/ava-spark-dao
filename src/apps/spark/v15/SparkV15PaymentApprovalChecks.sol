// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACapabilityKeys} from "@ava-protocol/contracts/src/core/AVACapabilityKeys.sol";
import {AVACoreRulePackageRegistry} from "@ava-protocol/contracts/src/core/AVACoreRulePackageRegistry.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {SparkV15, SparkV15ApplicationModule} from "./SparkV15ApplicationModule.sol";
import {SparkV15Booking} from "./SparkV15Booking.sol";
import {SparkV15Payments, SparkV15PaymentRevisionCommitment} from "./SparkV15Payments.sol";
import {SparkV15PaymentHolds} from "./SparkV15PaymentHolds.sol";
import {SparkV15Settlement} from "./SparkV15Settlement.sol";

/// @dev Keep Core request decoding and settlement inspection outside the contract that holds the approvals.
contract SparkV15PaymentApprovalChecks {
    error InvalidApproval();
    error InvalidCase();
    error ConflictedCaseActor();

    bytes32 public constant WAGE_RECEIPT_RECHECK_EVIDENCE =
        keccak256("spark.v1.5.review.recheck-native-wage-receipt");

    AVARequestAllocation private immutable REQUESTS;
    bytes32 private immutable WORKFLOW;

    constructor(AVARequestAllocation requests, bytes32 workflow) {
        REQUESTS = requests;
        WORKFLOW = workflow;
    }

    function requireAllocation(uint256 requestId, uint256 packageId, address actor)
        external
        view
        returns (bytes32 role, bytes32 authorityId)
    {
        AVARequestAllocation.RequestRecord memory request = REQUESTS.getRequest(requestId);
        if (
            packageId == 0 || request.appId != SparkV15.APP_ID || request.workflowKey != WORKFLOW
                || request.packageId != packageId || request.input.burdenHash != SparkV15.APPROVAL_BURDEN
                || actor != request.allocator || REQUESTS.scopedSupportByRequest(requestId)
        ) revert InvalidApproval();
        return (request.allocatorRoleKey, request.allocatorAuthorityId);
    }

    function legacyAuthority(uint256 requestId) external view returns (bytes32) {
        return REQUESTS.getRequest(requestId).allocatorAuthorityId;
    }

    function requireApprovalStopReview(
        SparkV15Payments payments,
        bytes32 caseId,
        uint256 requestId,
        bytes32 obligationId,
        bytes32 outcome,
        address reviewer
    ) external view {
        SparkV15Payments.Approval memory approval = payments.getApproval(requestId);
        if (
            approval.approver == address(0) || approval.terms.obligationId != obligationId
                || outcome != payments.stopApprovalOutcome(caseId, requestId)
        ) revert InvalidCase();
        if (approval.approver == reviewer) revert ConflictedCaseActor();
    }

    function requireOrdinaryWageAuthority(
        SparkV15Settlement settlement,
        bytes32 lessonId,
        bytes32 obligationId,
        uint256 packageId,
        address actor
    ) external view returns (bytes32) {
        _requireOrdinaryWage(settlement, lessonId, obligationId);
        AVACoreRulePackageRegistry packages = REQUESTS.RULE_PACKAGE_REGISTRY();
        if (packages.getActivePackageId(SparkV15.APP_ID, WORKFLOW) != packageId) revert InvalidApproval();
        SparkV15ApplicationModule application =
            SparkV15ApplicationModule(packages.getModule(packageId, AVACapabilityKeys.APPLICATION));
        return REQUESTS.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                actor, SparkV15.APP_ID, application.ALLOCATOR_ROLE(), AVACoreTypes.ACTION_RECORD_ALLOCATION
            );
    }

    function paymentScope(
        SparkV15Payments payments,
        bytes32 lessonId,
        uint256 packageId,
        bytes32 obligationId
    ) external view returns (bytes32) {
        SparkV15Payments.Obligation memory item = payments.getObligation(obligationId);
        if (item.terms.lessonId != lessonId || item.packageId != packageId) revert InvalidCase();
        return item.commitment;
    }

    function reviewPaymentRevision(
        SparkV15Payments payments,
        bytes32 caseId,
        SparkV15Payments.PaymentRevision calldata revision
    ) external view returns (bytes32) {
        SparkV15Payments.Obligation memory item = payments.getObligation(revision.obligationId);
        if (
            item.packageId == 0 || revision.expectedVersion != item.version
                || (item.terms.originalDebitAccount != bytes32(0)
                    && revision.correctAmount > item.terms.originalDebitAmount)
        ) revert InvalidCase();
        return SparkV15PaymentRevisionCommitment.hash(address(payments), caseId, revision, item.commitment);
    }

    /// @notice Check the reviewed revision, with a separately evidenced recheck of a subsequent native receipt.
    function paymentRevisionAtAdoption(
        SparkV15Payments payments,
        bytes32 caseId,
        SparkV15Payments.PaymentRevision calldata revision,
        bytes32 reviewedOutcome,
        uint64 reviewedAt,
        uint64 noticeSentAt,
        uint256 evidenceId
    ) external view returns (bytes32 effect, bytes32 recheck) {
        bytes32 obligationId = revision.obligationId;
        SparkV15Payments.Obligation memory item = payments.getObligation(obligationId);
        if (
            reviewedOutcome == bytes32(0)
                || reviewedOutcome
                    != SparkV15PaymentRevisionCommitment.hash(address(payments), caseId, revision, item.commitment)
        ) revert InvalidCase();
        if (revision.expectedVersion == item.version) return (reviewedOutcome, bytes32(0));
        AVACoreTypes.EvidenceRecord memory proof = REQUESTS.EVIDENCE_REGISTRY().getEvidence(evidenceId);
        if (proof.evidenceTypeHash != WAGE_RECEIPT_RECHECK_EVIDENCE) return (reviewedOutcome, bytes32(0));

        uint256 receiptId = payments.RETURNS().latestPaymentReceiptId(obligationId);
        SparkV15Payments.PaymentReceipt memory receipt = payments.getReceipt(receiptId);
        if (
            item.version == 0 || revision.expectedVersion != item.version - 1
                || item.terms.originalDebitAccount != bytes32(0) || item.beneficiary != item.destination
                || revision.beneficiary != revision.destination || receipt.obligationId != obligationId
                || receipt.paidAt <= reviewedAt || noticeSentAt <= receipt.paidAt
                || proof.registeredAt < noticeSentAt
        ) revert InvalidCase();
        // Only a native pay increments the obligation version AND appends a native receipt.
        SparkV15PaymentHolds.Status memory hold = payments.HOLDS().getStatus(obligationId);
        if (hold.active || hold.lastFullReleaseAt != 0) revert InvalidCase();
        SparkV15Settlement settlement = SparkV15Settlement(address(payments.settlementPolicy()));
        _requireOrdinaryWage(settlement, item.terms.lessonId, obligationId);
        settlement.retainedPayment(item.terms, item.packageId);

        effect = SparkV15PaymentRevisionCommitment.hashAtVersion(
            address(payments), caseId, revision, item.commitment, item.version
        );
        uint256 correctedNet = payments.retainedByBeneficiary(obligationId, revision.beneficiary);
        recheck = keccak256(abi.encode(receiptId, item.paid, correctedNet, effect));
    }

    function _requireOrdinaryWage(SparkV15Settlement settlement, bytes32 lessonId, bytes32 obligationId) private view {
        if (address(settlement) == address(0)) revert InvalidApproval();
        SparkV15Settlement.GroupSettlement memory result = settlement.getGroupSettlement(lessonId);
        if (
            !result.complete || result.route != SparkV15Settlement.Route.OrdinaryOneToOne
                || result.totalTutorPay != result.netTutorPay
        ) revert InvalidApproval();
        SparkV15Booking booking = settlement.BOOKING();
        SparkV15Booking.Lesson memory lesson = booking.getLesson(lessonId);
        bytes32[] memory forms = booking.getPlannedForms(lessonId);
        if (
            lesson.terms.materialsTermsRef != bytes32(0) || forms.length != 1
                || booking.getEffectiveArrangement(lessonId, uint64(block.timestamp)).changeId != bytes32(0)
        ) revert InvalidApproval();
        bytes32 formId = forms[0];
        SparkV15Booking.ServiceStatus service = booking.getServiceFeedback(formId).status;
        if (
            !settlement.isOrdinaryWageSeat(lessonId, formId, obligationId)
                || booking.isCancelledAt(formId, uint64(block.timestamp))
                || (service != SparkV15Booking.ServiceStatus.Unreported
                    && service != SparkV15Booking.ServiceStatus.FullyDelivered)
        ) revert InvalidApproval();
        if (!settlement.mayPaySettlementPart(obligationId)) revert InvalidApproval();
    }
}
