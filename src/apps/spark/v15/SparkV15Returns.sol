// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";

interface ISparkV15PaymentReturnsHost {
    function WORKFLOW() external view returns (bytes32);

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
        );

    function applyPaymentReturn(uint256 receiptId, address returningActor, uint128 amount) external;
}

/// @notice Authority and actual return history for one Spark installation's payment receipts.
contract SparkV15Returns {
    struct ReturnTerms {
        uint256 receiptId;
        uint128 amount;
        bytes32 recoveryRef;
    }

    struct ReturnAuthority {
        bytes32 commitment;
        address authorisedBy;
        bytes32 authorityId;
        uint64 authorisedAt;
        uint256 usedByReturn;
    }

    struct PaymentReturn {
        ReturnTerms terms;
        uint256 evidenceId;
        address returnedBy;
        bytes32 creditAccount;
        uint64 returnedAt;
    }

    error InvalidReturn();

    event PaymentReturnAuthorised(uint256 indexed receiptId, uint256 indexed evidenceId, address indexed authorisedBy);
    event PaymentReturned(
        bytes32 indexed obligationId,
        uint256 indexed receiptId,
        uint256 indexed returnId,
        address returnedBy,
        bytes32 creditAccount,
        uint128 amount
    );

    ISparkV15PaymentReturnsHost public immutable PAYMENTS;
    AVARequestAllocation public immutable REQUEST_ALLOCATION;
    bytes32 public immutable VERIFIER_ROLE;

    uint256 private nextReturnId = 1;
    mapping(uint256 => uint128) public returnedForReceipt;
    mapping(uint256 => ReturnAuthority) public returnAuthorisations;
    mapping(uint256 => PaymentReturn) private paymentReturns;
    mapping(uint256 => address) public receiptBeneficiary;
    mapping(bytes32 => uint256[]) private paymentReceiptIds;
    mapping(uint256 => uint256[]) private receiptReturnIds;

    constructor(address payments, AVARequestAllocation requests, bytes32 verifierRole) {
        if (payments == address(0) || address(requests).code.length == 0 || verifierRole == bytes32(0)) {
            revert InvalidReturn();
        }
        PAYMENTS = ISparkV15PaymentReturnsHost(payments);
        REQUEST_ALLOCATION = requests;
        VERIFIER_ROLE = verifierRole;
    }

    function WORKFLOW() public view returns (bytes32) {
        return PAYMENTS.WORKFLOW();
    }

    function recordPayment(bytes32 obligationId, uint256 receiptId, address beneficiary) external {
        if (msg.sender != address(PAYMENTS)) revert InvalidReturn();
        receiptBeneficiary[receiptId] = beneficiary;
        paymentReceiptIds[obligationId].push(receiptId);
    }

    function getPaymentReceiptIds(bytes32 obligationId) external view returns (uint256[] memory) {
        return paymentReceiptIds[obligationId];
    }

    function latestPaymentReceiptId(bytes32 obligationId) external view returns (uint256) {
        uint256[] storage ids = paymentReceiptIds[obligationId];
        return ids.length == 0 ? 0 : ids[ids.length - 1];
    }

    function returnedForReceiptBefore(uint256 receiptId, uint64 cutoff) external view returns (uint128 amount) {
        (amount,) = returnedForReceiptAtCutoff(receiptId, cutoff);
    }

    function returnedForReceiptAtCutoff(uint256 receiptId, uint64 cutoff)
        public
        view
        returns (uint128 beforeCutoff, uint128 atCutoff)
    {
        uint256[] storage ids = receiptReturnIds[receiptId];
        for (uint256 i; i < ids.length; ++i) {
            PaymentReturn storage item = paymentReturns[ids[i]];
            if (item.returnedAt > cutoff) break;
            if (item.returnedAt == cutoff) atCutoff += item.terms.amount;
            else beforeCutoff += item.terms.amount;
        }
    }

    /// @notice Check whether whole returns in this second can reach the amount in execution order.
    function hasReturnPrefixAtCutoff(uint256 receiptId, uint64 cutoff, uint128 expected) external view returns (bool) {
        if (expected == 0) return true;
        uint256[] storage ids = receiptReturnIds[receiptId];
        uint128 amount;
        for (uint256 i; i < ids.length; ++i) {
            PaymentReturn storage item = paymentReturns[ids[i]];
            if (item.returnedAt > cutoff) break;
            if (item.returnedAt < cutoff) continue;
            amount += item.terms.amount;
            if (amount >= expected) return amount == expected;
        }
        return false;
    }

    function returnEvidenceCommitment(ReturnTerms calldata terms) public view returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.payment-return"), block.chainid, address(PAYMENTS), terms));
    }

    /// @notice The verifier checks the recovery decision, applicable terms and exact receipt before its return.
    function authorisePaymentReturn(ReturnTerms calldata terms, uint256 evidenceId, bytes32 authorityId) external {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, VERIFIER_ROLE, SparkV15.ACTION_AUTHORISE_PAYMENT_RETURN, authorityId
            );
        (, address recipient,, uint128 received,, uint256 packageId) = PAYMENTS.paymentReturnBasis(terms.receiptId);
        bytes32 commitment = returnEvidenceCommitment(terms);
        if (
            recipient == address(0) || terms.recoveryRef == bytes32(0) || terms.amount == 0
                || terms.amount > received - returnedForReceipt[terms.receiptId]
                || returnAuthorisations[evidenceId].authorisedBy != address(0)
                || !matchesPaymentEvidence(evidenceId, packageId, commitment)
        ) revert InvalidReturn();

        returnAuthorisations[evidenceId] =
            ReturnAuthority(commitment, msg.sender, authorityId, uint64(block.timestamp), 0);
        emit PaymentReturnAuthorised(terms.receiptId, evidenceId, msg.sender);
    }

    function returnPayment(ReturnTerms calldata terms, uint256 evidenceId) external returns (uint256 returnId) {
        (
            bytes32 obligationId,
            address recipient,
            bytes32 creditAccount,
            uint128 received,
            uint64 paidAt,
            uint256 packageId
        ) = PAYMENTS.paymentReturnBasis(terms.receiptId);
        ReturnAuthority storage authority = returnAuthorisations[evidenceId];
        if (
            msg.sender != recipient || block.timestamp <= paidAt || authority.authorisedBy == address(0)
                || authority.usedByReturn != 0 || authority.commitment != returnEvidenceCommitment(terms)
                || terms.amount > received - returnedForReceipt[terms.receiptId]
        ) revert InvalidReturn();
        if (!matchesPaymentEvidence(evidenceId, packageId, authority.commitment)) revert InvalidReturn();

        returnedForReceipt[terms.receiptId] += terms.amount;
        returnId = nextReturnId++;
        authority.usedByReturn = returnId;
        paymentReturns[returnId] = PaymentReturn(terms, evidenceId, msg.sender, creditAccount, uint64(block.timestamp));
        receiptReturnIds[terms.receiptId].push(returnId);
        PAYMENTS.applyPaymentReturn(terms.receiptId, msg.sender, terms.amount);
        emit PaymentReturned(obligationId, terms.receiptId, returnId, msg.sender, creditAccount, terms.amount);
    }

    function getPaymentReturn(uint256 returnId) external view returns (PaymentReturn memory) {
        return paymentReturns[returnId];
    }

    function matchesPaymentEvidence(uint256 evidenceId, uint256 packageId, bytes32 commitment)
        public view returns (bool)
    {
        AVAEvidenceRegistry registry = REQUEST_ALLOCATION.EVIDENCE_REGISTRY();
        (bytes32 appId, bytes32 workflowKey,,,) =
            registry.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        return appId == SparkV15.APP_ID && workflowKey == WORKFLOW()
            && registry.getEvidenceReference(evidenceId).commitment == commitment;
    }
}
