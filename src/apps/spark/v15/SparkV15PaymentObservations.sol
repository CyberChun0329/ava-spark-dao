// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";

interface ISparkV15PaymentObservationHost {
    function TOKEN() external view returns (address);
    function FUNDS() external view returns (address);
    function REQUEST_ALLOCATION() external view returns (AVARequestAllocation);
    function VERIFIER_ROLE() external view returns (bytes32);
    function WORKFLOW() external view returns (bytes32);

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
        );

    function recognisedBeneficiary(bytes32 obligationId, address beneficiary) external view returns (bool);
    function applyObservedPayment(bytes32 obligationId, address beneficiary, uint128 amount, bool isReturn) external;
}

/// @notice Verified ERC-20 transfers outside the Spark payment entry point.
/// @dev The verifier checks canonical log data and business attribution using the exact evidence commitment.
contract SparkV15PaymentObservations {
    struct Transfer {
        bytes32 transactionHash;
        bytes32 blockHash;
        uint64 blockNumber;
        uint64 logIndex;
        uint64 occurredAt;
        address sender;
        address destination;
        uint128 amount;
    }

    struct PaymentTerms {
        bytes32 obligationId;
        address beneficiary;
        Transfer transfer;
        uint64 evidenceAvailableAt;
        // Independent evidence linking this transfer and beneficiary to the exact payment part.
        bytes32 attributionRef;
        // The return destination allowed by the verified original terms, if established.
        address returnDestination;
    }

    struct Verification {
        uint256 evidenceId;
        uint256 evidencePackageId;
        address verifier;
        bytes32 authorityId;
        uint64 verifiedAt;
    }

    struct PaymentObservation {
        PaymentTerms terms;
        Verification verification;
        uint256 obligationPackageId;
        bool qualifies;
        bool afterOriginalExecutionDeadline;
        bool afterLegalDeadline;
    }

    struct PaymentAttributionTerms {
        bytes32 paymentReceiptId;
        address beneficiary;
        bytes32 attributionRef;
        address returnDestination;
    }

    struct PaymentAttribution {
        PaymentAttributionTerms terms;
        Verification verification;
    }

    struct ReturnTerms {
        bytes32 paymentReceiptId;
        Transfer transfer;
        uint64 evidenceAvailableAt;
        bytes32 recoveryRef;
    }

    struct ReturnObservation {
        ReturnTerms terms;
        Verification verification;
    }

    struct ReturnProof {
        ReturnTerms terms;
        uint256 evidenceId;
    }

    struct AgreedRecipientTerms {
        bytes32 paymentReceiptId;
        address payee;
        uint64 agreedAt;
        uint64 ceasedAt;
        bool agreedByTransferWithinSecond;
        bool ceasedAfterTransferWithinSecond;
        bytes32 agreementRef;
    }

    struct AgreedRecipientObservation {
        AgreedRecipientTerms terms;
        Verification verification;
    }

    enum Finding {
        Unknown,
        No,
        Yes
    }

    struct ExecutionFindings {
        bytes32 paymentReceiptId;
        address actualExecutor;
        address namedExecutor;
        uint256 approvalRequestId;
        uint64 applicableDeadline;
        Finding approvalCoverage;
        Finding heldAtExecution;
        Finding paidByDeadline;
        Finding fullyPaidByDeadline;
        bytes32 executorEvidenceRef;
        bytes32 approvalEvidenceRef;
        bytes32 holdEvidenceRef;
        bytes32 deadlineEvidenceRef;
    }

    error InvalidObservation();

    event PaymentObserved(
        bytes32 indexed obligationId, bytes32 indexed receiptId, uint256 indexed evidenceId, bool qualifies
    );
    event PaymentReturnObserved(bytes32 indexed paymentReceiptId, bytes32 indexed returnId, uint256 indexed evidenceId);
    event PaymentAttributionVerified(bytes32 indexed paymentReceiptId, uint256 indexed evidenceId);
    event AgreedRecipientVerified(bytes32 indexed paymentReceiptId, uint256 indexed evidenceId);
    event PaymentExecutionAssessed(
        bytes32 indexed paymentReceiptId, ExecutionFindings findings, Verification verification
    );

    bytes32 public constant ACTION_VERIFY_OBSERVATION = keccak256("spark.action.verify-payment-observation.v1.5");
    bytes32 private constant PAYMENT_EVIDENCE = keccak256("spark.v1.5.observed-payment");
    bytes32 private constant ATTRIBUTION_EVIDENCE = keccak256("spark.v1.5.observed-payment-attribution");
    bytes32 private constant RETURN_EVIDENCE = keccak256("spark.v1.5.observed-payment-return");
    bytes32 private constant AGREED_RECIPIENT_EVIDENCE = keccak256("spark.v1.5.observed-agreed-recipient");
    bytes32 private constant EXECUTION_EVIDENCE = keccak256("spark.v1.5.observed-payment-execution");

    ISparkV15PaymentObservationHost public immutable PAYMENTS;
    AVARequestAllocation public immutable REQUEST_ALLOCATION;
    bytes32 public immutable VERIFIER_ROLE;
    bytes32 public immutable WORKFLOW;
    address public immutable TOKEN;

    mapping(bytes32 => PaymentObservation) private paymentObservations;
    mapping(bytes32 => PaymentAttribution) private paymentAttributions;
    mapping(bytes32 => ReturnObservation) private returnObservations;
    mapping(bytes32 => AgreedRecipientObservation) private agreedRecipients;
    /// @notice Block of the unique PaymentExecutionAssessed event for a receipt, or zero if none was adopted.
    mapping(bytes32 => uint256) public executionAssessmentBlock;
    mapping(bytes32 => bytes32[]) private qualifiedPaymentsByObligation;
    mapping(bytes32 => bytes32[]) private returnsByPayment;
    mapping(bytes32 => uint128) public returnedForReceipt;

    constructor(address payments, AVARequestAllocation requests, bytes32 verifierRole) {
        if (payments.code.length == 0 || address(requests).code.length == 0 || verifierRole == bytes32(0)) {
            revert InvalidObservation();
        }
        PAYMENTS = ISparkV15PaymentObservationHost(payments);
        if (PAYMENTS.REQUEST_ALLOCATION() != requests || PAYMENTS.VERIFIER_ROLE() != verifierRole) {
            revert InvalidObservation();
        }
        REQUEST_ALLOCATION = requests;
        VERIFIER_ROLE = verifierRole;
        WORKFLOW = PAYMENTS.WORKFLOW();
        TOKEN = PAYMENTS.TOKEN();
    }

    function sourceId(bytes32 transactionHash, uint64 logIndex) public view returns (bytes32) {
        return keccak256(abi.encode(block.chainid, TOKEN, transactionHash, logIndex));
    }

    function paymentEvidenceCommitment(PaymentTerms calldata terms) public view returns (bytes32) {
        (,, uint256 packageId,,,) = PAYMENTS.paymentObservationBasis(terms.obligationId);
        return _commitment(PAYMENT_EVIDENCE, packageId, keccak256(abi.encode(terms)));
    }

    function returnEvidenceCommitment(ReturnTerms calldata terms) public view returns (bytes32) {
        return _commitment(
            RETURN_EVIDENCE,
            paymentObservations[terms.paymentReceiptId].obligationPackageId,
            keccak256(abi.encode(terms))
        );
    }

    function agreedRecipientEvidenceCommitment(AgreedRecipientTerms calldata terms) public view returns (bytes32) {
        return _commitment(
            AGREED_RECIPIENT_EVIDENCE,
            paymentObservations[terms.paymentReceiptId].obligationPackageId,
            keccak256(abi.encode(terms))
        );
    }

    function attributionEvidenceCommitment(PaymentAttributionTerms calldata terms, ReturnProof[] calldata priorReturns)
        public
        view
        returns (bytes32)
    {
        return _commitment(
            ATTRIBUTION_EVIDENCE,
            paymentObservations[terms.paymentReceiptId].obligationPackageId,
            keccak256(abi.encode(terms, priorReturns))
        );
    }

    function executionEvidenceCommitment(ExecutionFindings calldata findings) public view returns (bytes32) {
        return _commitment(
            EXECUTION_EVIDENCE,
            paymentObservations[findings.paymentReceiptId].obligationPackageId,
            keccak256(abi.encode(findings))
        );
    }

    function verifyPayment(PaymentTerms calldata terms, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 receiptId)
    {
        _requireVerifier(authorityId);
        (, bytes32 creditAccount, uint256 packageId, uint64 executionDeadline, uint64 legalDeadline,) =
            PAYMENTS.paymentObservationBasis(terms.obligationId);
        Transfer calldata transfer = terms.transfer;
        if (
            transfer.sender == PAYMENTS.FUNDS()
                || (terms.attributionRef == bytes32(0) && terms.returnDestination != address(0))
                || (terms.attributionRef != bytes32(0) && terms.beneficiary == address(0))
        ) {
            revert InvalidObservation();
        }
        receiptId = _freshTransfer(transfer, terms.evidenceAvailableAt);
        bytes32 commitment = _commitment(PAYMENT_EVIDENCE, packageId, keccak256(abi.encode(terms)));
        Verification memory verification = _verification(evidenceId, packageId, commitment, authorityId);
        // The attributed payee can receive directly. A different wallet requires a verified designation at occurrence.
        bool qualifies = creditAccount == bytes32(0) && terms.attributionRef != bytes32(0)
            && transfer.destination == terms.beneficiary
            && PAYMENTS.recognisedBeneficiary(terms.obligationId, terms.beneficiary);
        paymentObservations[receiptId] = PaymentObservation({
            terms: terms,
            verification: verification,
            obligationPackageId: packageId,
            qualifies: qualifies,
            afterOriginalExecutionDeadline: transfer.occurredAt > executionDeadline,
            afterLegalDeadline: legalDeadline != 0 && transfer.occurredAt > legalDeadline
        });
        if (qualifies) {
            qualifiedPaymentsByObligation[terms.obligationId].push(receiptId);
            PAYMENTS.applyObservedPayment(terms.obligationId, terms.beneficiary, transfer.amount, false);
        }
        emit PaymentObserved(terms.obligationId, receiptId, evidenceId, qualifies);
    }

    /// @notice Links an already verified transfer to its observed obligation when exact evidence is available.
    function verifyPaymentAttribution(
        PaymentAttributionTerms calldata terms,
        uint256 evidenceId,
        ReturnProof[] calldata priorReturns,
        bytes32 authorityId
    ) external {
        _requireVerifier(authorityId);
        bytes32 receiptId = terms.paymentReceiptId;
        PaymentObservation storage original = paymentObservations[receiptId];
        bytes32 obligationId = original.terms.obligationId;
        (, bytes32 creditAccount,,,,) = PAYMENTS.paymentObservationBasis(obligationId);
        if (
            original.verification.evidenceId == 0 || original.terms.attributionRef != bytes32(0) || original.qualifies
                || paymentAttributions[receiptId].verification.evidenceId != 0
                || creditAccount != bytes32(0) || terms.attributionRef == bytes32(0)
                || (original.terms.beneficiary != address(0) && terms.beneficiary != original.terms.beneficiary)
                || !PAYMENTS.recognisedBeneficiary(obligationId, terms.beneficiary)
        ) revert InvalidObservation();

        _requireCurrentVerification(original.verification);
        Verification memory verification = _verification(
            evidenceId, original.obligationPackageId, attributionEvidenceCommitment(terms, priorReturns), authorityId
        );
        paymentAttributions[receiptId] = PaymentAttribution(terms, verification);
        for (uint256 i; i < priorReturns.length; ++i) {
            ReturnProof calldata returned = priorReturns[i];
            if (returned.terms.paymentReceiptId != receiptId) revert InvalidObservation();
            _verifyReturn(returned.terms, returned.evidenceId, authorityId);
        }
        if (terms.beneficiary == original.terms.transfer.destination) {
            _creditQualifiedPayment(receiptId, original, terms.beneficiary);
        }
        emit PaymentAttributionVerified(receiptId, evidenceId);
    }

    function verifyReturn(ReturnTerms calldata terms, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 returnId)
    {
        _requireVerifier(authorityId);
        return _verifyReturn(terms, evidenceId, authorityId);
    }

    function _verifyReturn(ReturnTerms calldata terms, uint256 evidenceId, bytes32 authorityId)
        private
        returns (bytes32 returnId)
    {
        PaymentObservation storage original = paymentObservations[terms.paymentReceiptId];
        Transfer storage payment = original.terms.transfer;
        PaymentAttribution storage attribution = paymentAttributions[terms.paymentReceiptId];
        address returnDestination = original.terms.attributionRef == bytes32(0)
            ? attribution.terms.returnDestination
            : original.terms.returnDestination;
        Transfer calldata transfer = terms.transfer;
        returnId = _freshTransfer(transfer, terms.evidenceAvailableAt);
        if (
            original.verification.evidenceId == 0 || terms.recoveryRef == bytes32(0)
                || transfer.sender != payment.destination || transfer.destination != returnDestination
                || transfer.occurredAt < payment.occurredAt || transfer.blockNumber < payment.blockNumber
                || (transfer.blockNumber == payment.blockNumber
                    && (transfer.blockHash != payment.blockHash || transfer.logIndex <= payment.logIndex))
                || transfer.amount > payment.amount - returnedForReceipt[terms.paymentReceiptId]
        ) revert InvalidObservation();

        Verification memory verification =
            _verification(evidenceId, original.obligationPackageId, returnEvidenceCommitment(terms), authorityId);
        returnObservations[returnId] = ReturnObservation(terms, verification);
        returnedForReceipt[terms.paymentReceiptId] += transfer.amount;
        returnsByPayment[terms.paymentReceiptId].push(returnId);
        if (original.qualifies) {
            address beneficiary = original.terms.attributionRef == bytes32(0)
                ? attribution.terms.beneficiary
                : original.terms.beneficiary;
            PAYMENTS.applyObservedPayment(original.terms.obligationId, beneficiary, transfer.amount, true);
        }
        emit PaymentReturnObserved(terms.paymentReceiptId, returnId, evidenceId);
    }

    /// @notice Recognises the delegation in force at this exact transfer's occurrence.
    function verifyAgreedRecipient(AgreedRecipientTerms calldata terms, uint256 evidenceId, bytes32 authorityId)
        external
    {
        _requireVerifier(authorityId);
        bytes32 receiptId = terms.paymentReceiptId;
        PaymentObservation storage payment = paymentObservations[receiptId];
        if (payment.verification.evidenceId == 0 || payment.qualifies) {
            revert InvalidObservation();
        }
        address beneficiary = payment.terms.beneficiary;
        if (payment.terms.attributionRef == bytes32(0)) {
            PaymentAttribution storage attribution = paymentAttributions[receiptId];
            if (attribution.verification.evidenceId == 0) revert InvalidObservation();
            _requireCurrentVerification(payment.verification);
            _requireCurrentVerification(attribution.verification);
            beneficiary = attribution.terms.beneficiary;
        }
        bytes32 obligationId = payment.terms.obligationId;
        (, bytes32 creditAccount,,,,) = PAYMENTS.paymentObservationBasis(obligationId);
        uint64 occurredAt = payment.terms.transfer.occurredAt;
        if (
            creditAccount != bytes32(0) || terms.payee != beneficiary
                || !PAYMENTS.recognisedBeneficiary(obligationId, terms.payee) || terms.agreementRef == bytes32(0)
                || terms.agreedAt == 0 || terms.agreedAt > occurredAt
                || (terms.agreedAt == occurredAt && !terms.agreedByTransferWithinSecond)
                || (terms.ceasedAt != 0
                    && (terms.ceasedAt < occurredAt
                        || (terms.ceasedAt == occurredAt && !terms.ceasedAfterTransferWithinSecond)))
        ) revert InvalidObservation();
        Verification memory verification = _verification(
            evidenceId, payment.obligationPackageId, agreedRecipientEvidenceCommitment(terms), authorityId
        );
        agreedRecipients[receiptId] = AgreedRecipientObservation(terms, verification);
        _creditQualifiedPayment(receiptId, payment, terms.payee);
        emit AgreedRecipientVerified(receiptId, evidenceId);
    }

    function _creditQualifiedPayment(bytes32 receiptId, PaymentObservation storage payment, address beneficiary) private {
        payment.qualifies = true;
        qualifiedPaymentsByObligation[payment.terms.obligationId].push(receiptId);
        uint128 retained = payment.terms.transfer.amount - returnedForReceipt[receiptId];
        if (retained != 0) PAYMENTS.applyObservedPayment(payment.terms.obligationId, beneficiary, retained, false);
    }

    function getQualifiedPaymentIds(bytes32 obligationId) external view returns (bytes32[] memory) {
        return qualifiedPaymentsByObligation[obligationId];
    }

    function getReturnIds(bytes32 receiptId) external view returns (bytes32[] memory) {
        return returnsByPayment[receiptId];
    }

    /// @notice Publishes independent historical findings for an observed transfer.
    function verifyExecutionAssessment(ExecutionFindings calldata findings, uint256 evidenceId, bytes32 authorityId)
        external
    {
        _requireVerifier(authorityId);
        bytes32 receiptId = findings.paymentReceiptId;
        PaymentObservation storage observed = paymentObservations[receiptId];
        if (observed.verification.evidenceId == 0 || executionAssessmentBlock[receiptId] != 0) {
            revert InvalidObservation();
        }
        (,,,, uint64 legalDeadline,) = PAYMENTS.paymentObservationBasis(observed.terms.obligationId);
        _checkExecutionFindings(findings, observed.terms.transfer.occurredAt, legalDeadline);
        Verification memory verification =
            _verification(evidenceId, observed.obligationPackageId, executionEvidenceCommitment(findings), authorityId);
        executionAssessmentBlock[receiptId] = block.number;
        emit PaymentExecutionAssessed(receiptId, findings, verification);
    }

    /// @notice Compatibility read for callers that also query legacy observers.
    /// @dev New installations file verified observations in the local archive.
    function archivedAt(bytes32) external pure returns (uint64) {
        return 0;
    }

    function getPaymentObservation(bytes32 receiptId) external view returns (PaymentObservation memory) {
        return paymentObservations[receiptId];
    }

    function getPaymentAttribution(bytes32 receiptId) external view returns (PaymentAttribution memory) {
        return paymentAttributions[receiptId];
    }

    function getReturnObservation(bytes32 returnId) external view returns (ReturnObservation memory) {
        return returnObservations[returnId];
    }

    function getAgreedRecipient(bytes32 receiptId) external view returns (AgreedRecipientObservation memory) {
        return agreedRecipients[receiptId];
    }

    function _checkExecutionFindings(ExecutionFindings calldata findings, uint64 occurredAt, uint64 legalDeadline)
        private
        pure
    {
        bool statesApproval = findings.approvalCoverage != Finding.Unknown || findings.namedExecutor != address(0)
            || findings.approvalRequestId != 0;
        bool statesDeadline = findings.paidByDeadline != Finding.Unknown
            || findings.fullyPaidByDeadline != Finding.Unknown || findings.applicableDeadline != 0;
        if (
            (findings.actualExecutor != address(0)) != (findings.executorEvidenceRef != bytes32(0))
                || statesApproval != (findings.approvalEvidenceRef != bytes32(0))
                || (findings.heldAtExecution != Finding.Unknown) != (findings.holdEvidenceRef != bytes32(0))
                || statesDeadline != (findings.deadlineEvidenceRef != bytes32(0))
                || (!statesApproval
                    && !statesDeadline
                    && findings.executorEvidenceRef == bytes32(0)
                    && findings.holdEvidenceRef == bytes32(0))
        ) revert InvalidObservation();
        if (
            findings.approvalCoverage == Finding.Yes
                && (findings.namedExecutor == address(0) || findings.actualExecutor != findings.namedExecutor)
        ) revert InvalidObservation();
        uint64 deadline = findings.applicableDeadline;
        if (
            (statesDeadline && deadline == 0) || (legalDeadline != 0 && deadline > legalDeadline)
                || (findings.paidByDeadline == Finding.Yes && occurredAt > deadline)
                || (findings.paidByDeadline == Finding.No && occurredAt < deadline)
        ) revert InvalidObservation();
    }

    function _hasTransfer(bytes32 id) private view returns (bool) {
        return
            paymentObservations[id].verification.evidenceId != 0 || returnObservations[id].verification.evidenceId != 0;
    }

    function _freshTransfer(Transfer calldata transfer, uint64 evidenceAvailableAt) private view returns (bytes32 id) {
        if (
            transfer.transactionHash == bytes32(0) || transfer.blockHash == bytes32(0)
                || transfer.blockNumber >= block.number || transfer.occurredAt == 0
                || transfer.occurredAt > block.timestamp || transfer.sender == address(0)
                || transfer.destination == address(0) || transfer.sender == transfer.destination || transfer.amount == 0
                || (evidenceAvailableAt != 0
                    && (evidenceAvailableAt < transfer.occurredAt || evidenceAvailableAt > block.timestamp))
        ) revert InvalidObservation();
        if (block.number - transfer.blockNumber <= 256 && blockhash(transfer.blockNumber) != transfer.blockHash) {
            revert InvalidObservation();
        }
        id = sourceId(transfer.transactionHash, transfer.logIndex);
        if (_hasTransfer(id)) revert InvalidObservation();
    }

    function _requireVerifier(bytes32 authorityId) private view {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, VERIFIER_ROLE, ACTION_VERIFY_OBSERVATION, authorityId
            );
    }

    function _requireCurrentVerification(Verification storage verification) private view {
        REQUEST_ALLOCATION.EVIDENCE_REGISTRY()
            .requireUsableEvidenceReferenceForPackage(verification.evidenceId, verification.evidencePackageId);
    }

    function _commitment(bytes32 operation, uint256 obligationPackageId, bytes32 termsHash)
        private
        view
        returns (bytes32)
    {
        return keccak256(abi.encode(operation, block.chainid, address(this), TOKEN, obligationPackageId, termsHash));
    }

    function _verification(uint256 evidenceId, uint256 packageId, bytes32 commitment, bytes32 authorityId)
        private
        view
        returns (Verification memory)
    {
        if (packageId == 0) revert InvalidObservation();
        AVAEvidenceRegistry registry = REQUEST_ALLOCATION.EVIDENCE_REGISTRY();
        AVAEvidenceRegistry.EvidenceReference memory evidence = registry.getEvidenceReference(evidenceId);
        if (
            evidence.appId != SparkV15.APP_ID || evidence.workflowKey != WORKFLOW || evidence.commitment != commitment
                || (evidence.packageId != packageId
                    && evidence.packageId
                        != REQUEST_ALLOCATION.RULE_PACKAGE_REGISTRY().getActivePackageId(SparkV15.APP_ID, WORKFLOW))
        ) {
            revert InvalidObservation();
        }
        registry.requireUsableEvidenceReferenceForPackage(evidenceId, evidence.packageId);
        return Verification(evidenceId, evidence.packageId, msg.sender, authorityId, uint64(block.timestamp));
    }
}
