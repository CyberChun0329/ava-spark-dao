// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15, SparkV15ApplicationModule} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {SparkV15PaymentObservations} from "../../../src/apps/spark/v15/SparkV15PaymentObservations.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {IERC20} from "../../../src/apps/spark/legacy/interfaces/IERC20.sol";
import {RequestAllocationFixture} from "../../helpers/RequestAllocationFixture.sol";
import {MockERC20} from "../mocks/MockERC20.sol";

interface PaymentObservationVm {
    function roll(uint256 blockNumber) external;
    function setBlockhash(uint256 blockNumber, bytes32 blockHash) external;
    function expectEmit(bool topic1, bool topic2, bool topic3, bool data, address emitter) external;
}

contract PaymentObservationTest is RequestAllocationFixture {
    PaymentObservationVm private constant CHAIN =
        PaymentObservationVm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint64 private constant DUE = 31 days;
    uint64 private constant LEGAL_DEADLINE = DUE + 1;
    uint64 private constant EXECUTION_DEADLINE = DUE + 5;
    uint64 private constant PAID_AT = DUE + 2;
    uint64 private constant VERIFIED_AT = DUE + 7;
    address private constant RECIPIENT = address(0xCAFE);
    address private constant OUTSIDE_PAYER = address(0xF001);
    address private constant RECEIVING_TREASURY = address(0xF002);
    bytes32 private constant VERIFIED_PAYMENT_TERMS = keccak256("receipt refers to the exact share and return terms");

    event PaymentExecutionAssessed(
        bytes32 indexed paymentReceiptId,
        SparkV15PaymentObservations.ExecutionFindings findings,
        SparkV15PaymentObservations.Verification verification
    );

    MockERC20 private token;
    SparkV15Payments private payments;
    SparkV15PaymentObservations private observations;
    bytes32 private fixtureAdoptedCase;
    bytes32 private fixtureAdoptedObligation;
    bytes32 private fixtureAdoptedOutcome;
    uint64 private fixtureAdoptedAt;

    function setUp() public {
        requestVm.warp(DUE - 1);
        _setUpRequestAllocation(
            SparkV15.APP_ID,
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR),
            SparkV15.OBJECT_PAYMENT_APPROVAL
        );
        token = new MockERC20("Spark fixture USD", "TUSD", 6);
        payments = new SparkV15Payments(requestAllocation, IERC20(address(token)), REQUEST_WORKFLOW, ROLE_VERIFIER);
        payments.bindHolds(
            new SparkV15PaymentHolds(address(payments), requestAllocation, REQUEST_WORKFLOW, ROLE_VERIFIER)
        );
        observations = new SparkV15PaymentObservations(address(payments), requestAllocation, ROLE_VERIFIER);
        payments.bindPaymentObservations(address(observations));
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_ESTABLISH_PAYMENT, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_FORMAL_HOLD, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, observations.ACTION_VERIFY_OBSERVATION(), true);
        token.mint(address(payments.FUNDS()), 24);
        token.mint(OUTSIDE_PAYER, 24);
    }

    function testVerifiedLatePaymentReleasesOnlyItsBackingAndKeepsArchivalLocal() public {
        bytes32 obligation = _establish(keccak256("first pay part"), RECIPIENT);
        bytes32 unrelated = _establish(keccak256("another pay part"), RECIPIENT);
        _imposeFormalHold(obligation);
        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, RECIPIENT, 8);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));

        requestVm.expectRevert();
        observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));
        bytes32[] memory qualified = observations.getQualifiedPaymentIds(obligation);
        require(qualified.length == 1 && qualified[0] == receipt, "qualified receipt index");

        SparkV15PaymentObservations.PaymentObservation memory fact = observations.getPaymentObservation(receipt);
        require(fact.terms.transfer.occurredAt == PAID_AT, "occurrence does not equal verification");
        require(fact.terms.evidenceAvailableAt == PAID_AT + 1, "evidence availability preserved");
        require(fact.qualifies && fact.afterLegalDeadline && !fact.afterOriginalExecutionDeadline, "deadline");
        require(fact.verification.verifiedAt == VERIFIED_AT && observations.archivedAt(receipt) == 0, "verification");
        require(payments.getObligation(obligation).paid == 8, "payment counted");
        require(payments.HOLDS().getStatus(obligation).activeFormalHolds == 1, "hold history intact");
        require(payments.FUNDS().paymentReserved(obligation) == 0, "only this backing released");
        require(
            payments.getObligation(unrelated).paid == 0 && payments.FUNDS().paymentReserved(unrelated) == 8,
            "other part"
        );
        require(token.balanceOf(RECIPIENT) == 8 && token.balanceOf(address(payments.FUNDS())) == 24, "actual balances");

        requestVm.warp(VERIFIED_AT + 1);
        bytes memory legacyArchiveCall =
            abi.encodeWithSignature("archiveObservation(bytes32,bytes32)", receipt, _authority(ROLE_VERIFIER));
        requestVm.prank(VERIFIER_ACTOR);
        (bool archived,) = address(observations).call(legacyArchiveCall);
        require(!archived && observations.archivedAt(receipt) == 0, "new observer files locally");

        terms.obligationId = unrelated;
        evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));
    }

    function testObservedReturnReopensDebtWithoutMovingVaultFundsOrUsingAnotherReserve() public {
        bytes32 obligation = _establish(keccak256("first pay part"), RECIPIENT);
        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, RECIPIENT, 10);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));
        require(payments.getObligation(obligation).paid == 10, "overpayment observed in full");
        _establish(keccak256("second pay part"), RECIPIENT);
        _establish(keccak256("third pay part"), RECIPIENT);
        _establish(keccak256("fourth pay part"), RECIPIENT);
        require(payments.FUNDS().reservedUnits() == 24, "vault backing fully committed");

        SparkV15PaymentObservations.ReturnTerms memory returned = _outsideReturn(receipt, RECIPIENT, 5);
        returned.transfer.destination = OUTSIDE_PAYER;
        evidence = _evidence(observations.returnEvidenceCommitment(returned));
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyReturn(returned, evidence, _authority(ROLE_VERIFIER));
        returned.transfer.destination = RECEIVING_TREASURY;
        evidence = _evidence(observations.returnEvidenceCommitment(returned));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 returnId = observations.verifyReturn(returned, evidence, _authority(ROLE_VERIFIER));
        bytes32[] memory indexedReturns = observations.getReturnIds(receipt);
        require(indexedReturns.length == 1 && indexedReturns[0] == returnId, "return index");

        require(observations.getReturnObservation(returnId).terms.paymentReceiptId == receipt, "exact original receipt");
        require(
            observations.returnedForReceipt(receipt) == 5 && payments.getObligation(obligation).paid == 5, "return net"
        );
        require(payments.FUNDS().paymentReserved(obligation) == 0 && payments.FUNDS().reservedUnits() == 24, "backing");
        require(
            token.balanceOf(RECEIVING_TREASURY) == 5 && token.balanceOf(address(payments.FUNDS())) == 24, "balances"
        );

        SparkV15PaymentObservations.PaymentTerms memory replay = SparkV15PaymentObservations.PaymentTerms({
            obligationId: obligation,
            beneficiary: RECIPIENT,
            transfer: returned.transfer,
            evidenceAvailableAt: 0,
            attributionRef: bytes32(0),
            returnDestination: address(0)
        });
        evidence = _evidence(observations.paymentEvidenceCommitment(replay));
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyPayment(replay, evidence, _authority(ROLE_VERIFIER));

        returned.transfer.transactionHash = keccak256("putative second return");
        returned.transfer.logIndex = 3;
        returned.transfer.amount = 6;
        evidence = _evidence(observations.returnEvidenceCommitment(returned));
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyReturn(returned, evidence, _authority(ROLE_VERIFIER));

        require(observations.archivedAt(returnId) == 0, "return is filed locally");
    }

    function testObservedReturnUsesOriginalBeneficiaryAfterAReviewedPartyChange() public {
        bytes32 obligation = _establish(keccak256("pay part with a corrected beneficiary"), RECIPIENT);
        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, RECIPIENT, 4);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));

        address correctedPayee = address(0xCAFF);
        _applyAdoptedRecipientRevision(obligation, correctedPayee, RECIPIENT);
        require(payments.retainedByBeneficiary(obligation, RECIPIENT) == 4, "original benefit retained");
        require(payments.getObligation(obligation).paid == 0, "prior receipt excluded from corrected debt");

        SparkV15PaymentObservations.ReturnTerms memory returned = _outsideReturn(receipt, RECIPIENT, 2);
        evidence = _evidence(observations.returnEvidenceCommitment(returned));
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyReturn(returned, evidence, _authority(ROLE_VERIFIER));

        require(observations.returnedForReceipt(receipt) == 2, "original receipt returned");
        require(payments.retainedByBeneficiary(obligation, RECIPIENT) == 2, "original benefit reduced");
        require(payments.retainedByBeneficiary(obligation, correctedPayee) == 0, "corrected payee unchanged");
        require(
            payments.getObligation(obligation).paid == 0 && token.balanceOf(RECEIVING_TREASURY) == 2, "actual return"
        );
    }

    function testHistoricDirectReceiptCreditsPayeeAfterDestinationChange() public {
        bytes32 obligation = _establish(keccak256("original wage destination"), RECIPIENT);
        bytes32 unrelated = _establish(keccak256("another wage obligation"), RECIPIENT);
        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, RECIPIENT, 6);
        address laterDestination = address(0xD34);
        _applyAdoptedRecipientRevision(obligation, RECIPIENT, laterDestination);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));

        require(observations.getPaymentObservation(receipt).qualifies, "original receipt lost after destination change");
        require(payments.retainedByBeneficiary(obligation, RECIPIENT) == 6, "verified payment not credited");
        require(payments.FUNDS().paymentReserved(obligation) == 2, "current unpaid amount not backed");
        require(payments.FUNDS().paymentReserved(unrelated) == 8, "other obligation backing changed");
        require(token.balanceOf(RECIPIENT) == 6 && token.balanceOf(laterDestination) == 0, "actual recipient changed");
        require(token.balanceOf(address(payments.FUNDS())) == 24, "receipt pulled from the vault");
    }

    function testLaterDesignatedAddressDoesNotQualifyAnEarlierTransfer() public {
        bytes32 obligation = _establish(keccak256("wage paid to a later designee"), RECIPIENT);
        address laterDestination = address(0xD34);
        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, laterDestination, 6);
        _applyAdoptedRecipientRevision(obligation, RECIPIENT, laterDestination);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));

        SparkV15PaymentObservations.PaymentObservation memory fact = observations.getPaymentObservation(receipt);
        require(fact.verification.evidenceId == evidence && fact.terms.transfer.occurredAt == PAID_AT, "lost receipt");
        require(!fact.qualifies && token.balanceOf(laterDestination) == 6, "later designation rewrote prior transfer");
        require(payments.retainedByBeneficiary(obligation, RECIPIENT) == 0, "misdirection credited");
        require(payments.FUNDS().paymentReserved(obligation) == 8, "misdirection released backing");

        SparkV15PaymentObservations.AgreedRecipientTerms memory agreement =
            SparkV15PaymentObservations.AgreedRecipientTerms({
                paymentReceiptId: receipt,
                payee: RECIPIENT,
                agreedAt: VERIFIED_AT,
                ceasedAt: 0,
                agreedByTransferWithinSecond: false,
                ceasedAfterTransferWithinSecond: false,
                agreementRef: keccak256("later reviewed designation")
            });
        evidence = _evidence(observations.agreedRecipientEvidenceCommitment(agreement));
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyAgreedRecipient(agreement, evidence, _authority(ROLE_VERIFIER));
    }

    function testHistoricReceiptStaysWithTheOriginalPayeeWhenTheWalletIsShared() public {
        bytes32 obligation = _establish(keccak256("wage with a reviewed beneficiary change"), RECIPIENT);
        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, RECIPIENT, 6);
        address correctedPayee = address(0xCAFF);
        _applyAdoptedRecipientRevision(obligation, correctedPayee, RECIPIENT);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));

        require(observations.getPaymentObservation(receipt).qualifies, "historical payee lost");
        require(payments.retainedByBeneficiary(obligation, RECIPIENT) == 6, "historical payee credit");
        require(payments.retainedByBeneficiary(obligation, correctedPayee) == 0, "new payee credited");

        SparkV15PaymentObservations.ReturnTerms memory returned = _outsideReturn(receipt, RECIPIENT, 2);
        evidence = _evidence(observations.returnEvidenceCommitment(returned));
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyReturn(returned, evidence, _authority(ROLE_VERIFIER));

        require(payments.retainedByBeneficiary(obligation, RECIPIENT) == 4, "wrong historical net payment");
        require(payments.getObligation(obligation).paid == 0, "old receipt reduced new debt");
        require(payments.FUNDS().paymentReserved(obligation) == 8, "new debt backing changed");
        require(token.balanceOf(RECEIVING_TREASURY) == 2, "actual return lost");
    }

    function adoptedPaymentEffect(bytes32 caseId) external view returns (bytes32, bytes32, uint64) {
        require(caseId == fixtureAdoptedCase, "fixture case");
        return (fixtureAdoptedObligation, fixtureAdoptedOutcome, fixtureAdoptedAt);
    }

    function _applyAdoptedRecipientRevision(bytes32 obligation, address beneficiary, address destination) private {
        bytes32 role = payments.caseEffectRole();
        authorityMatrix.setPermission(SparkV15.APP_ID, role, payments.ACTION_APPLY_CASE_EFFECT(), true);
        identityRegistry.assignSubject(address(this), SparkV15.APP_ID, role, _authority(role), "test:review-result");
        fixtureAdoptedCase = keccak256("reviewed payee correction");
        fixtureAdoptedObligation = obligation;
        fixtureAdoptedAt = uint64(block.timestamp);
        SparkV15Payments.PaymentRevision memory revision = SparkV15Payments.PaymentRevision({
            obligationId: obligation,
            correctAmount: 8,
            beneficiary: beneficiary,
            destination: destination,
            expectedVersion: payments.getObligation(obligation).version
        });
        fixtureAdoptedOutcome = keccak256(
            abi.encode(
                keccak256("spark.v1.5.revise-payment"),
                block.chainid,
                address(payments),
                fixtureAdoptedCase,
                revision,
                payments.getObligation(obligation).commitment
            )
        );
        payments.applyPaymentRevision(fixtureAdoptedCase, revision);
    }

    function testMisdirectionDuringEffectiveHoldKeepsFactAndIndependentHistoricFindings() public {
        bytes32 obligation = _establish(keccak256("held pay part"), RECIPIENT);
        bytes32 holdId = _imposeFormalHold(obligation);

        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, address(0xBAD), 8);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));
        require(!observations.getPaymentObservation(receipt).qualifies, "wrong payee counted");
        require(observations.executionAssessmentBlock(receipt) == 0, "Transfer implied authorization");

        CHAIN.roll(22);
        requestVm.warp(VERIFIED_AT + 1);
        SparkV15PaymentObservations.ExecutionFindings memory findings = SparkV15PaymentObservations.ExecutionFindings({
            paymentReceiptId: receipt,
            actualExecutor: OUTSIDE_PAYER,
            namedExecutor: address(0xE7),
            approvalRequestId: 0,
            applicableDeadline: LEGAL_DEADLINE,
            approvalCoverage: SparkV15PaymentObservations.Finding.No,
            heldAtExecution: SparkV15PaymentObservations.Finding.Yes,
            paidByDeadline: SparkV15PaymentObservations.Finding.No,
            fullyPaidByDeadline: SparkV15PaymentObservations.Finding.No,
            executorEvidenceRef: keccak256("actual executor witness"),
            approvalEvidenceRef: keccak256("original approver and named executor scope"),
            holdEvidenceRef: holdId,
            deadlineEvidenceRef: keccak256("legal deadline and eligible retained receipts at cutoff")
        });
        findings.holdEvidenceRef = bytes32(0);
        evidence = _evidence(observations.executionEvidenceCommitment(findings));
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyExecutionAssessment(findings, evidence, _authority(ROLE_VERIFIER));
        require(observations.executionAssessmentBlock(receipt) == 0, "Invalid findings were adopted");
        findings.holdEvidenceRef = holdId;
        evidence = _evidence(observations.executionEvidenceCommitment(findings));
        requestVm.expectRevert();
        observations.verifyExecutionAssessment(findings, evidence, _authority(ROLE_VERIFIER));
        CHAIN.expectEmit(true, false, false, true, address(observations));
        emit PaymentExecutionAssessed(
            receipt,
            findings,
            SparkV15PaymentObservations.Verification(
                evidence, requestPackageId, VERIFIER_ACTOR, _authority(ROLE_VERIFIER), VERIFIED_AT + 1
            )
        );
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyExecutionAssessment(findings, evidence, _authority(ROLE_VERIFIER));
        require(observations.executionAssessmentBlock(receipt) == 22, "Wrong adoption block");

        CHAIN.roll(23);
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyExecutionAssessment(findings, evidence, _authority(ROLE_VERIFIER));
        require(observations.executionAssessmentBlock(receipt) == 22, "Original adoption block changed");

        SparkV15Payments.Obligation memory payment = payments.getObligation(obligation);
        require(
            payment.paid == 0 && payment.firstApprovalRequestId == 0
                && payments.HOLDS().getStatus(obligation).activeFormalHolds == 1,
            "no policy effect"
        );
        require(
            token.balanceOf(address(0xBAD)) == 8 && payments.FUNDS().paymentReserved(obligation) == 8,
            "real misdirection"
        );
    }

    function testAgreedRecipientCreditsOnlyAProvenDesignationInForceAtTheReceipt() public {
        bytes32 obligation = _establish(keccak256("pay with agreed collector"), RECIPIENT);
        address designee = address(0xD34);
        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, designee, 8);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receiptId = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));
        require(payments.getObligation(obligation).paid == 0, "no verified designation");
        _applyAdoptedRecipientRevision(obligation, address(0xCAFF), RECIPIENT);

        SparkV15PaymentObservations.ReturnTerms memory returned = _outsideReturn(receiptId, designee, 3);
        evidence = _evidence(observations.returnEvidenceCommitment(returned));
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyReturn(returned, evidence, _authority(ROLE_VERIFIER));
        require(payments.retainedByBeneficiary(obligation, RECIPIENT) == 0, "unqualified return affected the payee");

        SparkV15PaymentObservations.AgreedRecipientTerms memory agreement =
            SparkV15PaymentObservations.AgreedRecipientTerms({
                paymentReceiptId: receiptId,
                payee: RECIPIENT,
                agreedAt: PAID_AT,
                ceasedAt: PAID_AT + 1,
                agreedByTransferWithinSecond: false,
                ceasedAfterTransferWithinSecond: false,
                agreementRef: keccak256("historic designation and verified order")
            });
        evidence = _evidence(observations.agreedRecipientEvidenceCommitment(agreement));
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyAgreedRecipient(agreement, evidence, _authority(ROLE_VERIFIER));
        agreement.agreedByTransferWithinSecond = true;
        evidence = _evidence(observations.agreedRecipientEvidenceCommitment(agreement));
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyAgreedRecipient(agreement, evidence, _authority(ROLE_VERIFIER));
        require(observations.getPaymentObservation(receiptId).qualifies, "historic eligible receipt");
        require(observations.getAgreedRecipient(receiptId).terms.agreedAt == PAID_AT, "historic agreement time");
        require(
            payments.retainedByBeneficiary(obligation, RECIPIENT) == 5 && token.balanceOf(designee) == 5,
            "only the net historic receipt credited"
        );
        require(token.balanceOf(RECEIVING_TREASURY) == 3, "actual return retained");
        require(
            payments.getObligation(obligation).paid == 0 && payments.FUNDS().paymentReserved(obligation) == 8,
            "corrected payee still backed and unpaid"
        );
    }

    function testSameWalletWithoutExactPartEvidenceRemainsUncredited() public {
        bytes32 obligation = _establish(keccak256("tutor share"), RECIPIENT);
        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, RECIPIENT, 8);
        terms.attributionRef = bytes32(0);
        terms.returnDestination = address(0);
        bytes32 canonicalBlock = terms.transfer.blockHash;
        terms.transfer.blockHash = keccak256("orphaned block");
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));

        terms.transfer.blockHash = canonicalBlock;
        evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receiptId = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));
        require(observations.archivedAt(receiptId) == 0, "actual transfer is filed locally");
        require(!observations.getPaymentObservation(receiptId).qualifies, "same payee is insufficient");
        require(payments.getObligation(obligation).paid == 0 && token.balanceOf(RECIPIENT) == 8, "no part credit");
    }

    function testSameWalletWithDifferentBeneficiaryPreservesObservationWithoutCoveringCurrentPayee() public {
        bytes32 obligation = _establish(keccak256("current recipient shares this transfer address"), RECIPIENT);
        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, RECIPIENT, 8);
        terms.beneficiary = address(0xCAFF);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));

        SparkV15PaymentObservations.PaymentObservation memory record = observations.getPaymentObservation(receipt);
        require(record.terms.beneficiary == address(0xCAFF) && !record.qualifies, "shared address did not qualify");
        require(payments.getObligation(obligation).paid == 0 && token.balanceOf(RECIPIENT) == 8, "transfer retained");

        SparkV15PaymentObservations.AgreedRecipientTerms memory agreement =
            SparkV15PaymentObservations.AgreedRecipientTerms({
                paymentReceiptId: receipt,
                payee: terms.beneficiary,
                agreedAt: PAID_AT - 1,
                ceasedAt: 0,
                agreedByTransferWithinSecond: false,
                ceasedAfterTransferWithinSecond: false,
                agreementRef: keccak256("delegation for a different claim holder")
            });
        evidence = _evidence(observations.agreedRecipientEvidenceCommitment(agreement));
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyAgreedRecipient(agreement, evidence, _authority(ROLE_VERIFIER));
    }

    function testVerifiedAttributionCreditsAnExistingReceiptAtItsOwnVerificationTime() public {
        bytes32 obligation = _establish(keccak256("tutor share with later attribution"), RECIPIENT);
        bytes32 unrelated = _establish(keccak256("unrelated tutor share"), RECIPIENT);
        SparkV15PaymentObservations.PaymentTerms memory initial = _transfer(obligation, RECIPIENT, 8);
        initial.beneficiary = address(0);
        initial.attributionRef = bytes32(0);
        initial.returnDestination = address(0);
        uint256 firstEvidence = _evidence(observations.paymentEvidenceCommitment(initial));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(initial, firstEvidence, _authority(ROLE_VERIFIER));
        require(!observations.getPaymentObservation(receipt).qualifies, "transfer observed without attribution");
        require(payments.FUNDS().paymentReserved(obligation) == 8, "first observation keeps backing");

        requestVm.warp(VERIFIED_AT + 1);
        SparkV15PaymentObservations.PaymentAttributionTerms memory attribution =
            SparkV15PaymentObservations.PaymentAttributionTerms(
                receipt, RECIPIENT, VERIFIED_PAYMENT_TERMS, RECEIVING_TREASURY
            );
        SparkV15PaymentObservations.ReturnProof[] memory priorReturns = new SparkV15PaymentObservations.ReturnProof[](0);
        uint256 evidence = _evidence(observations.attributionEvidenceCommitment(attribution, priorReturns));
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyPaymentAttribution(
            attribution, evidence, priorReturns, _authority(ROLE_VERIFIER)
        );

        SparkV15PaymentObservations.PaymentObservation memory original = observations.getPaymentObservation(receipt);
        SparkV15PaymentObservations.PaymentAttribution memory adopted = observations.getPaymentAttribution(receipt);
        require(original.terms.attributionRef == bytes32(0) && original.terms.beneficiary == address(0), "original stays");
        require(original.terms.transfer.occurredAt == PAID_AT && original.qualifies, "same actual receipt now qualifies");
        require(original.verification.verifiedAt == VERIFIED_AT, "original observation time");
        require(adopted.terms.beneficiary == RECIPIENT && adopted.verification.verifiedAt == VERIFIED_AT + 1, "later basis");
        require(payments.getObligation(obligation).paid == 8 && payments.FUNDS().paymentReserved(obligation) == 0, "paid");
        require(payments.getObligation(unrelated).paid == 0 && payments.FUNDS().paymentReserved(unrelated) == 8, "other part");
        bytes32[] memory qualified = observations.getQualifiedPaymentIds(obligation);
        require(qualified.length == 1 && qualified[0] == receipt && token.balanceOf(RECIPIENT) == 8, "one actual transfer");

        SparkV15PaymentObservations.ReturnTerms memory returned = _outsideReturn(receipt, RECIPIENT, 3);
        evidence = _evidence(observations.returnEvidenceCommitment(returned));
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyReturn(returned, evidence, _authority(ROLE_VERIFIER));
        require(payments.getObligation(obligation).paid == 5 && token.balanceOf(RECEIVING_TREASURY) == 3, "retained net");
    }

    function testLaterAttributionAndHistoricalDelegationCreditTheSameRetainedTransfer() public {
        bytes32 obligation = _establish(keccak256("tutor share sent to a designated wallet"), RECIPIENT);
        address designee = address(0xD311);
        SparkV15PaymentObservations.PaymentTerms memory initial = _transfer(obligation, designee, 8);
        initial.beneficiary = address(0);
        initial.attributionRef = bytes32(0);
        initial.returnDestination = address(0);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(initial));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(initial, evidence, _authority(ROLE_VERIFIER));

        requestVm.warp(VERIFIED_AT + 1);
        SparkV15PaymentObservations.PaymentAttributionTerms memory attribution =
            SparkV15PaymentObservations.PaymentAttributionTerms(
                receipt, RECIPIENT, VERIFIED_PAYMENT_TERMS, RECEIVING_TREASURY
            );
        SparkV15PaymentObservations.ReturnProof[] memory priorReturns = new SparkV15PaymentObservations.ReturnProof[](0);
        evidence = _evidence(observations.attributionEvidenceCommitment(attribution, priorReturns));
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyPaymentAttribution(
            attribution, evidence, priorReturns, _authority(ROLE_VERIFIER)
        );
        require(!observations.getPaymentObservation(receipt).qualifies, "delegation has not been verified");
        require(payments.FUNDS().paymentReserved(obligation) == 8, "awaiting recipient evidence");

        SparkV15PaymentObservations.ReturnTerms memory returned = _outsideReturn(receipt, designee, 3);
        evidence = _evidence(observations.returnEvidenceCommitment(returned));
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyReturn(returned, evidence, _authority(ROLE_VERIFIER));
        require(payments.getObligation(obligation).paid == 0, "unqualified receipt remains uncredited");

        requestVm.warp(VERIFIED_AT + 2);
        SparkV15PaymentObservations.AgreedRecipientTerms memory agreement = SparkV15PaymentObservations.AgreedRecipientTerms({
            paymentReceiptId: receipt,
            payee: RECIPIENT,
            agreedAt: PAID_AT - 1,
            ceasedAt: PAID_AT + 1,
            agreedByTransferWithinSecond: false,
            ceasedAfterTransferWithinSecond: false,
            agreementRef: keccak256("designation in force when the original transfer occurred")
        });
        evidence = _evidence(observations.agreedRecipientEvidenceCommitment(agreement));
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyAgreedRecipient(agreement, evidence, _authority(ROLE_VERIFIER));
        require(observations.getPaymentObservation(receipt).terms.transfer.occurredAt == PAID_AT, "actual payment");
        require(observations.getPaymentAttribution(receipt).verification.verifiedAt == VERIFIED_AT + 1, "attribution time");
        require(observations.getAgreedRecipient(receipt).verification.verifiedAt == VERIFIED_AT + 2, "designation time");
        require(payments.getObligation(obligation).paid == 5 && payments.FUNDS().paymentReserved(obligation) == 3, "net paid");
        require(token.balanceOf(designee) == 5 && token.balanceOf(RECEIVING_TREASURY) == 3, "actual net retained");
    }

    function testPriorActualReturnCanBeVerifiedWithAttributionBeforeCreditingDirectPayment() public {
        bytes32 obligation = _establish(keccak256("tutor share already partially returned"), RECIPIENT);
        SparkV15PaymentObservations.PaymentTerms memory initial = _transfer(obligation, RECIPIENT, 8);
        initial.attributionRef = bytes32(0);
        initial.returnDestination = address(0);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(initial));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(initial, evidence, _authority(ROLE_VERIFIER));
        SparkV15PaymentObservations.ReturnTerms memory returned = _outsideReturn(receipt, RECIPIENT, 3);
        require(payments.getObligation(obligation).paid == 0, "awaiting attribution and return proof");

        requestVm.warp(VERIFIED_AT + 2);
        SparkV15PaymentObservations.ReturnProof[] memory priorReturns = new SparkV15PaymentObservations.ReturnProof[](1);
        priorReturns[0] = SparkV15PaymentObservations.ReturnProof(
            returned, _evidence(observations.returnEvidenceCommitment(returned))
        );
        SparkV15PaymentObservations.PaymentAttributionTerms memory attribution =
            SparkV15PaymentObservations.PaymentAttributionTerms(
                receipt, RECIPIENT, VERIFIED_PAYMENT_TERMS, RECEIVING_TREASURY
            );
        evidence = _evidence(observations.attributionEvidenceCommitment(attribution, priorReturns));
        requestVm.prank(VERIFIER_ACTOR);
        requestVm.expectRevert(SparkV15PaymentObservations.InvalidObservation.selector);
        observations.verifyPaymentAttribution(
            attribution, evidence, new SparkV15PaymentObservations.ReturnProof[](0), _authority(ROLE_VERIFIER)
        );
        require(payments.getObligation(obligation).paid == 0, "verified basis includes the known return");
        uint256 version = payments.getObligation(obligation).version;
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyPaymentAttribution(attribution, evidence, priorReturns, _authority(ROLE_VERIFIER));
        SparkV15Payments.Obligation memory item = payments.getObligation(obligation);
        require(item.version == version + 1 && item.paid == 5, "only one net credit");
        require(payments.FUNDS().paymentReserved(obligation) == 3, "unpaid balance retains backing");
        bytes32[] memory returnIds = observations.getReturnIds(receipt);
        SparkV15PaymentObservations.ReturnObservation memory saved = observations.getReturnObservation(returnIds[0]);
        require(saved.terms.transfer.occurredAt == VERIFIED_AT + 1, "actual return time");
        require(saved.verification.verifiedAt == VERIFIED_AT + 2 && token.balanceOf(RECIPIENT) == 5, "verified net");
    }

    function testCurrentEvidenceCanVerifyAReceiptForAnOlderObligation() public {
        uint256 originalPackage = requestPackageId;
        bytes32 obligation = _establish(keccak256("older tutor share"), RECIPIENT);
        requestPackageId = _registerRequestPackage(
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR), 2
        );
        SparkV15PaymentObservations.PaymentTerms memory terms = _transfer(obligation, RECIPIENT, 8);
        uint256 evidence = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receiptId = observations.verifyPayment(terms, evidence, _authority(ROLE_VERIFIER));
        SparkV15PaymentObservations.PaymentObservation memory fact = observations.getPaymentObservation(receiptId);
        require(fact.qualifies && fact.obligationPackageId == originalPackage, "current proof for older obligation");
        require(payments.getObligation(obligation).packageId == originalPackage, "original obligation rules retained");
        require(fact.verification.evidencePackageId == requestPackageId, "evidence has current package");
    }

    function _imposeFormalHold(bytes32 obligation) private returns (bytes32) {
        SparkV15PaymentHolds.HoldTerms memory hold = SparkV15PaymentHolds.HoldTerms({
            obligationId: obligation,
            caseId: keccak256("fixture accepted dispute"),
            noticeHash: keccak256("notice covers this part"),
            reviewAt: EXECUTION_DEADLINE,
            expectedVersion: payments.getObligation(obligation).version
        });
        uint256 evidence = _evidence(payments.HOLDS().formalHoldCommitment(hold, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        return payments.imposeFormalHold(hold, evidence, _authority(ROLE_VERIFIER));
    }

    function _establish(bytes32 part, address recipient) private returns (bytes32) {
        SparkV15Payments.PaymentTerms memory terms = SparkV15Payments.PaymentTerms({
            lessonId: keccak256("fixture group lesson"),
            paymentPart: part,
            recipient: recipient,
            originalDebitAccount: bytes32(0),
            originalDebitAmount: 0,
            amount: 8,
            agreedStart: DUE - 30 days,
            dueAt: DUE,
            executionDeadline: EXECUTION_DEADLINE,
            legalDeadline: LEGAL_DEADLINE,
            postLiftDeadline: 0,
            postLiftPeriod: 0,
            dueAtExact: true,
            executionDeadlineExact: true,
            legalDeadlineExact: true,
            postLiftDeadlineExact: false,
            settlementProposer: address(0xCAF1),
            settlementApprover: address(0xCAF2)
        });
        bytes32 basis = keccak256("individually established tutor share");
        uint256 evidence = _evidence(payments.paymentEvidenceCommitment(terms, basis));
        requestVm.prank(VERIFIER_ACTOR);
        return payments.establishPayment(terms, basis, evidence, _authority(ROLE_VERIFIER));
    }

    function _transfer(bytes32 obligation, address destination, uint128 amount)
        private
        returns (SparkV15PaymentObservations.PaymentTerms memory)
    {
        requestVm.warp(PAID_AT);
        CHAIN.roll(20);
        requestVm.prank(OUTSIDE_PAYER);
        require(token.transfer(destination, amount), "outside transfer");
        CHAIN.roll(21);
        bytes32 blockHash = keccak256("canonical payment block");
        CHAIN.setBlockhash(20, blockHash);
        requestVm.warp(VERIFIED_AT);
        return SparkV15PaymentObservations.PaymentTerms({
            obligationId: obligation,
            beneficiary: RECIPIENT,
            transfer: SparkV15PaymentObservations.Transfer({
                transactionHash: keccak256("outside transfer"),
                blockHash: blockHash,
                blockNumber: 20,
                logIndex: 0,
                occurredAt: PAID_AT,
                sender: OUTSIDE_PAYER,
                destination: destination,
                amount: amount
            }),
            evidenceAvailableAt: PAID_AT + 1,
            attributionRef: VERIFIED_PAYMENT_TERMS,
            returnDestination: RECEIVING_TREASURY
        });
    }

    function _outsideReturn(bytes32 receipt, address sender, uint128 amount)
        private
        returns (SparkV15PaymentObservations.ReturnTerms memory)
    {
        uint64 returnedAt = VERIFIED_AT + 1;
        requestVm.warp(returnedAt);
        CHAIN.roll(22);
        requestVm.prank(sender);
        require(token.transfer(RECEIVING_TREASURY, amount), "outside return");
        CHAIN.roll(23);
        bytes32 returnBlockHash = keccak256("canonical return block");
        CHAIN.setBlockhash(22, returnBlockHash);
        return SparkV15PaymentObservations.ReturnTerms({
            paymentReceiptId: receipt,
            transfer: SparkV15PaymentObservations.Transfer({
                transactionHash: keccak256("outside return"),
                blockHash: returnBlockHash,
                blockNumber: 22,
                logIndex: 2,
                occurredAt: returnedAt,
                sender: sender,
                destination: RECEIVING_TREASURY,
                amount: amount
            }),
            evidenceAvailableAt: 0,
            recoveryRef: keccak256("exact approved recovery decision")
        });
    }

    function _evidence(bytes32 commitment) private returns (uint256) {
        requestVm.prank(SOURCE_ACTOR);
        return evidenceRegistry.registerEvidence(
            AVAEvidenceRegistry.EvidenceRegistrationInput({
                appId: SparkV15.APP_ID,
                workflowKey: REQUEST_WORKFLOW,
                packageId: requestPackageId,
                roleKey: ROLE_SOURCE,
                subjectId: _authority(ROLE_SOURCE),
                commitment: commitment,
                evidenceTypeHash: keccak256("spark.v1.5.verified-record"),
                disclosurePolicyId: requestPolicyId,
                authorityId: _authority(ROLE_SOURCE),
                uri: "test:spark-v15-payment-observation"
            })
        );
    }
}
