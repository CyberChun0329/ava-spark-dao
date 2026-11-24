// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {SparkV15, SparkV15ApplicationModule} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15TemporaryHolds} from "../../../src/apps/spark/v15/SparkV15TemporaryHolds.sol";
import {SparkV15Returns} from "../../../src/apps/spark/v15/SparkV15Returns.sol";
import {IERC20} from "../../../src/apps/spark/legacy/interfaces/IERC20.sol";
import {RequestAllocationFixture} from "../../helpers/RequestAllocationFixture.sol";
import {MockERC20} from "../mocks/MockERC20.sol";

contract IndependentPaymentsTest is RequestAllocationFixture {
    uint64 private constant AGREED_START = 1_000_000;
    uint64 private constant TUTOR_DUE = AGREED_START + 30 days;
    uint64 private constant EPOCH = TUTOR_DUE - 3;
    uint64 private constant TUTOR_DEADLINE = TUTOR_DUE + 4;
    bytes32 private constant LESSON = keccak256("v1.5 group lesson");
    bytes32 private constant ORIGINAL_ACCOUNT = keccak256("fixture original A debit account");
    address private constant TUTOR = address(0x7001);
    address private constant PAYMENT_EXECUTOR = address(0x7002);
    address private constant PAYER = address(0x7003);
    address private constant REFUND_EXECUTOR = address(0x7004);
    address private constant REVIEWER_ONE = address(0x7005);
    address private constant REVIEWER_TWO = address(0x7006);
    address private constant NEW_ALLOCATOR = address(0x7007);
    address private constant SETTLEMENT_PROPOSER = address(0x7008);
    address private constant SETTLEMENT_APPROVER = address(0x7009);
    address private constant ALTERNATIVE_CONTACT = address(0x7010);
    bytes32 private constant REVIEWER_ONE_ID = keccak256("reviewer one");
    bytes32 private constant REVIEWER_TWO_ID = keccak256("reviewer two");
    bytes32 private constant NEW_ALLOCATOR_ID = keccak256("new allocator");

    MockERC20 private token;
    SparkV15Payments private payments;

    function setUp() public {
        requestVm.warp(EPOCH);
        _setUpRequestAllocation(
            SparkV15.APP_ID,
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR),
            SparkV15.OBJECT_PAYMENT_APPROVAL
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_ESTABLISH_PAYMENT, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_FORMAL_HOLD, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_LIFT_HOLD, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_VERIFY_POST_LIFT_CLOCK, true);
        identityRegistry.assignSubject(REVIEWER_ONE, SparkV15.APP_ID, ROLE_VERIFIER, REVIEWER_ONE_ID, "test:reviewer1");
        identityRegistry.assignSubject(REVIEWER_TWO, SparkV15.APP_ID, ROLE_VERIFIER, REVIEWER_TWO_ID, "test:reviewer2");
        token = new MockERC20("Spark fixture USD", "TUSD", 6);
        payments = new SparkV15Payments(requestAllocation, IERC20(address(token)), REQUEST_WORKFLOW, ROLE_VERIFIER);
        payments.bindHolds(
            new SparkV15PaymentHolds(address(payments), requestAllocation, REQUEST_WORKFLOW, ROLE_VERIFIER)
        );
        token.mint(address(payments.FUNDS()), 16);
    }

    function testExactAllocationRecordsAnApprovalBeforeTheNamedExecutorPaysTheTutor() public {
        bytes32 obligationId = _establishTutorPay();
        uint256 requestId = _recordApproval(obligationId, PAYMENT_EXECUTOR, 8, TUTOR_DEADLINE + 10, EPOCH + 1);

        AVARequestAllocation.RequestRecord memory request = requestAllocation.getRequest(requestId);
        SparkV15Payments.Approval memory approval = payments.getApproval(requestId);
        require(request.completed && request.effectHash == keccak256(abi.encode(address(payments), requestId, approval)), "approval effect");
        require(payments.getApproval(type(uint256).max).approver == address(0), "unrecorded approval");
        require(approval.approver == ALLOCATOR_ACTOR && approval.authorityId == _authority(ROLE_ALLOCATOR), "actor");
        require(approval.terms.executor == PAYMENT_EXECUTOR && approval.grantedAt == request.approvedAt + 1, "terms");
        require(token.balanceOf(TUTOR) == 0 && payments.getObligation(obligationId).paid == 0, "approval paid funds");

        requestVm.warp(TUTOR_DEADLINE);
        requestVm.prank(PAYMENT_EXECUTOR);
        uint256 receiptId = payments.pay(requestId, 8);

        SparkV15Payments.PaymentReceipt memory receipt = payments.getReceipt(receiptId);
        require(receipt.obligationId == obligationId && receipt.approvalRequestId == requestId, "missing lineage");
        require(receipt.executor == PAYMENT_EXECUTOR && receipt.paidAt == TUTOR_DEADLINE, "actual occurrence");
        require(token.balanceOf(TUTOR) == 8 && token.balanceOf(address(payments.FUNDS())) == 8, "wrong token effects");
        require(payments.getObligation(obligationId).paid == 8 && payments.FUNDS().reservedUnits() == 0, "outstanding");
    }

    function testOverlappingRefundHoldsLeaveTutorPayFreeAndOriginalRefundApprovalSurvivesRotation() public {
        token.mint(address(payments.FUNDS()), 10);
        bytes32 tutorPay = _establishTutorPay();
        bytes32 refund = _establishRefund();
        _establishTutorPortion(keccak256("A's agreed tutor-pay portion"), 2);
        _establishTutorPortion(keccak256("C's agreed tutor-pay portion"), 6);
        uint256 refundApproval = _recordApproval(refund, REFUND_EXECUTOR, 10, EPOCH + 14, EPOCH);
        uint256 tutorApproval = _recordApproval(tutorPay, PAYMENT_EXECUTOR, 8, TUTOR_DEADLINE + 10, EPOCH);
        require(
            payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 0 && payments.FUNDS().reservedUnits() == 26,
            "initial balances"
        );

        requestVm.warp(EPOCH + 2);
        bytes32 firstHold =
            _imposeHold(refund, keccak256("A disputed original debit"), REVIEWER_ONE, REVIEWER_ONE_ID, EPOCH + 8);
        _expectPaymentRefused(refundApproval, REFUND_EXECUTOR, 10);
        _expectPaymentRefused(tutorApproval, PAYMENT_EXECUTOR, 8);

        requestVm.warp(EPOCH + 4);
        identityRegistry.deactivateSubject(_authority(ROLE_ALLOCATOR));
        identityRegistry.assignSubject(
            NEW_ALLOCATOR, SparkV15.APP_ID, ROLE_ALLOCATOR, NEW_ALLOCATOR_ID, "test:rotation"
        );

        requestVm.warp(EPOCH + 6);
        bytes32 secondHold = _imposeHold(
            refund, keccak256("A claimed earlier credit restoration"), REVIEWER_TWO, REVIEWER_TWO_ID, EPOCH + 10
        );
        requestVm.warp(TUTOR_DEADLINE);
        requestVm.prank(PAYMENT_EXECUTOR);
        uint256 tutorReceipt = payments.pay(tutorApproval, 8);
        require(token.balanceOf(TUTOR) == 8 && payments.getReceipt(tutorReceipt).obligationId == tutorPay, "B paid");
        _expectPaymentRefused(tutorApproval, PAYMENT_EXECUTOR, 8);
        require(payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 0, "A paid during hold");

        requestVm.warp(EPOCH + 8);
        _liftHold(firstHold, refund, REVIEWER_ONE, REVIEWER_ONE_ID);
        require(payments.HOLDS().getStatus(refund).firstFullReleaseAt == 0, "release still partial");
        _expectPaymentRefused(refundApproval, REFUND_EXECUTOR, 10);

        requestVm.warp(EPOCH + 10);
        _liftHold(secondHold, refund, REVIEWER_TWO, REVIEWER_TWO_ID);
        require(payments.HOLDS().getStatus(refund).firstFullReleaseAt == EPOCH + 10, "missing first full release");
        require(payments.getObligation(refund).terms.executionDeadline == EPOCH + 5, "original deadline changed");

        requestVm.warp(EPOCH + 11);
        _expectPaymentRefused(refundApproval, PAYMENT_EXECUTOR, 10);
        requestVm.prank(REFUND_EXECUTOR);
        uint256 refundReceipt = payments.pay(refundApproval, 10);
        SparkV15Payments.PaymentReceipt memory receipt = payments.getReceipt(refundReceipt);
        require(receipt.creditAccount == ORIGINAL_ACCOUNT && receipt.recipient == PAYER, "original credit destination");
        require(receipt.approvalRequestId == refundApproval && receipt.executor == REFUND_EXECUTOR, "original approval");
        SparkV15Payments.Approval memory originalApproval = payments.getApproval(refundApproval);
        require(originalApproval.approver == ALLOCATOR_ACTOR, "changed approving actor");
        require(originalApproval.authorityId == _authority(ROLE_ALLOCATOR), "changed approving authority");
        require(
            payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 10 && payments.getObligation(refund).paid == 10,
            "A restored"
        );
        require(token.balanceOf(TUTOR) == 8 && token.balanceOf(PAYER) == 0, "A affected token recipients");
        require(
            token.balanceOf(address(payments.FUNDS())) == 18 && payments.FUNDS().reservedUnits() == 18, "credit backing"
        );
        require(payments.getReceipt(tutorReceipt).paidAt == TUTOR_DEADLINE, "B receipt changed");
    }

    function testExpiredOriginalRequiresArrangementAndReplacementByCurrentAllocator() public {
        bytes32 refund = _establishRefund();
        uint256 original = _recordApproval(refund, REFUND_EXECUTOR, 10, EPOCH + 9, EPOCH);
        requestVm.warp(EPOCH + 2);
        bytes32 hold = _imposeHold(refund, keccak256("refund discrepancy"), REVIEWER_ONE, REVIEWER_ONE_ID, EPOCH + 10);
        identityRegistry.deactivateSubject(_authority(ROLE_ALLOCATOR));
        identityRegistry.assignSubject(
            NEW_ALLOCATOR, SparkV15.APP_ID, ROLE_ALLOCATOR, NEW_ALLOCATOR_ID, "test:rotation"
        );
        requestVm.warp(EPOCH + 10);
        _liftHold(hold, refund, REVIEWER_ONE, REVIEWER_ONE_ID);

        SparkV15Payments.ApprovalTerms memory terms = _approvalTerms(refund, PAYMENT_EXECUTOR, 10, EPOCH + 14, original);
        uint256 replacement = _allocate(terms, NEW_ALLOCATOR, NEW_ALLOCATOR_ID, EPOCH + 20);
        requestVm.expectRevert(SparkV15Payments.InvalidApproval.selector);
        requestVm.prank(NEW_ALLOCATOR);
        payments.recordApproval(replacement, terms);
        requestVm.prank(NEW_ALLOCATOR);
        payments.recordReplacementArrangement(replacement, terms);
        requestVm.prank(NEW_ALLOCATOR);
        payments.recordApproval(replacement, terms);
        (uint256 prior, address arranger, bytes32 authority, uint64 release, uint64 arrangedAt) =
            payments.approvalArrangements(replacement);
        require(prior == original && arranger == NEW_ALLOCATOR && authority == NEW_ALLOCATOR_ID, "arrangement actors");
        require(release == EPOCH + 10 && arrangedAt == release, "arrangement clock");

        requestVm.warp(EPOCH + 11);
        _expectPaymentRefused(original, REFUND_EXECUTOR, 10);
        _expectPaymentRefused(replacement, REFUND_EXECUTOR, 10);
        requestVm.prank(PAYMENT_EXECUTOR);
        uint256 receipt = payments.pay(replacement, 10);
        require(payments.getReceipt(receipt).approvedOutstandingBefore == 10, "missing approved outstanding");
        require(payments.getApproval(replacement).terms.replacesRequestId == original, "missing original lineage");
        require(
            payments.getApproval(original).paid == 0 && payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 10, "refund"
        );
    }

    function testFirstApprovalAfterReleaseUsesOriginalRelativeCutoffAcrossAnotherHold() public {
        bytes32 refund = _establishRefund(0, 4);
        requestVm.warp(EPOCH + 2);
        bytes32 hold =
            _imposeHold(refund, keccak256("initial refund discrepancy"), REVIEWER_ONE, REVIEWER_ONE_ID, EPOCH + 10);
        requestVm.warp(EPOCH + 10);
        _liftHold(hold, refund, REVIEWER_ONE, REVIEWER_ONE_ID);
        require(payments.getObligation(refund).firstApprovalRequestId == 0, "unexpected original approval");
        require(payments.HOLDS().getStatus(refund).postLiftCutoff == EPOCH + 14, "relative cutoff");
        SparkV15Payments.ApprovalTerms memory terms = _approvalTerms(refund, REFUND_EXECUTOR, 10, EPOCH + 20, 0);
        uint256 first = _allocate(terms, ALLOCATOR_ACTOR, _authority(ROLE_ALLOCATOR), EPOCH + 20);
        requestVm.prank(ALLOCATOR_ACTOR);
        payments.recordApproval(first, terms);

        requestVm.warp(EPOCH + 11);
        bytes32 second =
            _imposeHold(refund, keccak256("later refund concern"), REVIEWER_TWO, REVIEWER_TWO_ID, EPOCH + 13);
        _expectPaymentRefused(first, REFUND_EXECUTOR, 10);
        requestVm.warp(EPOCH + 13);
        _liftHold(second, refund, REVIEWER_TWO, REVIEWER_TWO_ID);
        require(payments.HOLDS().getStatus(refund).postLiftCutoff == EPOCH + 14, "window restarted");
        requestVm.warp(EPOCH + 14);
        _expectPaymentRefused(first, REFUND_EXECUTOR, 4);
        uint256 clockEvidence = _registerEvidence(payments.HOLDS().postLiftClockCommitment(refund));
        requestVm.prank(VERIFIER_ACTOR);
        payments.verifyPostLiftClock(refund, clockEvidence, _authority(ROLE_VERIFIER));
        requestVm.prank(REFUND_EXECUTOR);
        payments.pay(first, 4);
        requestVm.warp(EPOCH + 15);
        _expectPaymentRefused(first, REFUND_EXECUTOR, 6);
        require(payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 4, "late payment changed balance");
    }

    function testEarlierVerifiedLegalRequirementAllowsPayBeforeThirtyDays() public {
        SparkV15Payments.PaymentTerms memory terms = _tutorTerms(keccak256("B's agreed tutor-pay portion"), 8);
        terms.dueAt = EPOCH + 1;
        bytes32 basis = keccak256("fixture: earlier statutory requirement and all other agreed conditions met");
        uint256 evidenceId = _registerEvidence(payments.paymentEvidenceCommitment(terms, basis));
        requestVm.expectRevert(SparkV15Payments.InvalidObligation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        payments.establishPayment(terms, basis, evidenceId, _authority(ROLE_VERIFIER));

        terms.legalDeadline = EPOCH + 2;
        terms.legalDeadlineExact = true;
        evidenceId = _registerEvidence(payments.paymentEvidenceCommitment(terms, basis));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 obligation = payments.establishPayment(terms, basis, evidenceId, _authority(ROLE_VERIFIER));
        uint256 approval = _recordApproval(obligation, PAYMENT_EXECUTOR, 8, TUTOR_DEADLINE, EPOCH);

        requestVm.warp(terms.legalDeadline);
        requestVm.prank(PAYMENT_EXECUTOR);
        payments.pay(approval, 4);
        requestVm.warp(TUTOR_DUE);
        _expectPaymentRefused(approval, PAYMENT_EXECUTOR, 4);
        require(token.balanceOf(TUTOR) == 4 && payments.getObligation(obligation).paid == 4, "early route");
    }

    function testOriginalPaymentApproverCannotReviewAndAnotherPartCannotUseTheCaseEvidence() public {
        token.mint(address(payments.FUNDS()), 2);
        bytes32 tutorPay = _establishTutorPay();
        bytes32 refund = _establishRefund();
        _recordApproval(refund, REFUND_EXECUTOR, 10, EPOCH + 14, EPOCH);
        bytes32 formerAllocatorAsReviewer = keccak256("former allocator as reviewer");
        identityRegistry.deactivateSubject(_authority(ROLE_ALLOCATOR));
        identityRegistry.assignSubject(
            ALLOCATOR_ACTOR, SparkV15.APP_ID, ROLE_VERIFIER, formerAllocatorAsReviewer, "test:reviewer rotation"
        );
        requestVm.warp(EPOCH + 2);
        SparkV15PaymentHolds.HoldTerms memory hold = _holdTerms(refund, keccak256("A refund dispute"), EPOCH + 8);
        uint256 evidenceId = _registerEvidence(payments.HOLDS().formalHoldCommitment(hold, ALLOCATOR_ACTOR));
        requestVm.expectRevert(SparkV15Payments.InvalidFormalHold.selector);
        requestVm.prank(ALLOCATOR_ACTOR);
        payments.imposeFormalHold(hold, evidenceId, formerAllocatorAsReviewer);

        evidenceId = _registerEvidence(payments.HOLDS().formalHoldCommitment(hold, REVIEWER_ONE));
        requestVm.prank(PAYER);
        (bool permitted, bytes memory errorData) =
            address(payments).call(abi.encodeCall(payments.imposeFormalHold, (hold, evidenceId, REVIEWER_ONE_ID)));
        require(
            !permitted
                && keccak256(errorData)
                    == keccak256(
                        abi.encodeWithSelector(AVACoreTypes.NotAuthorised.selector, PAYER, SparkV15.ACTION_FORMAL_HOLD)
                    ),
            "unassigned reviewer"
        );

        hold.obligationId = tutorPay;
        hold.expectedVersion = payments.getObligation(tutorPay).version;
        requestVm.expectRevert(SparkV15Payments.InvalidFormalHold.selector);
        requestVm.prank(REVIEWER_ONE);
        payments.imposeFormalHold(hold, evidenceId, REVIEWER_ONE_ID);
        require(payments.HOLDS().getStatus(tutorPay).activeFormalHolds == 0, "B affected by A matter");
        require(payments.HOLDS().getStatus(refund).activeFormalHolds == 0, "disqualified actor held A");
    }

    function testTemporaryHoldExpiresAtItsFormTimeAndExtendsAnUninterruptedFormalRelease() public {
        token.mint(address(payments.FUNDS()), 2);
        bytes32 tutorPay = _establishTutorPay();
        bytes32 refund = _establishRefund();
        uint256 tutorApproval = _recordApproval(tutorPay, PAYMENT_EXECUTOR, 8, EPOCH + 14, EPOCH);
        uint256 refundApproval = _recordApproval(refund, REFUND_EXECUTOR, 10, EPOCH + 14, EPOCH);
        requestVm.warp(EPOCH + 2);
        bytes32 formal = _imposeHold(refund, keccak256("formal A concern"), REVIEWER_ONE, REVIEWER_ONE_ID, EPOCH + 8);
        requestVm.warp(EPOCH + 6);
        bytes32 tempCase = keccak256("temporary A concern");
        bytes32 temporary = _placeTemporaryHold(refund, tempCase, EPOCH + 10);
        requestVm.warp(TUTOR_DEADLINE);
        requestVm.prank(PAYMENT_EXECUTOR);
        payments.pay(tutorApproval, 8);
        require(token.balanceOf(TUTOR) == 8, "B affected by A hold");
        requestVm.warp(EPOCH + 8);
        _liftHold(formal, refund, REVIEWER_ONE, REVIEWER_ONE_ID);
        require(!payments.HOLDS().getFormalHold(formal).completelyReleased, "temporary hold still active");
        require(payments.HOLDS().getStatus(refund).firstFullReleaseAt == 0, "window opened before expiry");
        _expectPaymentRefused(refundApproval, REFUND_EXECUTOR, 10);

        requestVm.warp(EPOCH + 10);
        require(payments.HOLDS().getTemporaryHold(temporary).terms.expiresAt == EPOCH + 10, "time changed");
        require(payments.HOLDS().getStatus(refund).firstFullReleaseAt == EPOCH + 10, "expiry did not resolve release");
        requestVm.prank(REFUND_EXECUTOR);
        payments.pay(refundApproval, 10);
        require(payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 10, "A not restored");
    }

    function testFormalDecisionReplacesTheMatchingTemporaryHoldAndSetterMustRecuse() public {
        bytes32 refund = _establishRefund();
        uint256 approval = _recordApproval(refund, REFUND_EXECUTOR, 10, EPOCH + 14, EPOCH);
        bytes32 reviewRole = keccak256("alternative contact later appointed reviewer");
        bytes32 concern = keccak256("A amount dispute");
        requestVm.warp(EPOCH + 2);
        bytes32 temporary = _placeTemporaryHold(refund, concern, EPOCH + 12);
        _expectPaymentRefused(approval, REFUND_EXECUTOR, 10);
        require(payments.temporarySetterFor(LESSON, concern, ALTERNATIVE_CONTACT), "temporary setter omitted");
        identityRegistry.assignSubject(
            ALTERNATIVE_CONTACT, SparkV15.APP_ID, ROLE_VERIFIER, reviewRole, "test:later-reviewer"
        );
        requestVm.warp(EPOCH + 3);
        SparkV15PaymentHolds.HoldTerms memory hold = _holdTerms(refund, concern, EPOCH + 8);
        uint256 evidence = _registerEvidence(payments.HOLDS().formalHoldCommitment(hold, ALTERNATIVE_CONTACT));
        requestVm.expectRevert(SparkV15Payments.InvalidFormalHold.selector);
        requestVm.prank(ALTERNATIVE_CONTACT);
        payments.imposeFormalHold(hold, evidence, reviewRole);
        bytes32 formal = _imposeHold(refund, concern, REVIEWER_ONE, REVIEWER_ONE_ID, EPOCH + 8);
        require(
            payments.HOLDS().getTemporaryHold(temporary).replacedBy == formal, "same concern temporary not replaced"
        );
        requestVm.warp(EPOCH + 8);
        _liftHold(formal, refund, REVIEWER_ONE, REVIEWER_ONE_ID);
        require(payments.HOLDS().getStatus(refund).firstFullReleaseAt == EPOCH + 8, "replaced amount still on hold");
        require(payments.temporarySetterFor(LESSON, concern, ALTERNATIVE_CONTACT), "setter erased on replacement");
        requestVm.prank(REFUND_EXECUTOR);
        payments.pay(approval, 10);
        require(payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 10, "A not restored");
    }

    function testAFormalHoldAfterOriginalDeadlineDoesNotOpenAWindow() public {
        bytes32 refund = _establishRefund(EPOCH + 80, 0);
        uint256 original = _recordApproval(refund, REFUND_EXECUTOR, 10, EPOCH + 80, EPOCH);
        requestVm.warp(EPOCH + 6);
        bytes32 hold = _imposeHold(refund, keccak256("late refund dispute"), REVIEWER_ONE, REVIEWER_ONE_ID, EPOCH + 8);
        requestVm.warp(EPOCH + 8);
        _liftHold(hold, refund, REVIEWER_ONE, REVIEWER_ONE_ID);
        _expectPaymentRefused(original, REFUND_EXECUTOR, 10);
        require(payments.HOLDS().getStatus(refund).postLiftCutoff == 0, "no hold at original deadline");
        require(payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 0, "gap changed balance");
        require(payments.HOLDS().getStatus(refund).lastFullReleaseAt == EPOCH + 8, "missing actual release");
    }

    function testFixedPostLiftDateUsesTheFormCutoffWithoutRestartingTheClock() public {
        bytes32 refund = _establishRefund(EPOCH + 80, 0);
        uint256 original = _recordApproval(refund, REFUND_EXECUTOR, 10, EPOCH + 100, EPOCH);
        requestVm.warp(EPOCH + 2);
        bytes32 hold = _imposeHold(refund, keccak256("refund on hold"), REVIEWER_ONE, REVIEWER_ONE_ID, EPOCH + 8);
        requestVm.warp(EPOCH + 8);
        _liftHold(hold, refund, REVIEWER_ONE, REVIEWER_ONE_ID);
        require(payments.HOLDS().getStatus(refund).postLiftCutoff == EPOCH + 80, "fixed date changed");
        requestVm.warp(EPOCH + 80);
        requestVm.prank(REFUND_EXECUTOR);
        payments.pay(original, 4);
        requestVm.warp(EPOCH + 81);
        _expectPaymentRefused(original, REFUND_EXECUTOR, 6);
    }

    function testEarlierReceiptsReduceTheCeilingAcrossDifferentApprovals() public {
        bytes32 refund = _establishRefund();
        uint256 first = _recordApproval(refund, REFUND_EXECUTOR, 10, EPOCH + 14, EPOCH);
        uint256 narrower = _recordApproval(refund, PAYMENT_EXECUTOR, 6, EPOCH + 14, EPOCH);
        requestVm.warp(EPOCH + 1);
        requestVm.prank(REFUND_EXECUTOR);
        payments.pay(first, 4);
        _expectPaymentRefused(narrower, PAYMENT_EXECUTOR, 3);
        requestVm.prank(PAYMENT_EXECUTOR);
        uint256 receipt = payments.pay(narrower, 2);
        require(payments.getReceipt(receipt).approvedOutstandingBefore == 2, "scope ignored retained receipt");
        require(payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 6, "incorrect credit");
    }

    function testAnActualCreditReturnReopensTheExactNetApprovalScope() public {
        SparkV15Returns returnLedger = payments.RETURNS();
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_AUTHORISE_PAYMENT_RETURN, true);
        bytes32 refund = _establishRefund();
        uint256 approval = _recordApproval(refund, REFUND_EXECUTOR, 4, EPOCH + 5, EPOCH);
        requestVm.warp(EPOCH + 1);
        requestVm.prank(REFUND_EXECUTOR);
        uint256 firstReceipt = payments.pay(approval, 4);
        _expectPaymentRefused(approval, REFUND_EXECUTOR, 4);

        requestVm.warp(EPOCH + 2);
        SparkV15Returns.ReturnTerms memory terms = SparkV15Returns.ReturnTerms({
            receiptId: firstReceipt, amount: 4, recoveryRef: keccak256("recorded and notified refund return terms")
        });
        uint256 evidenceId = _registerEvidence(returnLedger.returnEvidenceCommitment(terms));
        requestVm.expectRevert(SparkV15Payments.InvalidReturn.selector);
        requestVm.prank(PAYER);
        payments.applyPaymentReturn(firstReceipt, PAYER, 4);
        requestVm.expectRevert(SparkV15Returns.InvalidReturn.selector);
        requestVm.prank(PAYER);
        returnLedger.returnPayment(terms, evidenceId);
        requestVm.prank(VERIFIER_ACTOR);
        returnLedger.authorisePaymentReturn(terms, evidenceId, _authority(ROLE_VERIFIER));
        requestVm.expectRevert(SparkV15Returns.InvalidReturn.selector);
        requestVm.prank(REFUND_EXECUTOR);
        returnLedger.returnPayment(terms, evidenceId);
        requestVm.prank(PAYER);
        uint256 returnId = returnLedger.returnPayment(terms, evidenceId);
        require(returnLedger.getPaymentReturn(returnId).terms.receiptId == firstReceipt, "return lost its receipt");
        require(returnLedger.getPaymentReturn(returnId).creditAccount == ORIGINAL_ACCOUNT, "return lost account");
        require(payments.getReceipt(firstReceipt).amount == 4, "original receipt rewritten");
        require(
            payments.FUNDS().reservedUnits() == 10 && payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 0,
            "refund backing"
        );
        require(payments.getObligation(refund).paid == 0, "returned receipt still counted");

        requestVm.warp(EPOCH + 3);
        requestVm.prank(REFUND_EXECUTOR);
        uint256 secondReceipt = payments.pay(approval, 4);
        require(
            secondReceipt != firstReceipt && payments.FUNDS().creditBalance(ORIGINAL_ACCOUNT) == 4, "repayment missing"
        );
        require(payments.getReceipt(secondReceipt).approvedOutstandingBefore == 4, "approval scope not restored");
        requestVm.expectRevert(SparkV15Returns.InvalidReturn.selector);
        requestVm.prank(PAYER);
        returnLedger.returnPayment(terms, evidenceId);
    }

    function testARefundHoldStopsPaymentAndPreservesAnApprovalGrantedWhileItWasHeld() public {
        bytes32 refund = _establishRefund(EPOCH + 4, 0);
        requestVm.warp(EPOCH + 2);
        bytes32 hold = _imposeHold(refund, keccak256("A-only concern"), REVIEWER_ONE, REVIEWER_ONE_ID, EPOCH + 3);
        uint256 approval = _recordApproval(refund, REFUND_EXECUTOR, 10, EPOCH + 5, EPOCH + 2);
        _expectPaymentRefused(approval, REFUND_EXECUTOR, 10);
        requestVm.warp(EPOCH + 3);
        _liftHold(hold, refund, REVIEWER_ONE, REVIEWER_ONE_ID);
        require(payments.HOLDS().getStatus(refund).firstFullReleaseAt == 0, "opened a replacement window");

        requestVm.warp(EPOCH + 5);
        requestVm.prank(REFUND_EXECUTOR);
        uint256 receiptId = payments.pay(approval, 10);
        SparkV15Payments.PaymentReceipt memory receipt = payments.getReceipt(receiptId);
        require(receipt.approvalRequestId == approval && receipt.paidAt == EPOCH + 5, "original permission and payment");
        require(receipt.promptCutoff == EPOCH + 4 && !receipt.promptCutoffMet, "missing prompt-payment result");
    }

    function testRefundEvidenceBindsLessonAccountRecipientAndRulePackage() public {
        SparkV15Payments.PaymentTerms memory terms = _refundTerms(EPOCH + 14, 0);
        bytes32 basis = keccak256("verified A original debit");
        uint256 evidenceId = _registerEvidence(payments.paymentEvidenceCommitment(terms, basis));

        terms.lessonId = keccak256("different lesson");
        _expectObligationRefused(terms, basis, evidenceId);
        terms.lessonId = LESSON;
        terms.originalDebitAccount = keccak256("different original account");
        _expectObligationRefused(terms, basis, evidenceId);
        terms.originalDebitAccount = ORIGINAL_ACCOUNT;
        terms.recipient = TUTOR;
        _expectObligationRefused(terms, basis, evidenceId);
        terms.recipient = PAYER;

        _registerRequestPackage(
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR), 2
        );
        require(
            packageRegistry.getActivePackageId(SparkV15.APP_ID, REQUEST_WORKFLOW) != requestPackageId, "new package"
        );
        requestVm.expectRevert();
        requestVm.prank(VERIFIER_ACTOR);
        payments.establishPayment(terms, basis, evidenceId, _authority(ROLE_VERIFIER));
        require(payments.FUNDS().reservedUnits() == 0, "unmatched evidence reserved funds");
    }

    function _establishTutorPay() private returns (bytes32) {
        return _establishTutorPortion(keccak256("B's agreed tutor-pay portion"), 8);
    }

    function _establishTutorPortion(bytes32 portion, uint128 amount) private returns (bytes32) {
        SparkV15Payments.PaymentTerms memory terms = _tutorTerms(portion, amount);
        bytes32 basis = keccak256("fixture: completed group settlement, B teacher wage terms, verification and clock");
        uint256 evidenceId = _registerEvidence(payments.paymentEvidenceCommitment(terms, basis));
        requestVm.prank(VERIFIER_ACTOR);
        return payments.establishPayment(terms, basis, evidenceId, _authority(ROLE_VERIFIER));
    }

    function _tutorTerms(bytes32 portion, uint128 amount) private pure returns (SparkV15Payments.PaymentTerms memory) {
        return SparkV15Payments.PaymentTerms({
            lessonId: LESSON,
            paymentPart: portion,
            recipient: TUTOR,
            originalDebitAccount: bytes32(0),
            originalDebitAmount: 0,
            amount: amount,
            agreedStart: AGREED_START,
            dueAt: TUTOR_DUE,
            executionDeadline: TUTOR_DEADLINE,
            legalDeadline: 0,
            postLiftDeadline: 0,
            postLiftPeriod: 0,
            dueAtExact: true,
            executionDeadlineExact: true,
            legalDeadlineExact: false,
            postLiftDeadlineExact: false,
            settlementProposer: SETTLEMENT_PROPOSER,
            settlementApprover: SETTLEMENT_APPROVER
        });
    }

    function _establishRefund() private returns (bytes32) {
        return _establishRefund(EPOCH + 14, 0);
    }

    function _establishRefund(uint64 fixedCutoff, uint64 duration) private returns (bytes32) {
        SparkV15Payments.PaymentTerms memory terms = _refundTerms(fixedCutoff, duration);
        bytes32 basis = keccak256("fixture: A original debit and 10 final charge, refund conditions and form cutoffs");
        uint256 evidenceId = _registerEvidence(payments.paymentEvidenceCommitment(terms, basis));
        requestVm.prank(VERIFIER_ACTOR);
        return payments.establishPayment(terms, basis, evidenceId, _authority(ROLE_VERIFIER));
    }

    function _refundTerms(uint64 fixedCutoff, uint64 duration)
        private
        pure
        returns (SparkV15Payments.PaymentTerms memory)
    {
        return SparkV15Payments.PaymentTerms({
            lessonId: LESSON,
            paymentPart: keccak256("A's lesson refund"),
            recipient: PAYER,
            originalDebitAccount: ORIGINAL_ACCOUNT,
            originalDebitAmount: 20,
            amount: 10,
            agreedStart: 0,
            dueAt: EPOCH + 1,
            executionDeadline: EPOCH + 5,
            legalDeadline: 0,
            postLiftDeadline: fixedCutoff,
            postLiftPeriod: duration,
            dueAtExact: true,
            executionDeadlineExact: true,
            legalDeadlineExact: false,
            postLiftDeadlineExact: fixedCutoff != 0,
            settlementProposer: SETTLEMENT_PROPOSER,
            settlementApprover: SETTLEMENT_APPROVER
        });
    }

    function _registerEvidence(bytes32 evidenceCommitment) private returns (uint256) {
        requestVm.prank(SOURCE_ACTOR);
        return evidenceRegistry.registerEvidence(
            AVAEvidenceRegistry.EvidenceRegistrationInput({
                appId: SparkV15.APP_ID,
                workflowKey: REQUEST_WORKFLOW,
                packageId: requestPackageId,
                roleKey: ROLE_SOURCE,
                subjectId: _authority(ROLE_SOURCE),
                commitment: evidenceCommitment,
                evidenceTypeHash: keccak256("spark.v1.5.verified-record"),
                disclosurePolicyId: requestPolicyId,
                authorityId: _authority(ROLE_SOURCE),
                uri: "test:spark-v15-established-group-wage"
            })
        );
    }

    function _recordApproval(bytes32 obligationId, address executor, uint128 ceiling, uint64 validThrough, uint64 nowAt)
        private
        returns (uint256 requestId)
    {
        SparkV15Payments.ApprovalTerms memory terms = _approvalTerms(obligationId, executor, ceiling, validThrough, 0);
        requestId = _allocate(terms, ALLOCATOR_ACTOR, _authority(ROLE_ALLOCATOR), TUTOR_DUE);
        requestVm.warp(nowAt);
        requestVm.prank(ALLOCATOR_ACTOR);
        payments.recordApproval(requestId, terms);
    }

    function _approvalTerms(
        bytes32 obligationId,
        address executor,
        uint128 ceiling,
        uint64 validThrough,
        uint256 original
    ) private pure returns (SparkV15Payments.ApprovalTerms memory) {
        return SparkV15Payments.ApprovalTerms(obligationId, executor, ceiling, validThrough, original);
    }

    function _allocate(
        SparkV15Payments.ApprovalTerms memory terms,
        address allocator,
        bytes32 authorityId,
        uint64 requestExpiry
    ) private returns (uint256 requestId) {
        bytes32 hash = payments.approvalParameters(terms);
        uint256 status = _createRequestState(
            address(payments), SparkV15.RESPONSE_APPROVE_PAYMENT, hash, SparkV15.APPROVAL_BURDEN, requestExpiry
        );
        requestId = _createRequest(
            AVARequestAllocation.RequestInput(
                status,
                address(payments),
                SparkV15.RESPONSE_APPROVE_PAYMENT,
                hash,
                SparkV15.APPROVAL_BURDEN,
                requestExpiry
            )
        );
        requestVm.prank(allocator);
        requestAllocation.approve(requestId, ROLE_ALLOCATOR, authorityId);
    }

    function _imposeHold(bytes32 obligationId, bytes32 caseId, address reviewer, bytes32 authorityId, uint64 reviewAt)
        private
        returns (bytes32)
    {
        SparkV15PaymentHolds.HoldTerms memory hold = _holdTerms(obligationId, caseId, reviewAt);
        uint256 evidenceId = _registerEvidence(payments.HOLDS().formalHoldCommitment(hold, reviewer));
        requestVm.prank(reviewer);
        return payments.imposeFormalHold(hold, evidenceId, authorityId);
    }

    function _holdTerms(bytes32 obligationId, bytes32 caseId, uint64 reviewAt)
        private
        view
        returns (SparkV15PaymentHolds.HoldTerms memory)
    {
        return SparkV15PaymentHolds.HoldTerms({
            obligationId: obligationId,
            caseId: caseId,
            noticeHash: keccak256(abi.encode("fixture notice delivered to A with reasons and review date", caseId)),
            reviewAt: reviewAt,
            expectedVersion: payments.getObligation(obligationId).version
        });
    }

    function _liftHold(bytes32 holdId, bytes32 obligationId, address reviewer, bytes32 authorityId) private {
        uint256 version = payments.getObligation(obligationId).version;
        bytes32 disposition = keccak256(abi.encode("verified original debit and no prior restoration", holdId));
        uint256 evidenceId =
            _registerEvidence(payments.HOLDS().formalLiftCommitment(holdId, disposition, version, reviewer));
        requestVm.prank(reviewer);
        payments.liftFormalHold(holdId, disposition, version, evidenceId, authorityId);
    }

    function _expectPaymentRefused(uint256 approvalId, address executor, uint128 amount) private {
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(executor);
        payments.pay(approvalId, amount);
    }

    function _placeTemporaryHold(bytes32 obligationId, bytes32 caseId, uint64 expiry) private returns (bytes32) {
        authorityMatrix.setPermission(
            SparkV15.APP_ID, SparkV15.ALTERNATIVE_CONTACT_ROLE, SparkV15.ACTION_TEMPORARY_HOLD, true
        );
        bytes32 authorityId = keccak256("fixture named alternative contact");
        identityRegistry.assignSubject(
            ALTERNATIVE_CONTACT, SparkV15.APP_ID, SparkV15.ALTERNATIVE_CONTACT_ROLE, authorityId, "test:alternative"
        );
        SparkV15TemporaryHolds.Terms memory terms = SparkV15TemporaryHolds.Terms({
            obligationId: obligationId,
            caseId: caseId,
            noticeHash: keccak256("verified immediate notice to A and partners"),
            authorisedAt: EPOCH,
            expiresAt: expiry,
            expectedVersion: payments.getObligation(obligationId).version
        });
        uint256 evidenceId = _registerEvidence(payments.HOLDS().temporaryHoldCommitment(terms, ALTERNATIVE_CONTACT));
        requestVm.prank(ALTERNATIVE_CONTACT);
        return payments.imposeTemporaryHold(terms, evidenceId, authorityId);
    }

    function _expectObligationRefused(SparkV15Payments.PaymentTerms memory terms, bytes32 basis, uint256 evidenceId)
        private
    {
        requestVm.expectRevert(SparkV15Payments.InvalidObligation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        payments.establishPayment(terms, basis, evidenceId, _authority(ROLE_VERIFIER));
    }
}
