// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {SparkV15, SparkV15ApplicationModule} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {
    ISparkV15BookingChanges,
    ISparkV15BookingFunds,
    SparkV15Booking,
    SparkV15BookingOpening
} from "../../../src/apps/spark/v15/SparkV15Booking.sol";
import {SparkV15BookingPrefunding} from "../../../src/apps/spark/v15/SparkV15BookingPrefunding.sol";
import {SparkV15CourseNotices} from "../../../src/apps/spark/v15/SparkV15CourseNotices.sol";
import {SparkV15TeachingEnd} from "../../../src/apps/spark/v15/SparkV15TeachingEnd.sol";
import {SparkV15BookingChanges} from "../../../src/apps/spark/v15/SparkV15BookingChanges.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {
    ISparkV15AdoptedDispositions,
    ISparkV15SettlementPaymentPolicy,
    SparkV15Payments
} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15PaymentTakeover} from "../../../src/apps/spark/v15/SparkV15PaymentTakeover.sol";
import {
    SparkV15ConcernIntake,
    SparkV15ReviewActions,
    SparkV15ReviewCases,
    SparkV15ReviewContext
} from "../../../src/apps/spark/v15/SparkV15ReviewCases.sol";
import {ISparkV15SettlementRemedies, SparkV15Settlement} from "../../../src/apps/spark/v15/SparkV15Settlement.sol";
import {SparkV15CustomerRedress, SparkV15LessonRemedies} from "../../../src/apps/spark/v15/SparkV15LessonRemedies.sol";
import {
    ISparkV15SettlementActors,
    SparkV15SettlementAlternatives
} from "../../../src/apps/spark/v15/SparkV15SettlementAlternatives.sol";
import {SparkV15SettlementOccurrences} from "../../../src/apps/spark/v15/SparkV15SettlementOccurrences.sol";
import {IERC20} from "../../../src/apps/spark/legacy/interfaces/IERC20.sol";
import {RequestAllocationFixture} from "../../helpers/RequestAllocationFixture.sol";
import {MockERC20} from "../mocks/MockERC20.sol";
import {BookingSignatureVm} from "./Booking.t.sol";

contract LessonSettlementTest is RequestAllocationFixture {
    uint64 private constant EPOCH = 1_000_000;
    uint64 private constant LOCK = EPOCH + 1 days;
    uint64 private constant START = EPOCH + 2 days;
    uint64 private constant END = START + 1 hours;
    uint64 private constant WAGE_DUE = START + 30 days;
    bytes32 private constant LESSON = keccak256("A, B and C group lesson");
    bytes32 private constant AGREEMENT = keccak256("signed teaching services agreement");
    bytes32 private constant TUTOR_CHANNEL = keccak256("signed tutor notice channel");
    bytes32 private constant CHANGE_TERMS = keccak256("signed cancellation and change terms");
    bytes32 private constant DOCUMENTS = keccak256("provided terms and course documents");
    bytes32 private constant CREDIT_PROVIDER_ID = keccak256("lesson credit provider");
    bytes32 private constant REVIEWER_ID = keccak256("independent hold reviewer");
    address private constant PROVIDER = address(0x7201);
    address private constant TUTOR = address(0x7202);
    address private constant COORDINATOR = address(0x7203);
    address private constant PAYER_A = address(0x7204);
    address private constant WAGE_RECIPIENT = address(0x7205);
    address private constant EXECUTOR = address(0x7206);
    address private constant REVIEWER = address(0x7207);
    address private constant REPLACEMENT = address(0x7208);

    MockERC20 private token;
    SparkV15Funds private funds;
    SparkV15Booking private booking;
    SparkV15Payments private payments;
    SparkV15Settlement private settlement;
    SparkV15SettlementAlternatives private alternatives;

    struct ReviewedWage {
        SparkV15ReviewCases review;
        bytes32 caseId;
        bytes32 coordinator;
        bytes32 paymentCommitment;
        bytes32 partiesHash;
        uint256 retained;
        uint256 reviewed;
        uint256 approval;
        uint256 earlierReceipt;
        SparkV15Payments.PaymentRevision revision;
    }

    function setUp() public {
        requestVm.warp(EPOCH);
        _setUpRequestAllocation(
            SparkV15.APP_ID,
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR),
            SparkV15.OBJECT_PAYMENT_APPROVAL
        );
        token = new MockERC20("Local settlement token", "STL", 6);
        payments = new SparkV15Payments(requestAllocation, IERC20(address(token)), REQUEST_WORKFLOW, ROLE_VERIFIER);
        payments.bindHolds(
            new SparkV15PaymentHolds(address(payments), requestAllocation, REQUEST_WORKFLOW, ROLE_VERIFIER)
        );
        funds = payments.FUNDS();
        booking = new SparkV15Booking(
            requestAllocation,
            ISparkV15BookingFunds(address(funds)),
            REQUEST_WORKFLOW,
            ROLE_SOURCE,
            ROLE_VERIFIER,
            PROVIDER
        );
        booking.bindOpening(new SparkV15BookingOpening(
            booking, new SparkV15BookingPrefunding(booking), new SparkV15TeachingEnd(booking), new SparkV15CourseNotices(booking)
        ));
        settlement = new SparkV15Settlement(booking, payments);
        alternatives =
            new SparkV15SettlementAlternatives(booking, payments, ISparkV15SettlementActors(address(settlement)));
        settlement.bindAlternatives(alternatives);
        payments.bindSettlementPolicy(ISparkV15SettlementPaymentPolicy(address(settlement)));
        identityRegistry.assignSubject(
            COORDINATOR, SparkV15.APP_ID, ROLE_SOURCE, keccak256("lesson coordinator"), "test:coordinator"
        );
        identityRegistry.assignSubject(REVIEWER, SparkV15.APP_ID, ROLE_VERIFIER, REVIEWER_ID, "test:reviewer");
        identityRegistry.assignSubject(
            PROVIDER, SparkV15.APP_ID, funds.CREDIT_PROVIDER_ROLE(), CREDIT_PROVIDER_ID, "test:provider"
        );
        identityRegistry.assignSubject(
            address(booking), SparkV15.APP_ID, funds.BOOKING_ROLE(), keccak256("booking contract"), "test:booking"
        );
        identityRegistry.assignSubject(
            address(settlement),
            SparkV15.APP_ID,
            payments.settlementRole(),
            keccak256("settlement contract"),
            "test:settlement"
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, booking.ACTION_COORDINATE_BOOKING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, booking.ACTION_VERIFY_PREFUNDING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, booking.ACTION_VERIFY_TEACHING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, funds.BOOKING_ROLE(), funds.ACTION_MANAGE_LESSON_FUNDS(), true);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, funds.CREDIT_PROVIDER_ROLE(), funds.ACTION_OFFER_RECHARGE(), true
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, settlement.ACTION_PROPOSE_GROUP_SETTLEMENT(), true);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, settlement.ACTION_APPROVE_GROUP_SETTLEMENT(), true
        );
        authorityMatrix.setPermission(
            SparkV15.APP_ID, payments.settlementRole(), payments.ACTION_RECORD_SETTLEMENT_OBLIGATION(), true
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_FORMAL_HOLD, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_LIFT_HOLD, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, alternatives.ACTION_CONFIRM_ONE_TO_ONE(), true);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, alternatives.ACTION_VERIFY_ONE_TO_ONE_ABSENCE(), true
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, alternatives.ACTION_IMPOSE_FEE_HOLD(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, alternatives.ACTION_LIFT_FEE_HOLD(), true);
    }

    function testBookedGroupSettlementFundsTheRefundAndThreeAgreedWagePortions() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(3, true);
        _propose(input);
        SparkV15Settlement.GroupPreview memory preview = settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
        require(preview.attendanceConfirmations == 2 && preview.totalTutorPay == 16, "wrong group outcome");
        require(preview.payments.length == 4, "wrong obligation count");
        uint256 approvalEvidence = _evidence(preview.basis);
        uint256[] memory paymentEvidence = new uint256[](4);
        for (uint256 i; i < paymentEvidence.length; ++i) {
            paymentEvidence[i] = _evidence(payments.paymentEvidenceCommitment(preview.payments[i], preview.basis));
        }

        uint256 held = funds.lessonReserved(LESSON);
        uint256 correctEvidence = paymentEvidence[3];
        paymentEvidence[3] = paymentEvidence[2];
        requestVm.expectRevert(SparkV15Payments.InvalidObligation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        settlement.approveOrdinaryGroup(LESSON, input, approvalEvidence, paymentEvidence);
        require(settlement.getGroupSettlement(LESSON).basis == bytes32(0), "incomplete settlement recorded");
        require(funds.lessonReserved(LESSON) == held, "wrong payment evidence consumed backing");

        paymentEvidence[3] = correctEvidence;
        requestVm.prank(VERIFIER_ACTOR);
        settlement.approveOrdinaryGroup(LESSON, input, approvalEvidence, paymentEvidence);
        require(funds.lessonReserved(LESSON) == held - 26, "obligations did not use lesson backing");
        require(funds.reservedUnits() == held, "settlement duplicated reserves");

        SparkV15Settlement.SeatSettlement memory a = settlement.getSeatSettlement(LESSON, input.seats[0].formId);
        SparkV15Settlement.SeatSettlement memory b = settlement.getSeatSettlement(LESSON, input.seats[1].formId);
        SparkV15Settlement.SeatSettlement memory c = settlement.getSeatSettlement(LESSON, input.seats[2].formId);
        require(a.debited == 20 && a.feeDue == 10 && a.refundDue == 10 && a.tutorPay == 2, "A assessment");
        require(b.feeDue == 20 && b.refundDue == 0 && b.tutorPay == 8, "B assessment");
        require(c.feeDue == 20 && c.refundDue == 0 && c.tutorPay == 6, "C assessment");
        SparkV15Payments.Obligation memory refund = payments.getObligation(a.refundObligationId);
        require(refund.terms.recipient == PAYER_A, "refund did not retain debit account owner");
        require(refund.terms.originalDebitAccount == funds.creditAccount(PAYER_A), "refund used a different account");
        require(refund.terms.settlementProposer == COORDINATOR, "proposer not retained");
        require(refund.terms.settlementApprover == VERIFIER_ACTOR, "approver not retained");
        require(funds.paymentReserved(a.tutorObligationId) == 2, "A tutor reserve");
        require(funds.paymentReserved(c.tutorObligationId) == 6, "C tutor reserve");

        uint256 refundApproval = _approvePayment(a.refundObligationId, 10);
        uint256 wageApproval = _approvePayment(b.tutorObligationId, 8);
        bytes32 holdId = _holdRefund(a.refundObligationId);
        requestVm.warp(WAGE_DUE);
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(refundApproval, 10);
        requestVm.prank(EXECUTOR);
        uint256 wageReceipt = payments.pay(wageApproval, 8);
        require(payments.getReceipt(wageReceipt).obligationId == b.tutorObligationId, "wage receipt scope");
        require(token.balanceOf(WAGE_RECIPIENT) == 8 && token.balanceOf(TUTOR) == 0, "wrong destination");
        require(funds.paymentReserved(a.refundObligationId) == 10, "held refund backing spent");

        _releaseRefund(holdId, a.refundObligationId);
        requestVm.prank(EXECUTOR);
        uint256 refundReceipt = payments.pay(refundApproval, 10);
        require(
            payments.getReceipt(refundReceipt).creditAccount == funds.creditAccount(PAYER_A), "refund receipt scope"
        );
        require(funds.creditBalance(funds.creditAccount(PAYER_A)) == 10, "actual debit credit not restored");
        require(funds.creditBalance(funds.creditAccount(_customer(0))) == 0, "customer received payer's credit");
    }

    function testProviderEarlyGroupUsesSeparateVerifiedAmountsAndPaysUnheldSeat() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndStartGroupWithoutPermission();
        bytes32 formA = input.seats[0].formId;
        bytes32 formB = input.seats[1].formId;
        _propose(input);
        SparkV15Settlement.GroupPreview memory whole = settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
        require(whole.payments.length == 4 && whole.totalTutorPay == 8, "missing separately verified amounts");

        address interestedSource = _customer(1);
        bytes32 sourceId = keccak256("source role held by B's customer");
        identityRegistry.assignSubject(interestedSource, SparkV15.APP_ID, ROLE_SOURCE, sourceId, "test:seat-b-source");
        uint256 evidence = _evidenceFrom(
            whole.basis, keccak256("verified Spark lesson settlement record"), interestedSource, sourceId
        );
        requestVm.expectRevert(SparkV15Settlement.InterestedSettlementActor.selector);
        requestVm.prank(VERIFIER_ACTOR);
        settlement.approveOrdinaryGroup(LESSON, input, evidence, new uint256[](4));
        require(!settlement.hasSeatSettlement(LESSON, formA), "interested source approved a settlement");

        bytes32 feeCase = _holdFee(formA);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);

        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.DeferredByHold;
        input.seats[0].feeHoldCaseId = feeCase;
        _propose(input);
        bytes32 partialBasis = _approveSettlement(input);
        require(!settlement.getSettlementTranche(partialBasis).complete, "held seat completed the lesson");
        require(!settlement.hasSeatSettlement(LESSON, formA), "held fee was assessed");
        SparkV15Settlement.SeatSettlement memory seatB = settlement.getSeatSettlement(LESSON, formB);
        require(seatB.debited == 20 && seatB.feeDue == 9 && seatB.refundDue == 11, "B's verified amounts or debit lost");
        require(seatB.tutorPay == 3, "B received A's tutor amount");
        uint256 refundB = _approvePayment(seatB.refundObligationId, 11);
        uint256 wageB = _approvePayment(seatB.tutorObligationId, 3);
        requestVm.warp(WAGE_DUE);
        requestVm.prank(EXECUTOR);
        payments.pay(refundB, 11);
        requestVm.prank(EXECUTOR);
        payments.pay(wageB, 3);
        require(funds.creditBalance(funds.creditAccount(_payer(1))) == 11, "B's original account was not restored");
        require(token.balanceOf(WAGE_RECIPIENT) == 3, "independent wage did not pay while A was held");

        _liftFee(feeCase);
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.ProviderStartedEarly;
        input.seats[0].feeHoldCaseId = bytes32(0);
        input.seats[1].disposition = SparkV15Settlement.SeatDisposition.PreviouslySettled;
        _propose(input);
        _approveSettlement(input);
        require(settlement.getGroupSettlement(LESSON).complete, "reviewed fee did not complete the lesson");
        SparkV15Settlement.SeatSettlement memory seatA = settlement.getSeatSettlement(LESSON, formA);
        require(seatA.debited == 20 && seatA.feeDue == 13 && seatA.refundDue == 7, "A's verified amounts or debit lost");
        require(seatA.tutorPay == 5 && settlement.getGroupSettlement(LESSON).totalTutorPay == 8, "wrong final tutor pay");
        uint256 refundA = _approvePaymentUntil(seatA.refundObligationId, 7, WAGE_DUE + 1 hours);
        uint256 wageA = _approvePaymentUntil(seatA.tutorObligationId, 5, WAGE_DUE + 1 hours);
        requestVm.prank(EXECUTOR);
        payments.pay(refundA, 7);
        requestVm.prank(EXECUTOR);
        payments.pay(wageA, 5);
        require(funds.creditBalance(funds.creditAccount(PAYER_A)) == 7, "A's designated payer was not restored");
        require(funds.creditBalance(funds.creditAccount(_customer(0))) == 0, "A's customer received the payer's credit");
        require(funds.creditBalance(funds.creditAccount(_payer(1))) == 11, "B's already restored account changed");
        require(token.balanceOf(WAGE_RECIPIENT) == 8 && token.balanceOf(address(funds)) == 212, "wrong actual cash");
        require(payments.getObligation(seatB.tutorObligationId).paid == 3, "B's previously paid wage changed");
    }

    function testExactlyHalfOfLockedRosterCannotSettleNormally() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(2, true);
        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
    }

    function testGroupProviderNoticeRefundKeepsIndependentTaughtSeatWagesPayable() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(3, true);
        bytes32 affected = input.seats[0].formId;
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.OrdinaryFee;
        input.seats[0].serviceAvailabilityRef = keccak256("verified provider notice error caused this place to miss teaching");
        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);

        bytes32 refund = _settleProviderNoticeRefund(affected);
        SparkV15Settlement.GroupPreview memory preview = settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
        require(preview.attendanceConfirmations == 2 && preview.totalTutorPay == 16, "wrong majority or agreed wages");
        require(preview.payments.length == 3, "settlement added a duplicate refund");
        _approveSettlement(input);

        SparkV15Settlement.SeatSettlement memory a = settlement.getSeatSettlement(LESSON, affected);
        SparkV15Settlement.SeatSettlement memory b = settlement.getSeatSettlement(LESSON, input.seats[1].formId);
        SparkV15Settlement.SeatSettlement memory c = settlement.getSeatSettlement(LESSON, input.seats[2].formId);
        require(a.disposition == SparkV15Settlement.SeatDisposition.ProviderRedressFee, "wrong customer fee route");
        require(a.feeDue == 0 && a.refundDue == 20 && a.refundAlreadyReceived == 20, "incorrect fee or receipt");
        require(a.refundObligationId == refund && a.noticeEvidenceId == 0, "wrong refund or notice reference");
        require(b.feeDue == 20 && c.feeDue == 20 && b.refundDue == 0 && c.refundDue == 0, "other fees changed");
        require(b.tutorNetPay == 8 && c.tutorNetPay == 6, "other wages changed");
        require(settlement.getGroupSettlement(LESSON).complete, "group remained unsettled");

        uint256 bApproval = _approvePayment(b.tutorObligationId, 8);
        uint256 cApproval = _approvePayment(c.tutorObligationId, 6);
        requestVm.warp(WAGE_DUE);
        requestVm.prank(EXECUTOR);
        payments.pay(bApproval, 8);
        requestVm.prank(EXECUTOR);
        payments.pay(cApproval, 6);
        require(token.balanceOf(WAGE_RECIPIENT) == 14, "the delivered seats' wages were not paid");
        require(funds.creditBalance(funds.creditAccount(PAYER_A)) == 20, "settlement changed the original refund");
    }

    function testGroupProviderRefundReadsAdoptedAmountWithoutRewritingReceipt() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(3, true);
        bytes32 formId = input.seats[1].formId;
        (SparkV15ReviewCases review, SparkV15LessonRemedies remedies, bytes32 caseId, bytes32 refund) =
            _groupProviderAdministrationRefund(formId);
        require(remedies.getFault(caseId, 1).kind == SparkV15LessonRemedies.FaultKind.ProviderAdministrationError);
        _reviseProviderRefund(review, caseId, refund, 6);
        _propose(input);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, formId);
        require(seat.feeDue == 14 && seat.refundDue == 6, "settlement ignored the adopted principal");
        require(seat.refundAlreadyReceived == 8 && seat.refundObligationId == refund, "actual refund history changed");
        require(funds.creditBalance(funds.creditAccount(_payer(1))) == 8, "settlement changed posted credit");
    }

    function testGroupNoFaultSettlementRetainsEarlierRefundWithoutRecoveringIt() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(3, true);
        bytes32 formId = input.seats[1].formId;
        (SparkV15ReviewCases review, SparkV15LessonRemedies remedies, bytes32 caseId, bytes32 refund) =
            _groupProviderAdministrationRefund(formId);
        _adoptProviderNoFault(review, remedies, caseId, formId);
        _propose(input);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, formId);
        require(seat.disposition == SparkV15Settlement.SeatDisposition.OrdinaryFee && seat.feeDue == 20, "wrong current fee");
        require(seat.refundDue == 0 && seat.refundAlreadyReceived == 8, "settlement ignored the historical refund");
        require(payments.getObligation(refund).paid == 8, "original refund receipt was lost");
        require(funds.creditBalance(funds.creditAccount(_payer(1))) == 8, "settlement attempted automatic recovery");
    }

    function testMissingAttendanceCannotEstablishAnAbsence() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(3, false);
        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
    }

    function testLaterVerifiedGroupRequiresMaturityAndASeparateVerifiedBoundaryAtEquality() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(2, true);
        input.route = SparkV15Settlement.Route.VerifiedGroup;
        input.verificationRef =
            keccak256("coordinator verified service at both places after missing attendance threshold");
        _propose(input);
        requestVm.warp(WAGE_DUE - 1);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
        requestVm.warp(WAGE_DUE);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);

        input.clockBoundaryRef = keccak256("elapsed boundary occurred before this filing in the observed second");
        input.clockEvidenceId = _evidence(alternatives.fallbackClockCommitment(LESSON, START, input.clockBoundaryRef));
        _propose(input);
        _approveSettlement(input);
        SparkV15Settlement.GroupSettlement memory result = settlement.getGroupSettlement(LESSON);
        require(result.complete && result.route == SparkV15Settlement.Route.VerifiedGroup, "wrong verified route");
        require(result.attendanceConfirmations == 1 && result.totalTutorPay == 10, "wrong later group result");
    }

    function testPartialGroupWagesRequireRealFeeHoldAndPreviouslySettledSeatsAreNotReservedTwice() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(3, true);
        SparkV15Settlement.SeatFinding memory originalA = SparkV15Settlement.SeatFinding(
            input.seats[0].formId,
            input.seats[0].disposition,
            input.seats[0].serviceAvailabilityRef,
            bytes32(0),
            false,
            0,
            0
        );
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.DeferredByHold;
        bytes32 unrelated = _establishFixtureRefund();
        uint256 priorApproval = _approvePayment(unrelated, 10);
        requestVm.prank(EXECUTOR);
        payments.pay(priorApproval, 3);
        bytes32 unrelatedHold = _holdRefund(unrelated);
        input.seats[0].feeHoldCaseId = payments.HOLDS().getFormalHold(unrelatedHold).terms.caseId;
        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);

        bytes32 feeCase = _holdFee(originalA.formId);
        input.seats[0].feeHoldCaseId = feeCase;
        _propose(input);
        bytes32 basis = _approveSettlement(input);
        SparkV15Settlement.GroupSettlement memory partialResult = settlement.getSettlementTranche(basis);
        require(
            partialResult.basis == basis && partialResult.approver == VERIFIER_ACTOR
                && !partialResult.complete && partialResult.totalTutorPay == 14,
            "wrong independent tranche"
        );
        require(settlement.isSettlementActor(LESSON, VERIFIER_ACTOR), "partial approval actor missing");
        require(!settlement.isSettlementActor(LESSON, address(0)), "unknown actor counted as approver");
        require(settlement.getGroupSettlement(LESSON).basis == bytes32(0), "partial is not final");
        require(settlement.getSeatSettlement(LESSON, originalA.formId).formId == bytes32(0), "held seat assessed");
        SparkV15Settlement.SeatSettlement memory b = settlement.getSeatSettlement(LESSON, input.seats[1].formId);
        require(settlement.mayPaySettlementPart(b.tutorObligationId), "eligible independent wage blocked");
        uint256 requestId = _approvePayment(b.tutorObligationId, 8);
        requestVm.warp(WAGE_DUE);
        requestVm.prank(EXECUTOR);
        payments.pay(requestId, 8);
        require(token.balanceOf(WAGE_RECIPIENT) == 8, "independent wage unpaid");

        _liftFee(feeCase);
        input.seats[0] = originalA;
        input.seats[1].disposition = SparkV15Settlement.SeatDisposition.PreviouslySettled;
        input.seats[2].disposition = SparkV15Settlement.SeatDisposition.PreviouslySettled;
        _propose(input);
        address finalApprover = address(0xF001);
        bytes32 finalAuthority = keccak256("final group settlement verifier");
        identityRegistry.assignSubject(finalApprover, SparkV15.APP_ID, ROLE_VERIFIER, finalAuthority, "test:final");
        require(!settlement.isSettlementActor(LESSON, finalApprover), "future approver counted too soon");
        SparkV15Settlement.GroupPreview memory finalPreview =
            settlement.previewOrdinaryGroup(LESSON, input, finalApprover);
        require(finalPreview.payments.length == 1 && finalPreview.totalTutorPay == 16, "prior obligations duplicated");
        bytes32 finalBasis = _approveSettlementAs(input, finalApprover);
        SparkV15Settlement.GroupSettlement memory finalResult = settlement.getGroupSettlement(LESSON);
        require(
            finalResult.complete && finalResult.approver == finalApprover
                && finalResult.approvalAuthorityId == finalAuthority && finalResult.basis == finalBasis,
            "final tranche does not preserve the actual approval"
        );
        require(settlement.isSettlementActor(LESSON, VERIFIER_ACTOR), "historical approver lost");
        require(settlement.isSettlementActor(LESSON, finalApprover), "final approver missing");
        require(!settlement.isSettlementActor(LESSON, address(0)), "unrecognised actor acquired approval");
        require(
            settlement.getSettlementTranche(keccak256("unknown tranche")).basis == bytes32(0),
            "unknown tranche acquired a basis"
        );
        require(
            keccak256(abi.encode(finalResult)) == keccak256(abi.encode(settlement.getSettlementTranche(finalBasis))),
            "final result differs from tranche"
        );
        require(
            keccak256(abi.encode(partialResult)) == keccak256(abi.encode(settlement.getSettlementTranche(basis))),
            "earlier tranche changed"
        );
        requestVm.expectRevert(SparkV15Settlement.InvalidGroupProposal.selector);
        requestVm.prank(VERIFIER_ACTOR);
        settlement.approveOrdinaryGroup(LESSON, input, 0, new uint256[](0));
        require(payments.getObligation(b.tutorObligationId).paid == 8, "earlier actual receipt lost");
        SparkV15Settlement.SeatSettlement memory a = settlement.getSeatSettlement(LESSON, originalA.formId);
        require(
            a.refundObligationId == unrelated && a.refundDue == 10 && a.refundAlreadyReceived == 3,
            "prior original credit lost"
        );

        // A later real tranche cannot be used as evidence of a wage established in the earlier tranche.
        SparkV15ReviewCases review = SparkV15ReviewCases(address(payments.reviewCases()));
        SparkV15PaymentTakeover takeover = new SparkV15PaymentTakeover(settlement, review, ROLE_SOURCE);
        SparkV15PaymentTakeover.Input memory takeoverInput;
        takeoverInput.termsId = _publishReviewTerms(review, input.seats[2].formId);
        takeoverInput.obligationId = settlement.getSeatSettlement(LESSON, input.seats[2].formId).tutorObligationId;
        takeoverInput.takenOverAt = uint64(block.timestamp);
        takeoverInput.settlementBasis = finalBasis;
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        takeover.takeoverCommitment(takeoverInput, ALLOCATOR_ACTOR);
        takeoverInput.settlementBasis = basis;
        require(takeover.takeoverCommitment(takeoverInput, ALLOCATOR_ACTOR) != bytes32(0), "original tranche missing");
    }

    function testOverdueIndependentWageCanBeTakenOverBeforeTheGroupFinishes() public {
        SparkV15Settlement.GroupAssessment memory assessment = _bookAndTeach(3, true);
        bytes32 heldForm = assessment.seats[0].formId;
        bytes32 feeCase = _holdFee(heldForm);
        assessment.seats[0].disposition = SparkV15Settlement.SeatDisposition.DeferredByHold;
        assessment.seats[0].feeHoldCaseId = feeCase;
        _propose(assessment);
        bytes32 basis = _approveSettlement(assessment);

        bytes32 paidForm = assessment.seats[1].formId;
        bytes32 obligation = settlement.getSeatSettlement(LESSON, paidForm).tutorObligationId;
        SparkV15ReviewCases review = SparkV15ReviewCases(address(payments.reviewCases()));
        bytes32 termsId = _publishReviewTerms(review, paidForm);
        SparkV15PaymentTakeover takeover = new SparkV15PaymentTakeover(settlement, review, ROLE_SOURCE);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_ALLOCATOR, SparkV15ReviewActions.ACTION_ESCALATE_CASE, true);
        uint256 approval = _approvePayment(obligation, 8);
        requestVm.warp(WAGE_DUE);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 3);

        uint64 deadline = WAGE_DUE + 3 days;
        requestVm.warp(deadline + 1);
        SparkV15PaymentTakeover.Input memory input;
        input.termsId = termsId;
        input.obligationId = obligation;
        input.takenOverAt = deadline + 1;
        input.responsible = COORDINATOR;
        input.assignedAt = deadline + 1;
        input.newActionDate = deadline + 2 days;
        input.progress = keccak256("three paid from the independent batch, five outstanding");
        input.notice = SparkV15ReviewContext.Notice(keccak256("delivered to provider and tutor"), deadline + 1);
        input.unpaidAtDeadline = 5;
        input.unpaidAtTakeover = 5;

        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        takeover.takeoverCommitment(input, ALLOCATOR_ACTOR);
        input.settlementBasis = keccak256("no approved tranche");
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        takeover.takeoverCommitment(input, ALLOCATOR_ACTOR);
        input.settlementBasis = basis;
        uint256 proof = _evidence(takeover.takeoverCommitment(input, ALLOCATOR_ACTOR));
        requestVm.prank(ALLOCATOR_ACTOR);
        bytes32 id = takeover.record(input, proof, _authority(ROLE_ALLOCATOR));

        SparkV15PaymentTakeover.Record memory saved = takeover.get(id);
        require(saved.obligationId == obligation && saved.cutoff == deadline, "wrong independent obligation");
        require(settlement.getSettlementTranche(basis).approvedAt < saved.takenOverAt, "tranche was not yet approved");
        require(!settlement.getGroupSettlement(LESSON).complete, "takeover completed the group");
        require(!settlement.hasSeatSettlement(LESSON, heldForm), "the held seat was settled");
        require(token.balanceOf(WAGE_RECIPIENT) == 3 && funds.paymentReserved(obligation) == 5, "payment changed");
    }

    function testOneToOneWithFullDiscountNeedsAllThreeCompletionConfirmations() public {
        SparkV15Settlement.GroupAssessment memory input = _assessment(1);
        input.route = SparkV15Settlement.Route.OrdinaryOneToOne;
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.OrdinaryFee;
        _publishLesson(input, 8);
        (bytes32[] memory forms,) = _bookGroup(1, true, bytes32(0));
        input.seats[0].formId = forms[0];
        _teach(forms, false);
        _reportAttendance(forms[0], 0, true);
        _reportFullService(forms[0], _student(0));
        _completion(forms[0], _student(0));
        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);

        _completion(forms[0], COORDINATOR);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, forms[0]);
        require(seat.normalFee == 20 && seat.debited == 0 && seat.feeDue == 0, "wrong verified full-discount fee");
        require(seat.refundObligationId == bytes32(0) && seat.tutorPay == 8, "discount changed tutor agreement");
    }

    function testLaterVerifiedOneToOneUsesVerifiedDeliveryWithMissingConfirmations() public {
        SparkV15Settlement.GroupAssessment memory input = _assessment(1);
        input.route = SparkV15Settlement.Route.VerifiedOneToOne;
        input.verificationRef =
            keccak256("coordinator verified the agreed one-to-one service from actual delivery evidence");
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.OrdinaryFee;
        _publishLesson(input, 8);
        (bytes32[] memory forms,) = _bookGroup(1, false, bytes32(0));
        input.seats[0].formId = forms[0];
        _teach(forms, false);
        _propose(input);
        requestVm.warp(WAGE_DUE);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
        requestVm.warp(WAGE_DUE + 1);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, forms[0]);
        require(seat.feeDue == 20 && seat.tutorPay == 8, "incorrect later one-to-one outcome");
    }

    function testNoticeRecordedBeforeOpeningInSameSecondKeepsOrdinaryAuthority() public {
        SparkV15Settlement.GroupAssessment memory input = _bookOneToOneForNoticeOrder();
        bytes32 formId = input.seats[0].formId;
        requestVm.warp(START);
        uint256 studentNotice = _recordCoordinatorStudentNotice(formId);
        _recordOpeningWithTutorNoticeOutstanding();

        require(booking.getTeaching(LESSON).startRecordedAt == START, "wrong opening recording time");
        require(booking.getStudentNotice(formId).recordedAt == START, "first notice is in the wrong second");
        _recordIndependentTutorNotice(START + 2);
        require(alternatives.OCCURRENCES().hasUsableLateOpeningNotices(LESSON), "early evidence treated as late");

        _recordEndAndTutorReport(END, TUTOR);
        _completion(formId, _student(0));
        _completion(formId, COORDINATOR);
        _propose(input);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, formId);
        require(seat.noticeEvidenceId == studentNotice && seat.feeDue == 20 && seat.tutorPay == 8, "wrong settlement");
        require(booking.getTeaching(LESSON).startPermission == SparkV15Booking.StartPermission.Unverified, "opening changed");

        uint256 approval = _approvePayment(seat.tutorObligationId, 8);
        requestVm.warp(WAGE_DUE);
        requestVm.prank(EXECUTOR);
        uint256 receipt = payments.pay(approval, 8);
        require(payments.getReceipt(receipt).amount == 8 && token.balanceOf(WAGE_RECIPIENT) == 8, "wage not received");
        require(token.balanceOf(address(funds)) == 192, "wrong vault cash after actual wage payment");
    }

    function testSameOrdinaryWageReviewCanBeAdoptedAfterOneNativeReceipt() public {
        (bytes32 formId, bytes32 obligationId) = _settledOrdinaryWage();
        ReviewedWage memory wage = _reviewOrdinaryWage(formId, obligationId);
        uint256 later = _adoptAfterLaterWageReceipt(wage);

        SparkV15Payments.Obligation memory corrected = payments.getObligation(obligationId);
        require(
            corrected.correctAmount == 7 && corrected.paid == 3 && funds.paymentReserved(obligationId) == 4,
            "wrong corrected balance"
        );
        require(
            wage.review.getAdoptedDisposition(wage.caseId).outcome
                == _wageRevisionOutcome(wage.caseId, wage.revision, wage.paymentCommitment),
            "original independent finding changed"
        );
        require(payments.getReceipt(wage.earlierReceipt).amount == 2 && payments.getReceipt(later).amount == 1, "receipt lost");
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(wage.approval, 5);
        requestVm.prank(EXECUTOR);
        uint256 finalReceipt = payments.pay(wage.approval, 4);
        require(payments.getReceipt(finalReceipt).amount == 4 && token.balanceOf(WAGE_RECIPIENT) == 7, "wrong final receipt");
    }

    function _settledOrdinaryWage() private returns (bytes32 formId, bytes32 obligationId) {
        SparkV15Settlement.GroupAssessment memory input = _bookOneToOneForNoticeOrder();
        formId = input.seats[0].formId;
        bytes32[] memory forms = new bytes32[](1);
        forms[0] = formId;
        _teach(forms, false);
        _reportAttendance(formId, 0, true);
        _reportFullService(formId, _student(0));
        _completion(formId, _student(0));
        _completion(formId, COORDINATOR);
        _propose(input);
        _approveSettlement(input);
        obligationId = settlement.getSeatSettlement(LESSON, formId).tutorObligationId;
    }

    function _reviewOrdinaryWage(bytes32 formId, bytes32 obligationId) private returns (ReviewedWage memory wage) {
        bytes32 termsId;
        (wage.review,, termsId) = _publishReviewContacts(formId);
        require(address(wage.review).code.length <= 24_576, "review runtime exceeds deployable size");
        wage.coordinator = identityRegistry.subjectOf(COORDINATOR, SparkV15.APP_ID, ROLE_SOURCE);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, true);
        bytes32 effectRole = payments.caseEffectRole();
        authorityMatrix.setPermission(SparkV15.APP_ID, effectRole, payments.ACTION_APPLY_CASE_EFFECT(), true);
        identityRegistry.assignSubject(
            address(wage.review), SparkV15.APP_ID, effectRole, _authority(effectRole), "test:case-effects"
        );

        SparkV15Payments.Obligation memory payment = payments.getObligation(obligationId);
        wage.paymentCommitment = payment.commitment;
        SparkV15ReviewContext.OriginalInput memory original;
        original.termsId = termsId;
        original.concernRef = keccak256("review of the original ordinary wage");
        original.obligationId = obligationId;
        original.paymentCommitment = payment.commitment;
        original.decider = VERIFIER_ACTOR;
        original.decidedAt = END + 1;
        original.outcome = keccak256("eight units of original teaching wage assessed");
        original.parties = new address[](2);
        original.parties[0] = TUTOR;
        original.parties[1] = PROVIDER;
        wage.partiesHash = keccak256(abi.encode(original.parties));
        wage.caseId = wage.review.caseIdFor(LESSON, original.concernRef);
        wage.retained = _evidence(wage.review.evidenceCommitment(
            wage.caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, COORDINATOR, keccak256(abi.encode(original))
        ));
        requestVm.prank(COORDINATOR);
        wage.review.retainOriginal(original, wage.retained, wage.coordinator);
        wage.approval = _approvePayment(obligationId, 8);
        requestVm.warp(WAGE_DUE);
        requestVm.prank(EXECUTOR);
        wage.earlierReceipt = payments.pay(wage.approval, 2);

        requestVm.warp(WAGE_DUE + 1);
        wage.revision = SparkV15Payments.PaymentRevision(
            obligationId, 7, payment.beneficiary, payment.destination, payments.getObligation(obligationId).version
        );
        SparkV15ReviewContext.ReviewInput memory finding = SparkV15ReviewContext.ReviewInput(
            SparkV15ReviewContext.ReviewDisposition.CorrectionRequired,
            _wageRevisionOutcome(wage.caseId, wage.revision, payment.commitment),
            keccak256("independently established the same tutor was owed seven units"),
            0
        );
        wage.reviewed = _evidence(wage.review.evidenceCommitment(
            wage.caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(finding))
        ));
        requestVm.prank(REVIEWER);
        wage.review.decidePaymentRevision(wage.caseId, finding, wage.revision, wage.reviewed, REVIEWER_ID);
    }

    function _adoptAfterLaterWageReceipt(ReviewedWage memory wage) private returns (uint256 later) {
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("correction and subsequent receipt notified"), WAGE_DUE + 3);
        bytes32 payload = keccak256(abi.encode(notice, wage.retained, wage.reviewed, wage.partiesHash, bytes32(0)));
        ++wage.revision.expectedVersion;
        bytes32 effect = _wageRevisionOutcome(wage.caseId, wage.revision, wage.paymentCommitment);
        --wage.revision.expectedVersion;
        bytes32 recheck = keccak256(abi.encode(wage.earlierReceipt + 1, uint256(3), uint256(3), effect));
        bytes32 commitment = wage.review.evidenceCommitment(
            wage.caseId, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, COORDINATOR, keccak256(abi.encode(payload, recheck))
        );
        bytes32 evidenceType = keccak256("spark.v1.5.review.recheck-native-wage-receipt");
        uint256 premature = _evidenceOfType(commitment, evidenceType);

        requestVm.warp(WAGE_DUE + 2);
        requestVm.prank(EXECUTOR);
        later = payments.pay(wage.approval, 1);
        require(later == wage.earlierReceipt + 1, "unexpected native receipt");
        require(token.balanceOf(WAGE_RECIPIENT) == 3, "intervening funds did not reach the recipient");
        requestVm.warp(WAGE_DUE + 3);
        uint256 originalAdoption = _evidence(
            wage.review.evidenceCommitment(wage.caseId, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, COORDINATOR, payload)
        );
        requestVm.expectRevert(SparkV15Payments.InvalidObligation.selector);
        requestVm.prank(COORDINATOR);
        wage.review.adoptPaymentRevision(wage.caseId, notice, originalAdoption, wage.coordinator, wage.revision);
        require(wage.review.getAdoptedDisposition(wage.caseId).adoptedAt == 0, "stale case was adopted");
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        requestVm.prank(COORDINATOR);
        wage.review.adoptPaymentRevision(wage.caseId, notice, premature, wage.coordinator, wage.revision);

        uint256 fresh = _evidenceOfType(commitment, evidenceType);
        requestVm.prank(COORDINATOR);
        wage.review.adoptPaymentRevision(wage.caseId, notice, fresh, wage.coordinator, wage.revision);
    }

    function _wageRevisionOutcome(bytes32 caseId, SparkV15Payments.PaymentRevision memory revision, bytes32 commitment)
        private
        view
        returns (bytes32)
    {
        return keccak256(abi.encode(
            keccak256("spark.v1.5.revise-payment"), block.chainid, address(payments), caseId, revision, commitment
        ));
    }

    function testIndependentlyVerifiedNoticeRecordedAfterOpeningInSameSecondRemainsUsable() public {
        bytes32 formId = _bookOneToOneForNoticeOrder().seats[0].formId;
        requestVm.warp(START);
        _recordCoordinatorStudentNotice(formId);
        _recordOpeningWithTutorNoticeOutstanding();
        _recordIndependentTutorNotice(START);
        require(booking.getTutorNotice(LESSON).recordedAt == START, "second notice is in the wrong second");
        require(alternatives.OCCURRENCES().hasUsableLateOpeningNotices(LESSON), "independent later notice lost");
    }

    function testNoticeDeclarationAfterOpeningInSameSecondStillNeedsIndependentEvidence() public {
        _assertNoticeDeclarationAfterOpeningCannotSettle(START);
    }

    function testNoticeDeclarationRecordedInALaterSecondStillNeedsIndependentEvidence() public {
        _assertNoticeDeclarationAfterOpeningCannotSettle(START + 1);
    }

    function _assertNoticeDeclarationAfterOpeningCannotSettle(uint64 recordedAt) private {
        SparkV15Settlement.GroupAssessment memory input = _bookOneToOneForNoticeOrder();
        bytes32 formId = input.seats[0].formId;
        _recordOpeningWithTutorNoticeOutstanding();
        requestVm.warp(recordedAt);
        uint256 studentNotice = _recordCoordinatorStudentNotice(formId);
        _recordIndependentTutorNotice(START + 2);
        require(!alternatives.OCCURRENCES().hasUsableLateOpeningNotices(LESSON), "later declaration treated as early");

        _recordEndAndTutorReport(END, TUTOR);
        _completion(formId, _student(0));
        _completion(formId, COORDINATOR);
        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        requestVm.prank(VERIFIER_ACTOR);
        settlement.approveOrdinaryGroup(LESSON, input, 0, new uint256[](0));
        require(booking.getStudentNotice(formId).evidenceId == studentNotice, "notice history lost");
        require(booking.getTeaching(LESSON).startedAt == START, "opening history lost");
        require(token.balanceOf(address(funds)) == 200, "rejected settlement affected cash");
    }

    function _bookOneToOneForNoticeOrder() private returns (SparkV15Settlement.GroupAssessment memory input) {
        input = _assessment(1);
        input.route = SparkV15Settlement.Route.OrdinaryOneToOne;
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.OrdinaryFee;
        _publishLesson(input, 8);
        (bytes32[] memory forms,) = _bookGroup(1, false, bytes32(0));
        input.seats[0].formId = forms[0];
    }

    function _recordCoordinatorStudentNotice(bytes32 formId) private returns (uint256 evidenceId) {
        uint64 deliveredAt = START - 12;
        bytes32 receipt = keccak256("coordinator's delivery record for the agreed student channel");
        bytes32 subject = identityRegistry.subjectOf(COORDINATOR, SparkV15.APP_ID, ROLE_SOURCE);
        bytes32 commitment = booking.studentNoticeCommitment(formId, deliveredAt, receipt);
        requestVm.prank(COORDINATOR);
        evidenceId = evidenceRegistry.registerEvidence(
            AVAEvidenceRegistry.EvidenceRegistrationInput({
                appId: SparkV15.APP_ID,
                workflowKey: REQUEST_WORKFLOW,
                packageId: requestPackageId,
                roleKey: ROLE_SOURCE,
                subjectId: subject,
                commitment: commitment,
                evidenceTypeHash: keccak256("verified Spark lesson settlement record"),
                disclosurePolicyId: requestPolicyId,
                authorityId: subject,
                uri: "test:original-notice-record"
            })
        );
        requestVm.prank(COORDINATOR);
        booking.recordStudentNotice(formId, deliveredAt, receipt, evidenceId);
    }

    function _recordOpeningWithTutorNoticeOutstanding() private {
        address[] memory present = new address[](1);
        present[0] = _student(0);
        _recordOpening(present, START);
        require(booking.getTeaching(LESSON).startPermission == SparkV15Booking.StartPermission.Unverified, "bad start");
    }

    function _recordIndependentTutorNotice(uint64 recordedAt) private {
        requestVm.warp(recordedAt);
        uint64 deliveredAt = START - 12;
        bytes32 receipt = keccak256("independently verified timely tutor notice");
        uint256 evidence = _evidence(booking.tutorNoticeCommitment(LESSON, TUTOR_CHANNEL, deliveredAt, receipt));
        requestVm.prank(COORDINATOR);
        booking.recordTutorNotice(LESSON, TUTOR_CHANNEL, deliveredAt, receipt, evidence);
    }

    function testStatutoryTutorDeadlineRequiresVerifiedScopeAndUsualSettlement() public {
        uint64 agreedDue = END + 2 days;
        uint64 legalDeadline = END + 3 days;
        SparkV15Settlement.GroupAssessment memory input = _assessment(1);
        input.route = SparkV15Settlement.Route.OrdinaryOneToOne;
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.OrdinaryFee;
        input.tutor.schedule.dueAt = agreedDue;
        _publishLesson(input, 8);
        (bytes32[] memory forms,) = _bookGroup(1, false, bytes32(0));
        input.seats[0].formId = forms[0];
        _teach(forms, false);
        _completion(forms[0], _student(0));
        _propose(input);

        requestVm.expectRevert(SparkV15Settlement.InvalidAgreedPaymentTerms.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
        _verifyStatutoryDeadline(legalDeadline);

        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
        _completion(forms[0], COORDINATOR);
        _approveSettlement(input);
        bytes32 obligation = settlement.getSeatSettlement(LESSON, forms[0]).tutorObligationId;
        SparkV15Payments.Obligation memory wage = payments.getObligation(obligation);
        require(wage.terms.agreedStart == START && wage.terms.dueAt == agreedDue, "rewrote agreed schedule");
        require(wage.terms.legalDeadline == legalDeadline && wage.terms.legalDeadlineExact, "lost statutory deadline");

        uint256 approval = _approvePayment(obligation, 8);
        requestVm.warp(agreedDue - 1);
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 4);

        requestVm.warp(legalDeadline);
        requestVm.prank(EXECUTOR);
        uint256 receipt = payments.pay(approval, 4);
        require(payments.getReceipt(receipt).paidAt == legalDeadline && legalDeadline < WAGE_DUE, "payment clock");
        require(token.balanceOf(WAGE_RECIPIENT) == 4, "earlier payment did not transfer assets");
        requestVm.warp(legalDeadline + 1);
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 4);
        require(payments.getObligation(obligation).paid == 4, "late payment changed the receipt total");
    }

    function _verifyStatutoryDeadline(uint64 deadline) private {
        SparkV15SettlementOccurrences occurrences = alternatives.OCCURRENCES();
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, occurrences.ACTION_VERIFY_EARLIER_TUTOR_DEADLINE(), true
        );
        SparkV15SettlementOccurrences.TutorLegalScope memory scope = SparkV15SettlementOccurrences.TutorLegalScope(
            LESSON, bytes32(0), TUTOR, AGREEMENT, booking.getLesson(LESSON).terms.tutorPayTermsRef, START
        );
        SparkV15SettlementOccurrences.StatutoryTutorDeadline memory right =
            SparkV15SettlementOccurrences.StatutoryTutorDeadline(
                scope,
                deadline,
                true,
                keccak256("fixture jurisdiction X"),
                keccak256("fixture wage code section 9"),
                keccak256("signed determination that section 9 covers the tutor pay for this teaching agreement")
            );
        bytes32 commitment = occurrences.earlierTutorDeadlineCommitment(right, REVIEWER);
        uint256 untyped = _evidence(commitment);
        requestVm.expectRevert(SparkV15SettlementOccurrences.InvalidStatutoryTutorDeadline.selector);
        requestVm.prank(REVIEWER);
        occurrences.verifyEarlierTutorDeadline(right, untyped, REVIEWER_ID);

        uint256 verified = _evidenceOfType(commitment, occurrences.STATUTORY_TUTOR_DEADLINE_EVIDENCE_TYPE());
        right.scope.agreedStartAnchor = START + 1;
        requestVm.expectRevert(SparkV15SettlementOccurrences.InvalidStatutoryTutorDeadline.selector);
        requestVm.prank(REVIEWER);
        occurrences.verifyEarlierTutorDeadline(right, verified, REVIEWER_ID);
        right.scope.agreedStartAnchor = START;
        requestVm.prank(REVIEWER);
        occurrences.verifyEarlierTutorDeadline(right, verified, REVIEWER_ID);
    }

    function testFullGroupWageChecksOtherFeeHoldsAtActualPayment() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(3, true);
        _propose(input);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory b = settlement.getSeatSettlement(LESSON, input.seats[1].formId);
        uint256 requestId = _approvePayment(b.tutorObligationId, 8);
        bytes32 caseId = _holdFee(input.seats[0].formId);
        requestVm.warp(WAGE_DUE);
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(requestId, 8);

        _liftFee(caseId);
        requestVm.prank(EXECUTOR);
        payments.pay(requestId, 8);
        require(token.balanceOf(WAGE_RECIPIENT) == 8, "full group wage did not resume");
    }

    function testSeparateGroupWageCanRelyOnHeldCorrespondingTutorPortion() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(3, true);
        bytes32 heldWage = _establishFixtureTutorPortion();
        _holdRefund(heldWage);
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.DeferredByHold;
        _propose(input);
        bytes32 basis = _approveSettlement(input);
        SparkV15Settlement.GroupSettlement memory result = settlement.getSettlementTranche(basis);
        require(
            !result.complete && result.totalTutorPay == 14,
            "held tutor portion did not support the independent group fees"
        );
        require(payments.HOLDS().getStatus(heldWage).active, "held wage was changed by other seats");
    }

    function testOneToOneAbsenceWithoutTeachingNeedsPositiveVerificationAndSplitsBothFees() public {
        SparkV15Settlement.GroupAssessment memory input = _assessment(1);
        input.route = SparkV15Settlement.Route.OneToOneAbsence;
        _publishLesson(input, 8);
        (bytes32[] memory forms,) = _bookGroup(1, false, bytes32(0));
        input.seats[0].formId = forms[0];
        _provideNotices(forms);
        requestVm.warp(END + 1);
        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);

        SparkV15SettlementAlternatives.AbsenceFacts memory facts = SparkV15SettlementAlternatives.AbsenceFacts(
            forms[0],
            START,
            keccak256("verified student unready and absent without valid reason; otherwise ready"),
            bytes32(0),
            SparkV15SettlementAlternatives.AbsenceReason.NoGoodReason
        );
        uint256 evidence = _evidence(alternatives.absenceCommitment(facts, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        alternatives.recordOneToOneAbsence(facts, evidence);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, forms[0]);
        require(booking.getTeaching(LESSON).startedAt == 0 && seat.feeDue == 10, "absence invented teaching");
        require(seat.refundDue == 10 && seat.tutorPay == 4, "wrong signed half fees");
    }

    function testOneToOneGoodReasonUsesSignedChangeAmounts() public {
        SparkV15Settlement.GroupAssessment memory input = _assessment(1);
        input.route = SparkV15Settlement.Route.OneToOneAgreedAbsence;
        input.seats[0].agreedAbsenceFee = 3;
        input.seats[0].agreedAbsenceTutorPay = 1;
        input.refund.serviceDocumentRef =
            alternatives.agreedAbsenceCommitment(LESSON, _place(0), DOCUMENTS, CHANGE_TERMS, 3, 1);
        _publishLesson(input, 8);
        (bytes32[] memory forms,) = _bookGroup(1, false, CHANGE_TERMS);
        input.seats[0].formId = forms[0];
        _provideNotices(forms);
        requestVm.warp(END + 1);
        SparkV15SettlementAlternatives.AbsenceFacts memory facts = SparkV15SettlementAlternatives.AbsenceFacts(
            forms[0],
            START,
            keccak256("verified sole absence with good reason"),
            bytes32(0),
            SparkV15SettlementAlternatives.AbsenceReason.GoodReason
        );
        uint256 evidence = _evidence(alternatives.absenceCommitment(facts, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        alternatives.recordOneToOneAbsence(facts, evidence);

        input.seats[0].agreedAbsenceFee = 10;
        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.InvalidAgreedPaymentTerms.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
        input.seats[0].agreedAbsenceFee = 3;
        _propose(input);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, forms[0]);
        require(seat.feeDue == 3 && seat.refundDue == 17 && seat.tutorPay == 1, "agreed absence amounts lost");
    }

    function testReplacedAndRescheduledTeachingUsesActiveTutorTermsAndKeepsTheStartedClock() public {
        SparkV15BookingChanges changes = new SparkV15BookingChanges(booking, payments);
        booking.bindBookingChanges(ISparkV15BookingChanges(address(changes)));
        SparkV15BookingChanges.ChangeTerms memory changeTerms;
        changeTerms.reschedule = SparkV15BookingChanges.Window(
            SparkV15BookingChanges.ClockMode.Fixed, START + 2 days, SparkV15BookingChanges.ClockMode.None, 0
        );

        SparkV15Settlement.GroupAssessment memory input = _assessment(1);
        input.route = SparkV15Settlement.Route.OrdinaryOneToOne;
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.OrdinaryFee;
        _publishLesson(input, 8);
        (bytes32[] memory forms,) = _bookGroup(1, false, changes.changeTermsCommitment(changeTerms));
        input.seats[0].formId = forms[0];
        changes.admitChangeTerms(forms[0], changeTerms);

        SparkV15Settlement.TutorPayTerms memory revised = SparkV15Settlement.TutorPayTerms({
            agreementRef: keccak256("replacement's signed teaching agreement"),
            recipient: REPLACEMENT,
            schedule: input.tutor.schedule,
            seats: new SparkV15Settlement.TutorSeatTerms[](1)
        });
        revised.seats[0] = SparkV15Settlement.TutorSeatTerms(_place(0), 11, 0);
        (bytes32 changeId, uint256 notice) = _finalizeReplacement(changes, forms[0], revised, true);
        address[] memory present = new address[](1);
        present[0] = _student(0);
        _recordTeaching(present, START + 1 days, END + 1 days, REPLACEMENT);
        _completion(forms[0], _student(0));
        _completion(forms[0], COORDINATOR);

        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.ApplicableArrangementChanged.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
        input.effectiveChangeId = changeId;
        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.InvalidAgreedPaymentTerms.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);

        input.tutor = revised;
        _propose(input);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, forms[0]);
        require(seat.noticeEvidenceId == notice && seat.replacementNoticeEvidenceId == notice, "wrong current notices");
        SparkV15Payments.Obligation memory wage = payments.getObligation(seat.tutorObligationId);
        require(wage.terms.recipient == REPLACEMENT && wage.terms.amount == 11, "old tutor agreement used");
        require(wage.terms.agreedStart == START && wage.terms.dueAt == WAGE_DUE, "restarted original payment clock");

        uint256 requestId = _approvePayment(seat.tutorObligationId, 11);
        requestVm.warp(WAGE_DUE);
        requestVm.prank(EXECUTOR);
        payments.pay(requestId, 11);
        require(token.balanceOf(REPLACEMENT) == 11 && token.balanceOf(WAGE_RECIPIENT) == 0, "paid old arrangement");
    }

    function testSameDateTutorReplacementKeepsAdoptedOriginalStudentNoticeInActualSettlement() public {
        SparkV15Settlement.GroupAssessment memory input = _assessment(1);
        input.route = SparkV15Settlement.Route.OrdinaryOneToOne;
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.OrdinaryFee;
        (uint256 originalNotice, uint256 replacementNotice) = _bookSameDateReplacement(input, 11);
        bytes32 formId = input.seats[0].formId;

        address[] memory present = new address[](1);
        present[0] = _student(0);
        _recordTeaching(present, START, END, REPLACEMENT);
        _completion(formId, _student(0));
        _completion(formId, COORDINATOR);
        _propose(input);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, formId);
        require(seat.noticeEvidenceId == originalNotice, "wrong original notice");
        require(seat.replacementNoticeEvidenceId == replacementNotice, "wrong replacement notice");
        SparkV15Payments.Obligation memory wage = payments.getObligation(seat.tutorObligationId);
        require(wage.terms.recipient == REPLACEMENT && wage.correctAmount == 11, "wrong independent replacement wage");
    }

    function testVerifiedNoShowAfterSameDateReplacementUsesNewTutorAndOriginalDebit() public {
        SparkV15Settlement.GroupAssessment memory input = _assessment(1);
        input.route = SparkV15Settlement.Route.OneToOneAbsence;
        (uint256 originalNotice, uint256 replacementNotice) = _bookSameDateReplacement(input, 12);
        bytes32 formId = input.seats[0].formId;

        requestVm.warp(END + 1);
        _recordAbsence(SparkV15SettlementAlternatives.AbsenceFacts(
            formId,
            START,
            keccak256("replacement was ready; student was unready and absent without good reason"),
            bytes32(0),
            SparkV15SettlementAlternatives.AbsenceReason.NoGoodReason
        ));
        _propose(input);
        _approveSettlement(input);

        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, formId);
        require(booking.getTeaching(LESSON).startedAt == 0 && seat.feeDue == 10, "wrong failed occurrence");
        require(seat.noticeEvidenceId == originalNotice
            && seat.replacementNoticeEvidenceId == replacementNotice, "wrong student notices");
        require(seat.debited == 20 && seat.refundDue == 10 && seat.tutorPay == 6, "wrong half fees");
        SparkV15Payments.Obligation memory wage = payments.getObligation(seat.tutorObligationId);
        require(wage.terms.recipient == REPLACEMENT && wage.correctAmount == 6, "wrong replacement terms");
        require(wage.terms.agreedStart == START && wage.terms.dueAt == WAGE_DUE, "changed payment clock");

        uint256 refundApproval = _approvePayment(seat.refundObligationId, 10);
        requestVm.prank(EXECUTOR);
        uint256 refundReceipt = payments.pay(refundApproval, 10);
        bytes32 account = funds.creditAccount(PAYER_A);
        require(payments.getReceipt(refundReceipt).creditAccount == account && funds.creditBalance(account) == 10,
            "refund did not restore original debit account");
        uint256 wageApproval = _approvePayment(seat.tutorObligationId, 6);
        requestVm.warp(WAGE_DUE);
        requestVm.prank(EXECUTOR);
        payments.pay(wageApproval, 6);
        require(token.balanceOf(REPLACEMENT) == 6 && token.balanceOf(WAGE_RECIPIENT) == 0, "wrong actual wage");
    }

    function _bookSameDateReplacement(SparkV15Settlement.GroupAssessment memory input, uint128 replacementFee)
        private
        returns (uint256 originalNotice, uint256 replacementNotice)
    {
        SparkV15BookingChanges changes = new SparkV15BookingChanges(booking, payments);
        booking.bindBookingChanges(ISparkV15BookingChanges(address(changes)));
        SparkV15BookingChanges.ChangeTerms memory changeTerms;
        changeTerms.reschedule = SparkV15BookingChanges.Window(
            SparkV15BookingChanges.ClockMode.Fixed, START + 2 days, SparkV15BookingChanges.ClockMode.None, 0
        );
        _publishLesson(input, 8);
        (bytes32[] memory forms,) = _bookGroup(1, false, changes.changeTermsCommitment(changeTerms));
        bytes32 formId = forms[0];
        changes.admitChangeTerms(formId, changeTerms);
        input.seats[0].formId = formId;
        originalNotice = _adoptOriginalStudentNotice(formId);

        SparkV15Settlement.TutorPayTerms memory revised = SparkV15Settlement.TutorPayTerms({
            agreementRef: keccak256("replacement tutor's accepted agreement"),
            recipient: REPLACEMENT,
            schedule: input.tutor.schedule,
            seats: new SparkV15Settlement.TutorSeatTerms[](1)
        });
        revised.seats[0] = SparkV15Settlement.TutorSeatTerms(_place(0), replacementFee, 0);
        (input.effectiveChangeId, replacementNotice) = _finalizeReplacement(changes, formId, revised, false);
        require(changes.usesInitialStudentNotice(input.effectiveChangeId), "same date lost original schedule");
        input.tutor = revised;
    }

    function _adoptOriginalStudentNotice(bytes32 formId) private returns (uint256) {
        uint256 signingKey = 0x7433;
        BookingSignatureVm signatures = BookingSignatureVm(address(requestVm));
        address source = signatures.addr(signingKey);
        bytes32 authority = keccak256("independent notice Source");
        identityRegistry.assignSubject(source, SparkV15.APP_ID, ROLE_SOURCE, authority, "test:notice proof");
        SparkV15CourseNotices notices = booking.OPENING().COURSE_NOTICES();
        bytes32 receipt = keccak256("original agreed schedule delivered to student");
        SparkV15CourseNotices.SourceProof memory proof = SparkV15CourseNotices.SourceProof(
            ROLE_SOURCE, authority, requestPolicyId, START, bytes32(0), bytes32(0)
        );
        (uint8 v, bytes32 r, bytes32 s) = signatures.sign(
            signingKey, notices.studentNoticeAdoptionDigest(formId, EPOCH + 1, receipt, COORDINATOR, proof)
        );
        proof.r = r;
        proof.vs = bytes32(uint256(s) | ((uint256(v) - 27) << 255));
        requestVm.prank(COORDINATOR);
        return notices.recordStudentNoticeWithConsent(formId, EPOCH + 1, receipt, proof);
    }

    function testAdoptedAbsenceReasonCorrectionAppendsHistoryAndPreservesActualRefund() public {
        SparkV15Settlement.GroupAssessment memory input = _assessment(1);
        input.route = SparkV15Settlement.Route.OneToOneAbsence;
        _publishLesson(input, 8);
        (bytes32[] memory forms,) = _bookGroup(1, false, bytes32(0));
        bytes32 formId = forms[0];
        input.seats[0].formId = formId;
        _provideNotices(forms);
        requestVm.warp(END + 1);
        (SparkV15ReviewCases review, SparkV15ConcernIntake intake, bytes32 caseId) =
            _receiveReviewMatter(formId, SparkV15ReviewContext.ConcernSubject.StudentAttendance);
        bytes32 originalOutcome =
            alternatives.absenceReasonOutcome(formId, SparkV15SettlementAlternatives.AbsenceReason.NoGoodReason);
        _retainInitialFinding(
            review,
            intake.getConcern(caseId),
            caseId,
            SparkV15ReviewContext.DisputedFinding.AbsenceReason,
            originalOutcome
        );
        SparkV15SettlementAlternatives.AbsenceFacts memory facts = SparkV15SettlementAlternatives.AbsenceFacts(
            formId,
            START,
            keccak256("verified absence and signed initial determination"),
            caseId,
            SparkV15SettlementAlternatives.AbsenceReason.NoGoodReason
        );
        _recordAbsence(facts);
        _propose(input);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory old = settlement.getSeatSettlement(LESSON, formId);
        uint256 approval = _approvePayment(old.refundObligationId, 3);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 3);
        require(settlement.mayPaySettlementPart(old.tutorObligationId), "original reason not operative");

        facts.reason = SparkV15SettlementAlternatives.AbsenceReason.GoodReason;
        uint256 rejected = _evidence(alternatives.absenceCommitment(facts, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15SettlementAlternatives.InvalidAbsence.selector);
        requestVm.prank(VERIFIER_ACTOR);
        alternatives.recordOneToOneAbsence(facts, rejected);
        _adoptAbsenceCorrection(review, intake.getConcern(caseId), caseId, formId);
        _recordAbsence(facts);

        SparkV15SettlementAlternatives.AbsenceRecord memory original = alternatives.getOneToOneAbsenceRecord(formId, 0);
        SparkV15SettlementAlternatives.AbsenceRecord memory revised = alternatives.getOneToOneAbsence(formId);
        require(
            original.facts.reason == SparkV15SettlementAlternatives.AbsenceReason.NoGoodReason, "lost original reason"
        );
        require(
            revised.facts.reason == SparkV15SettlementAlternatives.AbsenceReason.GoodReason, "missing adopted reason"
        );
        require(
            original.facts.occurredAt == revised.facts.occurredAt && revised.verifiedAt > original.verifiedAt,
            "rewrote occurrence or knowledge time"
        );
        require(!settlement.mayPaySettlementPart(old.tutorObligationId), "old absent-wage basis remained payable");
        require(payments.getObligation(old.refundObligationId).paid == 3, "rewrote actual credit receipt");
        require(funds.creditBalance(funds.creditAccount(PAYER_A)) == 3, "rewrote original payer credit");
    }

    function testScopedTutorFaultLeavesOtherPlaceFeesIntactAndRecordsZeroOriginalWages() public {
        SparkV15Settlement.GroupAssessment memory input = _bookAndTeach(3, true);
        bytes32 formB = input.seats[1].formId;
        (SparkV15ReviewCases review, SparkV15ConcernIntake intake, bytes32 caseId) =
            _receiveReviewMatter(formB, SparkV15ReviewContext.ConcernSubject.StudentService);
        SparkV15LessonRemedies remedies = new SparkV15LessonRemedies(booking, payments, review, ROLE_SOURCE);
        settlement.setRemedyPolicy(ISparkV15SettlementRemedies(address(remedies)));
        SparkV15LessonRemedies.FaultFinding memory fault;
        fault.kind = SparkV15LessonRemedies.FaultKind.SeriousTeachingIncident;
        fault.responsibleTutor = TUTOR;
        fault.tutorAgreementRef = AGREEMENT;
        fault.originalOccurredAt = END;
        fault.groundRef = keccak256("verified serious incident affecting student B");
        fault.tutorInquiryRef = keccak256("coordinator verified tutor's account");
        fault.tutorResponseOpportunityRef = keccak256("actual opportunity for tutor to respond");
        fault.affectedStudentsInquiryRef = keccak256("coordinator verified B's report");
        fault.affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        fault.affected[0] = SparkV15LessonRemedies.AffectedPlace(
            formB,
            SparkV15LessonRemedies.TeachingReceived.FullyDelivered,
            SparkV15LessonRemedies.Participation.AttendedAsAgreed,
            0,
            false,
            keccak256("verified targeted incident")
        );
        _retainInitialFinding(
            review,
            intake.getConcern(caseId),
            caseId,
            SparkV15ReviewContext.DisputedFinding.Fault,
            remedies.faultOutcome(caseId, fault)
        );
        remedies.recordFault(caseId, fault);

        _propose(input);
        requestVm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, input, VERIFIER_ACTOR);
        input.seats[1].disposition = SparkV15Settlement.SeatDisposition.TutorFaultFee;
        _propose(input);
        _approveSettlement(input);
        SparkV15Settlement.SeatSettlement memory a = settlement.getSeatSettlement(LESSON, input.seats[0].formId);
        SparkV15Settlement.SeatSettlement memory b = settlement.getSeatSettlement(LESSON, formB);
        SparkV15Settlement.SeatSettlement memory c = settlement.getSeatSettlement(LESSON, input.seats[2].formId);
        require(a.feeDue == 10 && a.refundObligationId != bytes32(0) && c.feeDue == 20, "unaffected tuition changed");
        require(
            b.feeDue == 10 && b.refundDue == 10 && b.refundObligationId == bytes32(0), "affected fee or redress scope"
        );
        require(
            a.tutorObligationId == bytes32(0) && b.tutorObligationId == bytes32(0) && c.tutorObligationId == bytes32(0),
            "original tutor fault left wages payable"
        );
        require(settlement.getGroupSettlement(LESSON).netTutorPay == 0, "original tutor deduction missing");
    }

    function _finalizeReplacement(
        SparkV15BookingChanges changes,
        bytes32 formId,
        SparkV15Settlement.TutorPayTerms memory revised,
        bool reschedule
    ) private returns (bytes32 changeId, uint256 studentNotice) {
        uint64 contacted = reschedule ? START + 10 : EPOCH + 1 minutes;
        requestVm.warp(contacted);
        SparkV15BookingChanges.ArrangementTerms memory next;
        next.startsAt = reschedule ? START + 1 days : START;
        next.endsAt = reschedule ? END + 1 days : END;
        next.effectiveAt = contacted + 5;
        next.timeZoneRef = reschedule ? keccak256("UTC") : booking.getLesson(LESSON).terms.timeZoneRef;
        if (reschedule) next.noOpeningRef = keccak256("verified that teaching had not begun under the first schedule");
        next.replacement = SparkV15BookingChanges.ReplacementTerms(
            REPLACEMENT,
            revised.seats[0].ordinaryPay,
            revised.agreementRef,
            settlement.tutorPayTermsCommitment(LESSON, revised),
            booking.getLesson(LESSON).terms.serviceTermsRef,
            DOCUMENTS,
            DOCUMENTS,
            TUTOR_CHANNEL
        );
        bytes32 contact = keccak256("authorized parties contacted about new teaching time and tutor");
        uint256 proposed = _evidence(changes.proposalCommitment(LESSON, next, contacted, contact));
        requestVm.prank(COORDINATOR);
        changeId = changes.proposeArrangement(LESSON, next, contacted, contact, proposed);
        bytes32 inventory = keccak256("actual available replacement teaching funds after other commitments");
        uint128 revisedReserve = 58 + (revised.seats[0].ordinaryPay - 8);
        uint256 funding = _evidence(changes.replacementFundingCommitment(changeId, revisedReserve, inventory));
        requestVm.prank(VERIFIER_ACTOR);
        changes.verifyReplacementFunding(changeId, revisedReserve, inventory, funding);
        requestVm.prank(PROVIDER);
        changes.signReplacementAgreement(changeId);
        requestVm.prank(REPLACEMENT);
        changes.signReplacementAgreement(changeId);
        requestVm.prank(PAYER_A);
        changes.acceptPlace(changeId, formId);
        requestVm.prank(REPLACEMENT);
        changes.acceptTutor(changeId);
        requestVm.prank(PROVIDER);
        changes.acceptProvider(changeId);
        requestVm.prank(COORDINATOR);
        changes.recordAgreement(changeId);

        requestVm.warp(contacted + 1);
        bytes32 notice = keccak256("received notices of the effective replacement and schedule");
        studentNotice = _evidence(changes.studentChangeNoticeCommitment(changeId, formId, contacted + 1, notice));
        requestVm.prank(COORDINATOR);
        changes.recordStudentChangeNotice(changeId, formId, contacted + 1, notice, studentNotice);
        uint256 tutorNotice =
            _evidence(changes.tutorChangeNoticeCommitment(changeId, TUTOR_CHANNEL, contacted + 1, notice));
        requestVm.prank(PROVIDER);
        changes.recordTutorChangeNotice(changeId, TUTOR_CHANNEL, contacted + 1, notice, tutorNotice);
        requestVm.prank(COORDINATOR);
        changes.finalizeArrangement(changeId);
    }

    function _bookAndStartGroupWithoutPermission() private returns (SparkV15Settlement.GroupAssessment memory input) {
        input = _assessment(2);
        _publishLesson(input, 16);
        (bytes32[] memory forms,) = _bookGroup(2, false, bytes32(0));
        _provideNotices(forms);
        uint64 actualStart = LOCK - 60;
        requestVm.warp(actualStart);
        address[] memory present = new address[](2);
        present[0] = _student(0);
        present[1] = _student(1);
        SparkV15Booking.StartObservation memory observation = SparkV15Booking.StartObservation(
            actualStart,
            true,
            present,
            keccak256("provider actually opened before the agreed time"),
            keccak256("independently verified unsatisfied agreed start condition")
        );
        uint256 startEvidence = _evidence(booking.teachingStartCommitment(LESSON, observation));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingStarted(LESSON, observation, startEvidence);
        require(
            booking.getTeaching(LESSON).startPermission == SparkV15Booking.StartPermission.RequirementsNotMet,
            "fixture did not establish the special route"
        );
        requestVm.warp(LOCK);
        bytes32 roster = keccak256("verified final register for both paid places");
        uint256 rosterEvidence = _evidence(booking.rosterLockCommitment(LESSON, roster));
        requestVm.prank(COORDINATOR);
        booking.lockRoster(LESSON, roster, rosterEvidence);
        require(booking.getRosterLock(LESSON).recordedAt > actualStart, "cutoff followed the early opening");
        _recordEndAndTutorReport(END, TUTOR);
        _reportAttendance(forms[0], 0, true);
        _reportAttendance(forms[1], 1, true);
        input.route = SparkV15Settlement.Route.ProviderStartedEarly;
        for (uint256 i; i < forms.length; ++i) {
            input.seats[i].formId = forms[i];
            input.seats[i].disposition = SparkV15Settlement.SeatDisposition.ProviderStartedEarly;
        }
        input.seats[0].agreedAbsenceFee = 13;
        input.seats[0].agreedAbsenceTutorPay = 5;
        input.seats[1].agreedAbsenceFee = 9;
        input.seats[1].agreedAbsenceTutorPay = 3;
    }

    function _bookAndTeach(uint256 count, bool reportAbsence)
        private
        returns (SparkV15Settlement.GroupAssessment memory input)
    {
        input = _assessment(count);
        uint128 normalTutorPay = count == 3 ? 22 : 16;
        _publishLesson(input, normalTutorPay);
        (bytes32[] memory forms, uint256[] memory rechargeReceipts) = _bookGroup(count, false, bytes32(0));
        _teach(forms, true);
        for (uint256 i; i < count; ++i) {
            input.seats[i].formId = forms[i];
            require(funds.getRechargeReceipt(rechargeReceipts[i]).received == 20, "charge lacked actual recharge");
            if (i != 0 || reportAbsence) _reportAttendance(forms[i], i, i != 0);
            if (i != 0) _reportFullService(forms[i], _student(i));
        }
    }

    function _assessment(uint256 count) private pure returns (SparkV15Settlement.GroupAssessment memory input) {
        SparkV15Settlement.TutorSeatTerms[] memory wageSeats = new SparkV15Settlement.TutorSeatTerms[](count);
        input.seats = new SparkV15Settlement.SeatFinding[](count);
        for (uint256 i; i < count; ++i) {
            wageSeats[i] = SparkV15Settlement.TutorSeatTerms(_place(i), i == 2 ? 6 : 8, i == 0 ? 2 : 0);
            input.seats[i] = SparkV15Settlement.SeatFinding({
                formId: bytes32(0),
                disposition: i == 0
                    ? SparkV15Settlement.SeatDisposition.VerifiedAbsence
                    : SparkV15Settlement.SeatDisposition.OrdinaryFee,
                serviceAvailabilityRef: keccak256(abi.encode("independently verified available service", i)),
                feeHoldCaseId: bytes32(0),
                studentFaultFound: false,
                agreedAbsenceFee: 0,
                agreedAbsenceTutorPay: 0
            });
        }
        input.tutor = SparkV15Settlement.TutorPayTerms(
            AGREEMENT,
            WAGE_RECIPIENT,
            SparkV15Settlement.PaymentSchedule(WAGE_DUE, WAGE_DUE + 3 days, 0, 1 days),
            wageSeats
        );
        input.refund = SparkV15Settlement.RefundTerms(
            DOCUMENTS, SparkV15Settlement.PaymentSchedule(END + 1, WAGE_DUE + 4 days, 0, 1 days)
        );
        input.clearanceRef =
            keccak256("signed case inventory, no disqualifying interests, deduction, hold or earlier deadline");
    }

    function _publishLesson(SparkV15Settlement.GroupAssessment memory input, uint128 fullTutorPay) private {
        SparkV15Booking.LessonTerms memory terms;
        terms.lessonId = LESSON;
        terms.provider = PROVIDER;
        terms.tutor = TUTOR;
        terms.coordinator = COORDINATOR;
        terms.startsAt = START;
        terms.endsAt = END;
        if (input.route <= SparkV15Settlement.Route.VerifiedGroup) {
            terms.rosterLockAt = LOCK;
            terms.rosterRef = keccak256("private agreed roster");
        }
        terms.timeZoneRef = keccak256("UTC");
        terms.tutorNoticeChannelRef = TUTOR_CHANNEL;
        terms.tutorFee = fullTutorPay;
        terms.tutorAgreementRef = AGREEMENT;
        terms.serviceTermsRef = settlement.refundTermsCommitment(LESSON, input.refund);
        terms.tutorPayTermsRef = settlement.tutorPayTermsCommitment(LESSON, input.tutor);
        terms.providerResponsibilitiesRef = DOCUMENTS;
        terms.tutorResponsibilitiesRef = DOCUMENTS;
        terms.startTermsRef = DOCUMENTS;
        terms.documentsRef = DOCUMENTS;
        requestVm.prank(COORDINATOR);
        booking.publishLesson(terms);
    }

    function _bookGroup(uint256 count, bool discountedFirst, bytes32 changeTermsRef)
        private
        returns (bytes32[] memory forms, uint256[] memory receipts)
    {
        forms = new bytes32[](count);
        receipts = new uint256[](count);
        for (uint256 i; i < count; ++i) {
            bool discounted = i == 0 && discountedFirst;
            if (!discounted) receipts[i] = _recharge(_payer(i));
            SparkV15Booking.PlaceTerms memory terms;
            terms.placeId = _place(i);
            terms.customer = _customer(i);
            terms.payer = _payer(i);
            terms.student = _student(i);
            terms.creditAccount = funds.creditAccount(_payer(i));
            terms.studentNoticeChannelRef = keccak256(abi.encode("signed student notice channel", i));
            terms.normalFee = 20;
            terms.payableFee = discounted ? 0 : 20;
            terms.changeTermsRef = changeTermsRef;
            if (discounted) terms.discountBasis = keccak256("the signed full discount");
            else terms.rechargeDebitsHash = keccak256(abi.encode(_rechargeDebit(receipts[i])));
            requestVm.prank(COORDINATOR);
            forms[i] = booking.publishForm(LESSON, terms);
            _provideForm(forms[i], terms.customer);
            _provideForm(forms[i], TUTOR);
        }

        // The fixture's 200 provider units include 20 for other commitments and leave 180 available.
        token.mint(PROVIDER, 200);
        requestVm.prank(PROVIDER);
        token.transfer(address(funds), 180);
        uint128 reserve = uint128(count * 58);
        bytes32 inventory = keccak256("verified concurrent customer and tutor funding cases");
        uint256 funding = _evidence(booking.prefundingCommitment(LESSON, forms, reserve, inventory));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, forms, reserve, inventory, funding);
        requestVm.warp(EPOCH + 1);
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(LESSON);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(LESSON);
        for (uint256 i; i < count; ++i) {
            _accept(forms[i], PROVIDER, SparkV15Booking.Acceptance.Provider);
            _accept(forms[i], TUTOR, SparkV15Booking.Acceptance.Tutor);
            _accept(forms[i], _customer(i), SparkV15Booking.Acceptance.Customer);
            if (i == 0) _accept(forms[i], PAYER_A, SparkV15Booking.Acceptance.Payer);
            if (i == 0 && discountedFirst) {
                bytes32 discountRef = keccak256("verified full-discount entitlement for this place");
                uint256 proof = _evidence(booking.fullDiscountCommitment(forms[i], discountRef));
                requestVm.prank(COORDINATOR);
                booking.confirmPlace(forms[i], discountRef, proof, new SparkV15Funds.RechargeDebit[](0));
            } else {
                requestVm.prank(COORDINATOR);
                booking.confirmPlace(forms[i], bytes32(0), 0, _rechargeDebit(receipts[i]));
            }
            require(funds.creditBalance(funds.creditAccount(_payer(i))) == 0, "place debit failed");
        }
    }

    function _provideNotices(bytes32[] memory forms) private {
        bytes32 notice = keccak256("verified notice delivered on the agreed channel");
        for (uint256 i; i < forms.length; ++i) {
            uint256 noticeEvidence = _evidence(booking.studentNoticeCommitment(forms[i], EPOCH + 1, notice));
            requestVm.prank(COORDINATOR);
            booking.recordStudentNotice(forms[i], EPOCH + 1, notice, noticeEvidence);
        }
        uint256 tutorNotice = _evidence(booking.tutorNoticeCommitment(LESSON, TUTOR_CHANNEL, EPOCH + 1, notice));
        requestVm.prank(COORDINATOR);
        booking.recordTutorNotice(LESSON, TUTOR_CHANNEL, EPOCH + 1, notice, tutorNotice);
    }

    function _teach(bytes32[] memory forms, bool group) private {
        _provideNotices(forms);
        if (group) {
            requestVm.warp(LOCK);
            bytes32 register = keccak256("verified final register");
            uint256 rosterEvidence = _evidence(booking.rosterLockCommitment(LESSON, register));
            requestVm.prank(COORDINATOR);
            booking.lockRoster(LESSON, register, rosterEvidence);
        }
        address[] memory present = new address[](group ? forms.length - 1 : 1);
        for (uint256 i; i < present.length; ++i) {
            present[i] = _student(group ? i + 1 : i);
        }
        _recordTeaching(present, START, END, TUTOR);
    }

    function _recordTeaching(address[] memory present, uint64 startedAt, uint64 endedAt, address tutor) private {
        _recordOpening(present, startedAt);
        _recordEndAndTutorReport(endedAt, tutor);
    }

    function _recordOpening(address[] memory present, uint64 startedAt) private {
        requestVm.warp(startedAt);
        SparkV15Booking.StartObservation memory start = SparkV15Booking.StartObservation(
            startedAt, true, present, keccak256("observed actual teaching start"), bytes32(0)
        );
        uint256 startEvidence = _evidence(booking.teachingStartCommitment(LESSON, start));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingStarted(LESSON, start, startEvidence);
    }

    function _recordEndAndTutorReport(uint64 endedAt, address tutor) private {
        requestVm.warp(endedAt);
        bytes32 end = keccak256("observed actual teaching end");
        uint256 endEvidence = _evidence(booking.teachingEndCommitment(LESSON, endedAt, end));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingEnded(LESSON, endedAt, end, endEvidence);
        requestVm.warp(endedAt + 1);
        bytes32 tutorReport = keccak256("tutor's actual delivery report");
        uint256 deliveryEvidence = _evidence(booking.tutorDeliveryCommitment(LESSON, true, tutorReport));
        requestVm.prank(tutor);
        booking.recordTutorDelivery(LESSON, true, tutorReport, deliveryEvidence);
    }

    function _reportAttendance(bytes32 formId, uint256 i, bool attended) private {
        bytes32 report = keccak256(abi.encode("student reported actual attendance", i, attended));
        uint256 evidence = _evidence(booking.attendanceCommitment(formId, attended, report));
        requestVm.prank(_student(i));
        booking.recordAttendance(formId, attended, report, evidence);
    }

    function _reportFullService(bytes32 formId, address student) private {
        bytes32 received = keccak256("agreed teaching fully received");
        SparkV15Booking.ServiceStatus status = SparkV15Booking.ServiceStatus.FullyDelivered;
        uint256 evidence = _evidence(booking.serviceFeedbackCommitment(formId, status, received, bytes32(0)));
        requestVm.prank(student);
        booking.recordServiceFeedback(formId, status, received, bytes32(0), evidence);
    }

    function _settleProviderNoticeRefund(bytes32 formId) private returns (bytes32 refund) {
        SparkV15ReviewCases review = new SparkV15ReviewCases(payments, ROLE_SOURCE);
        review.bindIntake(new SparkV15ConcernIntake(payments, ROLE_SOURCE, review));
        (SparkV15LessonRemedies remedies, SparkV15CustomerRedress redress) = _installProviderRedress(review);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_SOURCE, remedies.ACTION_RECORD_UNDISPUTED_PROVIDER_FAULT(), true
        );

        uint256 notice = booking.getStudentNotice(formId).evidenceId;
        requestVm.prank(SOURCE_ACTOR);
        evidenceRegistry.recordEvidenceLifecycle(
            notice, ROLE_SOURCE, _authority(ROLE_SOURCE), AVACoreTypes.EvidenceLifecycleKind.Revoke, 0,
            keccak256("the notice supplied the wrong teaching details for this place"), ""
        );
        SparkV15LessonRemedies.FaultFinding memory finding;
        finding.kind = SparkV15LessonRemedies.FaultKind.ProviderNoticeError;
        finding.groundRef = keccak256("independently verified notice error at the affected place");
        finding.affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        finding.affected[0] = SparkV15LessonRemedies.AffectedPlace(
            formId, SparkV15LessonRemedies.TeachingReceived.NoneDelivered,
            SparkV15LessonRemedies.Participation.DidNotAttendOrPrepare, 20, true,
            keccak256("the wrong notice caused the student to miss the entire lesson")
        );
        bytes32 matter = keccak256("independently established provider notice fault");
        bytes32 noDispute = keccak256("checked no open dispute for this matter");
        uint256 proof = _evidence(remedies.providerFaultCommitment(formId, matter, finding, noDispute, COORDINATOR));
        requestVm.prank(COORDINATOR);
        remedies.recordUndisputedProviderFault(formId, matter, finding, noDispute, proof);
        return _payProviderRefund(redress, formId, 20);
    }

    function _installProviderRedress(SparkV15ReviewCases review)
        private
        returns (SparkV15LessonRemedies remedies, SparkV15CustomerRedress redress)
    {
        remedies = new SparkV15LessonRemedies(booking, payments, review, ROLE_SOURCE);
        redress = new SparkV15CustomerRedress(remedies, ROLE_SOURCE);
        remedies.bindCustomerRedress(redress);
        settlement.setRemedyPolicy(ISparkV15SettlementRemedies(address(remedies)));
        bytes32 payRole = payments.settlementRole();
        identityRegistry.assignSubject(address(redress), SparkV15.APP_ID, payRole, _authority(payRole), "test:refund");
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, redress.ACTION_ASSESS_REFUND(), true);
    }

    function _groupProviderAdministrationRefund(bytes32 formId)
        private
        returns (SparkV15ReviewCases review, SparkV15LessonRemedies remedies, bytes32 caseId, bytes32 refund)
    {
        SparkV15ConcernIntake intake;
        (review, intake, caseId) = _receiveReviewMatter(formId, SparkV15ReviewContext.ConcernSubject.StudentService);
        SparkV15CustomerRedress redress;
        (remedies, redress) = _installProviderRedress(review);
        SparkV15LessonRemedies.FaultFinding memory finding;
        finding.kind = SparkV15LessonRemedies.FaultKind.ProviderAdministrationError;
        finding.groundRef = keccak256("verified omitted administrative support for a taught student");
        finding.affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        finding.affected[0] = SparkV15LessonRemedies.AffectedPlace(
            formId, SparkV15LessonRemedies.TeachingReceived.FullyDelivered,
            SparkV15LessonRemedies.Participation.AttendedAsAgreed, 8, false,
            keccak256("eight units independently assessed for missing administrative support")
        );
        _retainInitialFinding(
            review, intake.getConcern(caseId), caseId, SparkV15ReviewContext.DisputedFinding.Fault,
            remedies.faultOutcome(caseId, finding)
        );
        remedies.recordFault(caseId, finding);
        refund = _payProviderRefund(redress, formId, 8);
    }

    function _payProviderRefund(SparkV15CustomerRedress redress, bytes32 formId, uint128 amount)
        private
        returns (bytes32 refund)
    {
        SparkV15Booking.PlaceTerms memory place = booking.getForm(formId).terms;
        SparkV15CustomerRedress.RedressTerms memory terms =
            SparkV15CustomerRedress.RedressTerms(END + 7 days, END + 14 days, 0, 3 days, 0, 1 days, DOCUMENTS, DOCUMENTS);
        uint256 proof = _evidence(redress.redressTermsCommitment(formId, terms));
        requestVm.prank(PROVIDER);
        redress.publishRedressTerms(formId, terms, proof);
        requestVm.prank(place.customer);
        redress.requestDirectRefund(formId);
        SparkV15CustomerRedress.RefundBasis cause = SparkV15CustomerRedress.RefundBasis.DirectRequest;
        (SparkV15CustomerRedress.RefundAssessment memory assessed, SparkV15Payments.PaymentTerms memory payment) =
            redress.previewRefund(formId, cause, VERIFIER_ACTOR);
        require(assessed.finalFee == place.payableFee - amount && assessed.principal == amount, "wrong assessed refund");
        require(payment.recipient == place.payer && payment.originalDebitAccount == place.creditAccount);
        proof = _evidence(assessed.basis);
        requestVm.prank(VERIFIER_ACTOR);
        uint256 index = redress.assessRefund(formId, cause, proof, _authority(ROLE_VERIFIER));
        proof = _evidence(payments.paymentEvidenceCommitment(payment, assessed.basis));
        requestVm.prank(VERIFIER_ACTOR);
        refund = redress.establishRefundPayment(formId, index, proof);
        uint256 approval = _approvePayment(refund, amount);
        requestVm.prank(EXECUTOR);
        uint256 receipt = payments.pay(approval, amount);
        require(payments.getReceipt(receipt).creditAccount == payment.originalDebitAccount, "wrong refund destination");
        require(funds.creditBalance(payment.originalDebitAccount) == amount, "the original debit was not restored");
    }

    function _reviseProviderRefund(
        SparkV15ReviewCases review, bytes32 faultCase, bytes32 refund, uint128 correctedAmount
    ) private {
        SparkV15Payments.Obligation memory payment = payments.getObligation(refund);
        SparkV15ReviewContext.OriginalInput memory original;
        original.termsId = review.INTAKE().caseContext(faultCase).termsId;
        original.concernRef = keccak256("separate review of the same refund's established amount");
        original.obligationId = refund;
        original.paymentCommitment = payment.commitment;
        original.decider = VERIFIER_ACTOR;
        original.decidedAt = END + 1;
        original.outcome = keccak256(abi.encode(refund, payment.terms.amount));
        original.parties = new address[](2);
        original.parties[0] = payment.terms.recipient;
        original.parties[1] = PROVIDER;
        bytes32 caseId = review.caseIdFor(LESSON, original.concernRef);
        uint256 retained = _evidence(review.evidenceCommitment(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, COORDINATOR, keccak256(abi.encode(original))
        ));
        bytes32 coordinator = identityRegistry.subjectOf(COORDINATOR, SparkV15.APP_ID, ROLE_SOURCE);
        requestVm.prank(COORDINATOR);
        review.retainOriginal(original, retained, coordinator);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, true);
        bytes32 effectRole = payments.caseEffectRole();
        authorityMatrix.setPermission(SparkV15.APP_ID, effectRole, payments.ACTION_APPLY_CASE_EFFECT(), true);
        identityRegistry.assignSubject(address(review), SparkV15.APP_ID, effectRole, _authority(effectRole), "test:case-effects");

        requestVm.warp(END + 2);
        SparkV15Payments.PaymentRevision memory revision = SparkV15Payments.PaymentRevision(
            refund, correctedAmount, payment.beneficiary, payment.destination, payment.version
        );
        bytes32 outcome = keccak256(abi.encode(
            keccak256("spark.v1.5.revise-payment"), block.chainid, address(payments), caseId, revision, payment.commitment
        ));
        SparkV15ReviewContext.ReviewInput memory decision = SparkV15ReviewContext.ReviewInput(
            SparkV15ReviewContext.ReviewDisposition.CorrectionRequired, outcome, keccak256("refined exact value of lost support"), 0
        );
        uint256 reviewed = _evidence(review.evidenceCommitment(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(decision))
        ));
        requestVm.prank(REVIEWER);
        review.decidePaymentRevision(caseId, decision, revision, reviewed, REVIEWER_ID);
        requestVm.warp(END + 3);
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("notified both parties of the amount correction"), END + 3);
        bytes32 payload = keccak256(abi.encode(notice, retained, reviewed, keccak256(abi.encode(original.parties)), bytes32(0)));
        uint256 adopted = _evidence(review.evidenceCommitment(
            caseId, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, COORDINATOR, payload
        ));
        requestVm.prank(COORDINATOR);
        review.adoptPaymentRevision(caseId, notice, adopted, coordinator, revision);
        SparkV15Payments.Obligation memory corrected = payments.getObligation(refund);
        require(corrected.correctAmount == correctedAmount && corrected.paid == 8, "wrong live or historic amount");
    }

    function _adoptProviderNoFault(
        SparkV15ReviewCases review, SparkV15LessonRemedies remedies, bytes32 caseId, bytes32 formId
    ) private {
        SparkV15LessonRemedies.FaultFinding memory finding;
        finding.kind = SparkV15LessonRemedies.FaultKind.NoFault;
        finding.groundRef = keccak256("an independent review confirmed the separately agreed support was provided");
        finding.affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        finding.affected[0] = SparkV15LessonRemedies.AffectedPlace(
            formId, SparkV15LessonRemedies.TeachingReceived.FullyDelivered,
            SparkV15LessonRemedies.Participation.AttendedAsAgreed, 0, false,
            keccak256("the exact student's accepted original support and delivery receipt")
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, true);
        requestVm.warp(END + 2);
        SparkV15ReviewContext.ReviewInput memory decision = SparkV15ReviewContext.ReviewInput(
            SparkV15ReviewContext.ReviewDisposition.CorrectionRequired,
            remedies.faultOutcome(caseId, finding), finding.groundRef, 0
        );
        uint256 reviewed = _evidence(review.evidenceCommitment(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(decision))
        ));
        requestVm.prank(REVIEWER);
        review.decideReview(caseId, decision, reviewed, REVIEWER_ID);
        requestVm.warp(END + 3);
        SparkV15ReviewContext.OriginalOutcome memory original = review.getCase(caseId).original;
        SparkV15ReviewContext.Notice memory notice = SparkV15ReviewContext.Notice(
            keccak256("the original parties received the reviewed finding"), END + 3
        );
        bytes32 parties = review.INTAKE().getConcern(caseId).intake.partiesHash;
        bytes32 payload = keccak256(abi.encode(notice, original.evidenceId, reviewed, original.partiesHash, parties));
        uint256 adopted = _evidence(review.evidenceCommitment(
            caseId, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, COORDINATOR, payload
        ));
        bytes32 coordinator = identityRegistry.subjectOf(COORDINATOR, SparkV15.APP_ID, ROLE_SOURCE);
        requestVm.prank(COORDINATOR);
        review.adoptCorrection(caseId, notice, adopted, coordinator);
        remedies.recordFault(caseId, finding);
        require(remedies.placeFaultCase(formId) == bytes32(0) && remedies.isOperative(caseId, 2), "no current no-fault decision");
    }

    function _provideForm(bytes32 formId, address recipient) private {
        uint256 evidence = _evidence(booking.provisionCommitment(formId, recipient, DOCUMENTS));
        requestVm.prank(COORDINATOR);
        booking.recordTermsProvision(formId, recipient, DOCUMENTS, evidence);
    }

    function _accept(bytes32 formId, address signer, SparkV15Booking.Acceptance role) private {
        requestVm.prank(signer);
        booking.acceptForm(formId, role);
    }

    function _recharge(address payer) private returns (uint256 receipt) {
        requestVm.prank(PROVIDER);
        bytes32 offer =
            funds.offerRecharge(SparkV15Funds.RechargeTerms(payer, 20, 20, LOCK, AGREEMENT), CREDIT_PROVIDER_ID);
        token.mint(payer, 20);
        requestVm.startPrank(payer);
        token.approve(address(funds), 20);
        receipt = funds.recharge(offer);
        requestVm.stopPrank();
    }

    function _rechargeDebit(uint256 receipt) private pure returns (SparkV15Funds.RechargeDebit[] memory debits) {
        debits = new SparkV15Funds.RechargeDebit[](1);
        debits[0] = SparkV15Funds.RechargeDebit(receipt, 20);
    }

    function _propose(SparkV15Settlement.GroupAssessment memory input) private {
        bytes32 commitment = settlement.proposalCommitment(LESSON, input);
        requestVm.prank(COORDINATOR);
        settlement.proposeOrdinaryGroup(LESSON, commitment);
    }

    function _approveSettlement(SparkV15Settlement.GroupAssessment memory input) private returns (bytes32) {
        return _approveSettlementAs(input, VERIFIER_ACTOR);
    }

    function _approveSettlementAs(SparkV15Settlement.GroupAssessment memory input, address approver)
        private
        returns (bytes32 basis)
    {
        SparkV15Settlement.GroupPreview memory preview = settlement.previewOrdinaryGroup(LESSON, input, approver);
        basis = preview.basis;
        uint256 approvalEvidence = _evidence(basis);
        uint256[] memory paymentEvidence = new uint256[](preview.payments.length);
        for (uint256 i; i < paymentEvidence.length; ++i) {
            paymentEvidence[i] = _evidence(payments.paymentEvidenceCommitment(preview.payments[i], basis));
        }
        requestVm.prank(approver);
        settlement.approveOrdinaryGroup(LESSON, input, approvalEvidence, paymentEvidence);
    }

    function _completion(bytes32 formId, address actor) private {
        bytes32 report = keccak256("the actor confirmed that the agreed lesson was completed");
        uint256 evidence = _evidence(alternatives.completionCommitment(formId, report, actor));
        requestVm.prank(actor);
        alternatives.recordOneToOneCompletion(formId, report, evidence);
    }

    function _establishFixtureRefund() private returns (bytes32) {
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_ESTABLISH_PAYMENT, true);
        SparkV15Payments.PaymentTerms memory terms;
        terms.lessonId = LESSON;
        terms.paymentPart = settlement.refundPaymentPart(_place(0));
        terms.recipient = PAYER_A;
        terms.originalDebitAccount = funds.creditAccount(PAYER_A);
        terms.originalDebitAmount = 20;
        terms.amount = 10;
        terms.dueAt = END + 1;
        terms.dueAtExact = true;
        terms.executionDeadline = WAGE_DUE + 4 days;
        terms.executionDeadlineExact = true;
        terms.postLiftPeriod = 1 days;
        terms.settlementProposer = COORDINATOR;
        terms.settlementApprover = VERIFIER_ACTOR;
        bytes32 basis = keccak256("retained prior refund assessment for the original account and fee reduction");
        uint256 evidence = _evidence(payments.paymentEvidenceCommitment(terms, basis));
        requestVm.prank(VERIFIER_ACTOR);
        return payments.establishPayment(terms, basis, evidence, _authority(ROLE_VERIFIER));
    }

    function _establishFixtureTutorPortion() private returns (bytes32) {
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_ESTABLISH_PAYMENT, true);
        SparkV15Payments.PaymentTerms memory terms;
        terms.lessonId = LESSON;
        terms.paymentPart = settlement.tutorPaymentPart(TUTOR, _place(0));
        terms.recipient = WAGE_RECIPIENT;
        terms.amount = 2;
        terms.agreedStart = START;
        terms.dueAt = WAGE_DUE;
        terms.dueAtExact = true;
        terms.executionDeadline = WAGE_DUE + 3 days;
        terms.executionDeadlineExact = true;
        terms.postLiftPeriod = 1 days;
        terms.settlementProposer = COORDINATOR;
        terms.settlementApprover = VERIFIER_ACTOR;
        bytes32 basis = keccak256("verified already established corresponding tutor portion for the held place");
        uint256 evidence = _evidence(payments.paymentEvidenceCommitment(terms, basis));
        requestVm.prank(VERIFIER_ACTOR);
        return payments.establishPayment(terms, basis, evidence, _authority(ROLE_VERIFIER));
    }

    function _holdFee(bytes32 formId) private returns (bytes32 caseId) {
        (, SparkV15ConcernIntake intake, bytes32 matter) =
            _receiveReviewMatter(formId, SparkV15ReviewContext.ConcernSubject.CustomerFee);
        caseId = matter;
        SparkV15ReviewContext.Notice memory notice = SparkV15ReviewContext.Notice(
            keccak256("given to all parties with fee scope, reason and review date"),
            intake.getConcern(caseId).intake.receivedAt
        );
        SparkV15SettlementAlternatives.FeeHoldTerms memory hold =
            SparkV15SettlementAlternatives.FeeHoldTerms(formId, caseId, notice, WAGE_DUE + 1 days);
        uint256 evidence = _evidence(alternatives.feeHoldCommitment(hold, REVIEWER));
        requestVm.prank(REVIEWER);
        alternatives.imposeFeeHold(hold, evidence, REVIEWER_ID);
    }

    function _receiveReviewMatter(bytes32 formId, SparkV15ReviewContext.ConcernSubject subject)
        private
        returns (SparkV15ReviewCases review, SparkV15ConcernIntake intake, bytes32 caseId)
    {
        bytes32 termsId;
        (review, intake, termsId) = _publishReviewContacts(formId);
        address customer = booking.getForm(formId).terms.customer;
        SparkV15ReviewContext.ConcernInput memory input;
        input.termsId = termsId;
        input.concernRef = keccak256(abi.encode("review of an identified place", formId, subject));
        input.receiver = COORDINATOR;
        input.subject = subject;
        input.claim = keccak256("the customer disputes the original finding for this place");
        input.subjectRef = booking.getForm(formId).terms.placeId;
        input.parties = new address[](2);
        input.parties[0] = customer;
        input.parties[1] = PROVIDER;
        caseId = review.caseIdFor(LESSON, input.concernRef);
        uint256 filing = _evidence(
            review.evidenceCommitment(
                caseId, SparkV15ReviewActions.ACTION_RECEIVE_CONCERN, customer, keccak256(abi.encode(input))
            )
        );
        requestVm.prank(customer);
        intake.receiveConcern(input, filing);
    }

    function _publishReviewContacts(bytes32 formId)
        private
        returns (SparkV15ReviewCases review, SparkV15ConcernIntake intake, bytes32 termsId)
    {
        review = new SparkV15ReviewCases(payments, ROLE_SOURCE);
        intake = new SparkV15ConcernIntake(payments, ROLE_SOURCE, review);
        review.bindIntake(intake);
        payments.bindReviewCases(ISparkV15AdoptedDispositions(address(review)));
        bytes32 providerAuthority = keccak256("provider review publication authority");
        identityRegistry.assignSubject(
            PROVIDER, SparkV15.APP_ID, ROLE_VERIFIER, providerAuthority, "test:provider-review"
        );
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, true
        );
        termsId = _publishReviewTerms(review, formId);
    }

    function _publishReviewTerms(SparkV15ReviewCases review, bytes32 formId) private returns (bytes32 termsId) {
        SparkV15ReviewContext.ReviewTerms memory terms;
        terms.lessonId = LESSON;
        terms.publication = DOCUMENTS;
        terms.governingForm = formId;
        terms.provider = PROVIDER;
        terms.coordinator = COORDINATOR;
        terms.alternativeContact = _customer(2);
        terms.leadAcademicTutor = ALLOCATOR_ACTOR;
        terms.namedReviewer = REVIEWER;
        terms.escalationContact = ALLOCATOR_ACTOR;
        terms.replyPeriod = 1 days;
        terms.reviewDeadline = WAGE_DUE + 2 days;
        termsId = keccak256(abi.encode(terms));
        uint256 publication = _evidence(
            review.evidenceCommitment(termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, PROVIDER, termsId)
        );
        SparkV15ConcernIntake intake = review.INTAKE();
        requestVm.prank(PROVIDER);
        intake.publishContacts(terms, publication, keccak256("provider review publication authority"));
    }

    function _retainInitialFinding(
        SparkV15ReviewCases review,
        SparkV15ReviewContext.ConcernRecord memory concern,
        bytes32 caseId,
        SparkV15ReviewContext.DisputedFinding issue,
        bytes32 outcome
    ) private {
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_ALLOCATOR, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, true
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, true);
        SparkV15ReviewContext.InitialInput memory initial = SparkV15ReviewContext.InitialInput(
            issue, outcome, keccak256("initial reasons"), keccak256("verified then-available evidence")
        );
        uint256 evidence = _evidence(
            review.evidenceCommitment(
                caseId, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, ALLOCATOR_ACTOR, keccak256(abi.encode(initial))
            )
        );
        requestVm.prank(ALLOCATOR_ACTOR);
        review.decideInitial(caseId, initial, evidence, _authority(ROLE_ALLOCATOR));

        SparkV15ReviewContext.OriginalInput memory original;
        original.termsId = concern.termsId;
        original.concernRef = concern.concernRef;
        original.decider = ALLOCATOR_ACTOR;
        original.decidedAt = END + 1;
        original.outcome = outcome;
        original.parties = new address[](2);
        original.parties[0] = concern.intake.raisedBy;
        original.parties[1] = PROVIDER;
        uint256 retained = _evidence(
            review.evidenceCommitment(
                caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, COORDINATOR, keccak256(abi.encode(original))
            )
        );
        bytes32 authorityId = identityRegistry.subjectOf(COORDINATOR, SparkV15.APP_ID, ROLE_SOURCE);
        requestVm.prank(COORDINATOR);
        review.retainOriginal(original, retained, authorityId);
    }

    function _adoptAbsenceCorrection(
        SparkV15ReviewCases review,
        SparkV15ReviewContext.ConcernRecord memory concern,
        bytes32 caseId,
        bytes32 formId
    ) private {
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, true);
        requestVm.warp(END + 2);
        SparkV15ReviewContext.ReviewInput memory finding = SparkV15ReviewContext.ReviewInput(
            SparkV15ReviewContext.ReviewDisposition.CorrectionRequired,
            alternatives.absenceReasonOutcome(formId, SparkV15SettlementAlternatives.AbsenceReason.GoodReason),
            keccak256("independently verified a qualifying reason"),
            0
        );
        uint256 reviewed = _evidence(
            review.evidenceCommitment(
                caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(finding))
            )
        );
        requestVm.prank(REVIEWER);
        review.decideReview(caseId, finding, reviewed, REVIEWER_ID);
        requestVm.warp(END + 3);
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("notified both users of the reviewed reason"), END + 3);
        SparkV15ReviewContext.OriginalOutcome memory original = review.getCase(caseId).original;
        bytes32 payload = keccak256(
            abi.encode(notice, original.evidenceId, reviewed, original.partiesHash, concern.intake.partiesHash)
        );
        uint256 adopted = _evidence(
            review.evidenceCommitment(caseId, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, COORDINATOR, payload)
        );
        bytes32 authorityId = identityRegistry.subjectOf(COORDINATOR, SparkV15.APP_ID, ROLE_SOURCE);
        requestVm.prank(COORDINATOR);
        review.adoptCorrection(caseId, notice, adopted, authorityId);
    }

    function _recordAbsence(SparkV15SettlementAlternatives.AbsenceFacts memory facts) private {
        uint256 evidence = _evidence(alternatives.absenceCommitment(facts, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        alternatives.recordOneToOneAbsence(facts, evidence);
    }

    function _liftFee(bytes32 caseId) private {
        bytes32 disposition = keccak256("independent reviewer confirmed the fee can be assessed");
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("notified all parties of fee hold release"), WAGE_DUE);
        uint256 evidence = _evidence(alternatives.feeLiftCommitment(caseId, disposition, notice, REVIEWER));
        requestVm.prank(REVIEWER);
        alternatives.liftFeeHold(caseId, disposition, notice, evidence, REVIEWER_ID);
    }

    function _approvePayment(bytes32 obligation, uint128 amount) private returns (uint256 requestId) {
        return _approvePaymentUntil(obligation, amount, WAGE_DUE);
    }

    function _approvePaymentUntil(bytes32 obligation, uint128 amount, uint64 requestCutoff)
        private
        returns (uint256 requestId)
    {
        SparkV15Payments.ApprovalTerms memory terms =
            SparkV15Payments.ApprovalTerms(obligation, EXECUTOR, amount, WAGE_DUE + 1 days, 0);
        bytes32 parameters = payments.approvalParameters(terms);
        uint256 stateId = _createRequestState(
            address(payments), SparkV15.RESPONSE_APPROVE_PAYMENT, parameters, SparkV15.APPROVAL_BURDEN, requestCutoff
        );
        requestId = _createRequest(
            AVARequestAllocation.RequestInput(
                stateId,
                address(payments),
                SparkV15.RESPONSE_APPROVE_PAYMENT,
                parameters,
                SparkV15.APPROVAL_BURDEN,
                requestCutoff
            )
        );
        _approveRequest(requestId);
        requestVm.prank(ALLOCATOR_ACTOR);
        payments.recordApproval(requestId, terms);
    }

    function _holdRefund(bytes32 obligation) private returns (bytes32) {
        SparkV15PaymentHolds.HoldTerms memory terms = SparkV15PaymentHolds.HoldTerms(
            obligation,
            keccak256("case concerning only A's refund"),
            keccak256("notice to the account owner"),
            WAGE_DUE,
            payments.getObligation(obligation).version
        );
        uint256 evidence = _evidence(payments.HOLDS().formalHoldCommitment(terms, REVIEWER));
        requestVm.prank(REVIEWER);
        return payments.imposeFormalHold(terms, evidence, REVIEWER_ID);
    }

    function _releaseRefund(bytes32 hold, bytes32 obligation) private {
        uint256 version = payments.getObligation(obligation).version;
        bytes32 finding = keccak256("review confirmed A's original debit and refund");
        uint256 evidence = _evidence(payments.HOLDS().formalLiftCommitment(hold, finding, version, REVIEWER));
        requestVm.prank(REVIEWER);
        payments.liftFormalHold(hold, finding, version, evidence, REVIEWER_ID);
    }

    function _evidence(bytes32 commitment) private returns (uint256) {
        return _evidenceOfType(commitment, keccak256("verified Spark lesson settlement record"));
    }

    function _evidenceOfType(bytes32 commitment, bytes32 evidenceType) private returns (uint256) {
        return _evidenceFrom(commitment, evidenceType, SOURCE_ACTOR, _authority(ROLE_SOURCE));
    }

    function _evidenceFrom(bytes32 commitment, bytes32 evidenceType, address source, bytes32 sourceId)
        private
        returns (uint256)
    {
        requestVm.prank(source);
        return evidenceRegistry.registerEvidence(
            AVAEvidenceRegistry.EvidenceRegistrationInput({
                appId: SparkV15.APP_ID,
                workflowKey: REQUEST_WORKFLOW,
                packageId: requestPackageId,
                roleKey: ROLE_SOURCE,
                subjectId: sourceId,
                commitment: commitment,
                evidenceTypeHash: evidenceType,
                disclosurePolicyId: requestPolicyId,
                authorityId: sourceId,
                uri: "test:settlement-record"
            })
        );
    }

    function _place(uint256 i) private pure returns (bytes32) {
        return bytes32(i + 1);
    }

    function _customer(uint256 i) private pure returns (address) {
        return address(uint160(0x7250 + i));
    }

    function _payer(uint256 i) private pure returns (address) {
        return i == 0 ? PAYER_A : _customer(i);
    }

    function _student(uint256 i) private pure returns (address) {
        return address(uint160(0x7260 + i));
    }
}
