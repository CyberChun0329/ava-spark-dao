// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {SparkV15, SparkV15ApplicationModule} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {IERC20} from "../../../src/apps/spark/legacy/interfaces/IERC20.sol";
import {RequestAllocationFixture} from "../../helpers/RequestAllocationFixture.sol";
import {MockERC20} from "../mocks/MockERC20.sol";

contract SharedFundsTest is RequestAllocationFixture {
    bytes32 private constant LESSON_A = keccak256("lesson A");
    bytes32 private constant LESSON_B = keccak256("lesson B");
    bytes32 private constant PAYMENT_A = keccak256("lesson A teacher obligation");
    bytes32 private constant PAYMENT_B = keccak256("lesson B teacher obligation");
    address private constant TEACHER = address(0xCAFE);
    address private constant CUSTOMER = address(0xCAFE1);

    MockERC20 private token;
    SparkV15Funds private funds;

    function setUp() public {
        _setUpRequestAllocation(
            SparkV15.APP_ID,
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR),
            SparkV15.OBJECT_PAYMENT_APPROVAL
        );
        token = new MockERC20("Spark fixture USD", "TUSD", 6);
        funds = new SparkV15Funds(requestAllocation, IERC20(address(token)), REQUEST_WORKFLOW, address(this));
    }

    function testPaymentReusesItsLessonReserveAndCannotSpendAnotherLessonsReserve() public {
        _authoriseBooking(funds, address(this));
        token.mint(address(funds), 15);
        funds.reserveLessonBudget(LESSON_A, 7);
        funds.reserveLessonBudget(LESSON_A, 7);
        funds.reserveLessonBudget(LESSON_B, 5);
        funds.reservePayment(PAYMENT_A, LESSON_A, 8);

        require(funds.lessonReserved(LESSON_A) == 0 && funds.lessonReserved(LESSON_B) == 5, "wrong lesson backing");
        require(funds.paymentReserved(PAYMENT_A) == 8 && funds.reservedUnits() == 13, "wrong obligation backing");
        requestVm.expectRevert(SparkV15Funds.InsufficientFunds.selector);
        funds.reservePayment(PAYMENT_B, LESSON_A, 3);

        funds.disbursePayment(PAYMENT_A, TEACHER, bytes32(0), 8);
        require(token.balanceOf(TEACHER) == 8 && token.balanceOf(address(funds)) == 7, "wrong actual receipt");
        require(funds.paymentReserved(PAYMENT_A) == 0 && funds.reservedUnits() == 5, "wrong remaining reserve");
    }

    function testLessonRefundCreditCannotReplaceSpentUnitsOfTheOriginalRecharge() public {
        _authoriseBooking(funds, address(this));
        bytes32 account = funds.creditAccount(CUSTOMER);
        uint256 original = _recharge(10, 8, keccak256("recharge with a return cap"));
        require(token.balanceOf(address(funds)) == 10 && funds.creditBalance(account) == 10, "wrong recharge effect");
        requestVm.expectRevert(SparkV15Funds.InsufficientFunds.selector);
        funds.reserveLessonBudget(LESSON_B, 1);
        requestVm.expectRevert(SparkV15Funds.InsufficientFunds.selector);
        funds.chargeLesson(LESSON_A, account, 8);
        funds.chargeLessonFrom(LESSON_A, account, 8, _source(original, 8));
        funds.reservePayment(PAYMENT_A, LESSON_A, 8);
        funds.disbursePayment(PAYMENT_A, CUSTOMER, account, 8);
        require(funds.creditBalance(account) == 10 && funds.reservedUnits() == 10, "refund not backed");

        requestVm.expectRevert(SparkV15Funds.InvalidRecharge.selector);
        requestVm.prank(CUSTOMER);
        funds.returnRecharge(original, 3);
        requestVm.prank(CUSTOMER);
        funds.returnRecharge(original, 2);

        SparkV15Funds.RechargeReceipt memory receipt = funds.getRechargeReceipt(original);
        require(receipt.creditAccount == account && receipt.received == 10 && receipt.returned == 2, "wrong receipt");
        require(funds.creditBalance(account) == 8 && funds.reservedUnits() == 8, "refund credit lost");
        require(token.balanceOf(CUSTOMER) == 2 && token.balanceOf(address(funds)) == 8, "wrong return effect");
    }

    function testNamedRechargePaysWhileAnotherRechargeKeepsItsOriginalReturnTerms() public {
        _authoriseBooking(funds, address(this));
        bytes32 account = funds.creditAccount(CUSTOMER);
        uint256 original = _recharge(6, 6, keccak256("earlier refundable recharge"));
        uint256 selected = _recharge(5, 4, keccak256("later refundable recharge"));
        funds.chargeLessonFrom(LESSON_A, account, 4, _source(selected, 4));

        requestVm.expectRevert(SparkV15Funds.InvalidRecharge.selector);
        requestVm.prank(CUSTOMER);
        funds.returnRecharge(selected, 2);
        requestVm.prank(CUSTOMER);
        funds.returnRecharge(original, 6);
        require(funds.getRechargeReceipt(selected).unspentForReturn == 1, "selected source lost");
        require(funds.creditBalance(account) == 1 && funds.reservedUnits() == 5, "wrong remaining liabilities");
        require(funds.lessonReserved(LESSON_A) == 4 && token.balanceOf(CUSTOMER) == 6, "wrong actual effect");
    }

    function testOnlyExactCashReturningFromRecipientReopensThePaymentReserve() public {
        token.mint(address(funds), 8);
        funds.reservePayment(PAYMENT_A, LESSON_A, 8);
        funds.disbursePayment(PAYMENT_A, TEACHER, bytes32(0), 8);

        requestVm.expectRevert();
        funds.takePaymentReturn(PAYMENT_A, TEACHER, bytes32(0), 3);
        require(funds.reservedUnits() == 0 && funds.paymentReserved(PAYMENT_A) == 0, "unbacked reopening");
        require(token.balanceOf(TEACHER) == 8 && token.balanceOf(address(funds)) == 0, "failed return moved funds");

        requestVm.prank(TEACHER);
        token.approve(address(funds), 3);
        funds.takePaymentReturn(PAYMENT_A, TEACHER, bytes32(0), 3);
        require(funds.reservedUnits() == 3 && funds.paymentReserved(PAYMENT_A) == 3, "return did not reopen");
        require(token.balanceOf(TEACHER) == 5 && token.balanceOf(address(funds)) == 3, "wrong return effect");
    }

    function testNativeReturnMovesItsAccountBackingWithoutConsumingAnotherRecharge() public {
        bytes32 account = funds.creditAccount(CUSTOMER);
        uint256 receiptId = _recharge(6, 6, keccak256("recharge independent of existing refund"));
        token.mint(address(funds), 4);
        funds.reservePayment(PAYMENT_A, LESSON_A, 4);
        funds.disbursePayment(PAYMENT_A, CUSTOMER, account, 4);
        funds.takePaymentReturn(PAYMENT_A, CUSTOMER, account, 4);

        require(funds.paymentReserved(PAYMENT_A) == 4 && funds.creditBalance(account) == 6, "wrong reclassification");
        require(funds.getRechargeReceipt(receiptId).unspentForReturn == 6, "recovery spent an unrelated recharge");
        require(funds.reservedUnits() == 10 && token.balanceOf(address(funds)) == 10, "backing changed");
    }

    function testBookingAuthorityAndPaymentCallerAreBoundToTheirInstallation() public {
        SparkV15Funds other = new SparkV15Funds(requestAllocation, IERC20(address(token)), REQUEST_WORKFLOW, TEACHER);
        _authoriseBooking(funds, address(this));
        token.mint(address(funds), 5);
        token.mint(address(other), 5);
        funds.reserveLessonBudget(LESSON_A, 2);

        requestVm.expectRevert();
        other.reserveLessonBudget(LESSON_A, 2);
        requestVm.expectRevert(SparkV15Funds.NotPayments.selector);
        other.reservePayment(PAYMENT_A, LESSON_A, 2);
        requestVm.expectRevert(SparkV15Funds.NotPayments.selector);
        requestVm.prank(TEACHER);
        funds.reservePayment(PAYMENT_A, LESSON_A, 2);

        require(funds.reservedUnits() == 2 && other.reservedUnits() == 0, "funds crossed installations");
    }

    function testRechargeReturnIsLimitedToTheCustomerCumulativeCapAndDeadline() public {
        uint256 receiptId = _recharge(10, 5, keccak256("receipt with time and amount limits"));
        SparkV15Funds.RechargeReceipt memory receipt = funds.getRechargeReceipt(receiptId);
        SparkV15Funds.RechargeOffer memory offer = funds.getRechargeOffer(receipt.offerId);
        require(offer.provider == SOURCE_ACTOR && offer.receiptId == receiptId, "missing original approval");
        requestVm.expectRevert(SparkV15Funds.InvalidRecharge.selector);
        requestVm.prank(TEACHER);
        funds.returnRecharge(receiptId, 1);
        requestVm.expectRevert(SparkV15Funds.InvalidRecharge.selector);
        requestVm.prank(CUSTOMER);
        funds.recharge(receipt.offerId);

        requestVm.prank(CUSTOMER);
        funds.returnRecharge(receiptId, 4);
        requestVm.expectRevert(SparkV15Funds.InvalidRecharge.selector);
        requestVm.prank(CUSTOMER);
        funds.returnRecharge(receiptId, 2);
        requestVm.warp(offer.terms.returnThrough + 1);
        requestVm.expectRevert(SparkV15Funds.InvalidRecharge.selector);
        requestVm.prank(CUSTOMER);
        funds.returnRecharge(receiptId, 1);
        require(token.balanceOf(CUSTOMER) == 4 && funds.reservedUnits() == 6, "unexpected return");
    }

    function testRechargeThatReceivesLessThanTheAgreedAmountCreatesNoCreditOrReceipt() public {
        ShortReceiptToken shortToken = new ShortReceiptToken();
        funds = new SparkV15Funds(requestAllocation, shortToken, REQUEST_WORKFLOW, address(this));
        bytes32 offerId = _offerRecharge(10, 4, keccak256("recharge must be received in full"));
        shortToken.mint(CUSTOMER, 10);

        requestVm.expectRevert(SparkV15Funds.TransferMismatch.selector);
        requestVm.prank(CUSTOMER);
        funds.recharge(offerId);

        require(funds.getRechargeOffer(offerId).receiptId == 0 && funds.reservedUnits() == 0, "unverified receipt");
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == 0, "unverified credit");
        require(shortToken.balanceOf(CUSTOMER) == 10 && shortToken.balanceOf(address(funds)) == 0, "transfer stuck");
    }

    function _source(uint256 receiptId, uint128 amount) private pure returns (SparkV15Funds.RechargeDebit[] memory) {
        SparkV15Funds.RechargeDebit[] memory debits = new SparkV15Funds.RechargeDebit[](1);
        debits[0] = SparkV15Funds.RechargeDebit(receiptId, amount);
        return debits;
    }

    function _recharge(uint128 amount, uint128 returnCap, bytes32 agreementRef) private returns (uint256) {
        bytes32 offerId = _offerRecharge(amount, returnCap, agreementRef);
        token.mint(CUSTOMER, amount);
        requestVm.startPrank(CUSTOMER);
        token.approve(address(funds), amount);
        uint256 receiptId = funds.recharge(offerId);
        requestVm.stopPrank();
        return receiptId;
    }

    function _offerRecharge(uint128 amount, uint128 returnCap, bytes32 agreementRef) private returns (bytes32) {
        bytes32 role = funds.CREDIT_PROVIDER_ROLE();
        bytes32 authorityId = keccak256(abi.encode(role, SOURCE_ACTOR));
        if (identityRegistry.subjectOf(SOURCE_ACTOR, SparkV15.APP_ID, role) == bytes32(0)) {
            identityRegistry.assignSubject(SOURCE_ACTOR, SparkV15.APP_ID, role, authorityId, "test:provider");
            authorityMatrix.setPermission(SparkV15.APP_ID, role, funds.ACTION_OFFER_RECHARGE(), true);
        }
        SparkV15Funds.RechargeTerms memory terms = SparkV15Funds.RechargeTerms({
            customer: CUSTOMER,
            amount: amount,
            returnCap: returnCap,
            returnThrough: returnCap == 0 ? 0 : uint64(block.timestamp + 30 days),
            agreementRef: agreementRef
        });
        requestVm.prank(SOURCE_ACTOR);
        return funds.offerRecharge(terms, authorityId);
    }

    function _authoriseBooking(SparkV15Funds vault, address booking) private {
        bytes32 role = vault.BOOKING_ROLE();
        identityRegistry.assignSubject(
            booking, SparkV15.APP_ID, role, keccak256(abi.encode(role, booking)), "test:booking"
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, role, vault.ACTION_MANAGE_LESSON_FUNDS(), true);
    }
}

contract ShortReceiptToken is IERC20 {
    mapping(address => uint256) public balanceOf;

    function mint(address owner, uint256 amount) external {
        balanceOf[owner] += amount;
    }

    function transfer(address, uint256) external pure returns (bool) {
        return false;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        balanceOf[from] -= amount;
        balanceOf[to] += amount - 1;
        return true;
    }
}
