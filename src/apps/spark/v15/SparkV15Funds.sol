// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {IERC20} from "../legacy/interfaces/IERC20.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {SparkV15PaymentHolds} from "./SparkV15PaymentHolds.sol";

interface ISparkV15MaterialProtection {
    function FUNDING_CASES() external view returns (address);
    function requireAfterOutflow(
        bytes32 obligationId,
        uint128 proposedAmount,
        uint256 balanceAfter,
        uint256 baseReservedAfter
    ) external view;
}

interface ISparkV15BookingCoverage {
    function FUNDS() external view returns (address);
    function requireBookingCoverage(bytes32 lessonId, bytes32 formId) external view returns (bool);
    function markPostedBookingCredit(
        bytes32 lessonId,
        bytes32 placeId,
        address customer,
        uint128 amount,
        address issuer
    ) external returns (bool);
}

interface ISparkV15PaymentBacking {
    function VERIFIER_ROLE() external view returns (bytes32);
    function paymentHoldBasis(bytes32 obligationId) external view returns (SparkV15PaymentHolds.HoldBasis memory);
}

/// @notice ERC-20 backing for one Spark installation's course credit, lessons and payment obligations.
contract SparkV15Funds {
    struct PaymentReserve {
        bytes32 lessonId;
        uint128 units;
        uint128 feeUnits;
    }

    struct RechargeTerms {
        address customer;
        uint128 amount;
        uint128 returnCap;
        uint64 returnThrough;
        bytes32 agreementRef;
    }

    struct RechargeOffer {
        RechargeTerms terms;
        uint256 packageId;
        address provider;
        bytes32 authorityId;
        uint256 receiptId;
    }

    struct RechargeReceipt {
        bytes32 offerId;
        bytes32 creditAccount;
        uint128 received;
        uint128 returned;
        uint128 unspentForReturn;
        uint64 receivedAt;
    }

    struct RechargeDebit {
        uint256 receiptId;
        uint128 amount;
    }

    struct CompensationDebit {
        bytes32 originalLessonId;
        bytes32 originalPlaceId;
        uint128 amount;
    }

    struct CompensationCredit {
        bytes32 account;
        uint128 remaining;
    }

    error InvalidFundsOperation();
    error InsufficientFunds();
    error TransferMismatch();
    error NotPayments();
    error InvalidRecharge();

    event LessonBudgetReserved(bytes32 indexed lessonId, uint256 addedUnits, uint256 heldUnits);
    event LessonBudgetReleased(bytes32 indexed lessonId, uint128 amount);
    event ServiceFeesTransferred(bytes32 indexed lessonId, address indexed recipient, uint128 amount);
    event LessonCreditCharged(bytes32 indexed lessonId, bytes32 indexed creditAccount, uint128 amount);
    event RechargeOffered(bytes32 indexed offerId, address indexed provider, address indexed customer);
    event RechargeReceived(uint256 indexed receiptId, bytes32 indexed offerId, bytes32 indexed account, uint128 amount);
    event RechargeReturned(uint256 indexed receiptId, bytes32 indexed account, uint128 amount);
    event CompensationCredited(
        bytes32 indexed lessonId, bytes32 indexed placeId, bytes32 indexed account, uint128 amount
    );
    event CompensationCreditCharged(
        bytes32 indexed lessonId, bytes32 indexed originalLessonId, bytes32 indexed placeId, uint128 amount
    );
    event CompensationCreditRevoked(bytes32 indexed lessonId, bytes32 indexed placeId, uint128 amount);
    event CompensationBackingApplied(bytes32 indexed lessonId, bytes32 indexed placeId, uint128 amount);
    event RechargeCreditCharged(
        bytes32 indexed lessonId, bytes32 indexed creditAccount, uint256 indexed receiptId, uint128 amount
    );

    bytes32 public constant ACTION_MANAGE_LESSON_FUNDS = keccak256("spark.action.manage-lesson-funds.v1.5");
    bytes32 public constant ACTION_OFFER_RECHARGE = keccak256("spark.action.offer-recharge.v1.5");
    bytes32 public constant ACTION_GRANT_COMPENSATION = keccak256("spark.action.grant-compensation.v1.5");
    bytes32 public constant ACTION_REPLENISH_PAYMENT_BACKING = keccak256("spark.action.replenish-payment-backing.v1.5");

    AVARequestAllocation public immutable REQUEST_ALLOCATION;
    IERC20 public immutable TOKEN;
    bytes32 public immutable WORKFLOW;
    address public immutable PAYMENTS;
    bytes32 public immutable BOOKING_ROLE;
    bytes32 public immutable CREDIT_PROVIDER_ROLE;
    bytes32 public immutable COMPENSATION_ROLE;
    address public materialProvisions;
    address public materialBookingCoverage;

    // Account credit, lesson-held backing and obligation-held backing are disjoint.
    uint256 public reservedUnits;
    mapping(bytes32 => uint256) public creditBalance;
    mapping(bytes32 => uint256) public lessonReserved;
    mapping(bytes32 => uint256) public lessonFeeBalance;
    mapping(bytes32 => PaymentReserve) private paymentReserves;
    mapping(bytes32 => RechargeOffer) private rechargeOffers;
    mapping(uint256 => RechargeReceipt) private rechargeReceipts;
    mapping(bytes32 => uint256) private rechargeCredit;
    mapping(bytes32 => mapping(bytes32 => CompensationCredit)) private compensationCredits;
    mapping(bytes32 => uint256) private compensationCreditByAccount;
    mapping(bytes32 => uint256) public remainingCompensationCreditByLesson;
    uint256 private nextRechargeReceipt = 1;
    bool private transferring;
    address public ordinaryBookingCoverage;

    constructor(AVARequestAllocation requests, IERC20 token, bytes32 workflow, address payments) {
        if (
            address(requests).code.length == 0 || address(token).code.length == 0 || workflow == bytes32(0)
                || payments == address(0)
        ) revert InvalidFundsOperation();
        REQUEST_ALLOCATION = requests;
        TOKEN = token;
        WORKFLOW = workflow;
        PAYMENTS = payments;
        BOOKING_ROLE = keccak256(abi.encode("spark.role.booking-funds.v1.5", workflow, address(this)));
        CREDIT_PROVIDER_ROLE = keccak256(abi.encode("spark.role.credit-provider.v1.5", workflow, address(this)));
        COMPENSATION_ROLE = keccak256(abi.encode("spark.role.compensation-credit.v1.5", workflow, address(this)));
    }

    modifier onlyPayments() {
        if (msg.sender != PAYMENTS) revert NotPayments();
        _;
    }

    modifier onlyBooking() {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(msg.sender, SparkV15.APP_ID, BOOKING_ROLE, ACTION_MANAGE_LESSON_FUNDS);
        _;
    }

    modifier noTransferInProgress() {
        if (transferring) revert InvalidFundsOperation();
        _;
    }

    modifier tokenTransfer() {
        if (transferring) revert InvalidFundsOperation();
        transferring = true;
        _;
        transferring = false;
    }

    function paymentReserved(bytes32 obligationId) external view returns (uint128) {
        return paymentReserves[obligationId].units;
    }

    function creditAccount(address customer) public view returns (bytes32) {
        return keccak256(abi.encode("spark.account.course-credit.v1.5", block.chainid, address(this), customer));
    }

    function bindMaterialProvisions(address provisions) external {
        _bindMaterialProvisions(provisions, false);
    }

    /// @notice Install material protection and the prerequisite for new material bookings together.
    function bindMaterialProvisionsWithBookingCoverage(address provisions) external {
        _bindMaterialProvisions(provisions, true);
    }

    /// @notice Bind the ordinary-course inventory used to reclassify already backed compensation.
    function bindOrdinaryBookingCoverage(address coverage) external {
        REQUEST_ALLOCATION.IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
        if (
            ordinaryBookingCoverage != address(0) || materialProvisions != address(0) || coverage.code.length == 0
                || ISparkV15BookingCoverage(coverage).FUNDS() != address(this)
        ) revert InvalidFundsOperation();
        ordinaryBookingCoverage = coverage;
    }

    function _bindMaterialProvisions(address provisions, bool requireInventory) private {
        REQUEST_ALLOCATION.IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
        if (materialProvisions != address(0) || provisions.code.length == 0) revert InvalidFundsOperation();
        if (requireInventory) {
            address coverage = ISparkV15MaterialProtection(provisions).FUNDING_CASES();
            if (coverage.code.length == 0) revert InvalidFundsOperation();
            materialBookingCoverage = coverage;
        }
        materialProvisions = provisions;
    }

    function requireCommitmentFunding(bytes32 lessonId, bytes32 formId) external view {
        address coverage = materialBookingCoverage;
        if (coverage != address(0) && ISparkV15BookingCoverage(coverage).requireBookingCoverage(lessonId, formId)) {
            _requireMaterialProtection(bytes32(0), 0, _requireBacking(reservedUnits));
        }
    }

    function grantCompensationCredit(bytes32 lessonId, bytes32 placeId, address customer, uint128 amount)
        external
        noTransferInProgress
    {
        _requireCompensationAuthority();
        if (
            lessonId == bytes32(0) || placeId == bytes32(0) || customer == address(0) || amount == 0
                || compensationCredits[lessonId][placeId].account != bytes32(0)
        ) revert InvalidFundsOperation();
        bytes32 account = creditAccount(customer);
        compensationCredits[lessonId][placeId] = CompensationCredit(account, amount);
        compensationCreditByAccount[account] += amount;
        remainingCompensationCreditByLesson[lessonId] += amount;
        creditBalance[account] += amount;
        address coverage = materialBookingCoverage;
        if (coverage == address(0)) coverage = ordinaryBookingCoverage;
        if (
            coverage != address(0)
                && ISparkV15BookingCoverage(coverage)
                    .markPostedBookingCredit(lessonId, placeId, customer, amount, msg.sender)
        ) {
            lessonReserved[lessonId] -= amount;
            emit CompensationBackingApplied(lessonId, placeId, amount);
        } else {
            reservedUnits += amount;
        }
        _requireMaterialProtection(bytes32(0), 0, _requireBacking(reservedUnits));
        emit CompensationCredited(lessonId, placeId, account, amount);
    }

    function compensationCreditRemaining(bytes32 lessonId, bytes32 placeId) external view returns (uint128) {
        return compensationCredits[lessonId][placeId].remaining;
    }

    function revokeUnspentCompensation(bytes32 lessonId, bytes32 placeId, uint128 amount)
        external
        noTransferInProgress
    {
        _requireCompensationAuthority();
        CompensationCredit storage credit = compensationCredits[lessonId][placeId];
        if (amount == 0 || amount > credit.remaining) revert InvalidFundsOperation();
        _consumeCompensation(lessonId, credit, amount);
        creditBalance[credit.account] -= amount;
        reservedUnits -= amount;
        emit CompensationCreditRevoked(lessonId, placeId, amount);
    }

    function _requireCompensationAuthority() private view {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                msg.sender, SparkV15.APP_ID, COMPENSATION_ROLE, ACTION_GRANT_COMPENSATION
            );
    }

    function _consumeCompensation(bytes32 originalLessonId, CompensationCredit storage credit, uint128 amount) private {
        credit.remaining -= amount;
        compensationCreditByAccount[credit.account] -= amount;
        remainingCompensationCreditByLesson[originalLessonId] -= amount;
    }

    function releaseLessonBudget(bytes32 lessonId, uint128 amount) external noTransferInProgress {
        if (
            msg.sender != materialProvisions || amount == 0
                || amount > lessonReserved[lessonId] - lessonFeeBalance[lessonId]
        ) revert InvalidFundsOperation();
        lessonReserved[lessonId] -= amount;
        reservedUnits -= amount;
        emit LessonBudgetReleased(lessonId, amount);
    }

    function transferLessonFeesToServiceReserve(bytes32 lessonId, address recipient, uint128 amount)
        external
        tokenTransfer
    {
        if (
            msg.sender != materialProvisions || recipient == address(0) || recipient == address(this) || amount == 0
                || amount > lessonFeeBalance[lessonId]
        ) revert InvalidFundsOperation();
        uint256 beforeVault = _requireBacking(reservedUnits);
        lessonFeeBalance[lessonId] -= amount;
        lessonReserved[lessonId] -= amount;
        reservedUnits -= amount;
        _pushExact(bytes32(0), recipient, amount, beforeVault);
        emit ServiceFeesTransferred(lessonId, recipient, amount);
    }

    function getRechargeOffer(bytes32 offerId) external view returns (RechargeOffer memory) {
        return rechargeOffers[offerId];
    }

    function getRechargeReceipt(uint256 receiptId) external view returns (RechargeReceipt memory) {
        return rechargeReceipts[receiptId];
    }

    /// @notice Record the provider's terms for a particular recharge.
    function offerRecharge(RechargeTerms calldata terms, bytes32 authorityId)
        external
        noTransferInProgress
        returns (bytes32 offerId)
    {
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, CREDIT_PROVIDER_ROLE, ACTION_OFFER_RECHARGE, authorityId
            );
        if (
            terms.customer == address(0) || terms.customer == address(this) || terms.amount == 0
                || terms.returnCap > terms.amount || terms.agreementRef == bytes32(0)
                || (terms.returnCap == 0 ? terms.returnThrough != 0 : terms.returnThrough < block.timestamp)
        ) revert InvalidRecharge();
        uint256 packageId = REQUEST_ALLOCATION.RULE_PACKAGE_REGISTRY().getActivePackageId(SparkV15.APP_ID, WORKFLOW);
        offerId = keccak256(abi.encode(address(this), packageId, msg.sender, authorityId, terms));
        if (rechargeOffers[offerId].provider != address(0)) revert InvalidRecharge();
        rechargeOffers[offerId] = RechargeOffer(terms, packageId, msg.sender, authorityId, 0);
        emit RechargeOffered(offerId, msg.sender, terms.customer);
    }

    /// @notice Accept the provider's terms and post only tokens actually received.
    function recharge(bytes32 offerId) external tokenTransfer returns (uint256 receiptId) {
        RechargeOffer storage offer = rechargeOffers[offerId];
        RechargeTerms storage terms = offer.terms;
        if (terms.customer != msg.sender || offer.receiptId != 0) revert InvalidRecharge();
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                offer.provider, SparkV15.APP_ID, CREDIT_PROVIDER_ROLE, ACTION_OFFER_RECHARGE, offer.authorityId
            );
        uint256 beforeVault = _requireBacking(reservedUnits);
        _pullExact(msg.sender, terms.amount, beforeVault);
        receiptId = nextRechargeReceipt++;
        offer.receiptId = receiptId;
        bytes32 account = creditAccount(msg.sender);
        uint128 unspentForReturn = terms.returnCap == 0 ? 0 : terms.amount;
        rechargeReceipts[receiptId] =
            RechargeReceipt(offerId, account, terms.amount, 0, unspentForReturn, uint64(block.timestamp));
        creditBalance[account] += terms.amount;
        reservedUnits += terms.amount;
        rechargeCredit[account] += unspentForReturn;
        emit RechargeReceived(receiptId, offerId, account, terms.amount);
    }

    /// @notice Return unused units of the original recharge under the agreed cap and deadline.
    function returnRecharge(uint256 receiptId, uint128 amount) external tokenTransfer {
        RechargeReceipt storage receipt = rechargeReceipts[receiptId];
        RechargeTerms storage terms = rechargeOffers[receipt.offerId].terms;
        if (
            terms.customer != msg.sender || amount == 0 || amount > receipt.unspentForReturn
                || amount > terms.returnCap - receipt.returned || block.timestamp > terms.returnThrough
        ) revert InvalidRecharge();
        uint256 beforeVault = _requireBacking(reservedUnits);
        bytes32 account = receipt.creditAccount;
        receipt.returned += amount;
        receipt.unspentForReturn -= amount;
        rechargeCredit[account] -= amount;
        creditBalance[account] -= amount;
        reservedUnits -= amount;
        _pushExact(bytes32(0), msg.sender, amount, beforeVault);
        emit RechargeReturned(receiptId, account, amount);
    }

    /// @notice Hold at least the required backing for this lesson.
    function reserveLessonBudget(bytes32 lessonId, uint128 requiredUnits) external onlyBooking noTransferInProgress {
        if (lessonId == bytes32(0)) revert InvalidFundsOperation();
        uint256 held = lessonReserved[lessonId];
        uint256 added = requiredUnits > held ? requiredUnits - held : 0;
        uint256 total = reservedUnits + added;
        uint256 balance = _requireBacking(total);
        if (added != 0) {
            reservedUnits = total;
            lessonReserved[lessonId] = requiredUnits;
            _requireMaterialProtection(bytes32(0), 0, balance);
            emit LessonBudgetReserved(lessonId, added, requiredUnits);
        }
    }

    /// @notice Charge course credit for which the booking names no original recharge.
    function chargeLesson(bytes32 lessonId, bytes32 account, uint128 amount) external onlyBooking noTransferInProgress {
        _chargeLesson(lessonId, account, amount, 0);
    }

    /// @notice Charge the agreed recharge receipts and cover the balance from other course credit.
    function chargeLessonFrom(bytes32 lessonId, bytes32 account, uint128 amount, RechargeDebit[] calldata debits)
        external
        onlyBooking
        noTransferInProgress
    {
        _chargeLesson(lessonId, account, amount, _chargeRecharges(lessonId, account, debits));
    }

    function chargeLessonFromCredits(
        bytes32 lessonId,
        bytes32 account,
        uint128 amount,
        RechargeDebit[] calldata recharges,
        CompensationDebit[] calldata compensation
    ) external onlyBooking noTransferInProgress {
        uint256 named = _chargeRecharges(lessonId, account, recharges);
        for (uint256 i; i < compensation.length; ++i) {
            CompensationDebit calldata debit = compensation[i];
            CompensationCredit storage credit = compensationCredits[debit.originalLessonId][debit.originalPlaceId];
            if (credit.account != account || debit.amount == 0 || debit.amount > credit.remaining) {
                revert InvalidFundsOperation();
            }
            _consumeCompensation(debit.originalLessonId, credit, debit.amount);
            named += debit.amount;
            emit CompensationCreditCharged(lessonId, debit.originalLessonId, debit.originalPlaceId, debit.amount);
        }
        _chargeLesson(lessonId, account, amount, named);
    }

    function _chargeRecharges(bytes32 lessonId, bytes32 account, RechargeDebit[] calldata debits)
        private
        returns (uint256 amount)
    {
        for (uint256 i; i < debits.length; ++i) {
            RechargeDebit calldata debit = debits[i];
            RechargeReceipt storage receipt = rechargeReceipts[debit.receiptId];
            if (receipt.creditAccount != account || debit.amount == 0 || debit.amount > receipt.unspentForReturn) {
                revert InvalidRecharge();
            }
            receipt.unspentForReturn -= debit.amount;
            rechargeCredit[account] -= debit.amount;
            amount += debit.amount;
            emit RechargeCreditCharged(lessonId, account, debit.receiptId, debit.amount);
        }
    }

    /// @notice Hold an independent obligation, using its lesson's funds before unencumbered funds.
    function reservePayment(bytes32 obligationId, bytes32 lessonId, uint128 amount)
        external
        onlyPayments
        noTransferInProgress
    {
        if (
            obligationId == bytes32(0) || lessonId == bytes32(0) || amount == 0
                || paymentReserves[obligationId].lessonId != bytes32(0)
        ) revert InvalidFundsOperation();
        uint256 held = lessonReserved[lessonId];
        uint256 fromLesson = held < amount ? held : amount;
        uint256 total = reservedUnits + amount - fromLesson;
        uint256 balance = _requireBacking(total);
        lessonReserved[lessonId] = held - fromLesson;
        paymentReserves[obligationId] = PaymentReserve(lessonId, amount, _takeLessonFees(lessonId, fromLesson));
        reservedUnits = total;
        _requireMaterialProtection(obligationId, 0, balance);
    }

    function disbursePayment(bytes32 obligationId, address recipient, bytes32 creditAccountId, uint128 amount)
        external
        onlyPayments
        tokenTransfer
    {
        if (recipient == address(0) || recipient == address(this) || amount == 0) {
            revert InvalidFundsOperation();
        }
        PaymentReserve storage payment = paymentReserves[obligationId];
        if (payment.units < amount) revert InsufficientFunds();
        uint256 beforeVault = _requireBacking(reservedUnits);
        payment.units -= amount;
        payment.feeUnits -= payment.feeUnits < amount ? payment.feeUnits : amount;
        if (creditAccountId == bytes32(0)) {
            reservedUnits -= amount;
            _pushExact(obligationId, recipient, amount, beforeVault);
        } else {
            creditBalance[creditAccountId] += amount;
        }
    }

    function releasePaymentBacking(bytes32 obligationId, uint128 amount) external onlyPayments noTransferInProgress {
        PaymentReserve storage payment = paymentReserves[obligationId];
        uint128 released = payment.units < amount ? payment.units : amount;
        uint128 returnedFees = payment.feeUnits < released ? payment.feeUnits : released;
        payment.units -= released;
        payment.feeUnits -= returnedFees;
        lessonReserved[payment.lessonId] += returnedFees;
        lessonFeeBalance[payment.lessonId] += returnedFees;
        reservedUnits -= released - returnedFees;
    }

    function replenishPaymentBacking(bytes32 obligationId, uint128 amount, bytes32 authorityId)
        external
        noTransferInProgress
    {
        ISparkV15PaymentBacking host = ISparkV15PaymentBacking(PAYMENTS);
        REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, host.VERIFIER_ROLE(), ACTION_REPLENISH_PAYMENT_BACKING, authorityId
            );
        _addPaymentBacking(host, obligationId, amount);
    }

    function reserveAdditionalMaterialBacking(bytes32 obligationId, uint128 amount) external noTransferInProgress {
        if (msg.sender != materialProvisions) revert InvalidFundsOperation();
        _addPaymentBacking(ISparkV15PaymentBacking(PAYMENTS), obligationId, amount);
    }

    function _addPaymentBacking(ISparkV15PaymentBacking host, bytes32 obligationId, uint128 amount) private {
        PaymentReserve storage payment = paymentReserves[obligationId];
        if (
            payment.lessonId == bytes32(0) || amount == 0
                || uint256(payment.units) + amount > host.paymentHoldBasis(obligationId).outstanding
        ) {
            revert InvalidFundsOperation();
        }
        uint256 held = lessonReserved[payment.lessonId];
        uint256 fromLesson = held < amount ? held : amount;
        uint256 total = reservedUnits + amount - fromLesson;
        uint256 balance = _requireBacking(total);
        lessonReserved[payment.lessonId] = held - fromLesson;
        payment.units += amount;
        payment.feeUnits += _takeLessonFees(payment.lessonId, fromLesson);
        reservedUnits = total;
        _requireMaterialProtection(obligationId, 0, balance);
    }

    function takePaymentReturn(bytes32 obligationId, address returningActor, bytes32 creditAccountId, uint128 amount)
        external
        onlyPayments
        tokenTransfer
    {
        PaymentReserve storage payment = paymentReserves[obligationId];
        if (
            payment.lessonId == bytes32(0) || returningActor == address(0) || returningActor == address(this)
                || amount == 0
        ) revert InvalidFundsOperation();
        uint256 beforeVault = _requireBacking(reservedUnits);
        payment.units += amount;
        if (creditAccountId == bytes32(0)) {
            reservedUnits += amount;
            _pullExact(returningActor, amount, beforeVault);
        } else {
            _debitCredit(creditAccountId, amount);
        }
    }

    function _chargeLesson(bytes32 lessonId, bytes32 account, uint128 amount, uint256 named) private {
        if (lessonId == bytes32(0) || account == bytes32(0) || amount == 0 || named > amount) {
            revert InvalidFundsOperation();
        }
        _requireBacking(reservedUnits);
        _debitCredit(account, amount);
        lessonReserved[lessonId] += amount;
        lessonFeeBalance[lessonId] += amount;
        emit LessonCreditCharged(lessonId, account, amount);
    }

    function _takeLessonFees(bytes32 lessonId, uint256 fromLesson) private returns (uint128) {
        uint256 available = lessonFeeBalance[lessonId];
        uint128 used = uint128(available < fromLesson ? available : fromLesson);
        lessonFeeBalance[lessonId] -= used;
        return used;
    }

    function _debitCredit(bytes32 account, uint128 amount) private {
        uint256 credit = creditBalance[account];
        if (credit - rechargeCredit[account] - compensationCreditByAccount[account] < amount) {
            revert InsufficientFunds();
        }
        creditBalance[account] = credit - amount;
    }

    function _requireBacking(uint256 required) private view returns (uint256 balance) {
        balance = TOKEN.balanceOf(address(this));
        if (balance < required) revert InsufficientFunds();
    }

    function _requireMaterialProtection(bytes32 obligationId, uint128 amount, uint256 balanceAfter) private view {
        address provisions = materialProvisions;
        if (provisions != address(0)) {
            ISparkV15MaterialProtection(provisions)
                .requireAfterOutflow(obligationId, amount, balanceAfter, reservedUnits);
        }
    }

    function _pushExact(bytes32 obligationId, address recipient, uint128 amount, uint256 beforeVault) private {
        _requireMaterialProtection(obligationId, amount, beforeVault - amount);
        uint256 beforeRecipient = TOKEN.balanceOf(recipient);
        if (
            !TOKEN.transfer(recipient, amount) || TOKEN.balanceOf(recipient) != beforeRecipient + amount
                || TOKEN.balanceOf(address(this)) != beforeVault - amount
        ) revert TransferMismatch();
    }

    function _pullExact(address from, uint128 amount, uint256 beforeVault) private {
        uint256 beforeSender = TOKEN.balanceOf(from);
        if (
            beforeSender < amount || !TOKEN.transferFrom(from, address(this), amount)
                || TOKEN.balanceOf(address(this)) != beforeVault + amount
                || TOKEN.balanceOf(from) != beforeSender - amount
        ) revert TransferMismatch();
    }
}
