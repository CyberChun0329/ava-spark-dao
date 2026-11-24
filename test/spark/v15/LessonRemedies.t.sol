// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {SparkV15} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {ISparkV15BookingChanges, SparkV15Booking} from "../../../src/apps/spark/v15/SparkV15Booking.sol";
import {SparkV15ServiceReports} from "../../../src/apps/spark/v15/SparkV15ServiceReports.sol";
import {ISparkV15RemedyBooking, SparkV15BookingChanges} from "../../../src/apps/spark/v15/SparkV15BookingChanges.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15Settlement, ISparkV15SettlementRemedies} from "../../../src/apps/spark/v15/SparkV15Settlement.sol";
import {
    SparkV15SettlementAlternatives,
    ISparkV15SettlementActors
} from "../../../src/apps/spark/v15/SparkV15SettlementAlternatives.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {
    SparkV15LessonRemedies,
    SparkV15CustomerRedress,
    SparkV15TutorDebt,
    SparkV15RemedyBookings
} from "../../../src/apps/spark/v15/SparkV15LessonRemedies.sol";
import {
    SparkV15ReviewCases,
    SparkV15ConcernIntake,
    SparkV15ReviewContext,
    SparkV15ReviewActions
} from "../../../src/apps/spark/v15/SparkV15ReviewCases.sol";
import {BookingSignatureVm, SparkV15BookingFixture} from "./Booking.t.sol";

contract LessonRemediesTest is SparkV15BookingFixture {
    address private constant INITIAL_DECIDER = address(0x7401);
    address private constant REVIEWER = address(0x7402);
    address private constant SETTLEMENT_EVIDENCE_ACTOR = address(0x7403);
    bytes32 private constant CONCERN = keccak256("student's evidenced teaching concern");

    SparkV15ReviewCases private cases;
    SparkV15LessonRemedies private remedies;
    SparkV15CustomerRedress private redress;
    SparkV15TutorDebt private tutorDebt;
    SparkV15BookingChanges private changes;
    SparkV15RemedyBookings private remedyBookings;

    struct RefundRevisionFixture {
        bytes32 formId;
        bytes32 faultCaseId;
        bytes32 ordinary;
        bytes32 additional;
        uint64 paidAt;
        uint256 ordinaryApproval;
        uint256 additionalApproval;
        uint256 ordinaryReceipt;
        uint256 additionalReceipt;
    }

    function setUp() public override {
        super.setUp();
        payments.bindHolds(
            new SparkV15PaymentHolds(address(payments), requestAllocation, REQUEST_WORKFLOW, ROLE_VERIFIER)
        );
        cases = new SparkV15ReviewCases(payments, ROLE_SOURCE);
        cases.bindIntake(new SparkV15ConcernIntake(payments, ROLE_SOURCE, cases));
        remedies = new SparkV15LessonRemedies(booking, payments, cases, ROLE_SOURCE);
        redress = new SparkV15CustomerRedress(remedies, ROLE_SOURCE);
        tutorDebt = new SparkV15TutorDebt(remedies, redress, ROLE_SOURCE);
        remedies.bindCustomerRedress(redress);
        remedyBookings = new SparkV15RemedyBookings(redress, ROLE_SOURCE);
        redress.bindRemedyBookings(remedyBookings);
        changes = new SparkV15BookingChanges(booking, payments);
        booking.bindBookingChanges(ISparkV15BookingChanges(address(changes)));
        changes.bindRemedyBooking(ISparkV15RemedyBooking(address(remedyBookings)));
        require(address(remedies).code.length <= 24_576, "fault and tutor-pay module must fit EIP-170");
        require(address(redress).code.length <= 24_576, "redress module must fit EIP-170");
        require(address(remedyBookings).code.length <= 24_576, "remedy bookings module must fit EIP-170");
        require(address(tutorDebt).code.length <= 24_576, "tutor debt module must fit EIP-170");
        _grant(PROVIDER, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS);
        _grant(INITIAL_DECIDER, SparkV15ReviewActions.ACTION_DECIDE_INITIAL);
        _grant(VERIFIER_ACTOR, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL);
        bytes32 role = funds.COMPENSATION_ROLE();
        identityRegistry.assignSubject(address(redress), SparkV15.APP_ID, role, _authority(role), "test:remedy credit");
        authorityMatrix.setPermission(SparkV15.APP_ID, role, funds.ACTION_GRANT_COMPENSATION(), true);
    }

    function testOriginalTutorFaultMakesWagesZeroBeforeAnyCustomerChoice() public {
        bytes32 formId = _bookOneToOne();
        (bytes32 caseId, SparkV15LessonRemedies.FaultFinding memory finding) = _tutorFault(formId);

        require(remedies.allowsTutorWage(LESSON, TUTOR), "no retained decision yet");
        remedies.recordFault(caseId, finding);
        SparkV15LessonRemedies.FaultRecord memory record = remedies.getFault(caseId, 1);
        require(record.originalNormalTutorPay == 8 && record.originalDeduction == 8, "original wage basis");
        require(record.originalTutorPay == 0 && !remedies.allowsTutorWage(LESSON, TUTOR), "original wage zero");
        (, uint128 customerFee) = remedies.faultFee(formId);
        require(customerFee == 0, "verified zero teaching requires fee waiver");
        require(remedies.allowsTutorWage(LESSON, OTHER_STUDENT), "no effect on a different tutor");
    }

    function testUndisputedProviderFaultAllowsCustomerRedressAndKeepsTutorPayIndependent() public {
        bytes32 formId = _bookOneToOne();
        _publishRedressTerms(formId);
        requestVm.warp(LESSON_END + 1);
        SparkV15LessonRemedies.FaultFinding memory finding;
        finding.kind = SparkV15LessonRemedies.FaultKind.ProviderNoticeError;
        finding.groundRef = keccak256("provider notified the wrong address and missed the agreed service");
        finding.affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        finding.affected[0] = SparkV15LessonRemedies.AffectedPlace(
            formId,
            SparkV15LessonRemedies.TeachingReceived.NoneDelivered,
            SparkV15LessonRemedies.Participation.DidNotAttendOrPrepare,
            8,
            true,
            keccak256("verified notice failure and known affected student")
        );
        bytes32 noDispute = keccak256("independently checked the applicable evidentiary record for an open dispute");
        bytes32 matter = keccak256("undisputed provider error: verified facts");
        uint256 evidence = _evidence(remedies.providerFaultCommitment(formId, matter, finding, noDispute, SOURCE_ACTOR));
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_SOURCE, remedies.ACTION_RECORD_UNDISPUTED_PROVIDER_FAULT(), true
        );
        requestVm.prank(SOURCE_ACTOR);
        bytes32 caseId = remedies.recordUndisputedProviderFault(formId, matter, finding, noDispute, evidence);
        requestVm.prank(CUSTOMER);
        redress.acceptStandardCompensation(formId);
        require(redress.getRedress(formId).caseId == caseId, "provider error supported customer compensation");
        require(remedies.allowsTutorWage(LESSON, TUTOR), "provider error leaves the tutor's separate wages eligible");
    }

    function testAdoptedFaultCorrectionReopensFutureWagesAndKeepsTheActualCompensationHistory() public {
        bytes32 formId = _bookOneToOne();
        _publishRedressTerms(formId);
        (bytes32 caseId, SparkV15LessonRemedies.FaultFinding memory finding) = _tutorFault(formId);
        remedies.recordFault(caseId, finding);
        requestVm.prank(CUSTOMER);
        redress.acceptStandardCompensation(formId);
        _provideProviderFunds(8);
        redress.issueCourseCredit(formId);

        finding.kind = SparkV15LessonRemedies.FaultKind.NoFault;
        finding.groundRef = keccak256("independent review overturned the original tutor fault");
        bytes32 outcome = remedies.faultOutcome(caseId, finding);
        requestVm.expectRevert(SparkV15LessonRemedies.InvalidFault.selector);
        remedies.recordFault(caseId, finding);
        _adoptFaultCorrection(caseId, outcome);
        remedies.recordFault(caseId, finding);
        require(remedies.allowsTutorWage(LESSON, TUTOR), "current original wage can use a new lawful assessment");
        require(remedies.getFault(caseId, 1).originalDeduction == 8, "original wage decision remains in history");
        require(remedies.getFault(caseId, 2).outcome == outcome, "retained adopted successor");
        require(
            redress.getRedress(formId).creditIssuedAt != 0 && funds.creditBalance(funds.creditAccount(CUSTOMER)) == 8,
            "previous actual compensation remains a native receipt"
        );
    }

    function testStandardCompensationUsesTheOriginalFeeAndRequiresRealUsableCredit() public {
        bytes32 formId = _bookOneToOne();
        _publishRedressTerms(formId);
        (bytes32 caseId, SparkV15LessonRemedies.FaultFinding memory finding) = _tutorFault(formId);
        remedies.recordFault(caseId, finding);
        requestVm.prank(PAYER);
        requestVm.expectRevert(SparkV15CustomerRedress.InvalidCustomerChoice.selector);
        redress.acceptStandardCompensation(formId);

        requestVm.warp(LESSON_END + 2);
        requestVm.prank(CUSTOMER);
        redress.acceptStandardCompensation(formId);
        bytes32 customerAccount = funds.creditAccount(CUSTOMER);
        require(funds.creditBalance(customerAccount) == 0, "acceptance did not post actual credit");
        requestVm.expectRevert();
        redress.issueCourseCredit(formId);
        require(redress.getRedress(formId).creditIssuedAt == 0, "unfunded posting must not be reported");

        _provideProviderFunds(8);
        redress.issueCourseCredit(formId);
        SparkV15CustomerRedress.RedressRecord memory remedy = redress.getRedress(formId);
        require(remedy.acceptedBy == CUSTOMER && remedy.acceptedAt == LESSON_END + 2, "original customer choice");
        require(remedy.creditIssuedAt == LESSON_END + 2, "real availability time");
        require(funds.creditBalance(customerAccount) == 8, "full original normal fee credited and usable");
        require(funds.creditBalance(funds.creditAccount(PAYER)) == 0, "no compensation to the designated payer");
        requestVm.expectRevert(SparkV15CustomerRedress.InvalidCustomerChoice.selector);
        redress.issueCourseCredit(formId);
    }

    function testLaterDiscountIsUsableForTheChosenCourseAndBookingConsumesItOnlyAfterRealDebit() public {
        bytes32 originalForm = _bookOneToOne();
        _publishRedressTerms(originalForm);
        (bytes32 caseId, SparkV15LessonRemedies.FaultFinding memory finding) = _tutorFault(originalForm);
        remedies.recordFault(caseId, finding);
        requestVm.prank(CUSTOMER);
        redress.acceptStandardCompensation(originalForm);
        requestVm.prank(PROVIDER);
        bytes32 offer = remedyBookings.makeDiscountUsable(originalForm);
        require(remedyBookings.getDiscount(offer).fixedAmount == 4, "half the original fee");

        bytes32 differentLesson = keccak256("separate course taught by a different tutor");
        bytes32 selected =
            _prepareAnotherLesson(_anotherLessonTerms(differentLesson, OTHER_STUDENT, LESSON_END + 3 days), 4, offer);
        uint256 proof = _evidence(remedyBookings.discountSelectionCommitment(offer, selected, 8, bytes32(0), CUSTOMER));
        requestVm.prank(CUSTOMER);
        remedyBookings.selectDiscountCourse(offer, selected, 8, bytes32(0), proof);
        requestVm.expectRevert();
        _confirmOrdinary(selected, bytes32(0), 0);
        require(remedyBookings.getDiscount(offer).usedAt == 0, "failed debit rolls back discount consumption");

        _recharge(CUSTOMER, 4, 0);
        _confirmOrdinary(selected, bytes32(0), 0);
        SparkV15RemedyBookings.Discount memory used = remedyBookings.getDiscount(offer);
        require(used.usedFormId == selected && used.applied == 4 && used.unapplied == 0, "recorded real deduction");
        require(booking.getForm(selected).confirmation.debitedUnits == 4, "actual reduced debit on the selected course");
    }

    function testExtendingAnAcceptedRemedyRequiresSeparateTimelyCustomerConsent() public {
        bytes32 formId = _bookOneToOne();
        _publishRedressTerms(formId);
        (bytes32 caseId, SparkV15LessonRemedies.FaultFinding memory finding) = _tutorFault(formId);
        remedies.recordFault(caseId, finding);
        requestVm.prank(CUSTOMER);
        redress.acceptStandardCompensation(formId);
        uint64 oldDeadline = LESSON_END + 14 days;
        uint64 newDeadline = LESSON_END + 16 days;
        bytes32 source = keccak256("specific delivery deadline separately agreed before expiry");
        bytes32 extension = remedyBookings.extensionCommitment(formId, oldDeadline, newDeadline, source);
        uint256 proof = _evidence(extension);
        requestVm.prank(PROVIDER);
        remedyBookings.proposeExtension(formId, newDeadline, source, proof);
        require(redress.deliveryDeadline(formId) == oldDeadline, "provider proposal did not move the clock");
        requestVm.prank(PAYER);
        requestVm.expectRevert(SparkV15RemedyBookings.InvalidCustomerChoice.selector);
        remedyBookings.acceptExtension(extension);
        requestVm.prank(CUSTOMER);
        remedyBookings.acceptExtension(extension);
        require(redress.deliveryDeadline(formId) == newDeadline, "both affected parties consented to the new deadline");
    }

    function testRemedialTeachingUsesTheDatedBookingAndLeavesTheOriginalRefundOwed() public {
        _assertRemedialTeaching(false, false);
    }

    function testRemedialTeachingUsesAdoptedServiceFeedbackBeforeSettlement() public {
        _assertRemedialTeaching(true, false);
    }

    function testRemedialDeliveryCanUseTimelyNoticeVerifiedAfterStart() public {
        _assertRemedialTeaching(false, true);
    }

    function _assertRemedialTeaching(bool adoptFeedback, bool verifyNoticeAfterStart) private {
        bytes32 original = _bookOneToOne();
        _publishRedressTerms(original);
        (bytes32 caseId, SparkV15LessonRemedies.FaultFinding memory finding) = _tutorFault(original);
        remedies.recordFault(caseId, finding);
        bytes32 remedyLessonId = keccak256("dated remedial teaching with a new tutor");
        SparkV15Booking.LessonTerms memory terms =
            _anotherLessonTerms(remedyLessonId, OTHER_STUDENT, LESSON_END + 3 days);
        bytes32 selected = _configureAnotherLesson(terms, 8, bytes32(0));
        uint64 contactedAt = uint64(block.timestamp);
        bytes32 contact = keccak256("contact and actual proposed replacement lesson time");
        bytes32 link = changes.separateBookingCommitment(original, selected, contactedAt, contact);
        uint256 contactProof = _evidence(link);
        requestVm.prank(SOURCE_ACTOR);
        changes.proposeSeparateBooking(original, selected, contactedAt, contact, contactProof);
        requestVm.prank(PAYER);
        changes.acceptSeparateBooking(link);
        _acceptOtherLessonForm(selected, terms.tutor);
        _rechargeNextLesson(remedyLessonId, 8);
        _confirmOrdinary(selected, bytes32(0), 0);
        requestVm.warp(block.timestamp + 1);
        uint64 sentAt = uint64(block.timestamp);
        bytes32 notice = keccak256("the academic team notified the student of the specific remedial time");
        uint256 noticeProof = _evidence(changes.separateNoticeCommitment(link, sentAt, notice));
        requestVm.prank(SOURCE_ACTOR);
        changes.linkSeparateBooking(link, sentAt, notice, noticeProof);
        requestVm.prank(CUSTOMER);
        remedyBookings.acceptRemedialTeaching(original, link);
        requestVm.expectRevert(SparkV15CustomerRedress.InvalidCustomerChoice.selector);
        remedyBookings.recordRemedialDelivery(original);
        _teachConfirmedLesson(selected, terms, verifyNoticeAfterStart);
        bytes32 services = keccak256("student confirmed the agreed remedial teaching in full");
        if (adoptFeedback) {
            _recordAdoptedRemedyFeedback(selected, services);
        } else {
            SparkV15Booking.ServiceStatus status = SparkV15Booking.ServiceStatus.FullyDelivered;
            uint256 serviceProof = _evidence(booking.serviceFeedbackCommitment(selected, status, services, bytes32(0)));
            requestVm.prank(STUDENT);
            booking.recordServiceFeedback(selected, status, services, bytes32(0), serviceProof);
        }
        remedyBookings.recordRemedialDelivery(original);
        require(redress.getRedress(original).remedialDeliveryAt == terms.endsAt, "verified actual teaching delivery");
        (, bool complete) = redress.lessonRedressDelivered(LESSON);
        require(!complete, "the original full debit still needs actual restoration");
        if (adoptFeedback) {
            SparkV15ServiceReports reports = booking.OPENING().SERVICE_REPORTS();
            requestVm.prank(SOURCE_ACTOR);
            reports.recordFeedbackEvidenceLifecycle(
                selected,
                ROLE_SOURCE,
                _authority(ROLE_SOURCE),
                AVACoreTypes.EvidenceLifecycleKind.Revoke,
                0,
                keccak256("post-delivery evidence revocation")
            );
            requestVm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
            remedyBookings.remedialTeachingDeliveredAt(original, link);
            require(redress.getRedress(original).remedialDeliveryAt == terms.endsAt, "past delivery rewritten");
        }
    }

    function _recordAdoptedRemedyFeedback(bytes32 formId, bytes32 receivedRef) private {
        uint256 signingKey = 0x74123;
        BookingSignatureVm signatures = BookingSignatureVm(address(requestVm));
        address signingSource = signatures.addr(signingKey);
        bytes32 subject = keccak256("independent remedial teaching source");
        identityRegistry.assignSubject(signingSource, SparkV15.APP_ID, ROLE_SOURCE, subject, "test:remedy report");
        SparkV15ServiceReports.SourceProof memory proof = SparkV15ServiceReports.SourceProof(
            ROLE_SOURCE, subject, requestPolicyId, uint64(block.timestamp + 1 minutes), bytes32(0), bytes32(0)
        );
        SparkV15ServiceReports reports = booking.OPENING().SERVICE_REPORTS();
        (uint8 v, bytes32 r, bytes32 s) =
            signatures.sign(signingKey, reports.fullServiceFeedbackDigest(formId, receivedRef, proof));
        proof.r = r;
        proof.vs = bytes32(uint256(s) | ((uint256(v) - 27) << 255));
        requestVm.prank(STUDENT);
        reports.recordFullServiceFeedback(formId, receivedRef, proof);
    }

    function testFullRefundClosureRemovesOnlyTheVerifiedAmountFromTheOriginalGrant() public {
        bytes32 formId = _bookOneToOne();
        _publishRedressTerms(formId);
        (bytes32 caseId, SparkV15LessonRemedies.FaultFinding memory finding) = _tutorFault(formId);
        remedies.recordFault(caseId, finding);
        _grantRemedyPaymentsAndVerification();
        requestVm.prank(CUSTOMER);
        redress.acceptStandardCompensation(formId);
        _provideProviderFunds(8);
        redress.issueCourseCredit(formId);
        require(funds.compensationCreditRemaining(LESSON, PLACE) == 8, "named grant funded");

        requestVm.warp(LESSON_END + 3);
        bytes32 grounds = keccak256("customer may switch under the agreed remedy terms");
        uint256 proof = _evidence(remedyBookings.refundSwitchCommitment(formId, grounds, CUSTOMER));
        requestVm.prank(CUSTOMER);
        remedyBookings.switchToRefund(formId, grounds, proof);
        bytes32 obligation = _establishDirectRefund(formId);
        uint64 paidAt = LESSON_END + 3 + 1 days;
        uint256 approval = _approveRefund(obligation, paidAt);
        requestVm.warp(paidAt);
        requestVm.prank(PROVIDER);
        uint256 receipt = payments.pay(approval, 8);
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == 16, "actual refund plus separate unused grant");
        _closeRefund(formId, 8, 5);
        require(
            funds.compensationCreditRemaining(LESSON, PLACE) == 3, "three unused units remain under the agreed terms"
        );
        require(
            funds.creditBalance(funds.creditAccount(CUSTOMER)) == 11, "original debit restoration and permitted credit"
        );
        require(
            payments.getReceipt(receipt).amount == 8 && redress.getRedress(formId).unusedCreditRemoved == 5,
            "historical payment and grant closure retained"
        );
    }

    function testAdoptedRefundAmountsDriveBothLivePortionsAndPreserveActualCredit() public {
        RefundRevisionFixture memory value = _partiallyPayBothRefundPortions();
        _requireRefundStatus(value.formId, 8, 3);

        // Independent review reallocates the original debit restoration across the two portions.
        bytes32 termsId = cases.INTAKE().caseContext(value.faultCaseId).termsId;
        _grant(REVIEWER, SparkV15ReviewActions.ACTION_DECIDE_REVIEW);
        _grant(SOURCE_ACTOR, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION);
        bytes32 effectRole = payments.caseEffectRole();
        authorityMatrix.setPermission(SparkV15.APP_ID, effectRole, payments.ACTION_APPLY_CASE_EFFECT(), true);
        identityRegistry.assignSubject(address(cases), SparkV15.APP_ID, effectRole, _authority(effectRole), "test:case");

        _adoptRefundPrincipal(termsId, value.ordinary, 3);
        _requireRefundStatus(value.formId, 6, 3);
        _adoptRefundPrincipal(termsId, value.additional, 5);
        _requireRefundStatus(value.formId, 8, 3);
        require(payments.getObligation(value.ordinary).terms.amount == 5, "initial ordinary principal retained");
        require(payments.getObligation(value.additional).terms.amount == 3, "initial additional principal retained");

        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(PROVIDER);
        payments.pay(value.additionalApproval, 4);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, funds.ACTION_REPLENISH_PAYMENT_BACKING(), true);
        requestVm.prank(VERIFIER_ACTOR);
        funds.replenishPaymentBacking(value.additional, 2, _authority(ROLE_VERIFIER));
        uint256 correctedApproval = _approveRefund(value.additional, value.paidAt + 1 hours, 5);
        requestVm.prank(PROVIDER);
        payments.pay(value.ordinaryApproval, 1);
        requestVm.prank(PROVIDER);
        payments.pay(correctedApproval, 4);
        _requireRefundStatus(value.formId, 8, 8);
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == 8, "actual credit restored to the original account");
        require(payments.getReceipt(value.ordinaryReceipt).amount == 2, "initial ordinary receipt retained");
        require(payments.getReceipt(value.additionalReceipt).amount == 1, "initial additional receipt retained");
        require(payments.getApproval(value.additionalApproval).paid == 1, "initial approval only used for the first receipt");
    }

    function testRecoveryFollowsRealCustomerRefundAndMovesOnlyTheConfirmedTutorDebt() public {
        bytes32 formId = _bookOneToOne();
        _publishRedressTerms(formId);
        (bytes32 caseId, SparkV15LessonRemedies.FaultFinding memory finding) = _tutorFault(formId);
        remedies.recordFault(caseId, finding);
        _grantRemedyPaymentsAndVerification();

        bytes32 debtId = _confirmTutorLoss(caseId);
        token.mint(TUTOR, 10);
        requestVm.prank(TUTOR);
        token.approve(address(tutorDebt), 10);
        requestVm.prank(TUTOR);
        requestVm.expectRevert(SparkV15TutorDebt.InvalidDebt.selector);
        tutorDebt.collectDebt(debtId, 1);

        requestVm.warp(LESSON_END + 3);
        requestVm.prank(CUSTOMER);
        redress.requestDirectRefund(formId);
        bytes32 obligation = _establishDirectRefund(formId);
        (, bool satisfiedBefore) = redress.lessonRedressDelivered(LESSON);
        require(!satisfiedBefore, "an established obligation has yet to restore the actual debit");
        require(redress.getRedress(formId).creditIssuedAt == 0, "direct refund has no compensation grant");
        uint64 paidAt = LESSON_END + 3 + 1 days;
        uint256 requestId = _approveRefund(obligation, paidAt);
        requestVm.warp(paidAt);
        requestVm.prank(PROVIDER);
        uint256 receipt = payments.pay(requestId, 8);
        require(payments.getReceipt(receipt).amount == 8, "canonical payment receipt");
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == 8, "actual refund to the account debited");
        _closeRefund(formId, 0, 0);
        require(redress.getRedress(formId).closedAt == paidAt, "a full refund is retained as case closure");

        uint256 readyProof = _evidence(tutorDebt.recoveryReadinessCommitment(debtId, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        tutorDebt.verifyRecoveryReadiness(debtId, readyProof, _authority(ROLE_VERIFIER));
        requestVm.warp(paidAt + 1);
        uint256 previousProviderBalance = token.balanceOf(PROVIDER);
        requestVm.prank(TUTOR);
        tutorDebt.collectDebt(debtId, 2);
        require(token.balanceOf(PROVIDER) == previousProviderBalance + 2, "actual debt payment to provider");
        require(token.balanceOf(TUTOR) == 8 && tutorDebt.getDebt(debtId).remaining == 1, "remaining debt is separate");
        require(
            payments.getReceipt(receipt).amount == 8 && !remedies.allowsTutorWage(LESSON, TUTOR), "separate effects"
        );
    }

    function testFirstCompletedPayableLessonUsesTheSameTutorsOriginalFeeAndRetainsShortfall() public {
        bytes32 formId = _bookOneToOne();
        (bytes32 caseId, SparkV15LessonRemedies.FaultFinding memory finding) = _tutorFault(formId);
        remedies.recordFault(caseId, finding);
        bytes32 laterLesson = keccak256("the tutor's next completed lesson");
        SparkV15Settlement settlement = new SparkV15Settlement(booking, payments);
        SparkV15SettlementAlternatives alternatives =
            new SparkV15SettlementAlternatives(booking, payments, ISparkV15SettlementActors(address(settlement)));
        settlement.bindAlternatives(alternatives);
        settlement.setRemedyPolicy(ISparkV15SettlementRemedies(address(remedies)));
        SparkV15Booking.LessonTerms memory laterTerms = _anotherLessonTerms(laterLesson, TUTOR, LESSON_END + 3 days);
        SparkV15Settlement.GroupAssessment memory settlementInput = _laterAssessment(laterTerms);
        laterTerms.tutorPayTermsRef = settlement.tutorPayTermsCommitment(laterLesson, settlementInput.tutor);
        laterTerms.serviceTermsRef = settlement.refundTermsCommitment(laterLesson, settlementInput.refund);
        bytes32 laterForm = _completeAnotherLesson(laterTerms);
        settlementInput.seats[0].formId = laterForm;
        require(remedies.previewTutorDeductions(laterLesson, OTHER_STUDENT, 9) == 9, "different tutor unaffected");
        requestVm.expectRevert(SparkV15LessonRemedies.InvalidTutorPayHistory.selector);
        remedies.previewTutorDeductions(laterLesson, TUTOR, 3);

        SparkV15LessonRemedies.TutorPayHistoryInput memory input;
        input.lessonId = laterLesson;
        input.tutor = TUTOR;
        input.completed = true;
        input.payableBefore = 3;
        input.historyScopeRef = keccak256("checked all actual tutor completions and payable fees through the candidate");
        input.earlier = new SparkV15LessonRemedies.EarlierCompletion[](0);
        input.shares = new SparkV15LessonRemedies.DeductionShare[](1);
        input.shares[0] = SparkV15LessonRemedies.DeductionShare(LESSON, 3, keccak256("agreed shortfall treatment"));
        uint256 proof = _evidence(remedies.tutorPayHistoryCommitment(input, VERIFIER_ACTOR));
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, remedies.ACTION_VERIFY_TUTOR_PAY_HISTORY(), true);
        requestVm.prank(VERIFIER_ACTOR);
        remedies.verifyTutorPayHistory(input, proof, _authority(ROLE_VERIFIER));
        require(remedies.previewTutorDeductions(laterLesson, TUTOR, 3) == 0, "gross three is fully deducted");
        require(!remedies.mayPaySettledTutorDeductions(laterLesson, TUTOR), "not yet settled");
        requestVm.expectRevert();
        remedies.recordTutorDeductions(laterLesson, TUTOR, 3);

        _settleLaterLesson(settlement, alternatives, laterLesson, laterForm, settlementInput);
        require(
            settlement.getSeatSettlement(laterLesson, laterForm).tutorObligationId == bytes32(0),
            "settlement applied the verified zero net"
        );
        SparkV15LessonRemedies.TutorDeduction memory deduction = remedies.getTutorDeduction(TUTOR, LESSON);
        require(deduction.nextLessonId == laterLesson && deduction.fixedAmount == 4, "half the original eight");
        require(deduction.applied == 3 && deduction.unapplied == 1, "keep the one-unit shortfall");

        bytes32 followingLesson = keccak256("a still later actual same-tutor lesson");
        _completeAnotherLesson(_anotherLessonTerms(followingLesson, TUTOR, laterTerms.endsAt + 3 days));
        input.lessonId = followingLesson;
        input.shares = new SparkV15LessonRemedies.DeductionShare[](0);
        uint256 incompleteProof = _evidence(remedies.tutorPayHistoryCommitment(input, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        requestVm.expectRevert(SparkV15LessonRemedies.InvalidTutorPayHistory.selector);
        remedies.verifyTutorPayHistory(input, incompleteProof, _authority(ROLE_VERIFIER));

        input.earlier = new SparkV15LessonRemedies.EarlierCompletion[](1);
        input.earlier[0] =
            SparkV15LessonRemedies.EarlierCompletion(laterLesson, 3, settlement.getGroupSettlement(laterLesson).basis);
        uint256 completeProof = _evidence(remedies.tutorPayHistoryCommitment(input, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        remedies.verifyTutorPayHistory(input, completeProof, _authority(ROLE_VERIFIER));
        require(remedies.previewTutorDeductions(followingLesson, TUTOR, 3) == 3, "the same fault deducts only once");
    }

    function _laterAssessment(SparkV15Booking.LessonTerms memory lesson)
        private
        pure
        returns (SparkV15Settlement.GroupAssessment memory input)
    {
        uint64 wageDue = lesson.startsAt + 30 days;
        input.route = SparkV15Settlement.Route.OrdinaryOneToOne;
        input.clearanceRef = keccak256("independently verified ordinary completion and authorised deduction");
        input.tutor.agreementRef = lesson.tutorAgreementRef;
        input.tutor.recipient = TUTOR;
        input.tutor.schedule = SparkV15Settlement.PaymentSchedule(wageDue, wageDue + 1 days, 0, 1 days);
        input.tutor.seats = new SparkV15Settlement.TutorSeatTerms[](1);
        input.tutor.seats[0] = SparkV15Settlement.TutorSeatTerms(keccak256(abi.encode(lesson.lessonId, PLACE)), 3, 0);
        input.refund = SparkV15Settlement.RefundTerms(
            lesson.documentsRef, SparkV15Settlement.PaymentSchedule(lesson.endsAt, lesson.endsAt + 1 days, 0, 1 days)
        );
        input.seats = new SparkV15Settlement.SeatFinding[](1);
        input.seats[0].disposition = SparkV15Settlement.SeatDisposition.OrdinaryFee;
        input.seats[0].serviceAvailabilityRef = keccak256("agreed tutoring actually available");
    }

    function _settleLaterLesson(
        SparkV15Settlement settlement,
        SparkV15SettlementAlternatives alternatives,
        bytes32 lessonId,
        bytes32 formId,
        SparkV15Settlement.GroupAssessment memory input
    ) private {
        bytes32 role = payments.settlementRole();
        identityRegistry.assignSubject(
            address(settlement), SparkV15.APP_ID, role, _authority(role), "test:settlement writer"
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, role, payments.ACTION_RECORD_SETTLEMENT_OBLIGATION(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, alternatives.ACTION_CONFIRM_ONE_TO_ONE(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, settlement.ACTION_PROPOSE_GROUP_SETTLEMENT(), true);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, settlement.ACTION_APPROVE_GROUP_SETTLEMENT(), true
        );
        bytes32 report = keccak256("record of the later completed one-to-one lesson");
        uint256 studentConfirmation = _evidence(alternatives.completionCommitment(formId, report, STUDENT));
        requestVm.prank(STUDENT);
        alternatives.recordOneToOneCompletion(formId, report, studentConfirmation);
        uint256 coordinatorConfirmation = _evidence(alternatives.completionCommitment(formId, report, SOURCE_ACTOR));
        requestVm.prank(SOURCE_ACTOR);
        alternatives.recordOneToOneCompletion(formId, report, coordinatorConfirmation);
        bytes32 proposal = settlement.proposalCommitment(lessonId, input);
        requestVm.prank(SOURCE_ACTOR);
        settlement.proposeOrdinaryGroup(lessonId, proposal);
        SparkV15Settlement.GroupPreview memory preview =
            settlement.previewOrdinaryGroup(lessonId, input, VERIFIER_ACTOR);
        require(
            preview.totalTutorPay == 3 && preview.netTutorPay == 0 && preview.payments.length == 0,
            "exact settlement amounts"
        );
        bytes32 subjectId = keccak256("independent settlement evidence source");
        identityRegistry.assignSubject(
            SETTLEMENT_EVIDENCE_ACTOR, SparkV15.APP_ID, ROLE_SOURCE, subjectId, "test:independent source"
        );
        requestVm.prank(SETTLEMENT_EVIDENCE_ACTOR);
        uint256 evidenceId = evidenceRegistry.registerEvidence(
            AVAEvidenceRegistry.EvidenceRegistrationInput({
                appId: SparkV15.APP_ID,
                workflowKey: REQUEST_WORKFLOW,
                packageId: requestPackageId,
                roleKey: ROLE_SOURCE,
                subjectId: subjectId,
                commitment: preview.basis,
                evidenceTypeHash: keccak256("spark.v1.5.independent-settlement"),
                disclosurePolicyId: requestPolicyId,
                authorityId: subjectId,
                uri: "test:independently verified settlement"
            })
        );
        requestVm.prank(VERIFIER_ACTOR);
        settlement.approveOrdinaryGroup(lessonId, input, evidenceId, new uint256[](0));
    }

    function _completeAnotherLesson(SparkV15Booking.LessonTerms memory lesson) private returns (bytes32 formId) {
        formId = _prepareAnotherLesson(lesson, 8, bytes32(0));
        _rechargeNextLesson(lesson.lessonId, 8);
        _confirmOrdinary(formId, bytes32(0), 0);
        _teachConfirmedLesson(formId, lesson, false);
    }

    function _teachConfirmedLesson(bytes32 formId, SparkV15Booking.LessonTerms memory lesson, bool verifyNoticeAfterStart)
        private
    {
        bytes32 lessonId = lesson.lessonId;
        uint64 start = lesson.startsAt;
        requestVm.warp(start - 2);
        if (!verifyNoticeAfterStart) _studentNotice(formId, start - 2);
        uint256 tutorNotice = _evidence(booking.tutorNoticeCommitment(lessonId, TUTOR_CHANNEL, start - 2, TUTOR_NOTICE));
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTutorNotice(lessonId, TUTOR_CHANNEL, start - 2, TUTOR_NOTICE, tutorNotice);
        requestVm.warp(start);
        address[] memory students = new address[](1);
        students[0] = STUDENT;
        SparkV15Booking.StartObservation memory startObservation =
            SparkV15Booking.StartObservation(start, true, students, OPENING, bytes32(0));
        uint256 startId = _evidence(booking.teachingStartCommitment(lessonId, startObservation));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingStarted(lessonId, startObservation, startId);
        if (verifyNoticeAfterStart) {
            require(booking.getTeaching(lessonId).startPermission == SparkV15Booking.StartPermission.Unverified, "at start");
            _verifyEarlierStudentNotice(formId, start - 2);
        }
        requestVm.warp(start + 1 hours);
        uint256 endId = _evidence(booking.teachingEndCommitment(lessonId, start + 1 hours, ENDING));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingEnded(lessonId, start + 1 hours, ENDING, endId);
        bytes32 delivery = keccak256("the tutor completed the next lesson");
        uint256 deliveryId = _evidence(booking.tutorDeliveryCommitment(lessonId, true, delivery));
        requestVm.prank(lesson.tutor);
        booking.recordTutorDelivery(lessonId, true, delivery, deliveryId);
    }

    function _verifyEarlierStudentNotice(bytes32 formId, uint64 deliveredAt) private {
        bytes32 subject = keccak256("independent witness of the remedial lesson notice");
        identityRegistry.assignSubject(
            SETTLEMENT_EVIDENCE_ACTOR, SparkV15.APP_ID, ROLE_SOURCE, subject, "test:notice witness"
        );
        AVAEvidenceRegistry.EvidenceRegistrationInput memory input =
            _bookingEvidenceInput(booking.studentNoticeCommitment(formId, deliveredAt, NOTICE_DELIVERY));
        input.subjectId = subject;
        input.authorityId = subject;
        requestVm.warp(block.timestamp + 1);
        requestVm.prank(SETTLEMENT_EVIDENCE_ACTOR);
        uint256 proof = evidenceRegistry.registerEvidence(input);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordStudentNotice(formId, deliveredAt, NOTICE_DELIVERY, proof);
    }

    function _rechargeNextLesson(bytes32 lessonId, uint128 amount) private {
        requestVm.prank(PROVIDER);
        bytes32 offer = funds.offerRecharge(
            SparkV15Funds.RechargeTerms(CUSTOMER, amount, 0, 0, keccak256(abi.encode("lesson recharge", lessonId))),
            CREDIT_PROVIDER_ID
        );
        token.mint(CUSTOMER, amount);
        requestVm.startPrank(CUSTOMER);
        token.approve(address(funds), amount);
        funds.recharge(offer);
        requestVm.stopPrank();
    }

    function _anotherLessonTerms(bytes32 lessonId, address tutor, uint64 start)
        private
        pure
        returns (SparkV15Booking.LessonTerms memory lesson)
    {
        lesson = _lessonTerms(false);
        lesson.lessonId = lessonId;
        lesson.tutor = tutor;
        lesson.startsAt = start;
        lesson.endsAt = start + 1 hours;
        lesson.tutorFee = 3;
    }

    function _prepareAnotherLesson(SparkV15Booking.LessonTerms memory lesson, uint128 payableFee, bytes32 discount)
        private
        returns (bytes32 formId)
    {
        formId = _configureAnotherLesson(lesson, payableFee, discount);
        _acceptOtherLessonForm(formId, lesson.tutor);
    }

    function _configureAnotherLesson(SparkV15Booking.LessonTerms memory lesson, uint128 payableFee, bytes32 discount)
        private
        returns (bytes32 formId)
    {
        bytes32 lessonId = lesson.lessonId;
        address tutor = lesson.tutor;
        requestVm.prank(SOURCE_ACTOR);
        booking.publishLesson(lesson);
        SparkV15Booking.PlaceTerms memory place = _placeTerms(keccak256(abi.encode(lessonId, PLACE)), payableFee);
        place.remedyDiscountId = discount;
        requestVm.prank(SOURCE_ACTOR);
        formId = booking.publishForm(lessonId, place);
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, tutor);
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(lessonId);
        requestVm.prank(tutor);
        booking.signTeachingAgreement(lessonId);
        bytes32[] memory forms = new bytes32[](1);
        forms[0] = formId;
        _provideProviderFunds(23);
        uint256 fundingId = _evidence(booking.prefundingCommitment(lessonId, forms, 23, FUNDING_CHECK));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(lessonId, forms, 23, FUNDING_CHECK, fundingId);
        requestVm.warp(block.timestamp + 1);
    }

    function _acceptOtherLessonForm(bytes32 formId, address tutor) private {
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        _acceptForm(formId, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        _acceptForm(formId, tutor, SparkV15Booking.Acceptance.Tutor);
        _acceptForm(formId, PAYER, SparkV15Booking.Acceptance.Payer);
    }

    function _grantRemedyPaymentsAndVerification() private {
        bytes32 role = payments.settlementRole();
        identityRegistry.assignSubject(address(redress), SparkV15.APP_ID, role, _authority(role), "test:remedy refund");
        authorityMatrix.setPermission(SparkV15.APP_ID, role, payments.ACTION_RECORD_SETTLEMENT_OBLIGATION(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, redress.ACTION_ASSESS_REFUND(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, tutorDebt.ACTION_CONFIRM_TUTOR_LOSS(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, tutorDebt.ACTION_VERIFY_CUSTOMER_DELIVERY(), true);
    }

    function _closeRefund(bytes32 formId, uint128 unused, uint128 removal) private {
        SparkV15RemedyBookings.RefundClosureDecision memory treatment;
        treatment.termsAndLawRef = keccak256("verified source terms permitting this exact full-refund closure");
        if (redress.getRedress(formId).acceptedAt != 0) {
            treatment.remedyTreatmentRef = keccak256("outstanding compensation resolved by full debit restoration");
        }
        if (redress.getRedress(formId).creditIssuedAt != 0) {
            treatment.creditTreatmentRef = keccak256("agreed grant disposition removes only approved unused units");
        }
        treatment.unusedCredit = unused;
        treatment.creditRemoval = removal;
        uint256 proof = _evidence(remedyBookings.refundClosureCommitment(formId, 0, treatment));
        requestVm.prank(PROVIDER);
        remedyBookings.closeFullRefund(formId, 0, treatment, proof);
    }

    function _confirmTutorLoss(bytes32 caseId) private returns (bytes32) {
        SparkV15TutorDebt.LossFinding memory loss = SparkV15TutorDebt.LossFinding({
            lossId: keccak256("one actual tutor-breach loss"),
            lossEvidenceRef: keccak256("verified independent invoice and responsibility assessment"),
            teachingAgreementRef: keccak256("agreed tutor contract"),
            breachedAt: LESSON_START,
            incurredAt: LESSON_END,
            actualLoss: 4,
            responsibility: 3
        });
        uint256 proof = _evidence(tutorDebt.lossCommitment(caseId, loss, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        return tutorDebt.confirmTutorLoss(caseId, loss, proof, _authority(ROLE_VERIFIER));
    }

    function _establishDirectRefund(bytes32 formId) private returns (bytes32) {
        return _establishDirectRefund(formId, 8);
    }

    function _establishDirectRefund(bytes32 formId, uint128 principal) private returns (bytes32) {
        SparkV15CustomerRedress.RefundBasis reason = SparkV15CustomerRedress.RefundBasis.DirectRequest;
        (SparkV15CustomerRedress.RefundAssessment memory preview, SparkV15Payments.PaymentTerms memory terms) =
            redress.previewRefund(formId, reason, VERIFIER_ACTOR);
        require(preview.principal == principal && preview.finalFee == 0, "refund needed to restore original debit");
        require(preview.triggerAt == LESSON_END + 3, "use the actual customer choice as the refund trigger");
        uint256 assessmentProof = _evidence(preview.basis);
        requestVm.prank(VERIFIER_ACTOR);
        uint256 index = redress.assessRefund(formId, reason, assessmentProof, _authority(ROLE_VERIFIER));
        uint256 paymentProof = _evidence(payments.paymentEvidenceCommitment(terms, preview.basis));
        return redress.establishRefundPayment(formId, index, paymentProof);
    }

    function _approveRefund(bytes32 obligation, uint64 paidAt) private returns (uint256 requestId) {
        return _approveRefund(obligation, paidAt, 8);
    }

    function _approveRefund(bytes32 obligation, uint64 paidAt, uint128 ceiling) private returns (uint256 requestId) {
        SparkV15Payments.ApprovalTerms memory terms =
            SparkV15Payments.ApprovalTerms(obligation, PROVIDER, ceiling, paidAt + 1 days, 0);
        bytes32 hash = payments.approvalParameters(terms);
        uint256 status = _createRequestState(
            address(payments), SparkV15.RESPONSE_APPROVE_PAYMENT, hash, SparkV15.APPROVAL_BURDEN, paidAt
        );
        requestId = _createRequest(
            AVARequestAllocation.RequestInput(
                status, address(payments), SparkV15.RESPONSE_APPROVE_PAYMENT, hash, SparkV15.APPROVAL_BURDEN, paidAt
            )
        );
        _approveRequest(requestId);
        requestVm.prank(ALLOCATOR_ACTOR);
        payments.recordApproval(requestId, terms);
    }

    function _establishOrdinaryRefund(bytes32 formId, uint64 paidAt) private returns (bytes32) {
        SparkV15Booking.Form memory form = booking.getForm(formId);
        SparkV15Payments.PaymentTerms memory terms;
        terms.lessonId = form.lessonId;
        terms.paymentPart = keccak256(abi.encode("spark.v1.5.lesson-refund", form.terms.placeId));
        terms.recipient = CUSTOMER;
        terms.originalDebitAccount = form.terms.creditAccount;
        terms.originalDebitAmount = form.confirmation.debitedUnits;
        terms.amount = 5;
        terms.dueAt = paidAt;
        terms.executionDeadline = paidAt + 1 days;
        terms.dueAtExact = true;
        terms.executionDeadlineExact = true;
        terms.settlementProposer = SOURCE_ACTOR;
        terms.settlementApprover = VERIFIER_ACTOR;
        bytes32 basis = keccak256("independently verified original lesson refund portion");
        uint256 evidenceId = _evidence(payments.paymentEvidenceCommitment(terms, basis));
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_ESTABLISH_PAYMENT, true);
        requestVm.prank(VERIFIER_ACTOR);
        return payments.establishPayment(terms, basis, evidenceId, _authority(ROLE_VERIFIER));
    }

    function _partiallyPayBothRefundPortions() private returns (RefundRevisionFixture memory value) {
        value.formId = _bookOneToOne();
        _publishRedressTerms(value.formId);
        SparkV15LessonRemedies.FaultFinding memory finding;
        (value.faultCaseId, finding) = _tutorFault(value.formId);
        remedies.recordFault(value.faultCaseId, finding);
        _grantRemedyPaymentsAndVerification();
        requestVm.warp(LESSON_END + 3);
        requestVm.prank(CUSTOMER);
        redress.requestDirectRefund(value.formId);
        value.paidAt = LESSON_END + 3 + 1 days;
        value.ordinary = _establishOrdinaryRefund(value.formId, value.paidAt);
        value.additional = _establishDirectRefund(value.formId, 3);
        value.ordinaryApproval = _approveRefund(value.ordinary, value.paidAt, 5);
        value.additionalApproval = _approveRefund(value.additional, value.paidAt, 3);
        requestVm.warp(value.paidAt);
        requestVm.prank(PROVIDER);
        value.ordinaryReceipt = payments.pay(value.ordinaryApproval, 2);
        requestVm.prank(PROVIDER);
        value.additionalReceipt = payments.pay(value.additionalApproval, 1);
    }

    function _retainRefundPortion(bytes32 termsId, bytes32 obligationId, SparkV15Payments.Obligation memory payment)
        private
        returns (bytes32 caseId)
    {
        SparkV15ReviewContext.OriginalInput memory original;
        original.termsId = termsId;
        original.concernRef = keccak256(abi.encode("review of the original refund portion", obligationId));
        caseId = cases.caseIdFor(LESSON, original.concernRef);
        original.obligationId = obligationId;
        original.paymentCommitment = payment.commitment;
        original.decider = INITIAL_DECIDER;
        original.decidedAt = uint64(block.timestamp);
        original.outcome = keccak256(abi.encode(obligationId, payment.terms.amount));
        original.parties = new address[](2);
        original.parties[0] = CUSTOMER;
        original.parties[1] = PROVIDER;
        uint256 proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(original))
        );
        requestVm.prank(VERIFIER_ACTOR);
        cases.retainOriginal(original, proof, _businessAuthority(VERIFIER_ACTOR));
    }

    function _adoptRefundPrincipal(bytes32 termsId, bytes32 obligationId, uint128 amount) private {
        SparkV15Payments.Obligation memory payment = payments.getObligation(obligationId);
        bytes32 caseId = _retainRefundPortion(termsId, obligationId, payment);
        requestVm.warp(block.timestamp + 1);

        SparkV15Payments.PaymentRevision memory revision = SparkV15Payments.PaymentRevision(
            obligationId, amount, payment.beneficiary, payment.destination, payment.version
        );
        bytes32 outcome = keccak256(abi.encode(
            keccak256("spark.v1.5.revise-payment"), block.chainid, address(payments), caseId, revision, payment.commitment
        ));
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput(
            SparkV15ReviewContext.ReviewDisposition.CorrectionRequired,
            outcome, keccak256("verified amount for this portion of the original debit restoration"), 0
        );
        uint256 reviewProof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(review)));
        requestVm.prank(REVIEWER);
        cases.decidePaymentRevision(caseId, review, revision, reviewProof, _businessAuthority(REVIEWER));
        requestVm.warp(block.timestamp + 1);

        SparkV15ReviewContext.OriginalOutcome memory original = cases.getCase(caseId).original;
        SparkV15ReviewContext.Notice memory notice = SparkV15ReviewContext.Notice(
            keccak256("notified original parties of the correction"), uint64(block.timestamp)
        );
        bytes32 payload = keccak256(abi.encode(notice, original.evidenceId, reviewProof, original.partiesHash, bytes32(0)));
        uint256 adoptionProof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, SOURCE_ACTOR, payload);
        requestVm.prank(SOURCE_ACTOR);
        cases.adoptPaymentRevision(caseId, notice, adoptionProof, _businessAuthority(SOURCE_ACTOR), revision);
    }

    function _requireRefundStatus(bytes32 formId, uint256 principal, uint256 received) private view {
        (uint256 assessments, uint256 currentPrincipal, uint256 netReceived) = redress.refundStatus(formId);
        require(assessments == 1, "original additional assessment retained");
        require(currentPrincipal == principal, "current amount reflects adopted refunds");
        require(netReceived == received, "original account actual credit");
    }

    function _publishRedressTerms(bytes32 formId) private {
        SparkV15CustomerRedress.RedressTerms memory terms = SparkV15CustomerRedress.RedressTerms({
            acceptThrough: LESSON_END + 7 days,
            deliverThrough: LESSON_END + 14 days,
            refundDuePeriod: 1 days,
            refundExecutionPeriod: 3 days,
            earlierLegalExecutionPeriod: 0,
            postLiftPeriod: 2 days,
            coveredService: keccak256("the agreed original instruction"),
            agreementRef: keccak256("course terms, applicable deadlines and contacts")
        });
        uint256 proof = _evidence(redress.redressTermsCommitment(formId, terms));
        requestVm.prank(PROVIDER);
        redress.publishRedressTerms(formId, terms, proof);
    }

    function _tutorFault(bytes32 formId)
        private
        returns (bytes32 caseId, SparkV15LessonRemedies.FaultFinding memory finding)
    {
        bytes32 termsId = _publishContacts(formId);
        caseId = cases.caseIdFor(LESSON, CONCERN);
        finding.kind = SparkV15LessonRemedies.FaultKind.MissedAgreedTeaching;
        finding.responsibleTutor = TUTOR;
        finding.tutorAgreementRef = keccak256("agreed tutor contract");
        finding.originalOccurredAt = LESSON_START;
        finding.groundRef = keccak256("the agreed lesson could not be delivered by the tutor");
        finding.tutorInquiryRef = keccak256("coordinator checked with tutor");
        finding.tutorResponseOpportunityRef = keccak256("notice and opportunity to respond");
        finding.affectedStudentsInquiryRef = keccak256("actual readiness independently confirmed with student");
        finding.affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        finding.affected[0] = SparkV15LessonRemedies.AffectedPlace({
            formId: formId,
            teaching: SparkV15LessonRemedies.TeachingReceived.NoneDelivered,
            participation: SparkV15LessonRemedies.Participation.ReadyAsAgreed,
            lostServiceFee: 8,
            missedAgreedTeaching: true,
            evidenceRef: keccak256("independent record of the no-teaching occurrence and the student ready")
        });

        requestVm.warp(LESSON_END + 1);
        bytes32 outcome = remedies.faultOutcome(caseId, finding);
        address[] memory parties = new address[](3);
        parties[0] = CUSTOMER;
        parties[1] = STUDENT;
        parties[2] = TUTOR;
        SparkV15ReviewContext.OriginalInput memory retained = SparkV15ReviewContext.OriginalInput({
            termsId: termsId,
            concernRef: CONCERN,
            obligationId: bytes32(0),
            paymentCommitment: bytes32(0),
            decider: INITIAL_DECIDER,
            decidedAt: uint64(block.timestamp),
            outcome: outcome,
            parties: parties
        });
        uint256 originalEvidence = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(retained))
        );
        requestVm.prank(VERIFIER_ACTOR);
        cases.retainOriginal(retained, originalEvidence, _businessAuthority(VERIFIER_ACTOR));
        SparkV15ReviewContext.InitialInput memory initial = SparkV15ReviewContext.InitialInput({
            issue: SparkV15ReviewContext.DisputedFinding.Fault,
            outcome: outcome,
            reasons: keccak256("missed agreed service due to tutor fault"),
            support: finding.affected[0].evidenceRef
        });
        uint256 initialEvidence = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, INITIAL_DECIDER, keccak256(abi.encode(initial))
        );
        requestVm.prank(INITIAL_DECIDER);
        cases.decideInitial(caseId, initial, initialEvidence, _businessAuthority(INITIAL_DECIDER));
    }

    function _publishContacts(bytes32 formId) private returns (bytes32 termsId) {
        SparkV15ReviewContext.ReviewTerms memory terms = SparkV15ReviewContext.ReviewTerms({
            lessonId: LESSON,
            publication: keccak256("review contacts distributed with the lesson form"),
            governingForm: formId,
            provider: PROVIDER,
            coordinator: SOURCE_ACTOR,
            alternativeContact: OTHER_PAYER,
            leadAcademicTutor: INITIAL_DECIDER,
            namedReviewer: REVIEWER,
            escalationContact: OTHER_STUDENT,
            replyDate: 0,
            replyPeriod: 2 days,
            replyLegalDeadline: 0,
            reviewDeadline: LESSON_END + 7 days,
            reviewLegalDeadline: 0
        });
        termsId = keccak256(abi.encode(terms));
        uint256 evidenceId = _caseEvidence(termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, PROVIDER, termsId);
        SparkV15ConcernIntake intake = cases.INTAKE();
        requestVm.prank(PROVIDER);
        intake.publishContacts(terms, evidenceId, _businessAuthority(PROVIDER));
    }

    function _caseEvidence(bytes32 subject, bytes32 action, address actor, bytes32 payload) private returns (uint256) {
        return _evidence(cases.evidenceCommitment(subject, action, actor, payload));
    }

    function _adoptFaultCorrection(bytes32 caseId, bytes32 outcome) private {
        _grant(REVIEWER, SparkV15ReviewActions.ACTION_DECIDE_REVIEW);
        _grant(SOURCE_ACTOR, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION);
        requestVm.warp(LESSON_END + 2);
        SparkV15ReviewContext.ReviewInput memory finding = SparkV15ReviewContext.ReviewInput(
            SparkV15ReviewContext.ReviewDisposition.CorrectionRequired, outcome, keccak256("reviewed evidence"), 0
        );
        uint256 proof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(finding)));
        requestVm.prank(REVIEWER);
        cases.decideReview(caseId, finding, proof, _businessAuthority(REVIEWER));
        requestVm.warp(LESSON_END + 3);
        SparkV15ReviewContext.Notice memory notice = SparkV15ReviewContext.Notice(
            keccak256("delivery of the adopted disposition to original parties"), LESSON_END + 3
        );
        SparkV15ReviewContext.OriginalOutcome memory original = cases.getCase(caseId).original;
        bytes32 payload = keccak256(abi.encode(notice, original.evidenceId, proof, original.partiesHash, bytes32(0)));
        uint256 adoptionProof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, SOURCE_ACTOR, payload);
        requestVm.prank(SOURCE_ACTOR);
        cases.adoptCorrection(caseId, notice, adoptionProof, _businessAuthority(SOURCE_ACTOR));
    }

    function _grant(address actor, bytes32 action) private {
        bytes32 role = keccak256(abi.encode("lesson review role", actor));
        identityRegistry.assignSubject(actor, SparkV15.APP_ID, role, _businessAuthority(actor), "test:lesson review");
        authorityMatrix.setPermission(SparkV15.APP_ID, role, action, true);
    }

    function _businessAuthority(address actor) private pure returns (bytes32) {
        return keccak256(abi.encode("lesson review authority", actor));
    }
}
