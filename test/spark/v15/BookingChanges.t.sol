// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {ISparkV15BookingChanges, SparkV15Booking} from "../../../src/apps/spark/v15/SparkV15Booking.sol";
import {SparkV15} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {
    ISparkV15RemedyBooking,
    SparkV15BookingCancellations,
    SparkV15BookingChanges,
    SparkV15BookingCreditSelection
} from "../../../src/apps/spark/v15/SparkV15BookingChanges.sol";
import {SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {SparkV15BookingFixture} from "./Booking.t.sol";

contract BookingChangesTest is SparkV15BookingFixture {
    bytes32 private constant CONTACT = keccak256("actual contact to arrange a different time");
    bytes32 private constant OLD_ZONE = keccak256("UTC");
    bytes32 private constant CHANGE_NOTICE = keccak256("delivery of the agreed change to the student");
    bytes32 private constant NEXT_LESSON = keccak256("independently booked teaching");
    bytes32 private constant DISCOUNT = keccak256("verified once-only remedy entitlement");
    address private constant REPLACEMENT = address(0x7120);
    address private constant PAYMENT_EXECUTOR = address(0x7121);

    SparkV15BookingChanges private changes;
    SparkV15BookingCancellations private cancellations;

    function setUp() public override {
        super.setUp();
        changes = new SparkV15BookingChanges(booking, payments);
        booking.bindBookingChanges(ISparkV15BookingChanges(address(changes)));
        identityRegistry.assignSubject(
            address(changes.CREDIT_SELECTIONS()),
            SparkV15.APP_ID,
            funds.BOOKING_ROLE(),
            keccak256("installed booking credit selection"),
            "test:booking credit selection"
        );
        cancellations = new SparkV15BookingCancellations(changes);
        changes.bindCancellations(cancellations);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, cancellations.ACTION_VERIFY_CANCELLATION(), true);
        bytes32 settlementRole = payments.settlementRole();
        identityRegistry.assignSubject(
            address(cancellations),
            SparkV15.APP_ID,
            settlementRole,
            keccak256("test cancellation refunds"),
            "test:cancellations"
        );
        authorityMatrix.setPermission(
            SparkV15.APP_ID, settlementRole, payments.ACTION_RECORD_SETTLEMENT_OBLIGATION(), true
        );
        payments.bindHolds(
            new SparkV15PaymentHolds(address(payments), requestAllocation, REQUEST_WORKFLOW, ROLE_VERIFIER)
        );
    }

    function testScheduleChangeRequiresNamedPayerAndSeparateStudentNotice() public {
        bytes32 formId = _confirmedPlace(_terms());
        SparkV15BookingChanges.ArrangementTerms memory next;
        next.startsAt = LESSON_START + 1 days;
        next.endsAt = LESSON_END + 1 days;
        next.timeZoneRef = OLD_ZONE;
        next.effectiveAt = EPOCH + 20;
        bytes32 changeId = _propose(next);

        requestVm.expectRevert(SparkV15BookingChanges.UnauthorisedActor.selector);
        requestVm.prank(STUDENT);
        changes.acceptPlace(changeId, formId);
        requestVm.prank(PAYER);
        changes.acceptPlace(changeId, formId);
        requestVm.prank(TUTOR);
        changes.acceptTutor(changeId);
        requestVm.prank(PROVIDER);
        changes.acceptProvider(changeId);
        requestVm.warp(EPOCH + 3);
        requestVm.prank(SOURCE_ACTOR);
        changes.recordAgreement(changeId);

        requestVm.expectRevert(SparkV15BookingChanges.InvalidChange.selector);
        requestVm.prank(SOURCE_ACTOR);
        changes.finalizeArrangement(changeId);
        requestVm.warp(EPOCH + 4);
        uint256 notice = _evidence(changes.studentChangeNoticeCommitment(changeId, formId, EPOCH + 4, CHANGE_NOTICE));
        requestVm.prank(SOURCE_ACTOR);
        changes.recordStudentChangeNotice(changeId, formId, EPOCH + 4, CHANGE_NOTICE, notice);
        requestVm.prank(SOURCE_ACTOR);
        changes.finalizeArrangement(changeId);

        require(booking.getEffectiveArrangement(LESSON, EPOCH + 19).startsAt == LESSON_START, "changed early");
        ISparkV15BookingChanges.Arrangement memory effective = booking.getEffectiveArrangement(LESSON, EPOCH + 20);
        require(effective.changeId == changeId && effective.startsAt == next.startsAt, "wrong effective change");
        require(booking.getLesson(LESSON).terms.startsAt == LESSON_START, "rewrote signed form");
        require(booking.getLessonDeadlineAnchor(LESSON, LESSON_START) == next.startsAt, "old clock never ran");
    }

    function testPreLockChangeUsesOnlyConfirmedPlacesAndRetainsTheFundedPlan() public {
        (bytes32 confirmed, bytes32 pending) = _fundedGroup(ROSTER_LOCK);
        SparkV15BookingChanges.ArrangementTerms memory next = _nextGroupDate();
        bytes32 changeId = _propose(next);
        requestVm.expectRevert(SparkV15BookingChanges.InvalidChange.selector);
        requestVm.prank(OTHER_PAYER);
        changes.acceptPlace(changeId, pending);
        _acceptGroupDate(changeId, confirmed);
        requestVm.warp(EPOCH + 3);
        requestVm.prank(SOURCE_ACTOR);
        changes.recordAgreement(changeId);

        requestVm.warp(EPOCH + 4);
        uint256 studentNotice =
            _evidence(changes.studentChangeNoticeCommitment(changeId, confirmed, EPOCH + 4, CHANGE_NOTICE));
        requestVm.prank(SOURCE_ACTOR);
        changes.recordStudentChangeNotice(changeId, confirmed, EPOCH + 4, CHANGE_NOTICE, studentNotice);
        uint256 teacherNotice =
            _evidence(changes.tutorChangeNoticeCommitment(changeId, TUTOR_CHANNEL, EPOCH + 4, TUTOR_NOTICE));
        requestVm.prank(PROVIDER);
        changes.recordTutorChangeNotice(changeId, TUTOR_CHANNEL, EPOCH + 4, TUTOR_NOTICE, teacherNotice);
        requestVm.prank(SOURCE_ACTOR);
        changes.finalizeArrangement(changeId);

        require(booking.getPlannedForms(LESSON).length == 2, "lost funded booking history");
        require(booking.getLockedForms(LESSON).length == 0, "amendment locked the roster");
        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        _confirmOrdinary(pending, bytes32(0), 0);
        require(booking.getForm(pending).confirmation.confirmedAt == 0, "booked obsolete form");
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == 8, "pending place was charged");

        requestVm.warp(ROSTER_LOCK);
        uint256 registerEvidence = _evidence(booking.rosterLockCommitment(LESSON, REGISTER));
        requestVm.prank(SOURCE_ACTOR);
        booking.lockRoster(LESSON, REGISTER, registerEvidence);
        bytes32[] memory locked = booking.getLockedForms(LESSON);
        require(locked.length == 1 && locked[0] == confirmed, "locked a merely funded seat");

        requestVm.warp(next.startsAt);
        _recordOpening(next.startsAt, bytes32(0));
        require(
            booking.getTeaching(LESSON).startPermission == SparkV15Booking.StartPermission.Permitted,
            "expected actual start for the locked confirmed place"
        );
    }

    function testConfirmationBeforeAgreementRequiresANewGroupScope() public {
        (bytes32 first, bytes32 second) = _fundedGroup(ROSTER_LOCK);
        SparkV15BookingChanges.ArrangementTerms memory next = _nextGroupDate();
        bytes32 stale = _propose(next);
        _acceptGroupDate(stale, first);
        _confirmOrdinary(second, bytes32(0), 0);
        requestVm.warp(EPOCH + 3);
        requestVm.expectRevert(SparkV15BookingChanges.InvalidChange.selector);
        requestVm.prank(SOURCE_ACTOR);
        changes.recordAgreement(stale);

        bytes32 complete = _propose(next);
        _acceptGroupDate(complete, first);
        requestVm.expectRevert(SparkV15BookingChanges.InvalidChange.selector);
        requestVm.prank(SOURCE_ACTOR);
        changes.recordAgreement(complete);
        requestVm.prank(OTHER_PAYER);
        changes.acceptPlace(complete, second);
        requestVm.prank(SOURCE_ACTOR);
        changes.recordAgreement(complete);
        (, uint64 agreedAt,,,,) = changes.getAgreement(complete);
        require(agreedAt == EPOCH + 3 && booking.getLockedForms(LESSON).length == 0, "wrong agreement scope");
    }

    function testGroupNoFaultCancellationRequiresOfficialRoster() public {
        (bytes32 retained, bytes32 cancelled) = _fundedGroup(ROSTER_LOCK + 5);
        _confirmOrdinary(cancelled, bytes32(0), 0);
        requestVm.warp(EPOCH + 5);
        SparkV15BookingCancellations.DisruptionWitness memory facts = _disruptionFacts(EPOCH + 3);
        uint256 evidence = _evidence(cancellations.disruptionCommitment(cancelled, facts));
        requestVm.expectRevert(SparkV15BookingCancellations.InvalidCancellation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        cancellations.recordNoFaultDisruption(cancelled, facts, evidence);

        requestVm.warp(ROSTER_LOCK);
        uint256 register = _evidence(booking.rosterLockCommitment(LESSON, REGISTER));
        requestVm.prank(SOURCE_ACTOR);
        booking.lockRoster(LESSON, REGISTER, register);
        _disruptAt(cancelled, ROSTER_LOCK + 1);
        requestVm.warp(ROSTER_LOCK + 6);
        requestVm.prank(CUSTOMER);
        cancellations.requestNoFaultCancellation(cancelled);

        require(booking.getForm(cancelled).confirmation.debitedUnits == 8, "original debit was lost");
        require(booking.isCancelledAt(cancelled, ROSTER_LOCK + 6), "cancellation was lost");
        bytes32[] memory roster = booking.getLockedForms(LESSON);
        require(roster.length == 2 && roster[0] == retained && roster[1] == cancelled, "rewrote locked history");
    }

    function testVerifiedNoTeachingRestoresOnlyTheOriginalDebitThroughSettlement() public {
        bytes32 formId = _confirmedPlace(_terms());
        _disrupt(formId);
        requestVm.warp(ROSTER_LOCK);
        requestVm.expectRevert(SparkV15BookingCancellations.InvalidCancellation.selector);
        requestVm.prank(CUSTOMER);
        cancellations.requestNoFaultCancellation(formId);
        requestVm.warp(ROSTER_LOCK + 1);
        requestVm.prank(CUSTOMER);
        cancellations.requestNoFaultCancellation(formId);
        require(booking.isCancelledAt(formId, ROSTER_LOCK + 1), "lost signed cancellation");

        SparkV15BookingCancellations.ServiceEvidence memory service = SparkV15BookingCancellations.ServiceEvidence(
            SparkV15BookingCancellations.Delivery.NoneBeforeOpening, 0, keccak256("verified no teaching began")
        );
        uint256 assessment = _evidence(cancellations.serviceCommitment(formId, service));
        requestVm.prank(VERIFIER_ACTOR);
        cancellations.recordNoFaultAssessment(formId, service, assessment);
        (SparkV15Payments.PaymentTerms memory refund, bytes32 basis,) = cancellations.previewNoFaultRefund(formId);
        require(refund.amount == 8 && refund.originalDebitAmount == 8, "wrong original debit");
        require(
            refund.originalDebitAccount == funds.creditAccount(CUSTOMER) && refund.recipient == CUSTOMER,
            "wrong refund account"
        );
        require(refund.dueAt == ROSTER_LOCK + 1 hours + 1, "wrong refund clock");

        uint256 paymentProof = _evidence(payments.paymentEvidenceCommitment(refund, basis));
        bytes32 obligation = cancellations.establishNoFaultRefund(formId, paymentProof);
        require(payments.getObligation(obligation).terms.amount == 8, "missing shared refund obligation");
        require(funds.creditBalance(refund.originalDebitAccount) == 0, "approval or receipt invented");

        uint256 approval = _approveRefund(obligation, refund);
        requestVm.warp(refund.dueAt);
        requestVm.prank(PAYMENT_EXECUTOR);
        uint256 receipt = payments.pay(approval, 8);
        require(payments.getReceipt(receipt).creditAccount == refund.originalDebitAccount, "receipt wrong account");
        require(funds.creditBalance(refund.originalDebitAccount) == 8, "original debit not restored");
        require(funds.creditBalance(funds.creditAccount(PAYER)) == 0, "payer was not the debited account");
    }

    function testPartialNoFaultRefundUsesVerifiedUndeliveredValue() public {
        SparkV15BookingChanges.ChangeTerms memory terms = _terms();
        terms.noFaultAcceptanceDeadline = LESSON_END + 1 hours;
        bytes32 formId = _confirmedPlace(terms);
        requestVm.warp(LESSON_START - 1);
        _studentNotice(formId, LESSON_START - 2);
        _tutorNotice(LESSON_START - 2);
        requestVm.warp(LESSON_START);
        _recordOpening(LESSON_START, bytes32(0));
        uint64 endedAt = LESSON_START + 40 minutes;
        requestVm.warp(endedAt);
        _recordEnding(endedAt);
        _disruptAt(formId, endedAt + 1);

        requestVm.warp(terms.noFaultAcceptanceDeadline + 1);
        requestVm.prank(CUSTOMER);
        cancellations.requestNoFaultCancellation(formId);
        SparkV15BookingCancellations.ServiceEvidence memory finding = SparkV15BookingCancellations.ServiceEvidence(
            SparkV15BookingCancellations.Delivery.NoneBeforeOpening, 0, keccak256("incorrect no-teaching report")
        );
        uint256 wrong = _evidence(cancellations.serviceCommitment(formId, finding));
        requestVm.expectRevert(SparkV15BookingCancellations.InvalidCancellation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        cancellations.recordNoFaultAssessment(formId, finding, wrong);

        finding = SparkV15BookingCancellations.ServiceEvidence(
            SparkV15BookingCancellations.Delivery.Partial, 3, keccak256("verified value of undelivered services")
        );
        uint256 evidence = _evidence(cancellations.serviceCommitment(formId, finding));
        requestVm.prank(VERIFIER_ACTOR);
        cancellations.recordNoFaultAssessment(formId, finding, evidence);
        (SparkV15Payments.PaymentTerms memory refund,,) = cancellations.previewNoFaultRefund(formId);
        require(refund.originalDebitAmount == 8 && refund.amount == 3, "lost partial delivery assessment");
        require(booking.getTeaching(LESSON).endedAt == endedAt, "cancellation overwrote actual teaching");
    }

    function _approveRefund(bytes32 obligation, SparkV15Payments.PaymentTerms memory refund)
        private
        returns (uint256 id)
    {
        SparkV15Payments.ApprovalTerms memory approval = SparkV15Payments.ApprovalTerms(
            obligation, PAYMENT_EXECUTOR, refund.amount, refund.executionDeadline, 0
        );
        bytes32 commitment = payments.approvalParameters(approval);
        uint256 state = _createRequestState(
            address(payments),
            SparkV15.RESPONSE_APPROVE_PAYMENT,
            commitment,
            SparkV15.APPROVAL_BURDEN,
            refund.executionDeadline
        );
        id = _createRequest(
            AVARequestAllocation.RequestInput(
                state,
                address(payments),
                SparkV15.RESPONSE_APPROVE_PAYMENT,
                commitment,
                SparkV15.APPROVAL_BURDEN,
                refund.executionDeadline
            )
        );
        requestVm.prank(ALLOCATOR_ACTOR);
        requestAllocation.approve(id, ROLE_ALLOCATOR, _authority(ROLE_ALLOCATOR));
        requestVm.prank(ALLOCATOR_ACTOR);
        payments.recordApproval(id, approval);
    }

    function testTimelySeparateBookingUsesTwoConfirmedFormsAndPrecludesNoFaultWithdrawal() public {
        bytes32 from = _confirmedPlace(_terms());
        _disrupt(from);
        requestVm.warp(EPOCH + 6);
        SparkV15Booking.LessonTerms memory next = _lessonTerms(false);
        next.lessonId = NEXT_LESSON;
        next.startsAt += 2 days;
        next.endsAt += 2 days;
        requestVm.prank(SOURCE_ACTOR);
        booking.publishLesson(next);
        SparkV15Booking.PlaceTerms memory nextPlace = _placeTerms(PLACE, 8);
        requestVm.prank(SOURCE_ACTOR);
        bytes32 to = booking.publishForm(NEXT_LESSON, nextPlace);

        uint256 contact = _evidence(changes.separateBookingCommitment(from, to, EPOCH + 6, CONTACT));
        requestVm.prank(SOURCE_ACTOR);
        bytes32 linkId = changes.proposeSeparateBooking(from, to, EPOCH + 6, CONTACT, contact);
        requestVm.expectRevert(SparkV15BookingChanges.UnauthorisedActor.selector);
        requestVm.prank(STUDENT);
        changes.acceptSeparateBooking(linkId);
        requestVm.prank(PAYER);
        changes.acceptSeparateBooking(linkId);
        requestVm.warp(EPOCH + 7);
        _confirmNext(to);
        requestVm.warp(EPOCH + 8);
        uint256 notice = _evidence(changes.separateNoticeCommitment(linkId, EPOCH + 8, CHANGE_NOTICE));
        requestVm.prank(SOURCE_ACTOR);
        changes.linkSeparateBooking(linkId, EPOCH + 8, CHANGE_NOTICE, notice);
        require(changes.getSeparateBooking(linkId).nextFormId == to, "lost independent booking link");
        require(booking.getEffectiveArrangement(LESSON, EPOCH + 9).startsAt == LESSON_START, "rewrote original booking");
        require(
            booking.getEffectiveArrangement(NEXT_LESSON, EPOCH + 9).startsAt == next.startsAt, "rewrote next booking"
        );

        requestVm.warp(ROSTER_LOCK + 1);
        requestVm.expectRevert(SparkV15BookingCancellations.InvalidCancellation.selector);
        requestVm.prank(CUSTOMER);
        cancellations.requestNoFaultCancellation(from);
    }

    function testReplacementRequiresItsAgreementAndLeavesAnAlreadyStartedClockIntact() public {
        bytes32 formId = _confirmedPlace(_terms());
        uint64 changedAt = LESSON_START + 10;
        requestVm.warp(changedAt);
        SparkV15BookingChanges.ArrangementTerms memory next;
        next.startsAt = LESSON_START + 1 days;
        next.endsAt = LESSON_END + 1 days;
        next.effectiveAt = changedAt + 5;
        next.timeZoneRef = OLD_ZONE;
        next.noOpeningRef = keccak256("verified absence of teaching under the previous schedule");
        next.replacement = SparkV15BookingChanges.ReplacementTerms(
            REPLACEMENT,
            19,
            keccak256("replacement agreement"),
            keccak256("replacement pay"),
            booking.getLesson(LESSON).terms.serviceTermsRef,
            keccak256("replacement responsibilities"),
            keccak256("provider responsibilities under replacement"),
            TUTOR_CHANNEL
        );
        bytes32 changeId = _propose(next);
        requestVm.expectRevert(SparkV15BookingChanges.InvalidChange.selector);
        requestVm.prank(REPLACEMENT);
        changes.acceptTutor(changeId);

        requestVm.prank(PROVIDER);
        changes.signReplacementAgreement(changeId);
        requestVm.prank(REPLACEMENT);
        changes.signReplacementAgreement(changeId);
        requestVm.expectRevert(SparkV15BookingChanges.InvalidChange.selector);
        requestVm.prank(PAYER);
        changes.acceptPlace(changeId, formId);

        bytes32 inventory = keccak256("verified funding for the replacement pay and existing obligations");
        uint256 funding = _evidence(changes.replacementFundingCommitment(changeId, 39, inventory));
        requestVm.expectRevert(SparkV15Funds.InsufficientFunds.selector);
        requestVm.prank(VERIFIER_ACTOR);
        changes.verifyReplacementFunding(changeId, 39, inventory, funding);
        _provideProviderFunds(3);
        requestVm.prank(VERIFIER_ACTOR);
        changes.verifyReplacementFunding(changeId, 39, inventory, funding);
        require(funds.lessonReserved(LESSON) == 39, "replacement funding missing");

        requestVm.prank(PAYER);
        changes.acceptPlace(changeId, formId);
        requestVm.prank(REPLACEMENT);
        changes.acceptTutor(changeId);
        requestVm.prank(PROVIDER);
        changes.acceptProvider(changeId);
        requestVm.prank(SOURCE_ACTOR);
        changes.recordAgreement(changeId);
        requestVm.warp(changedAt + 1);
        uint256 studentNotice =
            _evidence(changes.studentChangeNoticeCommitment(changeId, formId, changedAt + 1, CHANGE_NOTICE));
        requestVm.prank(SOURCE_ACTOR);
        changes.recordStudentChangeNotice(changeId, formId, changedAt + 1, CHANGE_NOTICE, studentNotice);
        uint256 tutorNotice =
            _evidence(changes.tutorChangeNoticeCommitment(changeId, TUTOR_CHANNEL, changedAt + 1, TUTOR_NOTICE));
        requestVm.prank(PROVIDER);
        changes.recordTutorChangeNotice(changeId, TUTOR_CHANNEL, changedAt + 1, TUTOR_NOTICE, tutorNotice);
        requestVm.prank(SOURCE_ACTOR);
        changes.finalizeArrangement(changeId);

        require(booking.getLessonDeadlineAnchor(LESSON, next.startsAt) == LESSON_START, "restarted the matured clock");
        require(booking.getEffectiveArrangement(LESSON, next.startsAt).tutor == REPLACEMENT, "wrong active tutor");
        requestVm.warp(next.startsAt);
        _recordOpening(next.startsAt, bytes32(0));
        require(
            booking.getTeaching(LESSON).startPermission == SparkV15Booking.StartPermission.Permitted,
            "changed start rejected"
        );
        requestVm.warp(next.endsAt);
        _recordEnding(next.endsAt);
        bytes32 delivery = keccak256("replacement completed the agreed service");
        uint256 report = _evidence(booking.tutorDeliveryCommitment(LESSON, true, delivery));
        requestVm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        requestVm.prank(TUTOR);
        booking.recordTutorDelivery(LESSON, true, delivery, report);
        requestVm.prank(REPLACEMENT);
        booking.recordTutorDelivery(LESSON, true, delivery, report);
        require(booking.getTutorCompletedLessons(REPLACEMENT)[0] == LESSON, "missing actual tutor completion");
        require(booking.getTutorCompletedLessons(TUTOR).length == 0, "invented prior tutor completion");
    }

    function testSignedRemedyUseAndDebitCommitAtomically() public {
        bytes32 formId = _signedPlace(_terms(), 4, DISCOUNT);
        ConfirmedDiscountObserver policy = new ConfirmedDiscountObserver(booking);
        changes.bindRemedyBooking(ISparkV15RemedyBooking(address(policy)));
        _recharge(CUSTOMER, 2, 0);
        requestVm.expectRevert(SparkV15Funds.InsufficientFunds.selector);
        _confirmOrdinary(formId, bytes32(0), 0);
        require(policy.consumed() == bytes32(0) && booking.getForm(formId).confirmation.confirmedAt == 0, "partial use");
        _recharge(CUSTOMER, 8, 0);
        _confirmOrdinary(formId, bytes32(0), 0);
        require(policy.consumed() == DISCOUNT && funds.creditBalance(funds.creditAccount(CUSTOMER)) == 6, "wrong use");
    }

    function testConfirmationChargesExactlyTheSignedRechargeAndCompensationSources() public {
        bytes32 firstLesson = keccak256("first compensation origin");
        bytes32 secondLesson = keccak256("other compensation origin");
        bytes32 originalPlace = keccak256("affected place");
        _provideProviderFunds(10);
        bytes32 compensationRole = funds.COMPENSATION_ROLE();
        identityRegistry.assignSubject(
            address(this),
            SparkV15.APP_ID,
            compensationRole,
            keccak256("verified credit source fixture"),
            "test:credit source fixture"
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, compensationRole, funds.ACTION_GRANT_COMPENSATION(), true);
        funds.grantCompensationCredit(firstLesson, originalPlace, CUSTOMER, 5);
        funds.grantCompensationCredit(secondLesson, originalPlace, CUSTOMER, 5);
        uint256 receipt = _recharge(CUSTOMER, 3, 3);

        SparkV15Funds.RechargeDebit[] memory recharges = new SparkV15Funds.RechargeDebit[](1);
        recharges[0] = SparkV15Funds.RechargeDebit(receipt, 3);
        SparkV15Funds.CompensationDebit[] memory compensation = new SparkV15Funds.CompensationDebit[](1);
        compensation[0] = SparkV15Funds.CompensationDebit(firstLesson, originalPlace, 5);
        bytes32 creditScheme = keccak256("spark.v1.5.booking.credit-sources");
        bytes memory signedSources = abi.encode(creditScheme, recharges, compensation);
        SparkV15Booking.PlaceTerms memory place = _placeTerms(PLACE, 8);
        place.rechargeDebitsHash = keccak256(signedSources);
        bytes32 formId = _signedPlaceFromTerms(_terms(), place);

        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        _confirmOrdinary(formId, bytes32(0), 0);
        compensation[0].originalLessonId = secondLesson;
        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.confirmPlaceFromCredits(formId, abi.encode(creditScheme, recharges, compensation));
        requestVm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        requestVm.prank(PAYER);
        booking.confirmPlaceFromCredits(formId, signedSources);
        SparkV15BookingCreditSelection selections = changes.CREDIT_SELECTIONS();
        requestVm.expectRevert(SparkV15BookingCreditSelection.InvalidCreditSelection.selector);
        requestVm.prank(PAYER);
        selections.charge(formId, signedSources);

        requestVm.prank(SOURCE_ACTOR);
        booking.confirmPlaceFromCredits(formId, signedSources);
        require(funds.compensationCreditRemaining(firstLesson, originalPlace) == 0, "selected credit not debited");
        require(funds.compensationCreditRemaining(secondLesson, originalPlace) == 5, "other credit was debited");
        require(funds.getRechargeReceipt(receipt).unspentForReturn == 0, "selected recharge not debited");
        require(booking.getForm(formId).confirmation.debitedUnits == 8, "wrong recorded fee");
    }

    function testPaidFormRequiresTheCustomerOrDesignatedPayerAccount() public {
        _publishLesson(false);
        SparkV15Booking.PlaceTerms memory place = _placeTerms(PLACE, 8);
        place.creditAccount = funds.creditAccount(STUDENT);
        requestVm.expectRevert(SparkV15Booking.InvalidForm.selector);
        _publishForm(place);

        place.creditAccount = funds.creditAccount(PAYER);
        bytes32 formId = _publishForm(place);
        require(booking.getForm(formId).terms.creditAccount == place.creditAccount, "payer account was lost");
    }

    function _confirmNext(bytes32 formId) private {
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(NEXT_LESSON);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(NEXT_LESSON);
        bytes32[] memory planned = new bytes32[](1);
        planned[0] = formId;
        _provideProviderFunds(28);
        uint256 evidence = _evidence(booking.prefundingCommitment(NEXT_LESSON, planned, 28, FUNDING_CHECK));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(NEXT_LESSON, planned, 28, FUNDING_CHECK, evidence);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        _acceptForm(formId, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);
        _acceptForm(formId, PAYER, SparkV15Booking.Acceptance.Payer);
        _recharge(CUSTOMER, 9, 0);
        _confirmOrdinary(formId, bytes32(0), 0);
    }

    function _fundedGroup(uint64 noFaultDeadline) private returns (bytes32 first, bytes32 second) {
        _publishLesson(true);
        SparkV15BookingChanges.ChangeTerms memory terms = _terms();
        terms.noFaultAcceptanceDeadline = noFaultDeadline;
        SparkV15Booking.PlaceTerms memory place = _placeTerms(PLACE, 8);
        place.changeTermsRef = changes.changeTermsCommitment(terms);
        first = _publishForm(place);
        place.placeId = keccak256("other group place");
        place.student = OTHER_STUDENT;
        place.payer = OTHER_PAYER;
        second = _publishForm(place);
        changes.admitChangeTerms(first, terms);
        changes.admitChangeTerms(second, terms);
        bytes32[] memory planned = new bytes32[](2);
        planned[0] = first;
        planned[1] = second;
        _provideProviderFunds(48);
        uint256 evidence = _evidence(booking.prefundingCommitment(LESSON, planned, 48, FUNDING_CHECK));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, planned, 48, FUNDING_CHECK, evidence);

        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(LESSON);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(LESSON);
        for (uint256 i; i < planned.length; ++i) {
            _provideTerms(planned[i], CUSTOMER);
            _provideTerms(planned[i], TUTOR);
            _acceptForm(planned[i], PROVIDER, SparkV15Booking.Acceptance.Provider);
            _acceptForm(planned[i], CUSTOMER, SparkV15Booking.Acceptance.Customer);
            _acceptForm(planned[i], TUTOR, SparkV15Booking.Acceptance.Tutor);
        }
        _acceptForm(first, PAYER, SparkV15Booking.Acceptance.Payer);
        _acceptForm(second, OTHER_PAYER, SparkV15Booking.Acceptance.Payer);
        _recharge(CUSTOMER, 16, 0);
        requestVm.warp(EPOCH + 2);
        _confirmOrdinary(first, bytes32(0), 0);
    }

    function _acceptGroupDate(bytes32 changeId, bytes32 first) private {
        requestVm.prank(PAYER);
        changes.acceptPlace(changeId, first);
        requestVm.prank(TUTOR);
        changes.acceptTutor(changeId);
        requestVm.prank(PROVIDER);
        changes.acceptProvider(changeId);
    }

    function _nextGroupDate() private pure returns (SparkV15BookingChanges.ArrangementTerms memory next) {
        next.startsAt = LESSON_START + 1 days;
        next.endsAt = LESSON_END + 1 days;
        next.timeZoneRef = OLD_ZONE;
        next.effectiveAt = EPOCH + 20;
    }

    function _disrupt(bytes32 formId) private {
        _disruptAt(formId, EPOCH + 3);
    }

    function _disruptAt(bytes32 formId, uint64 verifiedAt) private {
        requestVm.warp(verifiedAt + 2);
        SparkV15BookingCancellations.DisruptionWitness memory facts = _disruptionFacts(verifiedAt);
        uint256 evidence = _evidence(cancellations.disruptionCommitment(formId, facts));
        requestVm.prank(VERIFIER_ACTOR);
        cancellations.recordNoFaultDisruption(formId, facts, evidence);
    }

    function _disruptionFacts(uint64 verifiedAt)
        private
        pure
        returns (SparkV15BookingCancellations.DisruptionWitness memory)
    {
        SparkV15BookingCancellations.RearrangementContact[] memory contacts =
            new SparkV15BookingCancellations.RearrangementContact[](1);
        contacts[0] = SparkV15BookingCancellations.RearrangementContact(CUSTOMER, verifiedAt + 1, CONTACT);
        return SparkV15BookingCancellations.DisruptionWitness(
            verifiedAt, true, false, keccak256("verified no-fault disruption"), contacts
        );
    }

    function _terms() private pure returns (SparkV15BookingChanges.ChangeTerms memory terms) {
        terms.reschedule = SparkV15BookingChanges.Window({
            closeMode: SparkV15BookingChanges.ClockMode.Fixed,
            close: LESSON_START + 2 days,
            openMode: SparkV15BookingChanges.ClockMode.None,
            open: 0
        });
        terms.noFaultAcceptanceDeadline = ROSTER_LOCK;
        terms.noFaultTermsRef = keccak256("agreed no-fault cancellation terms");
        terms.refund = SparkV15BookingChanges.RefundTiming(1 hours, 2 hours, 0, 1 hours, true);
    }

    function _confirmedPlace(SparkV15BookingChanges.ChangeTerms memory terms) private returns (bytes32 formId) {
        formId = _signedPlace(terms, 8, bytes32(0));
        _recharge(CUSTOMER, 8, 0);
        _confirmOrdinary(formId, bytes32(0), 0);
    }

    function _signedPlace(SparkV15BookingChanges.ChangeTerms memory terms, uint128 payableFee, bytes32 discountId)
        private
        returns (bytes32 formId)
    {
        SparkV15Booking.PlaceTerms memory place = _placeTerms(PLACE, payableFee);
        place.remedyDiscountId = discountId;
        return _signedPlaceFromTerms(terms, place);
    }

    function _signedPlaceFromTerms(
        SparkV15BookingChanges.ChangeTerms memory terms,
        SparkV15Booking.PlaceTerms memory place
    ) private returns (bytes32 formId) {
        _publishLesson(false);
        place.changeTermsRef = changes.changeTermsCommitment(terms);
        formId = _publishForm(place);
        changes.admitChangeTerms(formId, terms);
        _fundAndSignAgreement(formId);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        _acceptForm(formId, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);
        _acceptForm(formId, PAYER, SparkV15Booking.Acceptance.Payer);
    }

    function _propose(SparkV15BookingChanges.ArrangementTerms memory next) private returns (bytes32) {
        uint64 contactedAt = uint64(block.timestamp);
        uint256 evidence = _evidence(changes.proposalCommitment(LESSON, next, contactedAt, CONTACT));
        requestVm.prank(SOURCE_ACTOR);
        return changes.proposeArrangement(LESSON, next, contactedAt, CONTACT, evidence);
    }
}

contract ConfirmedDiscountObserver {
    SparkV15Booking public immutable BOOKING;
    bytes32 public consumed;

    constructor(SparkV15Booking booking) {
        BOOKING = booking;
    }

    function consumeBookingDiscount(bytes32 formId) external {
        require(msg.sender == address(BOOKING.bookingChanges()), "wrong caller");
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        require(form.confirmation.debitedUnits == 4 && form.confirmation.confirmedAt != 0, "missing signed form effect");
        require(consumed == bytes32(0) && form.terms.remedyDiscountId != bytes32(0), "unavailable entitlement");
        consumed = form.terms.remedyDiscountId;
    }
}
