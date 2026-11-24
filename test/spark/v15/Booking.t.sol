// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15, SparkV15ApplicationModule} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {ISparkV15BookingFunds, SparkV15Booking, SparkV15BookingOpening} from "../../../src/apps/spark/v15/SparkV15Booking.sol";
import {SparkV15BookingPrefunding} from "../../../src/apps/spark/v15/SparkV15BookingPrefunding.sol";
import {SparkV15CourseNotices} from "../../../src/apps/spark/v15/SparkV15CourseNotices.sol";
import {SparkV15TeachingEnd} from "../../../src/apps/spark/v15/SparkV15TeachingEnd.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {IERC20} from "../../../src/apps/spark/legacy/interfaces/IERC20.sol";
import {RequestAllocationFixture} from "../../helpers/RequestAllocationFixture.sol";
import {MockERC20} from "../mocks/MockERC20.sol";

interface BookingSignatureVm {
    function addr(uint256 privateKey) external returns (address);
    function sign(uint256 privateKey, bytes32 digest) external returns (uint8 v, bytes32 r, bytes32 s);
    function expectRevert(bytes calldata reason) external;
    function snapshotState() external returns (uint256);
    function revertToState(uint256 snapshotId) external returns (bool);
}

abstract contract SparkV15BookingFixture is RequestAllocationFixture {
    uint64 internal constant EPOCH = 1_000_000;
    uint64 internal constant ROSTER_LOCK = EPOCH + 1 days;
    uint64 internal constant LESSON_START = EPOCH + 2 days;
    uint64 internal constant LESSON_END = LESSON_START + 1 hours;
    bytes32 internal constant LESSON = keccak256("a scheduled lesson");
    bytes32 internal constant PLACE = keccak256("one place");
    bytes32 internal constant FORM_DELIVERY = keccak256("verified delivery of form and cited terms");
    bytes32 internal constant FUNDING_CHECK = keccak256("verified formation and scoped prefunding inventory");
    bytes32 internal constant CREDIT_PROVIDER_ID = keccak256("test credit provider");
    bytes32 internal constant NOTICE_DELIVERY = keccak256("coordinator's receipt of delivery to the student");
    bytes32 internal constant REGISTER = keccak256("exact confirmed group register at the agreed lock");
    bytes32 internal constant TUTOR_CHANNEL = keccak256("the tutor's agreed message channel");
    bytes32 internal constant TUTOR_NOTICE = keccak256("actual delivery to the tutor");
    bytes32 internal constant OPENING = keccak256("observed start of the verified teaching occurrence");
    bytes32 internal constant ENDING = keccak256("observed end of the verified teaching occurrence");
    address internal constant PROVIDER = address(0x7101);
    address internal constant TUTOR = address(0x7102);
    address internal constant CUSTOMER = address(0x7103);
    address internal constant REPRESENTATIVE = address(0x7104);
    address internal constant PAYER = address(0x7105);
    address internal constant STUDENT = address(0x7106);
    address internal constant OTHER_PAYER = address(0x7107);
    address internal constant OTHER_STUDENT = address(0x7108);

    MockERC20 internal token;
    SparkV15Funds internal funds;
    SparkV15Payments internal payments;
    SparkV15Booking internal booking;

    function setUp() public virtual {
        requestVm.warp(EPOCH);
        _setUpRequestAllocation(
            SparkV15.APP_ID,
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR),
            SparkV15.OBJECT_PAYMENT_APPROVAL
        );
        token = new MockERC20("Local booking token", "BOOK", 6);
        payments = new SparkV15Payments(requestAllocation, IERC20(address(token)), REQUEST_WORKFLOW, ROLE_VERIFIER);
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
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, booking.ACTION_COORDINATE_BOOKING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, booking.ACTION_VERIFY_PREFUNDING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, booking.ACTION_VERIFY_TEACHING(), true);
        bytes32 bookingRole = funds.BOOKING_ROLE();
        identityRegistry.assignSubject(
            address(booking), SparkV15.APP_ID, bookingRole, keccak256("test booking instance"), "test:booking instance"
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, bookingRole, funds.ACTION_MANAGE_LESSON_FUNDS(), true);
        bytes32 creditProviderRole = funds.CREDIT_PROVIDER_ROLE();
        identityRegistry.assignSubject(
            PROVIDER, SparkV15.APP_ID, creditProviderRole, CREDIT_PROVIDER_ID, "test:credit provider"
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, creditProviderRole, funds.ACTION_OFFER_RECHARGE(), true);
    }

    function _publishLesson(bool group) internal {
        requestVm.prank(SOURCE_ACTOR);
        booking.publishLesson(_lessonTerms(group));
    }

    function _lessonTerms(bool group) internal pure returns (SparkV15Booking.LessonTerms memory) {
        return SparkV15Booking.LessonTerms({
            lessonId: LESSON,
            provider: PROVIDER,
            tutor: TUTOR,
            coordinator: SOURCE_ACTOR,
            startsAt: LESSON_START,
            endsAt: LESSON_END,
            rosterLockAt: group ? ROSTER_LOCK : 0,
            rosterRef: group ? keccak256("private agreed roster") : bytes32(0),
            timeZoneRef: keccak256("UTC"),
            tutorNoticeChannelRef: TUTOR_CHANNEL,
            tutorFee: 8,
            tutorAgreementRef: keccak256("agreed tutor contract"),
            serviceTermsRef: keccak256("agreed service terms and items"),
            tutorPayTermsRef: keccak256("agreed tutor payment times"),
            providerResponsibilitiesRef: keccak256("provider responsibilities"),
            tutorResponsibilitiesRef: keccak256("tutor responsibilities"),
            startTermsRef: keccak256("agreed class formation conditions"),
            documentsRef: keccak256("course terms, applicable deadlines and contacts"),
            materialsTermsRef: bytes32(0)
        });
    }

    function _placeTerms(bytes32 placeId, uint128 payableFee)
        internal
        view
        returns (SparkV15Booking.PlaceTerms memory)
    {
        return SparkV15Booking.PlaceTerms({
            placeId: placeId,
            customer: CUSTOMER,
            customerRepresentative: REPRESENTATIVE,
            payer: PAYER,
            student: STUDENT,
            creditAccount: funds.creditAccount(CUSTOMER),
            studentNoticeChannelRef: keccak256("agreed internal student notice channel"),
            normalFee: 8,
            payableFee: payableFee,
            discountBasis: payableFee < 8 ? keccak256("agreed discount basis") : bytes32(0),
            rechargeDebitsHash: bytes32(0),
            materialsBundleRef: bytes32(0),
            materialPayer: address(0),
            changeTermsRef: bytes32(0),
            remedyDiscountId: bytes32(0)
        });
    }

    function _publishForm(SparkV15Booking.PlaceTerms memory terms) internal returns (bytes32) {
        requestVm.prank(SOURCE_ACTOR);
        return booking.publishForm(LESSON, terms);
    }

    function _provideTerms(bytes32 formId, address recipient) internal {
        bytes32 deliveryRef = keccak256(abi.encode(FORM_DELIVERY, recipient));
        uint256 evidenceId = _evidence(booking.provisionCommitment(formId, recipient, deliveryRef));
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvision(formId, recipient, deliveryRef, evidenceId);
    }

    function _provideProviderFunds(uint128 amount) internal {
        token.mint(PROVIDER, amount);
        requestVm.prank(PROVIDER);
        token.transfer(address(funds), amount);
    }

    function _fundAndSignAgreement(bytes32 formId) internal {
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        _signAgreementAndFund(formId);
    }

    function _signAgreementAndFund(bytes32 formId) internal {
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(LESSON);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(LESSON);
        bytes32[] memory formIds = new bytes32[](1);
        formIds[0] = formId;
        _provideProviderFunds(28);
        uint256 evidenceId = _evidence(booking.prefundingCommitment(LESSON, formIds, 28, FUNDING_CHECK));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, formIds, 28, FUNDING_CHECK, evidenceId);
        requestVm.warp(EPOCH + 2);
    }

    function _acceptForm(bytes32 formId, address signer, SparkV15Booking.Acceptance role) internal {
        requestVm.prank(signer);
        booking.acceptForm(formId, role);
    }

    function _bookOneToOne() internal returns (bytes32 formId) {
        _publishLesson(false);
        formId = _publishForm(_placeTerms(PLACE, 8));
        _fundAndSignAgreement(formId);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        _acceptForm(formId, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);
        _acceptForm(formId, PAYER, SparkV15Booking.Acceptance.Payer);
        _recharge(CUSTOMER, 8, 0);
        _confirmOrdinary(formId, bytes32(0), 0);
    }

    function _studentNotice(bytes32 formId, uint64 deliveredAt) internal {
        uint256 evidence = _evidence(booking.studentNoticeCommitment(formId, deliveredAt, NOTICE_DELIVERY));
        requestVm.prank(SOURCE_ACTOR);
        booking.recordStudentNotice(formId, deliveredAt, NOTICE_DELIVERY, evidence);
    }

    function _tutorNotice(uint64 deliveredAt) internal {
        uint256 evidence = _evidence(booking.tutorNoticeCommitment(LESSON, TUTOR_CHANNEL, deliveredAt, TUTOR_NOTICE));
        requestVm.prank(PROVIDER);
        booking.recordTutorNotice(LESSON, TUTOR_CHANNEL, deliveredAt, TUTOR_NOTICE, evidence);
    }

    function _recordOpening(uint64 occurredAt, bytes32 unmetConditionRef) internal returns (uint256 evidenceId) {
        address[] memory students = new address[](1);
        students[0] = STUDENT;
        SparkV15Booking.StartObservation memory observation =
            SparkV15Booking.StartObservation(occurredAt, true, students, OPENING, unmetConditionRef);
        evidenceId = _evidence(booking.teachingStartCommitment(LESSON, observation));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingStarted(LESSON, observation, evidenceId);
    }

    function _recordEnding(uint64 occurredAt) internal returns (uint256 evidenceId) {
        evidenceId = _evidence(booking.teachingEndCommitment(LESSON, occurredAt, ENDING));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingEnded(LESSON, occurredAt, ENDING, evidenceId);
    }

    function _confirmOrdinary(bytes32 formId, bytes32 discountRef, uint256 discountEvidenceId) internal {
        SparkV15Funds.RechargeDebit[] memory noRechargeDebits = new SparkV15Funds.RechargeDebit[](0);
        requestVm.prank(SOURCE_ACTOR);
        booking.confirmPlace(formId, discountRef, discountEvidenceId, noRechargeDebits);
    }

    function _recharge(address owner, uint128 amount, uint128 returnCap) internal returns (uint256 receiptId) {
        requestVm.prank(PROVIDER);
        bytes32 offer = funds.offerRecharge(
            SparkV15Funds.RechargeTerms(
                owner, amount, returnCap, returnCap == 0 ? 0 : EPOCH + 1 days, keccak256("agreed recharge terms")
            ),
            CREDIT_PROVIDER_ID
        );
        token.mint(owner, amount);
        requestVm.startPrank(owner);
        token.approve(address(funds), amount);
        receiptId = funds.recharge(offer);
        requestVm.stopPrank();
    }

    function _evidence(bytes32 commitment) internal returns (uint256) {
        requestVm.prank(SOURCE_ACTOR);
        return evidenceRegistry.registerEvidence(_bookingEvidenceInput(commitment));
    }

    function _bookingEvidenceInput(bytes32 commitment)
        internal
        view
        returns (AVAEvidenceRegistry.EvidenceRegistrationInput memory)
    {
        return AVAEvidenceRegistry.EvidenceRegistrationInput({
                appId: SparkV15.APP_ID,
                workflowKey: REQUEST_WORKFLOW,
                packageId: requestPackageId,
                roleKey: ROLE_SOURCE,
                subjectId: _authority(ROLE_SOURCE),
                commitment: commitment,
                evidenceTypeHash: keccak256("spark.v1.5.booking.receipt"),
                disclosurePolicyId: requestPolicyId,
                authorityId: _authority(ROLE_SOURCE),
                uri: "test:verified-booking-receipt"
            });
    }
}

contract BookingTest is SparkV15BookingFixture {
    BookingSignatureVm private constant signatures =
        BookingSignatureVm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 private constant DELIVERY_SOURCE_KEY = 0x7111;
    bytes32 private constant DELIVERY_SOURCE_ID = keccak256("test terms delivery source");
    bytes32 private constant TERMS_CONSENT_TYPEHASH = keccak256(
        "TermsProvisionConsent(uint256 packageId,bytes32 formId,address recipient,bytes32 deliveryRef,address coordinator,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId)"
    );

    function testTermsConsentFirstAdoptionAllowsAcceptanceWithoutRegisteringEvidence() public {
        _publishLesson(false);
        bytes32 formId = _publishForm(_placeTerms(PLACE, 8));
        _assignDeliverySource();
        SparkV15Booking.TermsProvisionConsent memory consent = _termsConsent(formId, CUSTOMER, SOURCE_ACTOR);
        SparkV15Booking.TermsProvisionConsent memory tutorConsent = _termsConsent(formId, TUTOR, SOURCE_ACTOR);
        uint256 nextEvidenceId = evidenceRegistry.nextEvidenceId();

        requestVm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);
        requestVm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, TUTOR, FORM_DELIVERY, tutorConsent);

        require(booking.hasTermsProvision(formId, CUSTOMER) && booking.hasTermsProvision(formId, TUTOR), "delivery missing");
        require(booking.termsProvisionEvidence(formId, CUSTOMER) == 0, "adoption acquired a Core evidence ID");
        require(evidenceRegistry.nextEvidenceId() == nextEvidenceId, "adoption registered reusable evidence");
        _signAgreementAndFund(formId);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        _acceptForm(formId, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);
        _acceptForm(formId, PAYER, SparkV15Booking.Acceptance.Payer);
        _recharge(CUSTOMER, 8, 0);
        _confirmOrdinary(formId, bytes32(0), 0);
        require(booking.getForm(formId).confirmation.debitedUnits == 8, "ordinary debit missing");
    }

    function testStandaloneTermsDeliveryBecomesUnavailableWhenItsSourceLeaves() public {
        _publishLesson(false);
        bytes32 formId = _publishForm(_placeTerms(PLACE, 8));
        _provideTerms(formId, CUSTOMER);
        _assignDeliverySource();
        SparkV15Booking.TermsProvisionConsent memory consent = _termsConsent(formId, TUTOR, SOURCE_ACTOR);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, TUTOR, FORM_DELIVERY, consent);
        _signAgreementAndFund(formId);
        _acceptForm(formId, CUSTOMER, SparkV15Booking.Acceptance.Customer);

        identityRegistry.deactivateSubject(DELIVERY_SOURCE_ID);
        requestVm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);

        (address signer,) = booking.acceptances(formId, SparkV15Booking.Acceptance.Customer);
        require(signer == CUSTOMER && booking.hasTermsProvision(formId, TUTOR), "acceptance or delivery history lost");
        require(booking.OPENING().hasUsableTermsProvision(formId, CUSTOMER, requestPackageId), "unrelated receipt lost");
    }

    function testTermsConsentRequiresBothCurrentActors() public {
        _publishLesson(false);
        bytes32 formId = _publishForm(_placeTerms(PLACE, 8));
        SparkV15Booking.TermsProvisionConsent memory consent = _termsConsent(formId, CUSTOMER, SOURCE_ACTOR);
        address source = signatures.addr(DELIVERY_SOURCE_KEY);
        bytes32 sourceAction = AVACoreTypes.ACTION_REGISTER_EVIDENCE;
        bytes32 coordinateAction = booking.ACTION_COORDINATE_BOOKING();

        signatures.expectRevert(abi.encodeWithSelector(AVACoreTypes.NotAuthorised.selector, source, sourceAction));
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);
        _assignDeliverySource();
        requestVm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        requestVm.prank(source);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);

        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, coordinateAction, false);
        signatures.expectRevert(abi.encodeWithSelector(AVACoreTypes.NotAuthorised.selector, SOURCE_ACTOR, coordinateAction));
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, coordinateAction, true);

        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, sourceAction, false);
        signatures.expectRevert(abi.encodeWithSelector(AVACoreTypes.NotAuthorised.selector, source, sourceAction));
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);
        require(!booking.hasTermsProvision(formId, CUSTOMER), "failed checks recorded delivery");
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, sourceAction, true);

        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);
        require(booking.hasTermsProvision(formId, CUSTOMER), "current dual authority failed");
    }

    function testTermsConsentCannotMoveToASupersedingFormOrFollowAnAcceptance() public {
        _publishLesson(false);
        SparkV15Booking.PlaceTerms memory terms = _placeTerms(PLACE, 8);
        bytes32 previous = _publishForm(terms);
        _assignDeliverySource();
        SparkV15Booking.TermsProvisionConsent memory consent = _termsConsent(previous, CUSTOMER, SOURCE_ACTOR);
        terms.payableFee = 6;
        terms.discountBasis = keccak256("agreed partial discount");
        bytes32 formId = _publishForm(terms);

        requestVm.expectRevert(SparkV15Booking.InvalidForm.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(previous, CUSTOMER, FORM_DELIVERY, consent);
        requestVm.expectRevert();
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);
        require(!booking.hasTermsProvision(formId, CUSTOMER), "old signature crossed a revision");

        consent = _termsConsent(formId, CUSTOMER, SOURCE_ACTOR);
        requestVm.expectRevert();
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, TUTOR, FORM_DELIVERY, consent);
        requestVm.expectRevert();
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, keccak256("different delivery"), consent);

        _provideTerms(formId, CUSTOMER);
        require(booking.hasTermsProvision(formId, CUSTOMER), "legacy delivery missing");
        require(booking.termsProvisionEvidence(formId, CUSTOMER) != 0, "legacy evidence ID lost");
        consent = _termsConsent(formId, TUTOR, SOURCE_ACTOR);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        requestVm.expectRevert(SparkV15Booking.InvalidForm.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, TUTOR, FORM_DELIVERY, consent);
        require(!booking.hasTermsProvision(formId, TUTOR), "prior acceptance allowed retrospective adoption");
        _provideTerms(formId, TUTOR);
        require(booking.hasTermsProvision(formId, TUTOR), "legacy recording order changed");
    }

    function testTermsConsentRequiresTheCurrentPackageWhileExistingEvidenceRetainsItsScope() public {
        _publishLesson(false);
        bytes32 formId = _publishForm(_placeTerms(PLACE, 8));
        _assignDeliverySource();
        SparkV15Booking.TermsProvisionConsent memory consent = _termsConsent(formId, CUSTOMER, SOURCE_ACTOR);
        uint256 evidenceId = _evidence(booking.provisionCommitment(formId, CUSTOMER, FORM_DELIVERY));

        uint256 newPackage = _registerRequestPackage(
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR), 2
        );
        require(newPackage != requestPackageId, "package did not advance");
        signatures.expectRevert(abi.encodeWithSelector(AVACoreTypes.InvalidState.selector, requestPackageId));
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);

        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvision(formId, CUSTOMER, FORM_DELIVERY, evidenceId);
        require(booking.termsProvisionEvidence(formId, CUSTOMER) == evidenceId, "old evidence was lost");
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
    }

    function testTermsConsentIsLimitedToLessonsWithoutMaterialTerms() public {
        SparkV15Booking.LessonTerms memory lesson = _lessonTerms(false);
        lesson.materialsTermsRef = keccak256("existing lesson material terms");
        requestVm.prank(SOURCE_ACTOR);
        booking.publishLesson(lesson);
        bytes32 formId = _publishForm(_placeTerms(PLACE, 8));
        _assignDeliverySource();
        SparkV15Booking.TermsProvisionConsent memory consent = _termsConsent(formId, CUSTOMER, SOURCE_ACTOR);

        requestVm.expectRevert(SparkV15Booking.InvalidForm.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);
        _provideTerms(formId, CUSTOMER);
        require(booking.termsProvisionEvidence(formId, CUSTOMER) != 0, "legacy material lesson delivery lost");
    }

    function testTermsConsentCannotUseTheCoordinatorAsTheSource() public {
        _assignDeliverySource();
        address source = signatures.addr(DELIVERY_SOURCE_KEY);
        SparkV15Booking.LessonTerms memory lesson = _lessonTerms(false);
        lesson.coordinator = source;
        SparkV15Booking.PlaceTerms memory terms = _placeTerms(PLACE, 8);
        requestVm.prank(source);
        booking.publishLesson(lesson);
        requestVm.prank(source);
        bytes32 formId = booking.publishForm(LESSON, terms);
        SparkV15Booking.TermsProvisionConsent memory consent = _termsConsent(formId, CUSTOMER, source);

        requestVm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        requestVm.prank(source);
        booking.recordTermsProvisionWithConsent(formId, CUSTOMER, FORM_DELIVERY, consent);
    }

    function _assignDeliverySource() private {
        identityRegistry.assignSubject(
            signatures.addr(DELIVERY_SOURCE_KEY), SparkV15.APP_ID, ROLE_SOURCE, DELIVERY_SOURCE_ID, "test:delivery source"
        );
    }

    function _termsConsent(bytes32 formId, address recipient, address coordinator)
        private
        returns (SparkV15Booking.TermsProvisionConsent memory consent)
    {
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256("Spark DAO Terms Delivery"),
                keccak256("1"),
                block.chainid,
                booking
            )
        );
        bytes32 message = keccak256(
            abi.encode(
                TERMS_CONSENT_TYPEHASH,
                requestPackageId,
                formId,
                recipient,
                FORM_DELIVERY,
                coordinator,
                ROLE_SOURCE,
                DELIVERY_SOURCE_ID,
                requestPolicyId
            )
        );
        (uint8 v, bytes32 r, bytes32 s) = signatures.sign(
            DELIVERY_SOURCE_KEY, keccak256(abi.encodePacked(hex"1901", domain, message))
        );
        return SparkV15Booking.TermsProvisionConsent(
            ROLE_SOURCE, DELIVERY_SOURCE_ID, requestPolicyId, r, bytes32(uint256(s) | ((uint256(v) - 27) << 255))
        );
    }

    function testOnlyTheCurrentFormCanBeAcceptedAndItsOwnProvisionMustBeEvidenced() public {
        _publishLesson(false);
        SparkV15Booking.PlaceTerms memory terms = _placeTerms(PLACE, 8);
        bytes32 first = _publishForm(terms);
        uint256 firstDelivery = _evidence(booking.provisionCommitment(first, CUSTOMER, FORM_DELIVERY));

        terms.payableFee = 6;
        terms.discountBasis = keccak256("agreed partial discount");
        bytes32 second = _publishForm(terms);
        require(booking.getForm(first).version == 1 && booking.getForm(second).version == 2, "lost form version");

        requestVm.expectRevert(SparkV15Booking.InvalidForm.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvision(first, CUSTOMER, FORM_DELIVERY, firstDelivery);
        requestVm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordTermsProvision(second, CUSTOMER, FORM_DELIVERY, firstDelivery);

        _provideTerms(second, CUSTOMER);
        requestVm.prank(PROVIDER);
        booking.acceptForm(second, SparkV15Booking.Acceptance.Provider);
        (address signer,) = booking.acceptances(second, SparkV15Booking.Acceptance.Provider);
        require(signer == PROVIDER, "provider approval missing");
    }

    function testTermsDeliveryLifecyclePreservesHistoryAndRequiresTheExactCurrentBasis() public {
        _publishLesson(false);
        bytes32 formId = _publishForm(_placeTerms(PLACE, 8));
        _fundAndSignAgreement(formId);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        _acceptForm(formId, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        _acceptForm(formId, PAYER, SparkV15Booking.Acceptance.Payer);
        _recharge(CUSTOMER, 8, 0);
        uint256 evidenceId = booking.termsProvisionEvidence(formId, TUTOR);
        require(evidenceId != 0);

        requestVm.warp(EPOCH + 3);
        uint256 beforeTutorAcceptance = signatures.snapshotState();
        _recordDeliveryLifecycle(evidenceId, AVACoreTypes.EvidenceLifecycleKind.Revoke, 0);
        requestVm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);
        require(signatures.revertToState(beforeTutorAcceptance));
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);

        uint256 beforeAlternatives = signatures.snapshotState();
        uint256 wrongRecipient = booking.termsProvisionEvidence(formId, CUSTOMER);
        _recordDeliveryLifecycle(evidenceId, AVACoreTypes.EvidenceLifecycleKind.Supersede, wrongRecipient);
        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        _confirmOrdinary(formId, bytes32(0), 0);
        require(booking.termsProvisionEvidence(formId, TUTOR) == evidenceId, "delivery history lost");
        require(booking.getForm(formId).confirmation.confirmedAt == 0, "invalid evidence confirmed the place");
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == 8, "failed booking debited original account");
        require(funds.lessonReserved(LESSON) == 28, "failed booking changed prior reserve");
        require(signatures.revertToState(beforeAlternatives));

        bytes32 deliveryRef = keccak256(abi.encode(FORM_DELIVERY, TUTOR));
        bytes32 commitment = booking.provisionCommitment(formId, TUTOR, deliveryRef);
        _assertCorrectionCannotReplaceTerms(formId, evidenceId, commitment);

        uint256 exactReplacement = _evidence(commitment);
        _recordDeliveryLifecycle(evidenceId, AVACoreTypes.EvidenceLifecycleKind.Supersede, exactReplacement);
        require(booking.OPENING().hasUsableTermsProvision(formId, TUTOR, requestPackageId));
        uint256 finalReplacement = _evidence(commitment);
        _recordDeliveryLifecycle(exactReplacement, AVACoreTypes.EvidenceLifecycleKind.Supersede, finalReplacement);
        uint256 beforeFinalRevoke = signatures.snapshotState();
        _recordDeliveryLifecycle(finalReplacement, AVACoreTypes.EvidenceLifecycleKind.Revoke, 0);
        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        _confirmOrdinary(formId, bytes32(0), 0);
        require(signatures.revertToState(beforeFinalRevoke));

        _confirmOrdinary(formId, bytes32(0), 0);
        require(booking.getForm(formId).confirmation.debitedUnits == 8, "second usable replacement did not support debit");
        require(booking.termsProvisionEvidence(formId, TUTOR) == evidenceId, "replacement overwrote prior delivery");
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == 0, "original account not charged");
    }

    function _assertCorrectionCannotReplaceTerms(bytes32 formId, uint256 evidenceId, bytes32 commitment) private {
        uint256 beforeCorrection = signatures.snapshotState();
        uint256 admissionPackage = _registerRequestPackage(
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR), 2
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, evidenceRegistry.ACTION_REGISTER_CORRECTION_EVIDENCE(), true);
        requestVm.prank(SOURCE_ACTOR);
        uint256 correction = evidenceRegistry.registerCorrectionEvidence(
            _bookingEvidenceInput(commitment), admissionPackage, keccak256("separate original-record correction")
        );
        _recordDeliveryLifecycle(evidenceId, AVACoreTypes.EvidenceLifecycleKind.Supersede, correction);
        require(evidenceRegistry.isCorrectionEvidence(correction));
        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        _confirmOrdinary(formId, bytes32(0), 0);
        require(signatures.revertToState(beforeCorrection));
    }

    function _recordDeliveryLifecycle(uint256 evidenceId, AVACoreTypes.EvidenceLifecycleKind kind, uint256 replacement)
        private
    {
        requestVm.prank(SOURCE_ACTOR);
        evidenceRegistry.recordEvidenceLifecycle(
            evidenceId,
            ROLE_SOURCE,
            _authority(ROLE_SOURCE),
            kind,
            replacement,
            keccak256("updated independently verified delivery basis"),
            "test:delivery evidence lifecycle"
        );
    }

    function testPublishedLessonKeepsExactSharedAndDistinctDocumentReferences() public {
        SparkV15Booking.Lesson memory absent = booking.getLesson(LESSON);
        SparkV15Booking.LessonTerms memory empty;
        require(absent.packageId == 0 && keccak256(abi.encode(absent.terms)) == keccak256(abi.encode(empty)));

        SparkV15Booking.LessonTerms memory terms = _lessonTerms(false);
        terms.providerResponsibilitiesRef = terms.documentsRef;
        terms.startTermsRef = terms.documentsRef;
        requestVm.prank(SOURCE_ACTOR);
        booking.publishLesson(terms);

        SparkV15Booking.Lesson memory stored = booking.getLesson(LESSON);
        require(stored.packageId != 0 && keccak256(abi.encode(stored.terms)) == keccak256(abi.encode(terms)));
        require(stored.commitment == keccak256(abi.encode(block.chainid, address(booking), stored.packageId, terms)));
    }

    function testCoordinatorCannotNameAnotherProviderForThisTreasury() public {
        SparkV15Booking.LessonTerms memory terms = _lessonTerms(false);
        terms.provider = OTHER_PAYER;
        requestVm.expectRevert(SparkV15Booking.InvalidLesson.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.publishLesson(terms);
    }

    function testTutorAndCustomerCannotCommitBeforeEvidenceAndSpendableProviderFunds() public {
        _publishLesson(false);
        bytes32 formId = _publishForm(_placeTerms(PLACE, 8));
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(LESSON);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(LESSON);
        bytes32[] memory formIds = new bytes32[](1);
        formIds[0] = formId;
        bytes32 prematureCheck = keccak256("anticipated funds before the deposit reached the treasury");
        uint256 prematureEvidence = _evidence(booking.prefundingCommitment(LESSON, formIds, 28, prematureCheck));

        requestVm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
        requestVm.prank(CUSTOMER);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Customer);
        requestVm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
        requestVm.prank(TUTOR);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Tutor);
        requestVm.expectRevert(SparkV15Funds.InsufficientFunds.selector);
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, formIds, 28, prematureCheck, prematureEvidence);

        requestVm.warp(EPOCH + 1);
        _provideProviderFunds(28);
        uint256 fundingEvidence = _evidence(booking.prefundingCommitment(LESSON, formIds, 28, FUNDING_CHECK));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, formIds, 28, FUNDING_CHECK, fundingEvidence);
        require(funds.lessonReserved(LESSON) == 28, "provider funds were not reserved");

        requestVm.warp(EPOCH + 2);
        requestVm.prank(CUSTOMER);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Customer);
        requestVm.prank(TUTOR);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Tutor);

        (address customer, uint64 acceptedAt) = booking.acceptances(formId, SparkV15Booking.Acceptance.Customer);
        require(customer == CUSTOMER && acceptedAt == EPOCH + 2, "wrong customer acceptance time");
        SparkV15Booking.FundingCheck memory funding = booking.getLesson(LESSON).prefunding;
        require(funding.evidenceId == fundingEvidence && funding.checkedAt == EPOCH + 1, "funding chronology lost");
    }

    function testSinglePlaceFundingDoesNotCoverADifferentFormForTheSameStudent() public {
        _publishLesson(false);
        bytes32 fundedForm = _publishForm(_placeTerms(PLACE, 8));
        bytes32 otherForm = _publishForm(_placeTerms(keccak256("unfunded second place"), 8));
        _fundAndSignAgreement(fundedForm);
        _provideTerms(otherForm, CUSTOMER);
        _provideTerms(otherForm, TUTOR);

        requestVm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
        _acceptForm(otherForm, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        requestVm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
        _acceptForm(otherForm, TUTOR, SparkV15Booking.Acceptance.Tutor);
        _acceptForm(fundedForm, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        _acceptForm(fundedForm, TUTOR, SparkV15Booking.Acceptance.Tutor);

        (bytes32 planned, uint64 confirmedAt) = booking.getStudentConfirmation(LESSON, STUDENT);
        require(planned == fundedForm && confirmedAt == 0, "selected form or confirmation changed");
        require(!booking.getForm(otherForm).hasAcceptance, "unfunded form gained acceptance");
        require(funds.lessonReserved(LESSON) == 28, "acceptance changed the shared reserve");
    }

    function testDesignatedPayerAndAuthorisedRepresentativeConfirmExactDebitWithSeparateStudentNotice() public {
        _publishLesson(false);
        bytes32 formId = _publishForm(_placeTerms(PLACE, 6));
        _fundAndSignAgreement(formId);

        requestVm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        requestVm.prank(REPRESENTATIVE);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Customer);
        requestVm.prank(CUSTOMER);
        booking.authoriseRepresentative(formId);
        _provideTerms(formId, REPRESENTATIVE);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        _acceptForm(formId, REPRESENTATIVE, SparkV15Booking.Acceptance.Customer);
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);

        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        _confirmOrdinary(formId, bytes32(0), 0);
        _recharge(OTHER_PAYER, 2, 0);
        requestVm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        requestVm.prank(OTHER_PAYER);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Payer);
        _acceptForm(formId, PAYER, SparkV15Booking.Acceptance.Payer);

        bytes32 account = funds.creditAccount(CUSTOMER);
        requestVm.expectRevert(SparkV15Funds.InsufficientFunds.selector);
        _confirmOrdinary(formId, bytes32(0), 0);
        require(booking.getForm(formId).confirmation.confirmedAt == 0, "booked despite failed debit");
        _recharge(CUSTOMER, 10, 0);
        _confirmOrdinary(formId, bytes32(0), 0);
        SparkV15Booking.Confirmation memory confirmation = booking.getForm(formId).confirmation;
        require(confirmation.debitedUnits == 6 && funds.creditBalance(account) == 4, "debit does not match payable fee");
        require(funds.lessonReserved(LESSON) == 34, "debit not held against lesson");

        uint64 deliveredAt = EPOCH + 3;
        requestVm.warp(EPOCH + 4);
        uint256 provisionEvidence = booking.termsProvisionEvidence(formId, REPRESENTATIVE);
        requestVm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordStudentNotice(formId, deliveredAt, NOTICE_DELIVERY, provisionEvidence);
        uint256 noticeEvidence = _evidence(booking.studentNoticeCommitment(formId, deliveredAt, NOTICE_DELIVERY));
        requestVm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        requestVm.prank(PAYER);
        booking.recordStudentNotice(formId, deliveredAt, NOTICE_DELIVERY, noticeEvidence);
        requestVm.prank(SOURCE_ACTOR);
        booking.recordStudentNotice(formId, deliveredAt, NOTICE_DELIVERY, noticeEvidence);
        SparkV15Booking.StudentNotice memory notice = booking.getStudentNotice(formId);
        require(notice.evidenceId == noticeEvidence && notice.sender == SOURCE_ACTOR, "missing signed notice");
        require(notice.deliveredAt == deliveredAt && notice.recordedAt == EPOCH + 4, "notice chronology lost");
    }

    function testVerifiedFullDiscountConfirmsWithNoDebitOrCreditTopUp() public {
        _publishLesson(false);
        bytes32 formId = _publishForm(_placeTerms(PLACE, 0));
        _fundAndSignAgreement(formId);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        _acceptForm(formId, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);
        _acceptForm(formId, PAYER, SparkV15Booking.Acceptance.Payer);

        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        _confirmOrdinary(formId, bytes32(0), 0);
        bytes32 proofRef = keccak256("receipt for the applicable full discount on this form");
        uint256 evidenceId = _evidence(booking.fullDiscountCommitment(formId, proofRef));
        _confirmOrdinary(formId, proofRef, evidenceId);

        SparkV15Booking.Confirmation memory confirmation = booking.getForm(formId).confirmation;
        require(confirmation.confirmedAt == EPOCH + 2 && confirmation.discountEvidenceId == evidenceId, "discount lost");
        require(confirmation.debitedUnits == 0 && funds.lessonReserved(LESSON) == 28, "full discount debited credit");
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == 0, "unexpected top-up");
        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        _confirmOrdinary(formId, proofRef, evidenceId);
    }

    function testConfirmationUsesOnlyTheRechargeReceiptNamedInTheSignedForm() public {
        _publishLesson(false);
        uint256 unselected = _recharge(CUSTOMER, 10, 10);
        uint256 selected = _recharge(CUSTOMER, 9, 9);
        SparkV15Booking.PlaceTerms memory terms = _placeTerms(PLACE, 6);
        SparkV15Funds.RechargeDebit[] memory debits = new SparkV15Funds.RechargeDebit[](1);
        debits[0] = SparkV15Funds.RechargeDebit(selected, 6);
        terms.rechargeDebitsHash = keccak256(abi.encode(debits));
        bytes32 formId = _publishForm(terms);
        _fundAndSignAgreement(formId);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        _acceptForm(formId, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);
        _acceptForm(formId, PAYER, SparkV15Booking.Acceptance.Payer);

        debits[0] = SparkV15Funds.RechargeDebit(unselected, 6);
        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.confirmPlace(formId, bytes32(0), 0, debits);
        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        _confirmOrdinary(formId, bytes32(0), 0);

        debits[0] = SparkV15Funds.RechargeDebit(selected, 6);
        requestVm.prank(SOURCE_ACTOR);
        booking.confirmPlace(formId, bytes32(0), 0, debits);
        require(funds.creditBalance(terms.creditAccount) == 13, "wrong account debit");
        require(funds.getRechargeReceipt(unselected).unspentForReturn == 10, "unselected receipt charged");
        require(funds.getRechargeReceipt(selected).unspentForReturn == 3, "signed recharge debit missing");
    }

    function testGroupPlanRequiresDistinctStudentsAndChargesEachPlaceToTheAgreedAccount() public {
        _publishLesson(true);
        SparkV15Booking.PlaceTerms memory second = _placeTerms(keccak256("another place"), 6);
        second.payer = CUSTOMER;
        bytes32[] memory formIds = new bytes32[](2);
        formIds[0] = _publishForm(_placeTerms(PLACE, 8));
        formIds[1] = _publishForm(second);
        _provideProviderFunds(46);

        uint256 duplicateRoster = _evidence(booking.prefundingCommitment(LESSON, formIds, 46, FUNDING_CHECK));
        requestVm.expectRevert(SparkV15Booking.InvalidPrefunding.selector);
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, formIds, 46, FUNDING_CHECK, duplicateRoster);
        require(funds.lessonReserved(LESSON) == 0, "invalid roster committed a reserve");

        second.student = OTHER_STUDENT;
        formIds[1] = _publishForm(second);
        uint256 validRoster = _evidence(booking.prefundingCommitment(LESSON, formIds, 46, FUNDING_CHECK));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, formIds, 46, FUNDING_CHECK, validRoster);
        _recharge(CUSTOMER, 15, 0);
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(LESSON);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(LESSON);
        for (uint256 i; i < formIds.length; ++i) {
            _provideTerms(formIds[i], CUSTOMER);
            _provideTerms(formIds[i], TUTOR);
            _acceptForm(formIds[i], PROVIDER, SparkV15Booking.Acceptance.Provider);
            _acceptForm(formIds[i], CUSTOMER, SparkV15Booking.Acceptance.Customer);
            _acceptForm(formIds[i], TUTOR, SparkV15Booking.Acceptance.Tutor);
            if (i == 0) _acceptForm(formIds[i], PAYER, SparkV15Booking.Acceptance.Payer);
            _confirmOrdinary(formIds[i], bytes32(0), 0);
        }

        bytes32[] memory planned = booking.getPlannedForms(LESSON);
        require(planned.length == 2 && planned[1] == formIds[1], "wrong funded roster");
        require(funds.creditBalance(second.creditAccount) == 1 && funds.lessonReserved(LESSON) == 60, "wrong debits");

        uint256 rosterEvidence = _evidence(booking.rosterLockCommitment(LESSON, REGISTER));
        requestVm.expectRevert(SparkV15Booking.InvalidRoster.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.lockRoster(LESSON, REGISTER, rosterEvidence);
        require(booking.getLockedForms(LESSON).length == 0, "planned forms treated as locked");

        requestVm.warp(ROSTER_LOCK + 3);
        requestVm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        requestVm.prank(SOURCE_ACTOR);
        booking.lockRoster(LESSON, REGISTER, validRoster);
        requestVm.prank(SOURCE_ACTOR);
        booking.lockRoster(LESSON, REGISTER, rosterEvidence);
        bytes32[] memory locked = booking.getLockedForms(LESSON);
        require(locked.length == 2 && locked[0] == formIds[0] && locked[1] == formIds[1], "wrong locked forms");
        SparkV15Booking.RosterLock memory roster = booking.getRosterLock(LESSON);
        require(roster.lockedAt == ROSTER_LOCK && roster.recordedAt == ROSTER_LOCK + 3, "wrong roster clock");
        require(roster.evidenceId == rosterEvidence, "lost roster proof");
    }

    function testTeachingRetainsTheActualIntervalWithBothAgreedNotices() public {
        bytes32 formId = _bookOneToOne();
        requestVm.warp(LESSON_START - 5);
        _studentNotice(formId, LESSON_START - 15);
        _tutorNotice(LESSON_START - 9);

        uint64 actualStart = LESSON_START + 7;
        requestVm.warp(actualStart + 3);
        uint256 openingEvidence = _recordOpening(actualStart, bytes32(0));
        uint64 actualEnd = LESSON_END + 23;
        requestVm.warp(actualEnd + 4);
        uint256 endingEvidence = _recordEnding(actualEnd);

        SparkV15Booking.Teaching memory actual = booking.getTeaching(LESSON);
        require(actual.startPermission == SparkV15Booking.StartPermission.Permitted, "permission lost");
        require(actual.startedAt == actualStart && actual.endedAt == actualEnd, "actual interval lost");
        require(
            actual.startRecordedAt == actualStart + 3 && actual.endRecordedAt == actualEnd + 4, "recording times lost"
        );
        require(actual.startEvidenceId == openingEvidence && actual.endEvidenceId == endingEvidence, "wrong proof");
        require(booking.getLesson(LESSON).terms.startsAt == LESSON_START, "actual start rewrote agreement");
    }

    function testVerifiedProviderTeachingWithoutAConfirmedPlacePreservesOccurrenceOnly() public {
        _publishLesson(false);
        _publishForm(_placeTerms(PLACE, 8));
        requestVm.warp(LESSON_START);
        uint256 startProof = _recordOpening(LESSON_START, keccak256("provider went ahead while the seat was unconfirmed"));
        requestVm.warp(LESSON_END);
        uint256 endProof = _recordEnding(LESSON_END);

        SparkV15Booking.Teaching memory occurrence = booking.getTeaching(LESSON);
        require(occurrence.startPermission == SparkV15Booking.StartPermission.RequirementsNotMet, "unpaid place gained permission");
        require(occurrence.providerWentAhead && occurrence.startEvidenceId == startProof
            && occurrence.endEvidenceId == endProof, "verified provider occurrence missing");
        require(booking.getConfirmedForms(LESSON).length == 0 && funds.lessonReserved(LESSON) == 0
            && funds.lessonFeeBalance(LESSON) == 0, "occurrence changed the booking or reserve");
    }

    function testAgreedButUnconfirmedProviderStartRetainsExactTermsWithoutChargingThePlace() public {
        _publishLesson(false);
        bytes32 formId = _publishForm(_placeTerms(PLACE, 8));
        _fundAndSignAgreement(formId);
        _acceptForm(formId, PROVIDER, SparkV15Booking.Acceptance.Provider);
        _acceptForm(formId, CUSTOMER, SparkV15Booking.Acceptance.Customer);
        _acceptForm(formId, TUTOR, SparkV15Booking.Acceptance.Tutor);
        _acceptForm(formId, PAYER, SparkV15Booking.Acceptance.Payer);
        _recharge(CUSTOMER, 8, 0);
        uint256 reservedBefore = funds.reservedUnits();
        uint64 startedAt = LESSON_START - 1;
        requestVm.warp(startedAt);
        bytes32 unmet = keccak256("provider started before the accepted place was confirmed and charged");
        uint256 startProof = _recordOpening(startedAt, unmet);
        requestVm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        _confirmOrdinary(formId, bytes32(0), 0);

        requestVm.warp(LESSON_END);
        uint256 endProof = _recordEnding(LESSON_END);
        bytes32 reportRef = keccak256("tutor reports part of the agreed teaching delivered");
        uint256 report = _evidence(booking.tutorDeliveryCommitment(LESSON, false, reportRef));
        requestVm.prank(TUTOR);
        booking.recordTutorDelivery(LESSON, false, reportRef, report);
        SparkV15Booking.Teaching memory occurrence = booking.getTeaching(LESSON);
        require(occurrence.startPermission == SparkV15Booking.StartPermission.RequirementsNotMet
            && occurrence.startEvidenceId == startProof && occurrence.endEvidenceId == endProof, "different occurrence");
        require(booking.getTutorDelivery(LESSON).evidenceId == report, "tutor record lost");
        (, uint64 tutorAcceptedAt) = booking.acceptances(formId, SparkV15Booking.Acceptance.Tutor);
        require(tutorAcceptedAt != 0 && tutorAcceptedAt < startedAt
            && booking.termsProvisionEvidence(formId, TUTOR) != 0, "prior agreements or delivery lost");
        require(booking.getForm(formId).confirmation.debitedUnits == 0 && booking.getConfirmedForms(LESSON).length == 0,
            "early occurrence created a confirmation or debit");
        require(funds.reservedUnits() == reservedBefore && funds.lessonReserved(LESSON) == 28
            && funds.lessonFeeBalance(LESSON) == 0 && funds.creditBalance(funds.creditAccount(CUSTOMER)) == 8,
            "early occurrence or report changed balances");
    }

    function testVerifiedUnauthorisedTeachingStillTakesSeparateReportsFromTheActualParties() public {
        bytes32 formId = _bookOneToOne();
        requestVm.warp(LESSON_START - 1);
        _tutorNotice(LESSON_START - 2);
        bytes32 unmet = keccak256("verifier confirmed the provider failed to send the student notice");
        requestVm.warp(LESSON_START);
        _recordOpening(LESSON_START, unmet);
        SparkV15Booking.Teaching memory actual = booking.getTeaching(LESSON);
        require(actual.startPermission == SparkV15Booking.StartPermission.RequirementsNotMet, "unauthorised class lost");
        require(actual.providerWentAhead && actual.unmetConditionRef == unmet, "unmet requirement or provider lost");

        bytes32 attendanceRef = keccak256("signed attendance report");
        uint256 earlyEvidence = _evidence(booking.attendanceCommitment(formId, true, attendanceRef));
        requestVm.expectRevert(SparkV15Booking.InvalidReport.selector);
        requestVm.prank(STUDENT);
        booking.recordAttendance(formId, true, attendanceRef, earlyEvidence);

        requestVm.warp(LESSON_END);
        _recordEnding(LESSON_END);
        require(booking.getAttendance(formId).evidenceId == 0, "missing report became a finding");
        uint256 attendanceEvidence = _evidence(booking.attendanceCommitment(formId, true, attendanceRef));
        requestVm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        requestVm.prank(PAYER);
        booking.recordAttendance(formId, true, attendanceRef, attendanceEvidence);
        requestVm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        requestVm.prank(STUDENT);
        booking.recordAttendance(formId, true, attendanceRef, earlyEvidence);
        requestVm.prank(STUDENT);
        booking.recordAttendance(formId, true, attendanceRef, attendanceEvidence);
        require(booking.getAttendance(formId).attended, "actual attendance lost");
        require(booking.getServiceFeedback(formId).evidenceId == 0, "attendance treated as service feedback");

        bytes32 received = keccak256("part of the agreed service delivered");
        bytes32 omitted = keccak256("part of the agreed service omitted");
        SparkV15Booking.ServiceStatus partialStatus = SparkV15Booking.ServiceStatus.PartiallyDelivered;
        uint256 feedback = _evidence(booking.serviceFeedbackCommitment(formId, partialStatus, received, omitted));
        requestVm.prank(STUDENT);
        booking.recordServiceFeedback(formId, partialStatus, received, omitted, feedback);
        require(booking.getServiceFeedback(formId).status == partialStatus, "partial service lost");

        bytes32 reportRef = keccak256("tutor account explaining partial delivery");
        uint256 tutorReport = _evidence(booking.tutorDeliveryCommitment(LESSON, false, reportRef));
        requestVm.prank(TUTOR);
        booking.recordTutorDelivery(LESSON, false, reportRef, tutorReport);
        SparkV15Booking.TutorDelivery memory delivery = booking.getTutorDelivery(LESSON);
        require(!delivery.completed && delivery.evidenceId == tutorReport, "incomplete tutor delivery lost");
    }

    function testSameSecondNoticePreservesTheStartButDoesNotEstablishPermission() public {
        bytes32 formId = _bookOneToOne();
        requestVm.warp(LESSON_START);
        _studentNotice(formId, LESSON_START);
        _tutorNotice(LESSON_START - 1);
        requestVm.warp(LESSON_START + 1);
        uint256 opening = _recordOpening(LESSON_START, bytes32(0));
        SparkV15Booking.Teaching memory actual = booking.getTeaching(LESSON);
        require(actual.startPermission == SparkV15Booking.StartPermission.Unverified, "guessed same-second order");
        require(actual.startedAt == LESSON_START && actual.startEvidenceId == opening, "lost actual opening");
        require(actual.unmetConditionRef == bytes32(0), "uncertain start became a finding");
    }

    function testConflictingPermissionEvidenceDoesNotEraseActualTeaching() public {
        bytes32 formId = _bookOneToOne();
        requestVm.warp(LESSON_START - 1);
        _studentNotice(formId, LESSON_START - 2);
        _tutorNotice(LESSON_START - 2);
        bytes32 disputedNotice = keccak256("later inspection contests the student notice receipt");
        requestVm.warp(LESSON_START);
        uint256 opening = _recordOpening(LESSON_START, disputedNotice);

        SparkV15Booking.Teaching memory actual = booking.getTeaching(LESSON);
        require(actual.startedAt == LESSON_START && actual.startEvidenceId == opening, "lost actual opening");
        require(actual.startPermission == SparkV15Booking.StartPermission.Unverified, "resolved conflicting proofs");
        require(actual.unmetConditionRef == disputedNotice, "lost the disputed requirement");
    }

    function testAgreedMaterialsBundleRequiresItsTermsAndResponsiblePayer() public {
        SparkV15Booking.LessonTerms memory lesson = _lessonTerms(false);
        lesson.materialsTermsRef = keccak256("applicable material revenue-sharing agreement");
        requestVm.prank(SOURCE_ACTOR);
        booking.publishLesson(lesson);

        SparkV15Booking.PlaceTerms memory place = _placeTerms(PLACE, 8);
        place.materialsBundleRef = keccak256("the agreed standard materials bundle");
        requestVm.expectRevert(SparkV15Booking.InvalidForm.selector);
        _publishForm(place);

        place.materialPayer = PROVIDER;
        bytes32 formId = _publishForm(place);
        SparkV15Booking.Form memory form = booking.getForm(formId);
        require(form.terms.materialsBundleRef == place.materialsBundleRef && form.terms.materialPayer == PROVIDER);
        require(booking.getLesson(LESSON).terms.materialsTermsRef == lesson.materialsTermsRef);
    }
}
