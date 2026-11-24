// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {IERC20} from "../../../src/apps/spark/legacy/interfaces/IERC20.sol";
import {SparkV15, SparkV15ApplicationModule} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {ISparkV15BookingFunds, SparkV15Booking, SparkV15BookingOpening} from "../../../src/apps/spark/v15/SparkV15Booking.sol";
import {SparkV15BookingPrefunding} from "../../../src/apps/spark/v15/SparkV15BookingPrefunding.sol";
import {SparkV15CourseNotices} from "../../../src/apps/spark/v15/SparkV15CourseNotices.sol";
import {SparkV15TeachingEnd} from "../../../src/apps/spark/v15/SparkV15TeachingEnd.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {
    SparkV15FundingCases,
    SparkV15MaterialBacking,
    SparkV15MaterialProvisions,
    SparkV15ObservedMaterialReceipts,
    SparkV15ServiceReserve
} from "../../../src/apps/spark/v15/SparkV15MaterialProvisions.sol";
import {SparkV15Materials, SparkV15MaterialsUse, ISparkV15MaterialInterests} from "../../../src/apps/spark/v15/SparkV15Materials.sol";
import {SparkV15MaterialRights} from "../../../src/apps/spark/v15/SparkV15MaterialRights.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15PaymentObservations} from "../../../src/apps/spark/v15/SparkV15PaymentObservations.sol";
import {SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {SparkV15LessonRemedies, SparkV15CustomerRedress} from "../../../src/apps/spark/v15/SparkV15LessonRemedies.sol";
import {
    SparkV15ReviewCases,
    SparkV15ReviewContext,
    SparkV15ReviewActions,
    SparkV15ConcernIntake
} from "../../../src/apps/spark/v15/SparkV15ReviewCases.sol";
import {RequestAllocationFixture} from "../../helpers/RequestAllocationFixture.sol";
import {MockERC20} from "../mocks/MockERC20.sol";

interface MaterialsObservationVm {
    function roll(uint256 blockNumber) external;
    function setBlockhash(uint256 blockNumber, bytes32 blockHash) external;
}

contract MaterialsFundingTest is RequestAllocationFixture {
    MaterialsObservationVm private constant observationVm = MaterialsObservationVm(address(requestVm));
    uint64 private constant EPOCH = 1_000_000;
    bytes32 private constant LESSON = bytes32(uint256(42));
    bytes32 private constant PLACE = bytes32(uint256(1));
    bytes32 private constant MAIN = bytes32(uint256(7));
    bytes32 private constant OTHER = bytes32(uint256(8));
    bytes32 private constant BOOKING_MATERIAL_COST = keccak256("booking's estimate for material 7");
    bytes32 private constant M3_ORIGINAL_CHARGE = keccak256("original M3 charge");
    bytes32 private constant BUNDLE = keccak256("two materials agreed for the lesson");
    bytes32 private constant AGREEMENT = keccak256("agreed teaching services");
    bytes32 private constant DOCUMENTS = keccak256("provided course confirmation");
    bytes32 private constant CHANNEL = keccak256("agreed tutor notice channel");
    address private constant PROVIDER = address(0x7901);
    address private constant COORDINATOR = address(0x7902);
    address private constant TUTOR = address(0x7903);
    address private constant CUSTOMER = address(0x7904);
    address private constant FIRST_HOLDER = address(0x7905);
    address private constant SECOND_HOLDER = address(0x7906);
    address private constant CREDIT_OWNER = address(0x7907);
    address private constant EXECUTOR = address(0x7908);
    address private constant DECIDER = address(0x7909);
    address private constant SERVICE_RESERVE_RECIPIENT = address(0x7910);
    address private constant GROUP_STUDENT_B = address(0x7911);
    bytes32 private constant ROLE_DECIDER = keccak256("service reserve case initial decider");
    bytes32 private constant GROUP_MATERIAL_COST =
        keccak256("licensed seat B material in the signed funding inventory");
    bytes32 private constant GROUP_TUTOR_WAGE = keccak256("tutor's signed independent eight-unit wage for teaching B");
    uint128 private constant GROUP_A_FEE = 20;
    uint128 private constant GROUP_B_FEE = 60;
    uint128 private constant GROUP_MATERIAL_UNITS = 6;
    uint128 private constant GROUP_WAGE_UNITS = 8;

    enum GroupRedress {
        None,
        FullRefund,
        StandardNoDelivery,
        StandardPartial,
        FailedPartialRemedy
    }

    MockERC20 private token;
    SparkV15Booking private booking;
    SparkV15Funds private funds;
    SparkV15Payments private payments;
    SparkV15Materials private materials;
    SparkV15MaterialProvisions private provisions;
    SparkV15ReviewCases private cases;
    bytes32 private formId;
    bytes32 private refund;

    function setUp() public {
        requestVm.warp(EPOCH + 1);
        _setUpRequestAllocation(
            SparkV15.APP_ID,
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR),
            SparkV15.OBJECT_PAYMENT_APPROVAL
        );
        token = new MockERC20("Local material-share cash", "MAT", 6);
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
        cases = new SparkV15ReviewCases(payments, ROLE_SOURCE);
        cases.bindIntake(new SparkV15ConcernIntake(payments, ROLE_SOURCE, cases));
        materials = new SparkV15Materials(booking, cases);
        materials.bindMaterialUse(new SparkV15MaterialsUse(materials));
        provisions = new SparkV15MaterialProvisions(materials, payments);
        provisions.bindMaterialBacking(new SparkV15MaterialBacking(provisions, materials, booking, payments));
        provisions.bindServiceReserveModule(new SparkV15ServiceReserve(provisions, booking, payments));

        _assign(COORDINATOR, ROLE_SOURCE);
        _assign(PROVIDER, ROLE_ALLOCATOR);
        _assign(PROVIDER, funds.CREDIT_PROVIDER_ROLE());
        _assign(address(booking), funds.BOOKING_ROLE());
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, booking.ACTION_COORDINATE_BOOKING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, materials.ACTION_VERIFY_USE(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, materials.ACTION_RECORD_GROSS(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, booking.ACTION_VERIFY_PREFUNDING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, booking.ACTION_VERIFY_TEACHING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_ESTABLISH_PAYMENT, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, provisions.ACTION_VERIFY_PROVISION(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, provisions.ACTION_VERIFY_ENTITLEMENT(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, provisions.ACTION_VERIFY_MATERIAL_RECEIPT(), true);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, provisions.MATERIAL_BACKING().ACTION_VERIFY_RECEIPT_ALLOCATION(), true
        );
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, provisions.SERVICE_RESERVE().ACTION_VERIFY_RESERVE_RELEASE(), true
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, funds.BOOKING_ROLE(), funds.ACTION_MANAGE_LESSON_FUNDS(), true);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, funds.CREDIT_PROVIDER_ROLE(), funds.ACTION_OFFER_RECHARGE(), true
        );
    }

    function testTwoScopedProvisionsCannotUseTheSameSixUnits() public {
        _book(6, 0);
        requestVm.warp(EPOCH + 20);
        _recordProvision(MAIN, 6);
        requestVm.warp(EPOCH + 21);
        SparkV15MaterialProvisions.ProvisionInput memory other = _provision(OTHER, 6);
        uint256 proof = _evidence(provisions.provisionEvidenceCommitment(other, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15MaterialProvisions.InsufficientMaterialBacking.selector);
        requestVm.prank(VERIFIER_ACTOR);
        provisions.recordProvision(other, proof, _authority(ROLE_VERIFIER));
        require(provisions.provisioningNeed(LESSON) == 6, "failed provision changed the first reserve");
        require(funds.paymentReserved(refund) == 120, "first reserve used the original debit backing");
        require(funds.creditBalance(funds.creditAccount(CREDIT_OWNER)) == 17, "reserve used another customer's balance");
    }

    function testProviderFundsCommittedToAnotherLessonDoNotBackThisEstimate() public {
        _book(6, 0);
        bytes32 otherLesson = keccak256("second lesson with independently reserved provider cash");
        SparkV15Booking.LessonTerms memory secondTerms = booking.getLesson(LESSON).terms;
        secondTerms.lessonId = otherLesson;
        secondTerms.materialsTermsRef = bytes32(0);
        requestVm.prank(COORDINATOR);
        booking.publishLesson(secondTerms);
        SparkV15Booking.PlaceTerms memory secondPlace = booking.getForm(formId).terms;
        secondPlace.materialsBundleRef = bytes32(0);
        secondPlace.materialPayer = address(0);
        requestVm.prank(COORDINATOR);
        bytes32 otherForm = booking.publishForm(otherLesson, secondPlace);
        bytes32[] memory selected = new bytes32[](1);
        selected[0] = otherForm;
        bytes32 inventory = keccak256("verified financing for the second lesson");
        uint256 evidenceId = _evidence(booking.prefundingCommitment(otherLesson, selected, 3, inventory));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(otherLesson, selected, 3, inventory, evidenceId);

        requestVm.warp(EPOCH + 20);
        SparkV15MaterialProvisions.ProvisionInput memory estimate = _provision(MAIN, 6);
        uint256 proof = _evidence(provisions.provisionEvidenceCommitment(estimate, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15MaterialProvisions.InsufficientMaterialBacking.selector);
        requestVm.prank(VERIFIER_ACTOR);
        provisions.recordProvision(estimate, proof, _authority(ROLE_VERIFIER));
        require(
            funds.lessonReserved(otherLesson) == 3 && token.balanceOf(address(funds)) == 143, "earlier cash was exposed"
        );
    }

    function testCompatibleOutcomesCanUseTheSameTwelveUnits() public {
        _book(12, 10);
        requestVm.warp(EPOCH + 20);
        _recordProvision(MAIN, 6);
        requestVm.warp(EPOCH + 21);
        _recordProvision(OTHER, 6);
        require(provisions.provisioningNeed(LESSON) == 12, "compatible booking alternatives were combined");
        requestVm.warp(EPOCH + 22);
        _recordProvision(MAIN, 6);
        require(provisions.provisioningNeed(LESSON) == 12, "same estimate counted twice");
    }

    function testCannotIgnoreACompatibleOutcomeWithMoreCostThanTheEstimate() public {
        _book(6, 10);
        requestVm.warp(EPOCH + 20);
        SparkV15MaterialProvisions.ProvisionInput memory input = _provision(MAIN, 6);
        uint256 proof = _evidence(provisions.provisionEvidenceCommitment(input, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15MaterialProvisions.InsufficientMaterialBacking.selector);
        requestVm.prank(VERIFIER_ACTOR);
        provisions.recordProvision(input, proof, _authority(ROLE_VERIFIER));
    }

    function testVerifiedReleaseLowersTheUncommittedProviderHoldWithoutMovingCash() public {
        _bookWithProviderHold(12, 0, 9, true);
        SparkV15ServiceReserve reserve = provisions.SERVICE_RESERVE();
        requestVm.warp(EPOCH + 20);
        require(reserve.releasableProviderHold(LESSON) == 3, "booked costs were not retained");
        bytes32 closeRef = keccak256("verified three provider units are no longer committed");
        uint256 proof = _evidence(reserve.releaseEvidenceCommitment(LESSON, 3, closeRef, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        reserve.releaseBudget(LESSON, 3, closeRef, proof, _authority(ROLE_VERIFIER));
        require(funds.lessonReserved(LESSON) == 6 && funds.reservedUnits() == 143, "wrong reserve release");
        require(token.balanceOf(address(funds)) == 149, "release moved money");
        require(
            funds.paymentReserved(refund) == 120 && funds.creditBalance(funds.creditAccount(CREDIT_OWNER)) == 17,
            "release consumed required amounts"
        );
        require(reserve.releasableProviderHold(LESSON) == 0, "committed booked cost was exposed");
    }

    function testTwoSeatGroupRetainsUnverifiedAndUndeliveredSeatProtection() public {
        (bytes32[] memory forms, SparkV15CustomerRedress redress) = _bookTwoSeatMaterialLesson();
        _teachTwoSeatLesson(forms, SparkV15Booking.ServiceStatus.NoneDelivered);

        SparkV15ServiceReserve reserve = provisions.SERVICE_RESERVE();
        require(reserve.releasableProviderHold(LESSON) == 96, "opening and student report changed A's funding");
        _recordTwoSeatProviderFault(redress, SparkV15LessonRemedies.TeachingReceived.NoneDelivered, GROUP_A_FEE);
        _assertOriginalRelief(redress, GROUP_A_FEE);

        require(funds.lessonReserved(LESSON) == 310, "verifying A changed the actual hold");
        require(reserve.releasableProviderHold(LESSON) == 96, "B's permitted opening lost A's no-delivery compensation");
    }

    function testMaterialFundingDeploysWithinCancunCodeLimits() public view {
        uint256 provisionsInitcode =
            type(SparkV15MaterialProvisions).creationCode.length + abi.encode(materials, payments).length;
        uint256 fundingCasesInitcode =
            type(SparkV15FundingCases).creationCode.length + abi.encode(booking, payments, materials).length;
        SparkV15FundingCases fundingCases = provisions.FUNDING_CASES();
        require(provisionsInitcode <= 49_152 && fundingCasesInitcode <= 49_152, "Cancun initcode limit");
        require(
            address(provisions).code.length <= 24_576 && address(fundingCases).code.length <= 24_576, "runtime limit"
        );
        require(fundingCases.BOOKING() == booking && fundingCases.PAYMENTS() == payments, "wrong material deployment");
    }

    function testTwoSeatGroupKeepsProtectionAfterIntakeOfOriginalDeliveryMatter() public {
        (bytes32[] memory forms, SparkV15CustomerRedress redress) = _bookTwoSeatMaterialLesson();
        bytes32 contactsA = _publishTwoSeatContacts(forms[0]);
        bytes32 contactsB = _publishTwoSeatContacts(forms[1]);
        _teachTwoSeatLesson(forms, SparkV15Booking.ServiceStatus.PartiallyDelivered);
        _recordTwoSeatProviderFault(redress, SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered, 10);

        SparkV15ServiceReserve reserve = provisions.SERVICE_RESERVE();
        SparkV15FundingCases fundingCases = provisions.FUNDING_CASES();
        require(reserve.releasableProviderHold(LESSON) == 106, "partial delivery was not operative");
        require(fundingCases.independentTeachingCosts(LESSON) == 198, "wrong independent costs before intake");

        _receiveTwoSeatConcern(contactsB, keccak256("B asks for the promised lesson notes"), forms[1], GROUP_STUDENT_B);
        require(reserve.releasableProviderHold(LESSON) == 106, "B's separate matter changed the release estimate");
        require(fundingCases.independentTeachingCosts(LESSON) == 198, "B's separate matter changed payment backing");

        bytes32 caseId = _receiveTwoSeatConcern(contactsA, fundingCases.deliveryMatter(forms[0]), forms[0], CUSTOMER);
        require(caseId == redress.REMEDIES().placeFaultCase(forms[0]), "intake did not identify A's original matter");
        require(reserve.releasableProviderHold(LESSON) == 96, "intake left the disputed A discount unprotected");
        require(fundingCases.independentTeachingCosts(LESSON) == 208, "payment path lost the disputed cost");
        require(funds.lessonReserved(LESSON) == 310 && token.balanceOf(address(funds)) == 310, "intake moved funds");

        bytes32 scopeId = _recordTwoSeatMaterialCharge(forms[1]);
        _releaseTwoSeatBudget(reserve, 96, keccak256("idle reserve exclusive of the disputed discount"));
        require(funds.lessonReserved(LESSON) == 214, "release consumed the disputed backing");
        require(token.balanceOf(address(funds)) == 310, "release moved cash");
        bytes32 otherLesson = _reserveIndependentLesson(96);
        _payTwoSeatMaterials(scopeId);
        require(funds.lessonReserved(LESSON) == 208, "separate material payments consumed the disputed backing");
        require(funds.lessonReserved(otherLesson) == 96 && funds.reservedUnits() == 304, "wrong later pool backing");
    }

    function testSeparatelyNumberedConcernRetainsVerifiedDeliveryProtection() public {
        (bytes32[] memory forms, SparkV15CustomerRedress redress) = _bookTwoSeatMaterialLesson();
        bytes32 contactsA = _publishTwoSeatContacts(forms[0]);
        bytes32 contactsB = _publishTwoSeatContacts(forms[1]);
        _teachTwoSeatLesson(forms, SparkV15Booking.ServiceStatus.PartiallyDelivered);
        _recordTwoSeatProviderFault(redress, SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered, 10);

        bytes32 otherConcern =
            _receiveTwoSeatConcern(contactsB, keccak256("B asks for lesson notes"), forms[1], GROUP_STUDENT_B);
        _replyToDeliveryConcern(otherConcern, keccak256("lesson notes were supplied"));
        _assertConcernFunding(106, 198);

        bytes32 concern =
            _receiveTwoSeatConcern(contactsA, keccak256("separately numbered A teaching concern"), forms[0], CUSTOMER);
        bytes32 original = redress.REMEDIES().placeFaultCase(forms[0]);
        require(concern != original, "concern and original finding must retain their numbers");
        _assertConcernFunding(106, 198);
        _replyToDeliveryConcern(concern, keccak256("the service scope needs further verification"));
        _assertConcernFunding(106, 198);

        (SparkV15ServiceReserve.DeliveryFinding memory finding, uint256 scopeProof) =
            _confirmSeparateDeliveryConcern(concern, forms[0], original);
        _settleAfterLinkedConcern(forms[1]);
        _withdrawDeliveryConcernEvidence(finding, scopeProof);
    }

    function _confirmSeparateDeliveryConcern(bytes32 concern, bytes32 form, bytes32 original)
        private
        returns (SparkV15ServiceReserve.DeliveryFinding memory finding, uint256 proof)
    {
        SparkV15ServiceReserve reserve = provisions.SERVICE_RESERVE();
        finding = SparkV15ServiceReserve.DeliveryFinding(LESSON, form, original, 1, EPOCH + 30, EPOCH + 32);
        bytes32 verification = keccak256("independent original teaching records verify the exact scope");
        bytes32 authority = _actorId(COORDINATOR, ROLE_SOURCE);
        proof = _evidence(reserve.deliveryConcernEvidenceCommitment(concern, finding, verification, COORDINATOR));
        require(reserve.getDeliveryConcerns(finding).length == 0, "evidence alone confirmed the scope");
        _assertConcernFunding(106, 198);
        _requireConcernConfirmationBasis(concern, finding, verification, proof, authority);

        SparkV15ServiceReserve.DeliveryFinding memory stale =
            SparkV15ServiceReserve.DeliveryFinding(LESSON, form, original, 2, EPOCH + 30, EPOCH + 32);
        requestVm.expectRevert(SparkV15ServiceReserve.InvalidReserveOperation.selector);
        requestVm.prank(COORDINATOR);
        reserve.confirmDeliveryConcern(concern, stale, verification, proof, authority);
        _assertConcernFunding(106, 198);

        requestVm.warp(EPOCH + 34);
        requestVm.prank(COORDINATOR);
        reserve.confirmDeliveryConcern(concern, finding, verification, proof, authority);
        SparkV15ServiceReserve.DeliveryConcernLink[] memory links = reserve.getDeliveryConcerns(finding);
        require(
            links.length == 1 && links[0].concernId == concern && links[0].evidenceId == proof
                && links[0].verifiedBy == COORDINATOR && links[0].verifiedAt == EPOCH + 34
                && links[0].authorityId == authority && links[0].verificationRef == verification,
            "missing verified scope history"
        );
        require(cases.INTAKE().getConcern(concern).intake.evidenceId == links[0].intakeEvidenceId, "intake lost");
        require(
            reserve.deliveryConcernStatus(finding) == SparkV15ServiceReserve.DeliveryConcernStatus.Verified,
            "confirmed scope was not current"
        );
        require(funds.lessonReserved(LESSON) == 310 && token.balanceOf(address(funds)) == 310, "link moved funds");
        _assertConcernFunding(96, 208);
    }

    function _requireConcernConfirmationBasis(
        bytes32 concern,
        SparkV15ServiceReserve.DeliveryFinding memory finding,
        bytes32 verification,
        uint256 proof,
        bytes32 authority
    ) private {
        SparkV15ServiceReserve reserve = provisions.SERVICE_RESERVE();
        bytes32 otherAuthority = _authority(ROLE_SOURCE);
        requestVm.expectRevert(SparkV15ServiceReserve.InvalidReserveOperation.selector);
        requestVm.prank(SOURCE_ACTOR);
        reserve.confirmDeliveryConcern(concern, finding, verification, proof, otherAuthority);

        uint256 intakeProof = cases.INTAKE().getConcern(concern).intake.evidenceId;
        requestVm.expectRevert(SparkV15ServiceReserve.InvalidReserveOperation.selector);
        requestVm.prank(COORDINATOR);
        reserve.confirmDeliveryConcern(concern, finding, verification, intakeProof, authority);
        require(reserve.getDeliveryConcerns(finding).length == 0, "unconfirmed scope was recorded");
    }

    function _assertConcernFunding(uint256 releasable, uint256 independent) private view {
        require(provisions.SERVICE_RESERVE().releasableProviderHold(LESSON) == releasable, "wrong release estimate");
        require(provisions.FUNDING_CASES().independentTeachingCosts(LESSON) == independent, "wrong payment backing");
    }

    function _settleAfterLinkedConcern(bytes32 seatB) private {
        bytes32 scopeId = _recordTwoSeatMaterialCharge(seatB);
        _releaseTwoSeatBudget(
            provisions.SERVICE_RESERVE(), 96, keccak256("authorised release with linked concern protected")
        );
        require(funds.lessonReserved(LESSON) == 214 && token.balanceOf(address(funds)) == 310, "wrong release");
        bytes32 otherLesson = _reserveIndependentLesson(96);
        _payTwoSeatMaterials(scopeId);
        require(funds.lessonReserved(LESSON) == 208, "payments consumed linked protection");
        require(funds.lessonReserved(otherLesson) == 96 && funds.reservedUnits() == 304, "wrong pool holds");
        require(token.balanceOf(address(funds)) == 304, "wrong pool cash after material payments");
    }

    function _withdrawDeliveryConcernEvidence(SparkV15ServiceReserve.DeliveryFinding memory finding, uint256 proof)
        private
    {
        _withdrawConcernProof(proof);
        SparkV15ServiceReserve reserve = provisions.SERVICE_RESERVE();
        require(
            reserve.deliveryConcernStatus(finding) == SparkV15ServiceReserve.DeliveryConcernStatus.Pending,
            "withdrawn scope evidence still counted as verified"
        );
        require(reserve.getDeliveryConcerns(finding).length == 1, "withdrawal erased scope history");
        _assertConcernFunding(0, 208);

        SparkV15ServiceReserve.DeliveryConcernLink memory retained = reserve.getDeliveryConcerns(finding)[0];
        bytes32 verification = keccak256("the exact scope was checked again from available records");
        uint256 refreshed = _evidence(
            reserve.deliveryConcernEvidenceCommitment(retained.concernId, finding, verification, COORDINATOR)
        );
        requestVm.prank(COORDINATOR);
        reserve.confirmDeliveryConcern(retained.concernId, finding, verification, refreshed, retained.authorityId);
        require(
            reserve.deliveryConcernStatus(finding) == SparkV15ServiceReserve.DeliveryConcernStatus.Verified,
            "new verified scope was unavailable"
        );
        _withdrawConcernProof(retained.acknowledgmentEvidenceId);
        require(
            reserve.deliveryConcernStatus(finding) == SparkV15ServiceReserve.DeliveryConcernStatus.Pending,
            "unavailable handler acknowledgment still supported verification"
        );
        require(reserve.getDeliveryConcerns(finding).length == 2, "scope history was rewritten");
        _assertConcernFunding(0, 208);
    }

    function _withdrawConcernProof(uint256 proof) private {
        requestVm.prank(SOURCE_ACTOR);
        evidenceRegistry.recordEvidenceLifecycle(
            proof,
            ROLE_SOURCE,
            _authority(ROLE_SOURCE),
            AVACoreTypes.EvidenceLifecycleKind.Revoke,
            0,
            keccak256("the scope verification source is no longer available"),
            "test:delivery-concern-evidence-revoked"
        );
    }

    function testTwoSeatGroupPartialDeliveryAllowsReleaseAndSeparateMaterialPayments() public {
        (bytes32[] memory forms, SparkV15CustomerRedress redress) = _bookTwoSeatMaterialLesson();
        _teachTwoSeatLesson(forms, SparkV15Booking.ServiceStatus.PartiallyDelivered);

        SparkV15ServiceReserve reserve = provisions.SERVICE_RESERVE();
        bytes32 releaseRef = keccak256("verified idle provider backing after A's service extent was confirmed");
        require(reserve.releasableProviderHold(LESSON) == 96, "unverified feedback reduced the retained fees");
        require(funds.lessonReserved(LESSON) == 310, "student feedback changed the hold");

        _recordTwoSeatProviderFault(redress, SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered, 10);
        _assertOriginalRelief(redress, 10);
        bytes32 scopeId = _recordTwoSeatMaterialCharge(forms[1]);

        require(reserve.releasableProviderHold(LESSON) == 106, "A's verified partial service did not narrow its costs");
        _releaseTwoSeatBudget(reserve, 106, releaseRef);
        require(funds.lessonReserved(LESSON) == 204, "wrong remaining backing after release");
        require(funds.lessonFeeBalance(LESSON) == 80 && token.balanceOf(address(funds)) == 310, "release moved cash");

        bytes32 otherLesson = _reserveIndependentLesson(106);
        require(funds.lessonReserved(otherLesson) == 106 && funds.reservedUnits() == 310, "released cash left idle");
        _payTwoSeatMaterials(scopeId);
        require(funds.lessonReserved(LESSON) == 198 && funds.lessonReserved(otherLesson) == 106, "wrong later backing");
        require(
            funds.reservedUnits() == 304 && token.balanceOf(address(funds)) == 304, "material debit missed the pool"
        );
    }

    function testServiceReserveMovesOnlyRemainingLessonFeesAfterActualFaultRefundAndArchivesLater() public {
        (SparkV15CustomerRedress redress, bytes32 faultRefund, uint64 dueAt) = this.prepareServiceRefund();
        SparkV15ServiceReserve reserve = provisions.SERVICE_RESERVE();
        require(funds.lessonFeeBalance(LESSON) == 80 && funds.paymentReserved(faultRefund) == 40, "refund not backed");
        SparkV15ServiceReserve.ServiceInput memory accounting = SparkV15ServiceReserve.ServiceInput(
            formId, 80, uint64(block.timestamp), keccak256("verified fee receipts and open liabilities")
        );
        uint256 proof = _evidence(reserve.serviceEvidenceCommitment(accounting, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15ServiceReserve.InvalidReserveOperation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        reserve.transferToServiceReserve(accounting, proof, _authority(ROLE_VERIFIER));
        require(token.balanceOf(SERVICE_RESERVE_RECIPIENT) == 0, "refund approval was treated as redress");

        uint256 approval = _approveMaterialThrough(faultRefund, 40, dueAt + 1 days);
        requestVm.warp(dueAt);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 40);
        require(redress.getRedress(formId).directRefundAt != 0, "missing refund election");
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == 40, "no actual redress");
        require(reserve.transferableServiceFees(LESSON) == 80, "wrong free fees");
        accounting.accountedAt = dueAt;
        accounting.accountingRef = keccak256("verified fee receipts, exact liabilities and actual redress");
        proof = _evidence(reserve.serviceEvidenceCommitment(accounting, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        uint256 transferId = reserve.transferToServiceReserve(accounting, proof, _authority(ROLE_VERIFIER));
        require(
            token.balanceOf(SERVICE_RESERVE_RECIPIENT) == 80 && token.balanceOf(address(funds)) == 69,
            "reserve did not receive actual fee cash"
        );
        require(
            funds.lessonReserved(LESSON) == 1 && funds.lessonFeeBalance(LESSON) == 0,
            "actual transfer consumed provider hold or left nominal fees"
        );
        require(funds.creditBalance(funds.creditAccount(CREDIT_OWNER)) == 17, "unrelated course credit exposed");

        requestVm.warp(dueAt + 1);
        requestVm.prank(COORDINATOR);
        reserve.fileServiceReserve(transferId);
        SparkV15ServiceReserve.ServiceTransfer memory transfer = reserve.getTransfer(transferId);
        require(transfer.paidAt == dueAt && transfer.filedAt == dueAt + 1, "archive changed the transfer date");
        require(
            token.balanceOf(SERVICE_RESERVE_RECIPIENT) == 80 && token.balanceOf(address(funds)) == 69,
            "archive moved cash"
        );
    }

    function prepareServiceRefund()
        external
        returns (SparkV15CustomerRedress redress, bytes32 faultRefund, uint64 dueAt)
    {
        _bookWithProviderHold(12, 0, 1, false);
        _teach();
        requestVm.warp(EPOCH + 33);
        redress = _serviceRedress();
        provisions.SERVICE_RESERVE().bindServiceReserve(address(redress), SERVICE_RESERVE_RECIPIENT);
        this.recordServiceFault(redress.REMEDIES());
        (faultRefund, dueAt) = _assessPartialRefund(redress);
    }

    function _serviceRedress() private returns (SparkV15CustomerRedress redress) {
        SparkV15LessonRemedies remedies = new SparkV15LessonRemedies(booking, payments, cases, ROLE_SOURCE);
        redress = new SparkV15CustomerRedress(remedies, ROLE_SOURCE);
        remedies.bindCustomerRedress(redress);
        bytes32 settlementRole = payments.settlementRole();
        _assign(address(redress), settlementRole);
        _assign(DECIDER, ROLE_DECIDER);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, settlementRole, payments.ACTION_RECORD_SETTLEMENT_OBLIGATION(), true
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, redress.ACTION_ASSESS_REFUND(), true);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_ALLOCATOR, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, true
        );
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, true
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_DECIDER, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, true);
        SparkV15ServiceReserve reserve = provisions.SERVICE_RESERVE();
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, reserve.ACTION_VERIFY_SERVICE_RESERVE(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, reserve.ACTION_FILE_SERVICE_RESERVE(), true);
        SparkV15CustomerRedress.RedressTerms memory terms = SparkV15CustomerRedress.RedressTerms(
            EPOCH + 34 + 7 days,
            EPOCH + 34 + 14 days,
            1 days,
            3 days,
            0,
            2 days,
            keccak256("redress for the agreed instruction"),
            DOCUMENTS
        );
        uint256 proof = _evidence(redress.redressTermsCommitment(formId, terms));
        requestVm.prank(PROVIDER);
        redress.publishRedressTerms(formId, terms, proof);
    }

    function recordServiceFault(SparkV15LessonRemedies remedies) external {
        _recordServiceFault(remedies, LESSON, 40, EPOCH + 32);
    }

    function _recordServiceFault(SparkV15LessonRemedies remedies, bytes32 lessonId, uint128 lostFee, uint64 occurredAt)
        private
    {
        bytes32 concern = keccak256("recognised fault affecting partially delivered teaching");
        SparkV15ReviewContext.ReviewTerms memory reviewTerms = SparkV15ReviewContext.ReviewTerms(
            lessonId,
            keccak256("contacts given with agreed terms"),
            formId,
            PROVIDER,
            COORDINATOR,
            CREDIT_OWNER,
            DECIDER,
            SECOND_HOLDER,
            FIRST_HOLDER,
            0,
            2 days,
            0,
            EPOCH + 10 days,
            0
        );
        bytes32 termsId = keccak256(abi.encode(reviewTerms));
        uint256 proof = _caseEvidence(termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, PROVIDER, termsId);
        SparkV15ConcernIntake intake = cases.INTAKE();
        requestVm.prank(PROVIDER);
        intake.publishContacts(reviewTerms, proof, _actorId(PROVIDER, ROLE_ALLOCATOR));
        bytes32 caseId = cases.caseIdFor(lessonId, concern);
        SparkV15LessonRemedies.AffectedPlace[] memory affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        affected[0] = SparkV15LessonRemedies.AffectedPlace(
            formId,
            SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered,
            SparkV15LessonRemedies.Participation.AttendedAsAgreed,
            lostFee,
            true,
            keccak256("actual partially delivered work")
        );
        SparkV15LessonRemedies.FaultFinding memory finding = SparkV15LessonRemedies.FaultFinding(
            SparkV15LessonRemedies.FaultKind.SeriousTeachingIncident,
            false,
            TUTOR,
            AGREEMENT,
            occurredAt,
            keccak256("verified tutor fault"),
            keccak256("inquiry with tutor"),
            keccak256("tutor opportunity to answer"),
            keccak256("inquiry with affected student"),
            affected
        );
        bytes32 outcome = remedies.faultOutcome(caseId, finding);
        address[] memory parties = new address[](2);
        parties[0] = CUSTOMER;
        parties[1] = TUTOR;
        SparkV15ReviewContext.OriginalInput memory original = SparkV15ReviewContext.OriginalInput(
            termsId, concern, bytes32(0), bytes32(0), DECIDER, uint64(block.timestamp), outcome, parties
        );
        proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(original))
        );
        requestVm.prank(VERIFIER_ACTOR);
        cases.retainOriginal(original, proof, _authority(ROLE_VERIFIER));
        SparkV15ReviewContext.InitialInput memory initial = SparkV15ReviewContext.InitialInput(
            SparkV15ReviewContext.DisputedFinding.Fault,
            outcome,
            keccak256("partially lost instruction"),
            affected[0].evidenceRef
        );
        proof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, DECIDER, keccak256(abi.encode(initial)));
        requestVm.prank(DECIDER);
        cases.decideInitial(caseId, initial, proof, _actorId(DECIDER, ROLE_DECIDER));
        remedies.recordFault(caseId, finding);
    }

    function _assessPartialRefund(SparkV15CustomerRedress redress) private returns (bytes32 refundId, uint64 dueAt) {
        requestVm.warp(EPOCH + 34);
        requestVm.prank(CUSTOMER);
        redress.requestDirectRefund(formId);
        SparkV15CustomerRedress.RefundBasis reason = SparkV15CustomerRedress.RefundBasis.DirectRequest;
        (SparkV15CustomerRedress.RefundAssessment memory refundAssessment, SparkV15Payments.PaymentTerms memory terms) =
            redress.previewRefund(formId, reason, VERIFIER_ACTOR);
        require(refundAssessment.principal == 40, "actual partial refund amount");
        uint256 assessmentProof = _evidence(refundAssessment.basis);
        requestVm.prank(VERIFIER_ACTOR);
        uint256 index = redress.assessRefund(formId, reason, assessmentProof, _authority(ROLE_VERIFIER));
        uint256 paymentProof = _evidence(payments.paymentEvidenceCommitment(terms, refundAssessment.basis));
        return (redress.establishRefundPayment(formId, index, paymentProof), terms.dueAt);
    }

    function _caseEvidence(bytes32 subject, bytes32 action, address actor, bytes32 payload) private returns (uint256) {
        return _evidence(cases.evidenceCommitment(subject, action, actor, payload));
    }

    function testCurrentProtectionCountsAReceiptAfterSameSecondVerification() public {
        (uint256 firstReceipt, uint256 secondApproval, bytes32 scope) = _prepareM3();
        uint64 sameSecond = EPOCH + 40;
        require(provisions.paymentProtection(LESSON, bytes32(0), 0) == 12, "unverified receipt counted");
        bytes32 secondObligation = provisions.entitlementFor(scope, SECOND_HOLDER);
        requestVm.expectRevert(SparkV15MaterialProvisions.InsufficientMaterialBacking.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(secondApproval, 4);
        require(token.balanceOf(address(funds)) == 147 && token.balanceOf(SECOND_HOLDER) == 0, "refusal moved cash");
        require(
            funds.paymentReserved(secondObligation) == 4 && payments.getApproval(secondApproval).paid == 0,
            "refusal consumed the approval or reserve"
        );

        _verifyReceipt(firstReceipt, sameSecond);

        SparkV15MaterialProvisions.MaterialReceipt memory verified = provisions.getMaterialReceipt(firstReceipt);
        require(verified.paidAt == sameSecond && verified.verifiedAt == sameSecond, "payment and check times differ");
        require(provisions.paymentProtection(LESSON, bytes32(0), 0) == 10, "verified receipt missing");
        require(provisions.provisioningNeed(LESSON) == 12, "part payment retired the provision");
        requestVm.prank(EXECUTOR);
        uint256 secondReceipt = payments.pay(secondApproval, 4);
        require(payments.getReceipt(secondReceipt).paidAt == sameSecond, "second payment changed time");
        require(token.balanceOf(SECOND_HOLDER) == 4 && token.balanceOf(address(funds)) == 143, "second payment absent");
    }

    function testSameSecondVerifiedReceiptsBackNextProvisionAtOriginalCash() public {
        (uint256 firstReceipt, uint256 secondApproval,) = _prepareM3(BOOKING_MATERIAL_COST);
        uint64 sameSecond = EPOCH + 40;
        _verifyReceipt(firstReceipt, sameSecond);
        requestVm.prank(EXECUTOR);
        uint256 secondReceipt = payments.pay(secondApproval, 4);
        _verifyReceipt(secondReceipt, sameSecond);
        require(payments.getReceipt(firstReceipt).paidAt == sameSecond, "first payment time");
        require(payments.getReceipt(secondReceipt).paidAt == sameSecond, "second payment time");
        require(provisions.getMaterialReceipt(firstReceipt).verifiedAt == sameSecond, "first verification time");
        require(provisions.getMaterialReceipt(secondReceipt).verifiedAt == sameSecond, "second verification time");
        require(token.balanceOf(FIRST_HOLDER) == 2 && token.balanceOf(SECOND_HOLDER) == 4, "actual payments");
        require(token.balanceOf(address(funds)) == 143 && funds.reservedUnits() == 137, "original cash and reserves");
        require(provisions.paymentProtection(LESSON, bytes32(0), 0) == 6, "current payment protection");
        require(provisions.provisioningNeed(LESSON) == 6, "same-second provision need");
        require(
            provisions.MATERIAL_BACKING().requiredBeyondLessonHold(LESSON, bytes32(0), 0, true) == 6,
            "same-second funding requirement"
        );

        _recordProvision(OTHER, 6);
        SparkV15MaterialProvisions.Provision memory latest = provisions.getLatestProvision(
            provisions.fundingKey(LESSON, PLACE, OTHER, booking.getLesson(LESSON).terms.materialsTermsRef)
        );
        require(latest.checkedAt == sameSecond && latest.input.budget == 6, "next provision not recorded");
        require(token.balanceOf(address(funds)) == 143 && funds.reservedUnits() == 137, "provision moved cash");
        require(provisions.provisioningNeed(LESSON) == 6, "same-second result changed");

        // This is a later observation, not a rewrite of the preceding state at the same timestamp.
        requestVm.warp(EPOCH + 41);
        require(provisions.provisioningNeed(LESSON) == 6, "later settled material need");
        require(
            provisions.MATERIAL_BACKING().requiredBeyondLessonHold(LESSON, bytes32(0), 0, true) == 6,
            "later funding requirement"
        );
    }

    function testSettledMaterialTransferKeepsOtherProvisionAtExactBacking() public {
        (uint256 firstReceipt, uint256 secondReceipt) = _settledTransfer(BOOKING_MATERIAL_COST, EPOCH + 46, false);
        require(
            provisions.MATERIAL_BACKING().requiredBeyondLessonHold(LESSON, bytes32(0), 0, true) == 6,
            "settled original counted again in forecast"
        );
        SparkV15FundingCases.FundingScenario[] memory inventory = provisions.FUNDING_CASES().getScenarios(LESSON);
        require(
            inventory[0].expenses[0].referenceId == BOOKING_MATERIAL_COST && inventory[0].expenses[0].units == 6,
            "inventory changed"
        );
        _recordProvision(OTHER, 6);
        require(provisions.provisioningNeed(LESSON) == 6, "other material need changed");
        require(token.balanceOf(address(funds)) == 143 && funds.reservedUnits() == 137, "provision moved backing");
        require(token.balanceOf(FIRST_HOLDER) == 2 && token.balanceOf(SECOND_HOLDER) == 4, "paid history changed");
        require(payments.getReceipt(firstReceipt).paidAt == EPOCH + 40, "first receipt changed");
        require(payments.getReceipt(secondReceipt).paidAt == EPOCH + 45, "second receipt changed");
    }

    function testSettledMaterialTransferLaterInSameSecondKeepsExactBacking() public {
        (uint256 firstReceipt, uint256 secondReceipt) = _settledTransfer(BOOKING_MATERIAL_COST, EPOCH + 45, false);
        requestVm.warp(EPOCH + 48);
        require(
            provisions.MATERIAL_BACKING().requiredBeyondLessonHold(LESSON, bytes32(0), 0, true) == 6,
            "settled original counted again after same-second transfer"
        );
        _recordProvision(OTHER, 6);
        require(token.balanceOf(address(funds)) == 143 && funds.reservedUnits() == 137, "backing changed");
        require(token.balanceOf(FIRST_HOLDER) == 2 && token.balanceOf(SECOND_HOLDER) == 4, "payments changed");
        require(payments.getReceipt(firstReceipt).paidAt == EPOCH + 40, "first receipt time changed");
        require(provisions.getMaterialReceipt(secondReceipt).verifiedAt == EPOCH + 45, "second verification changed");
        _assertSameSecondTransferCollection(secondReceipt);
    }

    function testLaterTransferRecordingDoesNotProveLaterEffectivenessInSameSecond() public {
        _settledTransfer(BOOKING_MATERIAL_COST, EPOCH + 45, true);
        require(provisions.provisioningNeed(LESSON) == 12, "later recording reordered an effective transfer");
        require(
            provisions.MATERIAL_BACKING().requiredBeyondLessonHold(LESSON, bytes32(0), 0, true) == 12,
            "ambiguous receipt retired original protection"
        );
        SparkV15MaterialRights rights = SparkV15MaterialRights(address(provisions.rights()));
        bytes32 scope = materials.originalFor(formId, MAIN);
        address successor = rights.getTransfer(rights.getTransfers(LESSON, MAIN)[0]).terms.transferee;
        requestVm.expectRevert(SparkV15MaterialRights.MaterialAllocationPending.selector);
        rights.holderPortion(scope, successor, EPOCH + 46, EPOCH + 46);
        (uint256 payablePart, uint256 pendingPart) =
            rights.readHolderAmounts(scope, successor, EPOCH + 46, EPOCH + 46, false, 0);
        require(payablePart == 0 && pendingPart == 4, "wrong pending original amount");
        SparkV15MaterialProvisions.EntitlementInput memory input = SparkV15MaterialProvisions.EntitlementInput(
            scope, successor, successor, EPOCH + 46, EPOCH + 80, keccak256("proposed successor of material 7")
        );
        requestVm.expectRevert(SparkV15MaterialRights.MaterialAllocationPending.selector);
        provisions.previewEntitlement(input, VERIFIER_ACTOR);
        require(provisions.entitlementFor(scope, successor) == bytes32(0), "pending part became an obligation");
    }

    function testUnlinkedMaterialExpenseRemainsProtectedAfterTransfer() public {
        _settledTransfer(M3_ORIGINAL_CHARGE, EPOCH + 45, false);
        require(provisions.provisioningNeed(LESSON) == 6, "known settled provision returned");
        require(
            provisions.MATERIAL_BACKING().requiredBeyondLessonHold(LESSON, bytes32(0), 0, true) == 12,
            "unlinked material expense removed"
        );
        SparkV15MaterialProvisions.ProvisionInput memory estimate = _provision(OTHER, 6);
        uint256 proof = _evidence(provisions.provisionEvidenceCommitment(estimate, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15MaterialProvisions.InsufficientMaterialBacking.selector);
        requestVm.prank(VERIFIER_ACTOR);
        provisions.recordProvision(estimate, proof, _authority(ROLE_VERIFIER));
        require(token.balanceOf(address(funds)) == 143 && funds.reservedUnits() == 137, "refusal moved backing");
    }

    function _settledTransfer(bytes32 sourceRef, uint64 transferAt, bool acceptedBeforeSecondPayment)
        private
        returns (uint256 firstReceipt, uint256 secondReceipt)
    {
        SparkV15MaterialRights rights = new SparkV15MaterialRights(materials, address(0x7911));
        materials.bindMaterialInterests(ISparkV15MaterialInterests(address(rights)));
        provisions.bindMaterialRights(address(rights));
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, rights.ACTION_VERIFY_TRANSFER(), true);

        uint256 secondApproval;
        (firstReceipt, secondApproval,) = _prepareM3(sourceRef);
        requestVm.warp(EPOCH + 44);
        _verifyReceipt(firstReceipt, EPOCH + 44);

        SparkV15MaterialRights.TransferTerms memory transfer;
        transfer.lessonId = LESSON;
        transfer.material = MAIN;
        transfer.publishedTermsRef = keccak256("agreed shares one third and two thirds");
        transfer.sourceRef = keccak256("transfer under the agreed material terms");
        transfer.transferor = SECOND_HOLDER;
        transfer.transferee = address(0x7912);
        transfer.units = 2;
        transfer.effectiveAt = transferAt;
        transfer.acceptThrough = transferAt;
        transfer.kind = SparkV15MaterialRights.TransferKind.Voluntary;
        transfer.unsettledEarlierUse = SparkV15MaterialRights.Assignment(0, 1);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        transfer.laterShortfall = SparkV15MaterialRights.Assignment(1, 1);
        bytes32 transferId = rights.transferCommitment(transfer);

        requestVm.warp(EPOCH + 45);
        if (acceptedBeforeSecondPayment) _acceptMaterialTransfer(rights, transfer, transferId);
        requestVm.prank(EXECUTOR);
        secondReceipt = payments.pay(secondApproval, 4);
        _verifyReceipt(secondReceipt, EPOCH + 45);
        require(provisions.provisioningNeed(LESSON) == 6, "settled first material retained");
        require(token.balanceOf(address(funds)) == 143 && funds.reservedUnits() == 137, "wrong material floor");

        requestVm.warp(acceptedBeforeSecondPayment ? EPOCH + 46 : transferAt);
        if (!acceptedBeforeSecondPayment) _acceptMaterialTransfer(rights, transfer, transferId);
        uint256 proof = _evidence(rights.transferEvidenceCommitment(transferId, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransfer(transfer, proof, _authority(ROLE_VERIFIER));
    }

    function _acceptMaterialTransfer(
        SparkV15MaterialRights rights,
        SparkV15MaterialRights.TransferTerms memory transfer,
        bytes32 transferId
    ) private {
        requestVm.prank(transfer.transferor);
        rights.acceptTransfer(transferId);
        requestVm.prank(transfer.transferee);
        rights.acceptTransfer(transferId);
    }

    function _assertSameSecondTransferCollection(uint256 receiptId) private {
        SparkV15MaterialRights rights = SparkV15MaterialRights(address(provisions.rights()));
        bytes32 scope = materials.originalFor(formId, MAIN);
        bytes32 transferId = rights.getTransfers(LESSON, MAIN)[0];
        address successor = rights.getTransfer(transferId).terms.transferee;
        require(rights.holderPortion(scope, SECOND_HOLDER, EPOCH + 48, EPOCH + 48) == 4, "collected share assigned");
        require(rights.holderPortion(scope, successor, EPOCH + 48, EPOCH + 48) == 0, "successor credited old cash");

        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, rights.ACTION_VERIFY_TRANSFER_COLLECTION(), true);
        SparkV15MaterialRights.SeatCollection[] memory seats = new SparkV15MaterialRights.SeatCollection[](1);
        seats[0] = SparkV15MaterialRights.SeatCollection(formId, 4);
        SparkV15MaterialRights.CollectionInput memory input = SparkV15MaterialRights.CollectionInput(
            transferId, scope, receiptId, SECOND_HOLDER, keccak256("same-second collection for the original seat"), seats
        );
        uint256 evidenceId = _evidence(rights.collectionEvidenceCommitment(input, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransferCollection(input, evidenceId, _authority(ROLE_VERIFIER));
        (, uint128 amount) = rights.getTransferCollection(transferId, scope, receiptId, formId);
        require(amount == 4, "original collection record changed");
    }

    function testM3VerifiedEarlierReceiptMakesSecondActualPaymentPossible() public {
        (uint256 firstReceipt, uint256 secondApproval, bytes32 scope) = _prepareM3();
        requestVm.warp(EPOCH + 44);
        _verifyReceipt(firstReceipt, EPOCH + 44);
        require(provisions.provisioningNeed(LESSON) == 12, "a partial receipt retired the entire provision");

        requestVm.warp(EPOCH + 45);
        bytes32 secondObligation = provisions.entitlementFor(scope, SECOND_HOLDER);
        require(
            provisions.paymentProtection(LESSON, secondObligation, 4) == 6,
            "same-charge overlap or second material lost"
        );
        _attributeFirstReceipt(scope, firstReceipt);
        require(
            provisions.paymentProtection(LESSON, secondObligation, 4) == 6, "explicit attribution was counted twice"
        );
        requestVm.prank(EXECUTOR);
        uint256 secondReceipt = payments.pay(secondApproval, 4);
        require(token.balanceOf(FIRST_HOLDER) == 2 && token.balanceOf(SECOND_HOLDER) == 4, "wrong actual cash receipts");
        require(payments.getReceipt(secondReceipt).paidAt == EPOCH + 45, "wrong second payment time");
        require(token.balanceOf(address(funds)) == 143, "wrong remaining custody");
        _verifyReceipt(secondReceipt, EPOCH + 45);
        SparkV15MaterialProvisions.MaterialReceipt memory first = provisions.getMaterialReceipt(firstReceipt);
        require(first.paidAt == EPOCH + 40 && first.verifiedAt == EPOCH + 44, "distinct payment and verification times");
        require(provisions.getMaterialReceipt(secondReceipt).verifiedAt == EPOCH + 45, "second verification time");
        require(provisions.provisioningNeed(LESSON) == 6, "paid original or independent material not reconciled");
        require(
            funds.paymentReserved(refund) == 120 && funds.creditBalance(funds.creditAccount(CREDIT_OWNER)) == 17,
            "other liabilities changed"
        );
    }

    function testRefundAndVerifiedMaterialReceiptsShareVaultAcrossLessons() public {
        (uint256 firstReceipt, uint256 secondApproval,) = _prepareM3();
        requestVm.warp(EPOCH + 44);
        _verifyReceipt(firstReceipt, EPOCH + 44);
        requestVm.warp(EPOCH + 45);
        requestVm.prank(EXECUTOR);
        uint256 secondReceipt = payments.pay(secondApproval, 4);
        _verifyReceipt(secondReceipt, EPOCH + 45);
        bytes32 materialForm = formId;
        _bookLaterRefundLesson(false);
        SparkV15CustomerRedress redress = _serviceRedress();
        _teachLaterRefundLesson();
        _recordServiceFault(redress.REMEDIES(), bytes32(uint256(100)), 2, EPOCH + 62);
        (bytes32 refundObligation, uint64 dueAt) = _establishLaterRefund(redress);
        (uint256 assessments, uint256 principal, uint256 received) = redress.refundStatus(formId);
        require(assessments == 1 && principal == 2 && received == 0, "expected unpaid lesson refund");
        SparkV15Booking.Form memory refundForm = booking.getForm(formId);
        require(refundForm.confirmation.debitedUnits == 4, "wrong original lesson debit");
        require(formId != materialForm && funds.paymentReserved(refundObligation) == 2, "separate refund liability");

        _assign(address(redress), funds.COMPENSATION_ROLE());
        authorityMatrix.setPermission(
            SparkV15.APP_ID, funds.COMPENSATION_ROLE(), funds.ACTION_GRANT_COMPENSATION(), true
        );
        requestVm.prank(CUSTOMER);
        redress.acceptStandardCompensation(formId);
        redress.issueCourseCredit(formId);
        require(
            funds.compensationCreditRemaining(refundForm.lessonId, refundForm.terms.placeId) == 4,
            "wrong compensation credit"
        );

        uint256 approval = _approveMaterialThrough(refundObligation, 2, dueAt + 1 days);
        requestVm.warp(dueAt);
        uint256 cashBefore = token.balanceOf(address(funds));
        uint256 creditBefore = funds.creditBalance(funds.creditAccount(CUSTOMER));
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 2);
        (,, received) = redress.refundStatus(formId);
        require(received == 2, "lesson refund not recorded");
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == creditBefore + 2, "customer balance not restored");
        require(token.balanceOf(address(funds)) == cashBefore, "credit restoration moved vault cash");
        require(payments.getApproval(approval).paid == 2, "refund approval not consumed");
        require(provisions.getMaterialReceipt(firstReceipt).verifiedAt == EPOCH + 44, "first verification changed");
        require(provisions.getMaterialReceipt(secondReceipt).verifiedAt == EPOCH + 45, "second verification changed");
        require(payments.getReceipt(firstReceipt).paidAt == EPOCH + 40, "first receipt changed");
        require(payments.getReceipt(secondReceipt).paidAt == EPOCH + 45, "second receipt changed");
        require(token.balanceOf(FIRST_HOLDER) == 2 && token.balanceOf(SECOND_HOLDER) == 4, "material payments changed");
        require(
            funds.compensationCreditRemaining(refundForm.lessonId, refundForm.terms.placeId) == 4,
            "refund spent accepted compensation credit"
        );
    }

    function testOrdinaryLessonUsesTheReserveForTheSameAcceptedCourseCredit() public {
        funds.bindMaterialProvisionsWithBookingCoverage(address(provisions));
        _bookLaterRefundLesson(true);
        SparkV15CustomerRedress redress = _serviceRedress();
        provisions.SERVICE_RESERVE().bindServiceReserve(address(redress), SERVICE_RESERVE_RECIPIENT);
        _teachLaterRefundLesson();
        bytes32 lessonId = bytes32(uint256(100));
        _recordServiceFault(redress.REMEDIES(), lessonId, 2, EPOCH + 62);
        _assign(address(redress), funds.COMPENSATION_ROLE());
        authorityMatrix.setPermission(
            SparkV15.APP_ID, funds.COMPENSATION_ROLE(), funds.ACTION_GRANT_COMPENSATION(), true
        );
        requestVm.prank(CUSTOMER);
        redress.acceptStandardCompensation(formId);

        uint256 totalBefore = funds.reservedUnits();
        uint256 cashBefore = token.balanceOf(address(funds));
        redress.issueCourseCredit(formId);
        require(funds.reservedUnits() == totalBefore, "course credit reserved twice");
        require(funds.lessonReserved(lessonId) == 10 && funds.lessonFeeBalance(lessonId) == 4, "wrong original hold");
        require(funds.compensationCreditRemaining(lessonId, bytes32(uint256(100))) == 4, "course credit unavailable");
        require(token.balanceOf(address(funds)) == cashBefore, "course credit spent cash");
    }

    function _bookLaterRefundLesson(bool retainCreditExpense) private {
        bytes32 lessonId = bytes32(uint256(100));
        requestVm.warp(EPOCH + 46);
        SparkV15Booking.LessonTerms memory lesson;
        lesson.lessonId = lessonId;
        lesson.provider = PROVIDER;
        lesson.tutor = TUTOR;
        lesson.coordinator = COORDINATOR;
        lesson.startsAt = EPOCH + 60;
        lesson.endsAt = EPOCH + 62;
        lesson.timeZoneRef = keccak256("UTC");
        lesson.tutorNoticeChannelRef = CHANNEL;
        lesson.tutorFee = 1;
        lesson.tutorAgreementRef = AGREEMENT;
        lesson.serviceTermsRef = DOCUMENTS;
        lesson.tutorPayTermsRef = AGREEMENT;
        lesson.providerResponsibilitiesRef = DOCUMENTS;
        lesson.tutorResponsibilitiesRef = AGREEMENT;
        lesson.startTermsRef = DOCUMENTS;
        lesson.documentsRef = DOCUMENTS;
        requestVm.prank(COORDINATOR);
        booking.publishLesson(lesson);
        SparkV15Booking.PlaceTerms memory place;
        place.placeId = bytes32(uint256(100));
        place.customer = CUSTOMER;
        place.payer = CUSTOMER;
        place.student = CUSTOMER;
        place.creditAccount = funds.creditAccount(CUSTOMER);
        place.studentNoticeChannelRef = keccak256("agreed student notice channel");
        place.normalFee = 4;
        place.payableFee = 4;
        requestVm.prank(COORDINATOR);
        formId = booking.publishForm(lessonId, place);
        token.mint(PROVIDER, 20);
        requestVm.prank(PROVIDER);
        require(token.transfer(address(funds), 20), "later lesson funding");
        _recharge(CUSTOMER, 4);
        this.verifyLaterLessonBacking(lessonId, retainCreditExpense);
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(lessonId);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(lessonId);
        requestVm.prank(PROVIDER);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Provider);
        requestVm.prank(TUTOR);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Tutor);
        requestVm.prank(CUSTOMER);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Customer);
        requestVm.prank(COORDINATOR);
        booking.confirmPlace(formId, bytes32(0), 0, new SparkV15Funds.RechargeDebit[](0));
    }

    function verifyLaterLessonBacking(bytes32 lessonId, bool retainCreditExpense) external {
        bytes32[] memory forms = _forms();
        bytes32 inventory = keccak256("verified later lesson funding");
        SparkV15FundingCases fundingCases = provisions.FUNDING_CASES();
        SparkV15FundingCases.FundingScenario[] memory scenarios;
        if (retainCreditExpense) {
            scenarios = new SparkV15FundingCases.FundingScenario[](1);
            scenarios[0].teachingBegan = true;
            scenarios[0].forms = forms;
            scenarios[0].outcomes = new bytes32[](1);
            scenarios[0].outcomes[0] = keccak256("partial delivery with the standard compensation");
            scenarios[0].expenses = new SparkV15FundingCases.Expense[](3);
            scenarios[0].expenses[0].referenceId = fundingCases.bookingExposureReference(formId, 0);
            scenarios[0].expenses[0].units = 2;
            scenarios[0].expenses[1].referenceId = fundingCases.bookingExposureReference(formId, 1);
            scenarios[0].expenses[1].units = 4;
            scenarios[0].expenses[2].referenceId = keccak256("separate teacher wage");
            scenarios[0].expenses[2].units = 1;
            inventory = fundingCases.inventoryReference(lessonId, scenarios);
        }
        uint256 proof = _evidence(booking.prefundingCommitment(lessonId, forms, 10, inventory));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(lessonId, forms, 10, inventory, proof);
        if (retainCreditExpense) fundingCases.retainInventory(lessonId, scenarios);
    }

    function _teachLaterRefundLesson() private {
        bytes32 lessonId = bytes32(uint256(100));
        bytes32 notice = keccak256("later lesson notice");
        uint256 proof = _evidence(booking.studentNoticeCommitment(formId, EPOCH + 46, notice));
        requestVm.prank(COORDINATOR);
        booking.recordStudentNotice(formId, EPOCH + 46, notice, proof);
        proof = _evidence(booking.tutorNoticeCommitment(lessonId, CHANNEL, EPOCH + 46, notice));
        requestVm.prank(COORDINATOR);
        booking.recordTutorNotice(lessonId, CHANNEL, EPOCH + 46, notice, proof);
        requestVm.warp(EPOCH + 60);
        address[] memory attending = new address[](1);
        attending[0] = CUSTOMER;
        SparkV15Booking.StartObservation memory start =
            SparkV15Booking.StartObservation(EPOCH + 60, true, attending, keccak256("actual later start"), bytes32(0));
        proof = _evidence(booking.teachingStartCommitment(lessonId, start));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingStarted(lessonId, start, proof);
        requestVm.warp(EPOCH + 62);
        bytes32 end = keccak256("actual later end");
        proof = _evidence(booking.teachingEndCommitment(lessonId, EPOCH + 62, end));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingEnded(lessonId, EPOCH + 62, end, proof);
    }

    function _establishLaterRefund(SparkV15CustomerRedress redress) private returns (bytes32, uint64) {
        (SparkV15CustomerRedress.RefundAssessment memory assessment, SparkV15Payments.PaymentTerms memory terms) =
            redress.previewRefund(formId, SparkV15CustomerRedress.RefundBasis.OriginalRelief, VERIFIER_ACTOR);
        require(assessment.principal == 2 && terms.originalDebitAmount == 4, "wrong assessed refund");
        require(terms.originalDebitAccount == funds.creditAccount(CUSTOMER), "wrong original account");
        uint256 proof = _evidence(assessment.basis);
        requestVm.prank(VERIFIER_ACTOR);
        uint256 index = redress.assessRefund(
            formId, SparkV15CustomerRedress.RefundBasis.OriginalRelief, proof, _authority(ROLE_VERIFIER)
        );
        proof = _evidence(payments.paymentEvidenceCommitment(terms, assessment.basis));
        return (redress.establishRefundPayment(formId, index, proof), terms.dueAt);
    }

    function testM3ActualFirstPaymentWithLateEvidenceCannotFundTheEarlierSecondPayment() public {
        (uint256 firstReceipt, uint256 secondApproval, bytes32 scope) = _prepareM3();
        bytes32 secondObligation = provisions.entitlementFor(scope, SECOND_HOLDER);
        requestVm.warp(EPOCH + 45);
        require(
            provisions.paymentProtection(LESSON, secondObligation, 4) == 8, "unverified transfer counted for protection"
        );
        requestVm.expectRevert(SparkV15MaterialProvisions.InsufficientMaterialBacking.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(secondApproval, 4);
        require(token.balanceOf(address(funds)) == 147, "refused payment changed custody");
        require(
            token.balanceOf(FIRST_HOLDER) == 2 && token.balanceOf(SECOND_HOLDER) == 0,
            "refusal changed actual recipients"
        );
        require(
            funds.paymentReserved(secondObligation) == 4 && payments.getApproval(secondApproval).paid == 0,
            "refusal consumed backing or approval"
        );
        require(payments.getReceipt(firstReceipt).paidAt == EPOCH + 40, "original actual transfer absent");
        require(provisions.getMaterialReceipt(firstReceipt).verifiedAt == 0, "unverified payment gained a verification");

        requestVm.warp(EPOCH + 46);
        uint256 proof = _evidence(provisions.receiptEvidenceCommitment(firstReceipt, EPOCH + 44, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15MaterialProvisions.InvalidMaterialReceipt.selector);
        requestVm.prank(VERIFIER_ACTOR);
        provisions.verifyMaterialReceipt(firstReceipt, EPOCH + 44, proof, _authority(ROLE_VERIFIER));
        _verifyReceipt(firstReceipt, EPOCH + 46);
        require(provisions.getMaterialReceipt(firstReceipt).verifiedAt == EPOCH + 46, "late verification business date");
        require(payments.getApproval(secondApproval).paid == 0, "late evidence reused refused payment");
    }

    function testVerifiedExternalReceiptChangesProtectionAtVerificationAndReturnChangesOnlyTheLaterBalance() public {
        _checkExternalReceiptTiming(address(0), false);
    }

    function testDirectExternalReceiptToMaterialHolderCountsWhenAnotherCollectorIsNamed() public {
        _checkExternalReceiptTiming(address(0x79AA), false);
    }

    function testMaterialProtectionUsesWhenAnExistingExternalReceiptWasAttributed() public {
        _checkExternalReceiptTiming(address(0), true);
    }

    function _checkExternalReceiptTiming(address collector, bool lateAttribution) private {
        bytes32 obligationId = this.prepareMaterialPartForObservation(collector);
        if (collector != address(0)) {
            SparkV15Payments.Obligation memory obligation = payments.getObligation(obligationId);
            require(obligation.destination == collector && obligation.beneficiary == FIRST_HOLDER, "collector not set");
        }
        SparkV15PaymentObservations observer =
            new SparkV15PaymentObservations(address(payments), requestAllocation, ROLE_VERIFIER);
        payments.bindPaymentObservations(address(observer));
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, observer.ACTION_VERIFY_OBSERVATION(), true);
        SparkV15ObservedMaterialReceipts observed = provisions.MATERIAL_BACKING().OBSERVED_RECEIPTS();

        SparkV15PaymentObservations.Transfer memory outward =
            _externalTransfer(EPOCH + 40, 100, PROVIDER, FIRST_HOLDER, 2);
        require(
            token.balanceOf(FIRST_HOLDER) == 2 && token.balanceOf(address(funds)) == 149,
            "external rail moved the vault"
        );
        requestVm.warp(EPOCH + 44);
        require(provisions.paymentProtection(LESSON, bytes32(0), 0) == 12, "unverified observation covered protection");
        bytes32 attributionRef = keccak256("exact independently verified material rail");
        SparkV15PaymentObservations.PaymentTerms memory terms = SparkV15PaymentObservations.PaymentTerms(
            obligationId, FIRST_HOLDER, outward, EPOCH + 44,
            lateAttribution ? bytes32(0) : attributionRef, lateAttribution ? address(0) : PROVIDER
        );
        uint256 proof = _evidence(observer.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 observedId = observer.verifyPayment(terms, proof, _authority(ROLE_VERIFIER));
        uint64 qualifiedAt = EPOCH + 44;
        if (lateAttribution) {
            require(provisions.paymentProtection(LESSON, bytes32(0), 0) == 12, "unattributed cash opened protection");
            qualifiedAt = EPOCH + 45;
            requestVm.warp(qualifiedAt);
            SparkV15PaymentObservations.PaymentAttributionTerms memory attribution =
                SparkV15PaymentObservations.PaymentAttributionTerms(observedId, FIRST_HOLDER, attributionRef, PROVIDER);
            SparkV15PaymentObservations.ReturnProof[] memory priorReturns = new SparkV15PaymentObservations.ReturnProof[](0);
            proof = _evidence(observer.attributionEvidenceCommitment(attribution, priorReturns));
            requestVm.prank(VERIFIER_ACTOR);
            observer.verifyPaymentAttribution(
                attribution, proof, priorReturns, _authority(ROLE_VERIFIER)
            );
        }
        require(provisions.paymentProtection(LESSON, bytes32(0), 0) == 10, "qualified external payment absent");
        require(
            funds.paymentReserved(obligationId) == 0 && payments.getObligation(obligationId).paid == 2,
            "wrong external settlement"
        );
        require(
            observed.retainedPaymentBefore(obligationId, observedId, EPOCH + 45, qualifiedAt - 1) == 0,
            "later proof was backdated"
        );

        requestVm.warp(EPOCH + 46);
        (uint128 retained, uint64 occurredAt, uint64 verifiedAt, uint64 archivedAt) =
            observed.retainedPayment(obligationId, observedId);
        require(
            retained == 2 && occurredAt == EPOCH + 40 && verifiedAt == qualifiedAt && archivedAt == 0,
            "external verification stays distinct from local archival"
        );
        require(provisions.paymentProtection(LESSON, bytes32(0), 0) == 10, "filing changed economic protection");

        SparkV15PaymentObservations.Transfer memory recovery =
            _externalTransfer(EPOCH + 47, 102, FIRST_HOLDER, PROVIDER, 1);
        requestVm.warp(EPOCH + 48);
        SparkV15PaymentObservations.ReturnTerms memory returnTerms = SparkV15PaymentObservations.ReturnTerms(
            observedId, recovery, EPOCH + 48, keccak256("verified actual external return")
        );
        proof = _evidence(observer.returnEvidenceCommitment(returnTerms));
        requestVm.prank(VERIFIER_ACTOR);
        observer.verifyReturn(returnTerms, proof, _authority(ROLE_VERIFIER));
        require(
            token.balanceOf(FIRST_HOLDER) == 1 && provisions.paymentProtection(LESSON, bytes32(0), 0) == 11,
            "observed return did not restore protection"
        );
        require(
            observed.retainedPaymentBefore(obligationId, observedId, EPOCH + 45, EPOCH + 48) == 2,
            "later return rewrote historical retained amount"
        );
    }

    function prepareMaterialPartForObservation(address collector) external returns (bytes32) {
        (,, bytes32 scopeId) = _prepareMaterialApprovals(M3_ORIGINAL_CHARGE, collector);
        return provisions.entitlementFor(scopeId, FIRST_HOLDER);
    }

    function _externalTransfer(uint64 occurredAt, uint64 blockNumber, address from, address to, uint128 amount)
        private
        returns (SparkV15PaymentObservations.Transfer memory)
    {
        requestVm.warp(occurredAt);
        observationVm.roll(blockNumber);
        if (from == PROVIDER) token.mint(PROVIDER, amount);
        requestVm.prank(from);
        require(token.transfer(to, amount), "actual external transfer");
        bytes32 blockHash = keccak256(abi.encode("observed local block", blockNumber));
        observationVm.roll(blockNumber + 1);
        observationVm.setBlockhash(blockNumber, blockHash);
        return SparkV15PaymentObservations.Transfer(
            keccak256(abi.encode("verified local transfer", from, to, amount, occurredAt)),
            blockHash,
            blockNumber,
            0,
            occurredAt,
            from,
            to,
            amount
        );
    }

    function _prepareM3() private returns (uint256 firstReceipt, uint256 secondApproval, bytes32 scopeId) {
        return _prepareM3(M3_ORIGINAL_CHARGE);
    }

    function _prepareM3(bytes32 sourceRef)
        private
        returns (uint256 firstReceipt, uint256 secondApproval, bytes32 scopeId)
    {
        uint256 firstApproval;
        (firstApproval, secondApproval, scopeId) = _prepareMaterialApprovals(sourceRef, address(0));
        requestVm.warp(EPOCH + 40);
        requestVm.prank(EXECUTOR);
        firstReceipt = payments.pay(firstApproval, 2);
        require(
            payments.getReceipt(firstReceipt).paidAt == EPOCH + 40 && token.balanceOf(FIRST_HOLDER) == 2,
            "missing first actual transfer"
        );
        require(token.balanceOf(address(funds)) == 147, "first payment did not leave ten potentially available");
        require(provisions.getMaterialReceipt(firstReceipt).verifiedAt == 0, "transfer also verified itself");
    }

    function _prepareMaterialApprovals(bytes32 sourceRef, address collector)
        private
        returns (uint256 firstApproval, uint256 secondApproval, bytes32 scopeId)
    {
        _book(12, 0);
        requestVm.warp(EPOCH + 20);
        _recordProvision(MAIN, 6);
        requestVm.warp(EPOCH + 21);
        _recordProvision(OTHER, 6);
        require(provisions.provisioningNeed(LESSON) == 12, "two estimates did not protect twelve");
        _teach();
        requestVm.warp(EPOCH + 33);
        SparkV15Materials.UseCheck memory finding = SparkV15Materials.UseCheck(
            formId,
            MAIN,
            EPOCH + 30,
            EPOCH + 33,
            SparkV15Materials.UseSource.LessonRecord,
            keccak256("actual teaching service"),
            keccak256("verified per-seat material use"),
            false,
            false,
            bytes32(0)
        );
        uint256 proof = _materialEvidence(materials.ACTION_VERIFY_USE(), abi.encode(finding));
        requestVm.prank(COORDINATOR);
        materials.verifyUse(finding, proof);
        requestVm.warp(EPOCH + 34);
        SparkV15Materials.GrossInput memory gross =
            SparkV15Materials.GrossInput(LESSON, MAIN, bytes32(0), sourceRef, EPOCH + 34, _forms());
        proof = _materialEvidence(materials.ACTION_RECORD_GROSS(), abi.encode(gross));
        requestVm.prank(COORDINATOR);
        scopeId = materials.recordGross(gross, proof);
        require(materials.getHistoricalCharge(scopeId, formId).amount == 6, "wrong gross from normal fee");
        requestVm.warp(EPOCH + 35);
        if (collector != address(0)) {
            requestVm.prank(FIRST_HOLDER);
            provisions.agreeMaterialRecipient(scopeId, collector);
        }
        bytes32 firstPart = _entitlement(scopeId, FIRST_HOLDER);
        bytes32 secondPart = _entitlement(scopeId, SECOND_HOLDER);
        require(
            funds.paymentReserved(firstPart) == 2 && funds.paymentReserved(secondPart) == 4, "wrong assigned shares"
        );
        requestVm.warp(EPOCH + 38);
        firstApproval = _approveMaterial(firstPart, 2);
        secondApproval = _approveMaterial(secondPart, 4);
    }

    function _teach() private {
        requestVm.warp(EPOCH + 22);
        bytes32 notice = keccak256("notice actually delivered");
        uint256 proof = _evidence(booking.studentNoticeCommitment(formId, EPOCH + 22, notice));
        requestVm.prank(COORDINATOR);
        booking.recordStudentNotice(formId, EPOCH + 22, notice, proof);
        proof = _evidence(booking.tutorNoticeCommitment(LESSON, CHANNEL, EPOCH + 22, notice));
        requestVm.prank(COORDINATOR);
        booking.recordTutorNotice(LESSON, CHANNEL, EPOCH + 22, notice, proof);
        requestVm.warp(EPOCH + 30);
        address[] memory attending = new address[](1);
        attending[0] = CUSTOMER;
        SparkV15Booking.StartObservation memory start =
            SparkV15Booking.StartObservation(EPOCH + 30, true, attending, keccak256("actual start"), bytes32(0));
        proof = _evidence(booking.teachingStartCommitment(LESSON, start));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingStarted(LESSON, start, proof);
        requestVm.warp(EPOCH + 32);
        bytes32 end = keccak256("actual end");
        proof = _evidence(booking.teachingEndCommitment(LESSON, EPOCH + 32, end));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingEnded(LESSON, EPOCH + 32, end, proof);
    }

    function _entitlement(bytes32 scopeId, address holder) private returns (bytes32 obligationId) {
        address collector = provisions.agreedRecipient(scopeId, holder);
        SparkV15MaterialProvisions.EntitlementInput memory input = SparkV15MaterialProvisions.EntitlementInput(
            scopeId,
            holder,
            collector == address(0) ? holder : collector,
            EPOCH + 35,
            EPOCH + 80,
            keccak256("verified historical holder shares")
        );
        (SparkV15Payments.PaymentTerms memory terms, bytes32 basis) =
            provisions.previewEntitlement(input, VERIFIER_ACTOR);
        bytes32 schedule =
            keccak256(abi.encode(keccak256("spark.v1.5.material-schedule"), basis, input.verifiedAt, true));
        uint256 proof = _evidence(payments.paymentEvidenceCommitment(terms, schedule));
        requestVm.prank(VERIFIER_ACTOR);
        return provisions.establishEntitlement(input, proof, _authority(ROLE_VERIFIER));
    }

    function _approveMaterial(bytes32 obligationId, uint128 amount) private returns (uint256 requestId) {
        return _approveMaterialThrough(obligationId, amount, EPOCH + 60);
    }

    function _approveMaterialThrough(bytes32 obligationId, uint128 amount, uint64 through)
        private
        returns (uint256 requestId)
    {
        SparkV15Payments.ApprovalTerms memory terms =
            SparkV15Payments.ApprovalTerms(obligationId, EXECUTOR, amount, through, 0);
        bytes32 parameters = payments.approvalParameters(terms);
        uint256 status = _createRequestState(
            address(payments), SparkV15.RESPONSE_APPROVE_PAYMENT, parameters, SparkV15.APPROVAL_BURDEN, through - 1
        );
        requestId = _createRequest(
            AVARequestAllocation.RequestInput(
                status,
                address(payments),
                SparkV15.RESPONSE_APPROVE_PAYMENT,
                parameters,
                SparkV15.APPROVAL_BURDEN,
                through - 1
            )
        );
        requestVm.startPrank(PROVIDER);
        requestAllocation.approve(requestId, ROLE_ALLOCATOR, _actorId(PROVIDER, ROLE_ALLOCATOR));
        payments.recordApproval(requestId, terms);
        requestVm.stopPrank();
    }

    function _verifyReceipt(uint256 receiptId, uint64 verifiedAt) private {
        uint256 proof = _evidence(provisions.receiptEvidenceCommitment(receiptId, verifiedAt, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        provisions.verifyMaterialReceipt(receiptId, verifiedAt, proof, _authority(ROLE_VERIFIER));
    }

    function _attributeFirstReceipt(bytes32 scope, uint256 receiptId) private {
        SparkV15MaterialBacking backing = provisions.MATERIAL_BACKING();
        SparkV15MaterialBacking.SeatReceipt[] memory seats = new SparkV15MaterialBacking.SeatReceipt[](1);
        seats[0] = SparkV15MaterialBacking.SeatReceipt(keccak256("different seat"), 2);
        SparkV15MaterialBacking.ReceiptAllocationInput memory allocation = SparkV15MaterialBacking.ReceiptAllocationInput(
            scope, receiptId, keccak256("where the actual receipt applies"), seats
        );
        uint256 proof = _evidence(backing.receiptAllocationEvidenceCommitment(allocation, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15MaterialBacking.InvalidReceiptAllocation.selector);
        requestVm.prank(VERIFIER_ACTOR);
        backing.verifyReceiptAllocation(allocation, proof, _authority(ROLE_VERIFIER));

        allocation.seats[0].formId = formId;
        proof = _evidence(backing.receiptAllocationEvidenceCommitment(allocation, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        backing.verifyReceiptAllocation(allocation, proof, _authority(ROLE_VERIFIER));
    }

    function _materialEvidence(bytes32 action, bytes memory payload) private returns (uint256) {
        return _evidence(materials.operationEvidenceCommitment(LESSON, action, COORDINATOR, keccak256(payload)));
    }

    function _bookTwoSeatMaterialLesson() private returns (bytes32[] memory forms, SparkV15CustomerRedress redress) {
        funds.bindMaterialProvisionsWithBookingCoverage(address(provisions));
        SparkV15Materials.Terms memory terms = _terms();
        SparkV15Materials.MaterialTerms[] memory licensed = new SparkV15Materials.MaterialTerms[](1);
        licensed[0] = SparkV15Materials.MaterialTerms(MAIN, 10, terms.materials[0].holders, new address[](0));
        terms.materials = licensed;
        bytes32 termsRef = materials.termsCommitment(terms);
        _publishMaterialLesson(termsRef, GROUP_WAGE_UNITS, EPOCH + 25);
        _adoptMaterialTerms(terms, termsRef);

        forms = new bytes32[](2);
        SparkV15Funds.RechargeDebit[] memory debitsA = new SparkV15Funds.RechargeDebit[](1);
        SparkV15Funds.RechargeDebit[] memory debitsB = new SparkV15Funds.RechargeDebit[](1);
        debitsA[0] = SparkV15Funds.RechargeDebit(_recharge(CUSTOMER, GROUP_A_FEE, GROUP_A_FEE, EPOCH + 25), GROUP_A_FEE);
        debitsB[0] =
            SparkV15Funds.RechargeDebit(_recharge(GROUP_STUDENT_B, GROUP_B_FEE, GROUP_B_FEE, EPOCH + 25), GROUP_B_FEE);
        formId = _publishTwoSeatForm(PLACE, CUSTOMER, GROUP_A_FEE, debitsA, false);
        forms[0] = formId;
        forms[1] = _publishTwoSeatForm(bytes32(uint256(2)), GROUP_STUDENT_B, GROUP_B_FEE, debitsB, true);

        token.mint(PROVIDER, 230);
        requestVm.prank(PROVIDER);
        require(token.transfer(address(funds), 230), "missing provider prefunding");
        SparkV15FundingCases fundingCases = provisions.FUNDING_CASES();
        SparkV15FundingCases.FundingScenario[] memory scenarios = _twoSeatScenarios(forms, termsRef);
        bytes32 inventory = fundingCases.inventoryReference(LESSON, scenarios);
        uint256 proof = _evidence(booking.prefundingCommitment(LESSON, forms, 230, inventory));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, forms, 230, inventory, proof);
        fundingCases.retainInventory(LESSON, scenarios);
        require(fundingCases.bookingCoverageRequired(LESSON) == 214, "wrong highest joint booking scenario");

        requestVm.warp(EPOCH + 3);
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(LESSON);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(LESSON);
        _confirmTwoSeatForm(forms[0], CUSTOMER, debitsA);
        _confirmTwoSeatForm(forms[1], GROUP_STUDENT_B, debitsB);
        redress = _serviceRedress();
        provisions.SERVICE_RESERVE().bindServiceReserve(address(redress), SERVICE_RESERVE_RECIPIENT);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_SOURCE, redress.REMEDIES().ACTION_RECORD_UNDISPUTED_PROVIDER_FAULT(), true
        );

        requestVm.warp(EPOCH + 20);
        SparkV15MaterialProvisions.ProvisionInput memory estimate =
            SparkV15MaterialProvisions.ProvisionInput(forms[1], MAIN, GROUP_MATERIAL_UNITS, GROUP_MATERIAL_COST);
        proof = _evidence(provisions.provisionEvidenceCommitment(estimate, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        provisions.recordProvision(estimate, proof, _authority(ROLE_VERIFIER));
        require(funds.lessonReserved(LESSON) == 310 && funds.lessonFeeBalance(LESSON) == 80, "seat fees not debited");
    }

    function _publishTwoSeatForm(
        bytes32 placeId,
        address student,
        uint128 fee,
        SparkV15Funds.RechargeDebit[] memory debits,
        bool hasMaterial
    ) private returns (bytes32) {
        SparkV15Booking.PlaceTerms memory place;
        place.placeId = placeId;
        place.customer = student;
        place.payer = student;
        place.student = student;
        place.creditAccount = funds.creditAccount(student);
        place.studentNoticeChannelRef = keccak256(abi.encode("agreed notice for this place", placeId));
        place.normalFee = fee;
        place.payableFee = fee;
        place.rechargeDebitsHash = keccak256(abi.encode(debits));
        if (hasMaterial) {
            place.materialsBundleRef = BUNDLE;
            place.materialPayer = PROVIDER;
        }
        requestVm.prank(COORDINATOR);
        return booking.publishForm(LESSON, place);
    }

    function _confirmTwoSeatForm(bytes32 seatForm, address student, SparkV15Funds.RechargeDebit[] memory debits)
        private
    {
        _provideTerms(seatForm, student);
        _provideTerms(seatForm, TUTOR);
        requestVm.prank(PROVIDER);
        booking.acceptForm(seatForm, SparkV15Booking.Acceptance.Provider);
        requestVm.prank(TUTOR);
        booking.acceptForm(seatForm, SparkV15Booking.Acceptance.Tutor);
        requestVm.prank(student);
        booking.acceptForm(seatForm, SparkV15Booking.Acceptance.Customer);
        requestVm.prank(COORDINATOR);
        booking.confirmPlace(seatForm, bytes32(0), 0, debits);
        require(funds.creditBalance(funds.creditAccount(student)) == 0, "signed debit was not taken");
    }

    function _twoSeatScenarios(bytes32[] memory forms, bytes32 termsRef)
        private
        view
        returns (SparkV15FundingCases.FundingScenario[] memory scenarios)
    {
        GroupRedress[6] memory aAlternatives = [
            GroupRedress.StandardNoDelivery,
            GroupRedress.FullRefund,
            GroupRedress.StandardPartial,
            GroupRedress.FailedPartialRemedy,
            GroupRedress.FullRefund,
            GroupRedress.None
        ];
        SparkV15LessonRemedies.TeachingReceived[6] memory aDelivery = [
            SparkV15LessonRemedies.TeachingReceived.NoneDelivered,
            SparkV15LessonRemedies.TeachingReceived.NoneDelivered,
            SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered,
            SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered,
            SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered,
            SparkV15LessonRemedies.TeachingReceived.FullyDelivered
        ];
        // B may use the material independently during the group opening while receiving no instruction.
        // Keep its use estimate alongside each B redress option at every A outcome.
        GroupRedress[5] memory bAlternatives = [
            GroupRedress.None,
            GroupRedress.StandardPartial,
            GroupRedress.FailedPartialRemedy,
            GroupRedress.FullRefund,
            GroupRedress.StandardNoDelivery
        ];
        scenarios = new SparkV15FundingCases.FundingScenario[](34);
        uint256 index;
        for (uint256 i; i < aAlternatives.length; ++i) {
            for (uint256 j; j < bAlternatives.length; ++j) {
                scenarios[index++] =
                    _twoSeatScenario(forms, termsRef, true, aDelivery[i], aAlternatives[i], bAlternatives[j]);
            }
        }
        for (uint256 i; i < 2; ++i) {
            for (uint256 j; j < 2; ++j) {
                scenarios[index++] =
                    _twoSeatScenario(forms, termsRef, false, aDelivery[0], aAlternatives[i], aAlternatives[j]);
            }
        }
    }

    function _twoSeatScenario(
        bytes32[] memory forms,
        bytes32 termsRef,
        bool started,
        SparkV15LessonRemedies.TeachingReceived deliveryA,
        GroupRedress redressA,
        GroupRedress redressB
    ) private view returns (SparkV15FundingCases.FundingScenario memory) {
        uint128[3] memory exposureA = _groupExposure(redressA, GROUP_A_FEE);
        uint128[3] memory exposureB = _groupExposure(redressB, GROUP_B_FEE);
        uint256 expenseCount = started ? 2 : 0;
        for (uint256 i; i < 3; ++i) {
            if (exposureA[i] != 0) ++expenseCount;
            if (exposureB[i] != 0) ++expenseCount;
        }
        SparkV15FundingCases.Expense[] memory expenses = new SparkV15FundingCases.Expense[](expenseCount);
        uint256 index = _writeGroupExposure(expenses, 0, forms[0], exposureA);
        index = _writeGroupExposure(expenses, index, forms[1], exposureB);
        if (started) {
            SparkV15FundingCases.MaterialPortion[] memory portions = new SparkV15FundingCases.MaterialPortion[](1);
            portions[0] = SparkV15FundingCases.MaterialPortion(forms[1], GROUP_MATERIAL_UNITS);
            expenses[index++] = SparkV15FundingCases.Expense(
                GROUP_MATERIAL_COST, bytes32(0), MAIN, termsRef, GROUP_MATERIAL_UNITS, portions
            );
            expenses[index] = _groupCost(GROUP_TUTOR_WAGE, GROUP_WAGE_UNITS);
        }
        bytes32[] memory outcomes = new bytes32[](2);
        outcomes[0] = started
            ? provisions.FUNDING_CASES().deliveryOutcome(forms[0], uint8(deliveryA))
            : keccak256(abi.encode("A: no group opening", redressA));
        outcomes[1] = keccak256(abi.encode("B: independent option in this group case", started, redressB));
        return SparkV15FundingCases.FundingScenario(started, forms, outcomes, expenses);
    }

    function _groupExposure(GroupRedress option, uint128 fee) private pure returns (uint128[3] memory) {
        if (option == GroupRedress.FullRefund) return [fee, 0, 0];
        if (option == GroupRedress.StandardNoDelivery) return [fee, fee, fee / 2];
        if (option == GroupRedress.StandardPartial) return [fee / 2, fee, 0];
        // A failed remedy can require full restoration after the customer's already spent credit.
        if (option == GroupRedress.FailedPartialRemedy) return [fee, fee, 0];
        return [uint128(0), 0, 0];
    }

    function _writeGroupExposure(
        SparkV15FundingCases.Expense[] memory expenses,
        uint256 index,
        bytes32 seatForm,
        uint128[3] memory exposure
    ) private view returns (uint256) {
        SparkV15FundingCases fundingCases = provisions.FUNDING_CASES();
        for (uint8 category; category < 3; ++category) {
            if (exposure[category] == 0) continue;
            expenses[index++] =
                _groupCost(fundingCases.bookingExposureReference(seatForm, category), exposure[category]);
        }
        return index;
    }

    function _groupCost(bytes32 referenceId, uint128 units) private pure returns (SparkV15FundingCases.Expense memory) {
        return SparkV15FundingCases.Expense(
            referenceId, bytes32(0), bytes32(0), bytes32(0), units, new SparkV15FundingCases.MaterialPortion[](0)
        );
    }

    function _teachTwoSeatLesson(bytes32[] memory forms, SparkV15Booking.ServiceStatus deliveryA) private {
        requestVm.warp(EPOCH + 22);
        bytes32 notice = keccak256("both students and tutor received agreed notices");
        for (uint256 i; i < forms.length; ++i) {
            uint256 studentNotice = _evidence(booking.studentNoticeCommitment(forms[i], EPOCH + 22, notice));
            requestVm.prank(COORDINATOR);
            booking.recordStudentNotice(forms[i], EPOCH + 22, notice, studentNotice);
        }
        uint256 proof = _evidence(booking.tutorNoticeCommitment(LESSON, CHANNEL, EPOCH + 22, notice));
        requestVm.prank(COORDINATOR);
        booking.recordTutorNotice(LESSON, CHANNEL, EPOCH + 22, notice, proof);

        requestVm.warp(EPOCH + 25);
        bytes32 register = keccak256("independently checked exact confirmed two-seat register");
        proof = _evidence(booking.rosterLockCommitment(LESSON, register));
        requestVm.prank(COORDINATOR);
        booking.lockRoster(LESSON, register, proof);
        bytes32[] memory locked = booking.getLockedForms(LESSON);
        require(locked.length == 2 && locked[0] == forms[0] && locked[1] == forms[1], "missing exact group roster");

        bool aAttended = deliveryA == SparkV15Booking.ServiceStatus.PartiallyDelivered;
        address[] memory takingLesson = new address[](aAttended ? 2 : 1);
        takingLesson[0] = GROUP_STUDENT_B;
        if (aAttended) takingLesson[1] = CUSTOMER;
        requestVm.warp(EPOCH + 30);
        SparkV15Booking.StartObservation memory start = SparkV15Booking.StartObservation(
            EPOCH + 30, true, takingLesson, keccak256("actual opening with B in the teaching room"), bytes32(0)
        );
        proof = _evidence(booking.teachingStartCommitment(LESSON, start));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingStarted(LESSON, start, proof);
        require(
            booking.getTeaching(LESSON).startPermission == SparkV15Booking.StartPermission.Permitted,
            "group did not open lawfully"
        );

        requestVm.warp(EPOCH + 32);
        bytes32 end = keccak256("B reached the agreed end of the lesson");
        proof = _evidence(booking.teachingEndCommitment(LESSON, EPOCH + 32, end));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingEnded(LESSON, EPOCH + 32, end, proof);

        requestVm.warp(EPOCH + 33);
        bytes32 aReceived = aAttended ? keccak256("student's statement of the part received") : bytes32(0);
        bytes32 aMissed = keccak256("student's statement of the instruction missed");
        _twoSeatReport(forms[0], CUSTOMER, aAttended, deliveryA, aReceived, aMissed);
        _twoSeatReport(
            forms[1],
            GROUP_STUDENT_B,
            true,
            SparkV15Booking.ServiceStatus.FullyDelivered,
            keccak256("B's account of all agreed teaching"),
            bytes32(0)
        );
    }

    function _twoSeatReport(
        bytes32 seatForm,
        address student,
        bool attended,
        SparkV15Booking.ServiceStatus delivery,
        bytes32 received,
        bytes32 missed
    ) private {
        bytes32 attendance = keccak256("student's separate account of attendance");
        uint256 proof = _evidence(booking.attendanceCommitment(seatForm, attended, attendance));
        requestVm.prank(student);
        booking.recordAttendance(seatForm, attended, attendance, proof);
        proof = _evidence(booking.serviceFeedbackCommitment(seatForm, delivery, received, missed));
        requestVm.prank(student);
        booking.recordServiceFeedback(seatForm, delivery, received, missed, proof);
    }

    function _recordTwoSeatProviderFault(
        SparkV15CustomerRedress redress,
        SparkV15LessonRemedies.TeachingReceived delivery,
        uint128 lostFee
    ) private {
        SparkV15LessonRemedies remedies = redress.REMEDIES();
        bool none = delivery == SparkV15LessonRemedies.TeachingReceived.NoneDelivered;
        SparkV15LessonRemedies.FaultFinding memory finding;
        finding.kind = SparkV15LessonRemedies.FaultKind.ProviderArrangementError;
        finding.originalOccurredAt = EPOCH + 32;
        finding.groundRef = keccak256("the provider mistakenly assigned A to a separate room during agreed teaching");
        finding.affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        finding.affected[0] = SparkV15LessonRemedies.AffectedPlace(
            formId,
            delivery,
            none
                ? SparkV15LessonRemedies.Participation.ReadyAsAgreed
                : SparkV15LessonRemedies.Participation.AttendedAsAgreed,
            lostFee,
            true,
            keccak256(abi.encode(LESSON, formId, EPOCH + 30, EPOCH + 32, "independent room and instruction record"))
        );
        bytes32 matter = provisions.FUNDING_CASES().deliveryMatter(formId);
        bytes32 undisputed = keccak256("coordinator independently checked provider and student records and no dispute");
        uint256 proof = _evidence(remedies.providerFaultCommitment(formId, matter, finding, undisputed, COORDINATOR));
        requestVm.prank(COORDINATOR);
        bytes32 caseId = remedies.recordUndisputedProviderFault(formId, matter, finding, undisputed, proof);
        require(remedies.isOperative(caseId, 1) && remedies.placeFaultCase(formId) == caseId, "missing seat finding");
        require(remedies.getFault(caseId, 1).caseEvidenceId == proof, "finding lost its usable evidence");
        require(remedies.getPlaceFinding(caseId, 1, formId).teaching == delivery, "wrong seat delivery");
        require(remedies.allowsTutorWage(LESSON, TUTOR), "separate tutor wage was lost");
    }

    function _assertOriginalRelief(SparkV15CustomerRedress redress, uint128 refundAmount) private {
        requestVm.prank(CUSTOMER);
        redress.acceptStandardCompensation(formId);
        (SparkV15CustomerRedress.RefundAssessment memory assessment, SparkV15Payments.PaymentTerms memory terms) =
            redress.previewRefund(formId, SparkV15CustomerRedress.RefundBasis.OriginalRelief, VERIFIER_ACTOR);
        require(
            assessment.principal == refundAmount && terms.originalDebitAccount == funds.creditAccount(CUSTOMER)
                && terms.originalDebitAmount == GROUP_A_FEE,
            "A's original relief used a different seat or service extent"
        );
    }

    function _releaseTwoSeatBudget(SparkV15ServiceReserve reserve, uint128 amount, bytes32 releaseRef) private {
        uint256 proof = _evidence(reserve.releaseEvidenceCommitment(LESSON, amount, releaseRef, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        reserve.releaseBudget(LESSON, amount, releaseRef, proof, _authority(ROLE_VERIFIER));
        require(reserve.usedAccountingEvidence(proof), "release proof was not consumed");
    }

    function _publishTwoSeatContacts(bytes32 seatForm) private returns (bytes32 termsId) {
        SparkV15ReviewContext.ReviewTerms memory terms;
        terms.lessonId = LESSON;
        terms.publication = DOCUMENTS;
        terms.governingForm = seatForm;
        terms.provider = PROVIDER;
        terms.coordinator = COORDINATOR;
        terms.alternativeContact = DECIDER;
        terms.leadAcademicTutor = TUTOR;
        terms.escalationContact = DECIDER;
        terms.replyPeriod = 1 days;
        terms.reviewDeadline = EPOCH + 7 days;
        termsId = keccak256(abi.encode(terms));
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_ALLOCATOR, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, true
        );
        uint256 proof = _evidence(
            cases.evidenceCommitment(termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, PROVIDER, termsId)
        );
        SparkV15ConcernIntake intake = cases.INTAKE();
        requestVm.prank(PROVIDER);
        intake.publishContacts(terms, proof, _actorId(PROVIDER, ROLE_ALLOCATOR));
    }

    function _receiveTwoSeatConcern(bytes32 termsId, bytes32 matter, bytes32 seatForm, address student)
        private
        returns (bytes32 caseId)
    {
        SparkV15ReviewContext.ConcernInput memory input;
        input.termsId = termsId;
        input.concernRef = matter;
        input.receiver = COORDINATOR;
        input.subject = SparkV15ReviewContext.ConcernSubject.StudentService;
        input.claim = keccak256(abi.encode("independently retained service concern", matter));
        input.subjectRef = seatForm;
        input.parties = new address[](2);
        input.parties[0] = student;
        input.parties[1] = PROVIDER;
        caseId = cases.caseIdFor(LESSON, matter);
        uint256 proof = _evidence(
            cases.evidenceCommitment(
                caseId, SparkV15ReviewActions.ACTION_RECEIVE_CONCERN, student, keccak256(abi.encode(input))
            )
        );
        SparkV15ConcernIntake intake = cases.INTAKE();
        requestVm.prank(student);
        require(intake.receiveConcern(input, proof) == caseId, "wrong received concern");
        require(intake.getConcern(caseId).intake.evidenceId == proof, "concern proof was not recorded");
    }

    function _replyToDeliveryConcern(bytes32 concern, bytes32 outcome) private {
        SparkV15ConcernIntake intake = cases.INTAKE();
        SparkV15ReviewContext.ConcernRecord memory saved = intake.getConcern(concern);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_ACKNOWLEDGE_CONCERN, true
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN, true);
        if (saved.acknowledgment.evidenceId == 0) {
            SparkV15ReviewContext.AcknowledgmentInput memory acknowledgment = SparkV15ReviewContext.AcknowledgmentInput({
                handler: COORDINATOR,
                replyDeadline: saved.replyCutoff,
                escalationContact: DECIDER,
                notice: SparkV15ReviewContext.Notice(keccak256("receipt of A's concern"), uint64(block.timestamp))
            });
            uint256 acknowledgmentProof = _evidence(
                cases.evidenceCommitment(
                    concern,
                    SparkV15ReviewActions.ACTION_ACKNOWLEDGE_CONCERN,
                    COORDINATOR,
                    keccak256(abi.encode(acknowledgment, saved.intake.raisedBy))
                )
            );
            requestVm.prank(COORDINATOR);
            intake.acknowledge(concern, acknowledgment, acknowledgmentProof, _actorId(COORDINATOR, ROLE_SOURCE));
        }
        SparkV15ReviewContext.ReplyInput memory reply = SparkV15ReviewContext.ReplyInput({
            checkedAt: uint64(block.timestamp),
            factCheck: keccak256(abi.encode("concern facts reviewed", outcome)),
            outcome: outcome,
            reasons: keccak256("independent records identify the same seat and teaching interval"),
            reviewEvidenceId: 0,
            notice: SparkV15ReviewContext.Notice(keccak256("fact check communicated"), uint64(block.timestamp))
        });
        uint256 proof = _evidence(
            cases.evidenceCommitment(
                concern,
                SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN,
                COORDINATOR,
                keccak256(abi.encode(reply, saved.intake.partiesHash))
            )
        );
        requestVm.prank(COORDINATOR);
        intake.reply(concern, reply, proof, _actorId(COORDINATOR, ROLE_SOURCE));
    }

    function _recordTwoSeatMaterialCharge(bytes32 seatB) private returns (bytes32 scopeId) {
        SparkV15Materials.UseCheck memory use = SparkV15Materials.UseCheck(
            seatB,
            MAIN,
            EPOCH + 30,
            EPOCH + 33,
            SparkV15Materials.UseSource.LessonRecord,
            keccak256("B's opening instructional material use"),
            keccak256("independently verified licensed use at B's seat"),
            false,
            false,
            bytes32(0)
        );
        uint256 proof = _materialEvidence(materials.ACTION_VERIFY_USE(), abi.encode(use));
        requestVm.prank(COORDINATOR);
        materials.verifyUse(use, proof);
        require(materials.originalFor(formId, MAIN) == bytes32(0), "A was charged for B's licensed materials");

        requestVm.warp(EPOCH + 34);
        bytes32[] memory chargedForms = new bytes32[](1);
        chargedForms[0] = seatB;
        SparkV15Materials.GrossInput memory gross =
            SparkV15Materials.GrossInput(LESSON, MAIN, bytes32(0), GROUP_MATERIAL_COST, EPOCH + 34, chargedForms);
        proof = _materialEvidence(materials.ACTION_RECORD_GROSS(), abi.encode(gross));
        requestVm.prank(COORDINATOR);
        scopeId = materials.recordGross(gross, proof);
        require(materials.getHistoricalCharge(scopeId, seatB).amount == GROUP_MATERIAL_UNITS, "wrong separate charge");
    }

    function _reserveIndependentLesson(uint128 amount) private returns (bytes32 lessonId) {
        // An independently scheduled booking commits the provider cash made available by the authorized release.
        lessonId = keccak256("subsequent independently funded booking");
        SparkV15Booking.LessonTerms memory nextLesson = booking.getLesson(LESSON).terms;
        nextLesson.lessonId = lessonId;
        nextLesson.startsAt = EPOCH + 70;
        nextLesson.endsAt = EPOCH + 72;
        nextLesson.rosterLockAt = 0;
        nextLesson.rosterRef = bytes32(0);
        nextLesson.tutorFee = amount;
        nextLesson.materialsTermsRef = bytes32(0);
        requestVm.prank(COORDINATOR);
        booking.publishLesson(nextLesson);
        SparkV15Booking.PlaceTerms memory nextPlace = booking.getForm(formId).terms;
        nextPlace.rechargeDebitsHash = bytes32(0);
        bytes32[] memory planned = new bytes32[](1);
        requestVm.prank(COORDINATOR);
        planned[0] = booking.publishForm(lessonId, nextPlace);
        bytes32 inventory = keccak256("verified upcoming independent agreed tutor costs");
        uint256 proof = _evidence(booking.prefundingCommitment(lessonId, planned, amount, inventory));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(lessonId, planned, amount, inventory, proof);
    }

    function _payTwoSeatMaterials(bytes32 scopeId) private {
        requestVm.warp(EPOCH + 35);
        bytes32 first = _entitlement(scopeId, FIRST_HOLDER);
        bytes32 second = _entitlement(scopeId, SECOND_HOLDER);
        require(funds.paymentReserved(first) == 2 && funds.paymentReserved(second) == 4, "wrong separate entitlements");

        requestVm.warp(EPOCH + 38);
        uint256 firstApproval = _approveMaterial(first, 2);
        uint256 secondApproval = _approveMaterial(second, 4);
        requestVm.warp(EPOCH + 40);
        requestVm.prank(EXECUTOR);
        uint256 firstReceipt = payments.pay(firstApproval, 2);
        _verifyReceipt(firstReceipt, EPOCH + 40);
        require(funds.reservedUnits() == 308 && token.balanceOf(address(funds)) == 308, "first outflow lost backing");
        requestVm.prank(EXECUTOR);
        uint256 secondReceipt = payments.pay(secondApproval, 4);
        _verifyReceipt(secondReceipt, EPOCH + 40);
        require(token.balanceOf(FIRST_HOLDER) == 2 && token.balanceOf(SECOND_HOLDER) == 4, "missing actual transfers");
        require(
            funds.paymentReserved(first) == 0 && funds.paymentReserved(second) == 0, "paid entitlements remained held"
        );
    }

    function _book(uint128 providerFunds, uint128 unassignedCancellationCost) private {
        _bookWithProviderHold(providerFunds, unassignedCancellationCost, 1, true);
    }

    function _bookWithProviderHold(
        uint128 providerFunds,
        uint128 unassignedCancellationCost,
        uint128 held,
        bool reserveDebit
    ) private {
        funds.bindMaterialProvisions(address(provisions));
        SparkV15Materials.Terms memory terms = _terms();
        bytes32 termsRef = materials.termsCommitment(terms);
        _publishMaterialLesson(termsRef, 1, 0);
        _adoptMaterialTerms(terms, termsRef);
        _publishPlace();

        token.mint(PROVIDER, providerFunds);
        requestVm.prank(PROVIDER);
        require(token.transfer(address(funds), providerFunds), "provider deposit");
        _recharge(CUSTOMER, 120);
        _recharge(CREDIT_OWNER, 17);

        bytes32[] memory forms = _forms();
        SparkV15FundingCases fundingCases = provisions.FUNDING_CASES();
        SparkV15FundingCases.FundingScenario[] memory scenarios =
            _fundingScenarios(termsRef, unassignedCancellationCost);
        bytes32 inventory = fundingCases.inventoryReference(LESSON, scenarios);
        uint256 proof = _evidence(booking.prefundingCommitment(LESSON, forms, held, inventory));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, forms, held, inventory, proof);
        fundingCases.retainInventory(LESSON, scenarios);
        requestVm.warp(EPOCH + 3);
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(LESSON);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(LESSON);
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        requestVm.prank(PROVIDER);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Provider);
        requestVm.prank(TUTOR);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Tutor);
        requestVm.prank(CUSTOMER);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Customer);
        requestVm.prank(COORDINATOR);
        booking.confirmPlace(formId, bytes32(0), 0, new SparkV15Funds.RechargeDebit[](0));
        if (reserveDebit) _reserveOriginalDebit();
    }

    function _publishMaterialLesson(bytes32 termsRef, uint128 tutorFee, uint64 rosterLockAt) private {
        SparkV15Booking.LessonTerms memory lesson;
        lesson.lessonId = LESSON;
        lesson.provider = PROVIDER;
        lesson.tutor = TUTOR;
        lesson.coordinator = COORDINATOR;
        lesson.startsAt = EPOCH + 30;
        lesson.endsAt = EPOCH + 32;
        lesson.rosterLockAt = rosterLockAt;
        if (rosterLockAt != 0) lesson.rosterRef = keccak256("agreed private group roster");
        lesson.timeZoneRef = keccak256("UTC");
        lesson.tutorNoticeChannelRef = CHANNEL;
        lesson.tutorFee = tutorFee;
        lesson.tutorAgreementRef = AGREEMENT;
        lesson.serviceTermsRef = DOCUMENTS;
        lesson.tutorPayTermsRef = AGREEMENT;
        lesson.providerResponsibilitiesRef = DOCUMENTS;
        lesson.tutorResponsibilitiesRef = AGREEMENT;
        lesson.startTermsRef = DOCUMENTS;
        lesson.documentsRef = DOCUMENTS;
        lesson.materialsTermsRef = termsRef;
        requestVm.prank(COORDINATOR);
        booking.publishLesson(lesson);
    }

    function _adoptMaterialTerms(SparkV15Materials.Terms memory terms, bytes32 termsRef) private {
        requestVm.prank(FIRST_HOLDER);
        materials.acceptTerms(termsRef);
        requestVm.prank(SECOND_HOLDER);
        materials.acceptTerms(termsRef);
        requestVm.prank(PROVIDER);
        materials.adoptTerms(terms);
    }

    function _fundingScenarios(bytes32 termsRef, uint128 unassignedCancellationCost)
        private
        view
        returns (SparkV15FundingCases.FundingScenario[] memory scenarios)
    {
        scenarios = new SparkV15FundingCases.FundingScenario[](2);
        bytes32[] memory taughtOutcomes = new bytes32[](1);
        taughtOutcomes[0] = keccak256("ordinary lesson was taught");
        SparkV15FundingCases.Expense[] memory taughtExpenses = new SparkV15FundingCases.Expense[](1);
        SparkV15FundingCases.MaterialPortion[] memory portions = new SparkV15FundingCases.MaterialPortion[](1);
        portions[0] = SparkV15FundingCases.MaterialPortion(formId, 6);
        taughtExpenses[0] = SparkV15FundingCases.Expense(BOOKING_MATERIAL_COST, bytes32(0), MAIN, termsRef, 6, portions);
        scenarios[0] = SparkV15FundingCases.FundingScenario(true, _forms(), taughtOutcomes, taughtExpenses);

        bytes32[] memory cancelledOutcomes = new bytes32[](1);
        cancelledOutcomes[0] = keccak256("no teaching and the fee is restored");
        SparkV15FundingCases.Expense[] memory cancelled =
            new SparkV15FundingCases.Expense[](unassignedCancellationCost == 0 ? 1 : 2);
        cancelled[0] = SparkV15FundingCases.Expense(
            keccak256("original customer debit"),
            keccak256(abi.encode(LESSON, keccak256("independent original-debit liability"))),
            bytes32(0),
            bytes32(0),
            120,
            new SparkV15FundingCases.MaterialPortion[](0)
        );
        if (unassignedCancellationCost != 0) {
            cancelled[1] = SparkV15FundingCases.Expense(
                keccak256("additional cancellation expense"),
                bytes32(0),
                bytes32(0),
                bytes32(0),
                unassignedCancellationCost,
                new SparkV15FundingCases.MaterialPortion[](0)
            );
        }
        scenarios[1] = SparkV15FundingCases.FundingScenario(false, _forms(), cancelledOutcomes, cancelled);
    }

    function _publishPlace() private {
        SparkV15Booking.PlaceTerms memory place;
        place.placeId = PLACE;
        place.customer = CUSTOMER;
        place.payer = CUSTOMER;
        place.student = CUSTOMER;
        place.creditAccount = funds.creditAccount(CUSTOMER);
        place.studentNoticeChannelRef = keccak256("agreed student notice channel");
        place.normalFee = 120;
        place.payableFee = 120;
        place.materialsBundleRef = BUNDLE;
        place.materialPayer = PROVIDER;
        requestVm.prank(COORDINATOR);
        formId = booking.publishForm(LESSON, place);
    }

    function _reserveOriginalDebit() private {
        SparkV15Payments.PaymentTerms memory terms;
        terms.lessonId = LESSON;
        terms.paymentPart = keccak256("independent original-debit liability");
        terms.recipient = CUSTOMER;
        terms.originalDebitAccount = funds.creditAccount(CUSTOMER);
        terms.originalDebitAmount = 120;
        terms.amount = 120;
        terms.dueAt = EPOCH + 50;
        terms.executionDeadline = EPOCH + 60;
        terms.dueAtExact = true;
        terms.executionDeadlineExact = true;
        terms.settlementProposer = COORDINATOR;
        terms.settlementApprover = PROVIDER;
        bytes32 basis = keccak256("verified original course credit debit");
        uint256 proof = _evidence(payments.paymentEvidenceCommitment(terms, basis));
        requestVm.prank(VERIFIER_ACTOR);
        refund = payments.establishPayment(terms, basis, proof, _authority(ROLE_VERIFIER));
    }

    function _recharge(address customer, uint128 amount) private returns (uint256 receiptId) {
        return _recharge(customer, amount, 0, 0);
    }

    function _recharge(address customer, uint128 amount, uint128 returnCap, uint64 returnThrough)
        private
        returns (uint256 receiptId)
    {
        SparkV15Funds.RechargeTerms memory terms = SparkV15Funds.RechargeTerms(
            customer, amount, returnCap, returnThrough, keccak256("accepted recharge terms")
        );
        bytes32 authority = _actorId(PROVIDER, funds.CREDIT_PROVIDER_ROLE());
        requestVm.prank(PROVIDER);
        bytes32 offer = funds.offerRecharge(terms, authority);
        token.mint(customer, amount);
        requestVm.startPrank(customer);
        token.approve(address(funds), amount);
        receiptId = funds.recharge(offer);
        requestVm.stopPrank();
    }

    function _provideTerms(bytes32 governedForm, address recipient) private {
        uint256 proof = _evidence(booking.provisionCommitment(governedForm, recipient, DOCUMENTS));
        requestVm.prank(COORDINATOR);
        booking.recordTermsProvision(governedForm, recipient, DOCUMENTS, proof);
    }

    function _recordProvision(bytes32 material, uint128 amount) private {
        SparkV15MaterialProvisions.ProvisionInput memory input = _provision(material, amount);
        uint256 proof = _evidence(provisions.provisionEvidenceCommitment(input, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        provisions.recordProvision(input, proof, _authority(ROLE_VERIFIER));
    }

    function _provision(bytes32 material, uint128 amount)
        private
        view
        returns (SparkV15MaterialProvisions.ProvisionInput memory)
    {
        return SparkV15MaterialProvisions.ProvisionInput(formId, material, amount, keccak256("verified dated estimate"));
    }

    function _terms() private pure returns (SparkV15Materials.Terms memory) {
        SparkV15Materials.HolderShare[] memory holders = new SparkV15Materials.HolderShare[](2);
        holders[0] = SparkV15Materials.HolderShare(FIRST_HOLDER, 1);
        holders[1] = SparkV15Materials.HolderShare(SECOND_HOLDER, 2);
        SparkV15Materials.MaterialTerms[] memory bundle = new SparkV15Materials.MaterialTerms[](2);
        bundle[0] = SparkV15Materials.MaterialTerms(MAIN, 5, holders, new address[](0));
        bundle[1] = SparkV15Materials.MaterialTerms(OTHER, 5, holders, new address[](0));
        return SparkV15Materials.Terms(
            LESSON,
            BUNDLE,
            PROVIDER,
            keccak256("agreed material payment contact"),
            keccak256("licence for both materials"),
            keccak256("agreed shares one third and two thirds"),
            EPOCH + 50,
            EPOCH + 60,
            100,
            bundle,
            new SparkV15Materials.PriceRow[](0)
        );
    }

    function _forms() private view returns (bytes32[] memory forms) {
        forms = new bytes32[](1);
        forms[0] = formId;
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
                evidenceTypeHash: keccak256("spark.materials.funding.verified"),
                disclosurePolicyId: requestPolicyId,
                authorityId: _authority(ROLE_SOURCE),
                uri: "test:verified-materials-funding"
            })
        );
    }

    function _assign(address actor, bytes32 role) private {
        identityRegistry.assignSubject(actor, SparkV15.APP_ID, role, _actorId(actor, role), "test:materials-funding");
    }

    function _actorId(address actor, bytes32 role) private pure returns (bytes32) {
        return keccak256(abi.encode("materials funding actor", actor, role));
    }
}
