// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {DeployAVACore} from "@ava-protocol/contracts/script/DeployAVACore.s.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAAuthorityMatrix} from "@ava-protocol/contracts/src/core/AVAAuthorityMatrix.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVAGovernanceKernel} from "@ava-protocol/contracts/src/core/AVAGovernanceKernel.sol";
import {AVAIdentityRegistry} from "@ava-protocol/contracts/src/core/AVAIdentityRegistry.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {DeploySparkV15OnExistingCore} from "../../../script/DeploySparkV15OnExistingCore.s.sol";
import {SparkV15} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {
    ISparkV15BookingFunds,
    SparkV15Booking,
    SparkV15BookingOpening
} from "../../../src/apps/spark/v15/SparkV15Booking.sol";
import {SparkV15BookingChanges} from "../../../src/apps/spark/v15/SparkV15BookingChanges.sol";
import {SparkV15BookingPrefunding} from "../../../src/apps/spark/v15/SparkV15BookingPrefunding.sol";
import {SparkV15CourseNotices} from "../../../src/apps/spark/v15/SparkV15CourseNotices.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {SparkV15LessonRemedies} from "../../../src/apps/spark/v15/SparkV15LessonRemedies.sol";
import {
    SparkV15FundingCases,
    SparkV15MaterialProvisions,
    SparkV15ServiceReserve
} from "../../../src/apps/spark/v15/SparkV15MaterialProvisions.sol";
import {SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {
    SparkV15ConcernIntake,
    SparkV15ReviewActions,
    SparkV15ReviewContext
} from "../../../src/apps/spark/v15/SparkV15ReviewCases.sol";
import {SparkV15Settlement} from "../../../src/apps/spark/v15/SparkV15Settlement.sol";
import {SparkV15SettlementAlternatives} from "../../../src/apps/spark/v15/SparkV15SettlementAlternatives.sol";
import {SparkV15SettlementOccurrences} from "../../../src/apps/spark/v15/SparkV15SettlementOccurrences.sol";
import {SparkV15ServiceReports} from "../../../src/apps/spark/v15/SparkV15ServiceReports.sol";
import {SparkV15TeachingEnd} from "../../../src/apps/spark/v15/SparkV15TeachingEnd.sol";
import {MockERC20} from "../mocks/MockERC20.sol";

interface InstalledPhaseOneVm {
    function addr(uint256 key) external pure returns (address);
    function sign(uint256 key, bytes32 digest) external pure returns (uint8, bytes32, bytes32);
    function chainId(uint256 value) external;
    function warp(uint256 value) external;
    function setEnv(string calldata name, string calldata value) external;
    function toString(address value) external pure returns (string memory);
    function prank(address actor) external;
    function expectRevert(bytes4 selector) external;
    function expectPartialRevert(bytes4 selector) external;
    function expectEmit(bool topic1, bool topic2, bool topic3, bool data, address emitter) external;
    function record() external;
    function snapshotState() external returns (uint256);
    function revertToState(uint256 snapshotId) external returns (bool);
    function accesses(address target) external returns (bytes32[] memory reads, bytes32[] memory writes);
    function load(address target, bytes32 slot) external view returns (bytes32);
}

interface IOrdinaryBookingAcceptances {
    function confirmOrdinaryPlaceWithAcceptances(
        bytes32 formId, SparkV15Funds.RechargeDebit[] calldata debits, bytes calldata signatures, bytes calldata agreements
    ) external;
}

interface IInstalledBookingPrefunding {
    struct Proof {
        bytes32 sourceRole;
        bytes32 sourceAuthorityId;
        uint256 disclosurePolicyId;
        uint64 validThrough;
        bytes32 r;
        bytes32 vs;
    }

    function adoptOrdinaryBookingDraftWithPrefundingProof(
        SparkV15Booking.LessonTerms calldata lesson,
        SparkV15Booking.PlaceTerms calldata place,
        uint128 requiredUnits,
        bytes32 fundingRef,
        uint64 draftValidThrough,
        bytes32 draftR,
        bytes32 draftVs,
        Proof calldata proof
    ) external returns (bytes32 formId);

    function getAdoptedEvidence(bytes32 lessonId)
        external
        view
        returns (uint256, bytes32, uint256, AVACoreTypes.EvidenceStatus, uint256);

    function recordEvidenceLifecycle(
        bytes32 lessonId,
        bytes32 role,
        bytes32 authorityId,
        AVACoreTypes.EvidenceLifecycleKind kind,
        uint256 replacementCoreEvidenceId,
        bytes32 reasonHash
    ) external;
}

interface IInstalledBookingPrefundingBinding {
    function PREFUNDING() external view returns (IInstalledBookingPrefunding);
}

/// @notice Installed route for an agreed place taught without confirmation or debit.
contract InstalledUnconfirmedEarlyStartTest {
    enum DraftBasis {
        Registered,
        Adopted,
        AdoptedWithAmountControl,
        AdoptedInventory
    }

    InstalledPhaseOneVm private constant vm =
        InstalledPhaseOneVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address private constant ADMIN = address(0x7400);
    address private constant CORE_PARTNER = address(0x7403);
    address private constant ALLOCATOR = address(0x7406);
    address private constant REVIEWER = address(0x7407);
    uint256 private constant STUDENT_KEY = 0x7409;
    address private constant EXECUTOR = address(0x7412);
    address private constant MATERIALS_DAO = address(0x7413);
    address private constant SERVICE_RESERVE = address(0x7414);
    uint256 private constant COORDINATOR_KEY = 0x7402;
    uint256 private constant SOURCE_KEY = 0x7404;
    uint256 private constant VERIFIER_KEY = 0x7405;
    uint256 private constant PROVIDER_KEY = 0x7401;
    uint256 private constant TUTOR_KEY = 0x7408;
    uint256 private constant CUSTOMER_KEY = 0x7410;
    uint256 private constant PAYER_KEY = 0x7411;

    uint64 private constant EPOCH = 1_000_000;
    uint64 private constant START = EPOCH + 2 days;
    uint64 private constant END = START + 1 hours;
    uint64 private constant DUE = START + 30 days;
    uint128 private constant FEE = 20;
    uint128 private constant WAGE = 8;
    uint128 private constant LESSON_BACKING = 58;
    bytes32 private constant LESSON = keccak256("installed ordinary one-to-one lesson");
    bytes32 private constant PLACE = keccak256("agreed single place");
    bytes32 private constant AGREEMENT = keccak256("signed teaching services agreement");
    bytes32 private constant DOCUMENTS = keccak256("provided course terms and documents");
    bytes32 private constant TUTOR_CHANNEL = keccak256("agreed tutor notice channel");

    event OrdinarySettlementConsented(
        bytes32 indexed lessonId, bytes32 indexed basis, address indexed source, bytes32 sourceAuthorityId
    );
    event log_named_uint(string key, uint256 value);

    address private COORDINATOR;
    address private SOURCE;
    address private VERIFIER;
    address private PROVIDER;
    address private TUTOR;
    address private STUDENT;
    address private CUSTOMER;
    address private PAYER;
    DeploySparkV15OnExistingCore.Deployment private app;
    MockERC20 private token;
    SparkV15Funds private funds;

    function setUp() public {
        COORDINATOR = vm.addr(COORDINATOR_KEY);
        SOURCE = vm.addr(SOURCE_KEY);
        VERIFIER = vm.addr(VERIFIER_KEY);
        PROVIDER = vm.addr(PROVIDER_KEY);
        TUTOR = vm.addr(TUTOR_KEY);
        STUDENT = vm.addr(STUDENT_KEY);
        CUSTOMER = vm.addr(CUSTOMER_KEY);
        PAYER = vm.addr(PAYER_KEY);
        vm.chainId(31337);
        vm.warp(EPOCH);
        DeployAVACore.Deployment memory core = new DeployAVACore().run(ADMIN);
        token = new MockERC20("Local lesson token", "TEST", 6);
        _env("AVA_ROOT_ADMIN", ADMIN);
        _env("AVA_EXISTING_KERNEL", address(core.kernel));
        _env("AVA_EXISTING_REQUESTS", address(core.requests));
        _env("SPARK_V15_TOKEN", address(token));
        _env("SPARK_V15_COURSE_PROVIDER", PROVIDER);
        _env("SPARK_V15_BOOKING_COORDINATOR", COORDINATOR);
        _env("SPARK_V15_CORE_PARTNER", CORE_PARTNER);
        _env("SPARK_V15_SOURCE", SOURCE);
        _env("SPARK_V15_VERIFIER", VERIFIER);
        _env("SPARK_V15_ALLOCATOR", ALLOCATOR);
        _env("SPARK_V15_REVIEWER", REVIEWER);
        _env("SPARK_V15_ALTERNATIVE_CONTACT", address(0));
        _env("SPARK_V15_MATERIALS_DAO", MATERIALS_DAO);
        _env("SPARK_V15_SERVICE_RESERVE", SERVICE_RESERVE);
        app = new DeploySparkV15OnExistingCore().run();
        funds = app.payments.FUNDS();
        require(address(app.kernel) == address(core.kernel), "wrong installed Core");
        require(address(app.payments.REQUEST_ALLOCATION()) == address(core.requests), "wrong request allocation");
        require(funds.materialBookingCoverage().code.length != 0, "missing installed booking coverage");
    }

    function _liftEarlyStartFeeHold(bytes32 caseId) private {
        SparkV15SettlementAlternatives alternatives = app.settlement.ALTERNATIVES();
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("fee decision notified to the concerned parties"), END + 2);
        bytes32 disposition = keccak256("fee hold fully lifted without changing the verified valuation");
        uint256 liftEvidence = _evidence(alternatives.feeLiftCommitment(caseId, disposition, notice, REVIEWER));
        bytes32 reviewer = _subject(REVIEWER, app.applicationModule.VERIFIER_ROLE());
        vm.prank(REVIEWER);
        alternatives.liftFeeHold(caseId, disposition, notice, liftEvidence, reviewer);
    }

    function testInstalledUnconfirmedEarlyStartAssessesServiceAndPaysOnlyTutor() public {
        this.assessAndPayUnconfirmedEarlyStart(DraftBasis.Adopted);
    }

    function testInstalledUnconfirmedEarlyStartUsesRegisteredDraftAndPaysOnlyTutor() public {
        this.assessAndPayUnconfirmedEarlyStart(DraftBasis.Registered);
    }

    function assessAndPayUnconfirmedEarlyStart(DraftBasis basis) external {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = this.prepareUnconfirmedEarlyStart(basis, true);
        this.releaseExpiredUnconfirmedPreparation();
        _observeUnconfirmedProviderStart(START + 1);
        _finishTeaching(formId, false, false);
        _proposeUnconfirmedProviderAssessment(assessment, formId, 5);

        SparkV15Settlement.GroupPreview memory preview = app.settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        require(preview.payments.length == 1 && preview.totalTutorPay == 5, "only the verified wage is payable");
        require(preview.payments[0].amount == 5 && preview.payments[0].originalDebitAccount == bytes32(0), "wrong wage");
        uint256 support = _evidence(preview.basis);
        uint256[] memory evidence = new uint256[](1);
        evidence[0] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis));
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, support, evidence);

        SparkV15Settlement.SeatSettlement memory seat = app.settlement.getSeatSettlement(LESSON, formId);
        bytes32 payerAccount = funds.creditAccount(PAYER);
        require(app.booking.getForm(formId).terms.creditAccount == payerAccount, "agreed account lost");
        require(seat.debitAccount == bytes32(0) && seat.debitOwner == address(0), "phantom original debit identity");
        require(seat.debited == 0 && seat.feeDue == 13 && seat.tutorPay == 5, "verified fee, actual debit, or wage wrong");
        require(seat.refundDue == 0 && seat.refundObligationId == bytes32(0), "phantom refund");
        require(seat.tutorObligationId != bytes32(0) && funds.paymentReserved(seat.tutorObligationId) == 5, "wage not backed");
        require(funds.lessonReserved(LESSON) == 0 && funds.reservedUnits() == FEE + 5, "wage did not reserve free cash");
        require(app.booking.getConfirmedForms(LESSON).length == 0, "settlement booked the place");
        require(funds.creditBalance(payerAccount) == FEE && funds.lessonFeeBalance(LESSON) == 0, "settlement charged the place");

        this.payUnconfirmedEarlyStartWage(seat.tutorObligationId);
        require(funds.creditBalance(payerAccount) == FEE && funds.lessonFeeBalance(LESSON) == 0, "wage charged the place");
        require(funds.reservedUnits() == FEE, "wage backing not consumed");
        require(app.booking.getForm(formId).confirmation.debitedUnits == 0, "late debit created");
    }

    function releaseExpiredUnconfirmedPreparation() external {
        vm.warp(START);
        require(app.booking.getConfirmedForms(LESSON).length == 0, "booking has not lapsed");
        require(app.booking.getTeaching(LESSON).startedAt == 0 && funds.lessonFeeBalance(LESSON) == 0, "existing service or fee");
        SparkV15ServiceReserve release = SparkV15MaterialProvisions(funds.materialProvisions()).SERVICE_RESERVE();
        require(release.releasableProviderHold(LESSON) == LESSON_BACKING, "preparation backing not idle");
        bytes32 verifiedIdle = keccak256("booking cutoff passed without a booking, debit, teaching, or known payable item");
        uint256 proof = _evidence(release.releaseEvidenceCommitment(LESSON, LESSON_BACKING, verifiedIdle, VERIFIER));
        bytes32 authority = _subject(VERIFIER, app.booking.VERIFIER_ROLE());
        vm.prank(VERIFIER);
        release.releaseBudget(LESSON, LESSON_BACKING, verifiedIdle, proof, authority);
        require(funds.lessonReserved(LESSON) == 0 && funds.reservedUnits() == FEE, "draft budget still holds cash");
        require(token.balanceOf(address(funds)) == 200, "budget release moved cash");
    }

    function payUnconfirmedEarlyStartWage(bytes32 obligationId) external {
        uint256 request = _approvePayment(obligationId, 5, DUE);
        require(app.payments.getObligation(obligationId).paid == 0, "approval paid the wage");
        require(token.balanceOf(TUTOR) == 0 && token.balanceOf(address(funds)) == 200, "approval moved funds");
        vm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        vm.prank(EXECUTOR);
        app.payments.pay(request, 5);
        vm.warp(DUE);
        vm.prank(EXECUTOR);
        uint256 receiptId = app.payments.pay(request, 5);
        SparkV15Payments.PaymentReceipt memory receipt = app.payments.getReceipt(receiptId);
        require(receipt.amount == 5 && receipt.recipient == TUTOR && receipt.creditAccount == bytes32(0), "wrong actual wage");
        require(token.balanceOf(TUTOR) == 5 && token.balanceOf(address(funds)) == 195, "wrong actual cash movement");
    }

    function prepareUnconfirmedEarlyStart(DraftBasis basis, bool includePayerAssent)
        external
        returns (bytes32 formId)
    {
        uint256 funding;
        (formId, funding,) = _adoptPrefundedDraft(basis);
        if (basis == DraftBasis.Registered) {
            (uint256 firstUseProof,,,,) = _prefundingModule().getAdoptedEvidence(LESSON);
            AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
            require(firstUseProof == 0 && registry.isEvidenceAvailableForPackage(funding, app.packageId), "wrong draft origin");
            require(app.booking.getLesson(LESSON).prefunding.evidenceId == funding, "registered proof not retained");
        }
        vm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
        vm.prank(TUTOR);
        app.booking.signTeachingAgreement(LESSON);
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        vm.warp(EPOCH + 1);
        vm.prank(PROVIDER);
        app.booking.signTeachingAgreement(LESSON);
        vm.prank(TUTOR);
        app.booking.signTeachingAgreement(LESSON);
        _accept(formId, SparkV15Booking.Acceptance.Provider, PROVIDER);
        _accept(formId, SparkV15Booking.Acceptance.Tutor, TUTOR);
        _accept(formId, SparkV15Booking.Acceptance.Customer, CUSTOMER);
        if (includePayerAssent) _accept(formId, SparkV15Booking.Acceptance.Payer, PAYER);
    }

    function testInstalledUnconfirmedEarlyStartRetainsHistoricalDraftAfterFundingProofRevocation() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = this.prepareUnconfirmedEarlyStart(DraftBasis.Adopted, true);
        this.releaseExpiredUnconfirmedPreparation();
        this.revokeExpiredPreparationProof();
        SparkV15BookingOpening opening = app.booking.OPENING();
        require(opening.hasUsableTermsProvision(formId, CUSTOMER, app.packageId), "customer receipt unavailable");
        require(opening.hasUsableTermsProvision(formId, TUTOR, app.packageId), "tutor receipt unavailable");
        require(funds.lessonReserved(LESSON) == 0 && funds.reservedUnits() == FEE, "wrong current backing");

        _observeUnconfirmedProviderStart(START + 1);
        _finishTeaching(formId, false, false);
        _proposeUnconfirmedProviderAssessment(assessment, formId, 5);
        SparkV15Settlement.GroupPreview memory preview = app.settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        require(preview.payments.length == 1 && preview.payments[0].amount == 5, "verified wage not available");
        uint256 support = _evidence(preview.basis);
        uint256[] memory evidence = new uint256[](1);
        evidence[0] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis));
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, support, evidence);

        SparkV15Settlement.SeatSettlement memory seat = app.settlement.getSeatSettlement(LESSON, formId);
        require(seat.feeDue == 13 && seat.debited == 0 && seat.refundDue == 0, "wrong assessed service or actual debit");
        require(app.payments.getObligation(seat.tutorObligationId).paid == 0, "settlement posted a payment");
        require(funds.paymentReserved(seat.tutorObligationId) == 5 && funds.reservedUnits() == FEE + 5, "wage not backed");
        require(token.balanceOf(address(funds)) == 200 && token.balanceOf(TUTOR) == 0, "cash moved on settlement");
    }

    function revokeExpiredPreparationProof() external {
        IInstalledBookingPrefunding module = _prefundingModule();
        (uint256 original,,,,) = module.getAdoptedEvidence(LESSON);
        bytes32 role = app.applicationModule.VERIFIER_ROLE();
        bytes32 reviewer = _subject(REVIEWER, role);
        _allowEvidenceLifecycle(role);
        vm.prank(REVIEWER);
        module.recordEvidenceLifecycle(
            LESSON, role, reviewer, AVACoreTypes.EvidenceLifecycleKind.Revoke, 0,
            keccak256("withdrawn funding proof after the expired booking preparation")
        );
        (uint256 retained,,, AVACoreTypes.EvidenceStatus status,) = module.getAdoptedEvidence(LESSON);
        require(original != 0 && retained == original && status == AVACoreTypes.EvidenceStatus.Revoked, "wrong history");
    }

    function testInstalledUnconfirmedEarlyStartRejectsPayerAssentAfterTheActualStart() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = this.prepareUnconfirmedEarlyStart(DraftBasis.Adopted, false);
        _observeUnconfirmedProviderStart(START - 2);
        vm.warp(START - 1);
        _accept(formId, SparkV15Booking.Acceptance.Payer, PAYER);
        _finishTeaching(formId, false, false);
        _proposeUnconfirmedProviderAssessment(assessment, formId, 5);

        (, uint64 payerSignedAt) = app.booking.acceptances(formId, SparkV15Booking.Acceptance.Payer);
        require(payerSignedAt == START - 1 && payerSignedAt > app.booking.getTeaching(LESSON).startedAt, "wrong order");
        vm.expectRevert(SparkV15SettlementOccurrences.OrdinaryGroupConditionsNotMet.selector);
        app.settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        require(!app.settlement.hasSeatSettlement(LESSON, formId), "late assent created a settlement");
        require(funds.creditBalance(funds.creditAccount(PAYER)) == FEE, "late assent debited the account");
    }

    function testInstalledUnconfirmedEarlyStartRejectsLegacyAgreementBeforeTermsDelivery() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = this.prepareLegacyAgreementBeforeDelivery();
        _recordUnconfirmedProviderStart(formId);
        _proposeUnconfirmedProviderAssessment(assessment, formId, 5);
        vm.expectRevert(SparkV15SettlementOccurrences.OrdinaryGroupConditionsNotMet.selector);
        app.settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        require(!app.settlement.hasSeatSettlement(LESSON, formId), "legacy ordering created a settlement");
    }

    function prepareLegacyAgreementBeforeDelivery() external returns (bytes32 formId) {
        SparkV15Booking.LessonTerms memory lesson = _ordinaryLessonTerms(_assessment());
        vm.prank(COORDINATOR);
        app.booking.publishLesson(lesson);
        SparkV15Funds.RechargeDebit[] memory debits = new SparkV15Funds.RechargeDebit[](1);
        debits[0] = SparkV15Funds.RechargeDebit(_rechargePayer(), FEE);
        SparkV15Booking.PlaceTerms memory place = _ordinaryPlaceTerms(debits);
        vm.prank(COORDINATOR);
        formId = app.booking.publishForm(LESSON, place);

        token.mint(PROVIDER, 180);
        vm.prank(PROVIDER);
        require(token.transfer(address(funds), 180), "provider backing transfer failed");
        bytes32[] memory forms = new bytes32[](1);
        forms[0] = formId;
        bytes32 inventory = keccak256("verified concurrent customer and tutor funding cases");
        uint256 funding = _evidence(app.booking.prefundingCommitment(LESSON, forms, LESSON_BACKING, inventory));
        vm.prank(VERIFIER);
        app.booking.verifyPrefunding(LESSON, forms, LESSON_BACKING, inventory, funding);
        vm.warp(EPOCH + 1);
        vm.prank(PROVIDER);
        app.booking.signTeachingAgreement(LESSON);
        vm.prank(TUTOR);
        app.booking.signTeachingAgreement(LESSON);
        vm.warp(EPOCH + 2);
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        _accept(formId, SparkV15Booking.Acceptance.Provider, PROVIDER);
        _accept(formId, SparkV15Booking.Acceptance.Tutor, TUTOR);
        _accept(formId, SparkV15Booking.Acceptance.Customer, CUSTOMER);
        _accept(formId, SparkV15Booking.Acceptance.Payer, PAYER);
    }

    function testInstalledUnconfirmedEarlyStartHonorsFeeHoldAndLiftsAfterProofRevocation() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = this.prepareUnconfirmedEarlyStart(DraftBasis.Adopted, true);
        _recordUnconfirmedProviderStart(formId);
        _proposeUnconfirmedProviderAssessment(assessment, formId, 5);

        SparkV15Settlement.GroupPreview memory preview = app.settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        uint256 support = _evidence(preview.basis);
        uint256[] memory evidence = new uint256[](1);
        evidence[0] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis));
        bytes32 caseId = _holdFeeForEarlyProviderStart(formId);
        vm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, support, evidence);
        require(!app.settlement.hasSeatSettlement(LESSON, formId), "held fee settled");

        uint256 deliveryEvidence = app.booking.termsProvisionEvidence(formId, TUTOR);
        bytes32 reviewerRole = app.applicationModule.VERIFIER_ROLE();
        bytes32 reviewer = _subject(REVIEWER, reviewerRole);
        _allowEvidenceLifecycle(reviewerRole);
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        vm.prank(REVIEWER);
        registry.recordEvidenceLifecycle(
            deliveryEvidence, reviewerRole, reviewer, AVACoreTypes.EvidenceLifecycleKind.Revoke, 0,
            keccak256("independently verified withdrawal of the tutor delivery proof"), ""
        );
        vm.warp(END + 2);
        _liftEarlyStartFeeHold(caseId);
        require(app.settlement.ALTERNATIVES().activeFeeHolds(formId) == 0, "already valid hold could not be lifted");
        vm.expectRevert(SparkV15SettlementOccurrences.OrdinaryGroupConditionsNotMet.selector);
        app.settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        require(app.booking.getTeaching(LESSON).startedAt == START - 2, "history lost with the proof");
    }

    function _recordUnconfirmedProviderStart(bytes32 formId) private {
        _observeUnconfirmedProviderStart(START - 2);
        _finishTeaching(formId, false, false);
    }

    function _observeUnconfirmedProviderStart(uint64 startedAt) private {
        vm.warp(startedAt);
        SparkV15Booking.StartObservation memory observation = _startObservation(keccak256("unconfirmed, unpaid place"));
        observation.occurredAt = startedAt;
        _recordLegacyStart(observation);
    }

    function _proposeUnconfirmedProviderAssessment(
        SparkV15Settlement.GroupAssessment memory assessment,
        bytes32 formId,
        uint128 tutorAmount
    ) private {
        assessment.seats[0].formId = formId;
        assessment.seats[0].serviceAvailabilityRef = keccak256("verified service under the exact prior agreement");
        assessment.route = SparkV15Settlement.Route.ProviderStartedEarly;
        assessment.seats[0].disposition = SparkV15Settlement.SeatDisposition.ProviderStartedEarly;
        assessment.verificationRef =
            app.settlement.ALTERNATIVES().OCCURRENCES().encodeProviderStartedEarlyAmounts(13, tutorAmount);
        assessment.clearanceRef = keccak256("independent verified service, wage, and agreed terms");
        bytes32 commitment = app.settlement.proposalCommitment(LESSON, assessment);
        vm.prank(COORDINATOR);
        app.settlement.proposeOrdinaryGroup(LESSON, commitment);
    }

    function _holdFeeForEarlyProviderStart(bytes32 formId) private returns (bytes32 caseId) {
        SparkV15ConcernIntake intake = app.cases.INTAKE();
        SparkV15ReviewContext.ReviewTerms memory terms;
        terms.lessonId = LESSON;
        terms.publication = DOCUMENTS;
        terms.governingForm = formId;
        terms.provider = PROVIDER;
        terms.coordinator = COORDINATOR;
        terms.alternativeContact = CORE_PARTNER;
        terms.leadAcademicTutor = ALLOCATOR;
        terms.namedReviewer = REVIEWER;
        terms.escalationContact = CORE_PARTNER;
        terms.replyPeriod = 1 days;
        terms.reviewDeadline = DUE;
        bytes32 termsId = keccak256(abi.encode(terms));
        uint256 publication = _evidence(
            app.cases.evidenceCommitment(termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, PROVIDER, termsId)
        );
        bytes32 provider = _subject(PROVIDER, funds.CREDIT_PROVIDER_ROLE());
        vm.prank(PROVIDER);
        intake.publishContacts(terms, publication, provider);

        SparkV15ReviewContext.ConcernInput memory input;
        input.termsId = termsId;
        input.concernRef = keccak256("concern about fees for the start without the agreed notices");
        input.receiver = COORDINATOR;
        input.subject = SparkV15ReviewContext.ConcernSubject.CustomerFee;
        input.claim = keccak256("disputed amount for verified teaching in this seat");
        input.subjectRef = PLACE;
        input.parties = new address[](2);
        input.parties[0] = CUSTOMER;
        input.parties[1] = PROVIDER;
        caseId = app.cases.caseIdFor(LESSON, input.concernRef);
        uint256 filing = _evidence(app.cases.evidenceCommitment(
            caseId, SparkV15ReviewActions.ACTION_RECEIVE_CONCERN, CUSTOMER, keccak256(abi.encode(input))
        ));
        vm.prank(CUSTOMER);
        intake.receiveConcern(input, filing);

        SparkV15SettlementAlternatives alternatives = app.settlement.ALTERNATIVES();
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("independent holder notified the parties"), END + 1);
        SparkV15SettlementAlternatives.FeeHoldTerms memory hold =
            SparkV15SettlementAlternatives.FeeHoldTerms(formId, caseId, notice, DUE);
        uint256 evidence = _evidence(alternatives.feeHoldCommitment(hold, REVIEWER));
        bytes32 reviewer = _subject(REVIEWER, app.applicationModule.VERIFIER_ROLE());
        vm.prank(REVIEWER);
        alternatives.imposeFeeHold(hold, evidence, reviewer);
    }

    function _allowEvidenceLifecycle(bytes32 role) private {
        AVAAuthorityMatrix matrix = app.kernel.AUTHORITY_MATRIX();
        vm.prank(ADMIN);
        matrix.setPermission(SparkV15.APP_ID, role, AVACoreTypes.ACTION_RECORD_EVIDENCE_LIFECYCLE, true);
    }

    function _assessment() private view returns (SparkV15Settlement.GroupAssessment memory assessment) {
        SparkV15Settlement.TutorSeatTerms[] memory wages = new SparkV15Settlement.TutorSeatTerms[](1);
        wages[0] = SparkV15Settlement.TutorSeatTerms(PLACE, WAGE, 2);
        assessment.tutor = SparkV15Settlement.TutorPayTerms(
            AGREEMENT, TUTOR, SparkV15Settlement.PaymentSchedule(DUE, DUE + 3 days, 0, 1 days), wages
        );
        assessment.refund = SparkV15Settlement.RefundTerms(
            DOCUMENTS, SparkV15Settlement.PaymentSchedule(END + 1, DUE + 4 days, 0, 1 days)
        );
        assessment.clearanceRef = keccak256("verified clearance and absence of wage deductions or holds");
        assessment.route = SparkV15Settlement.Route.OrdinaryOneToOne;
        assessment.seats = new SparkV15Settlement.SeatFinding[](1);
        assessment.seats[0].disposition = SparkV15Settlement.SeatDisposition.OrdinaryFee;
        assessment.seats[0].serviceAvailabilityRef = keccak256("verified available service on the agreed place");
    }

    function _ordinaryLessonTerms(SparkV15Settlement.GroupAssessment memory assessment)
        private view returns (SparkV15Booking.LessonTerms memory lesson)
    {
        lesson.lessonId = LESSON;
        lesson.provider = PROVIDER;
        lesson.tutor = TUTOR;
        lesson.coordinator = COORDINATOR;
        lesson.startsAt = START;
        lesson.endsAt = END;
        lesson.timeZoneRef = keccak256("UTC");
        lesson.tutorNoticeChannelRef = TUTOR_CHANNEL;
        lesson.tutorFee = WAGE;
        lesson.tutorAgreementRef = AGREEMENT;
        lesson.serviceTermsRef = app.settlement.refundTermsCommitment(LESSON, assessment.refund);
        lesson.tutorPayTermsRef = app.settlement.tutorPayTermsCommitment(LESSON, assessment.tutor);
        lesson.providerResponsibilitiesRef = DOCUMENTS;
        lesson.tutorResponsibilitiesRef = DOCUMENTS;
        lesson.startTermsRef = DOCUMENTS;
        lesson.documentsRef = DOCUMENTS;
    }

    function _ordinaryPlaceTerms(SparkV15Funds.RechargeDebit[] memory debits)
        private view returns (SparkV15Booking.PlaceTerms memory place)
    {
        place.placeId = PLACE;
        place.customer = CUSTOMER;
        place.payer = PAYER;
        place.student = STUDENT;
        place.creditAccount = funds.creditAccount(PAYER);
        place.studentNoticeChannelRef = keccak256("agreed student notice channel");
        place.normalFee = FEE;
        place.payableFee = FEE;
        place.rechargeDebitsHash = keccak256(abi.encode(debits));
    }

    function _prefundingModule() private view returns (IInstalledBookingPrefunding) {
        return IInstalledBookingPrefundingBinding(address(app.booking)).PREFUNDING();
    }

    function _adoptPrefundedDraft(DraftBasis basis)
        private
        returns (bytes32 formId, uint256 funding, SparkV15Funds.RechargeDebit[] memory debits)
    {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        SparkV15Booking.LessonTerms memory lesson = _ordinaryLessonTerms(assessment);
        debits = new SparkV15Funds.RechargeDebit[](1);
        debits[0] = SparkV15Funds.RechargeDebit(_rechargePayer(), FEE);
        SparkV15Booking.PlaceTerms memory place = _ordinaryPlaceTerms(debits);
        token.mint(PROVIDER, 180);
        vm.prank(PROVIDER);
        require(token.transfer(address(funds), 180), "provider backing transfer failed");

        IInstalledBookingPrefunding module = _prefundingModule();
        SparkV15BookingOpening opening = app.booking.OPENING();
        (uint256 packageId, bytes32 lessonCommitment) = opening.prepareLesson(lesson);
        formId = opening.prepareForm(place, lesson.materialsTermsRef, lessonCommitment, 1);
        bytes32[] memory forms = new bytes32[](1);
        forms[0] = formId;
        bytes32 fundingRef = basis == DraftBasis.AdoptedInventory
            ? SparkV15FundingCases(funds.materialBookingCoverage()).inventoryReference(LESSON, _ordinaryRefundScenario(formId))
            : keccak256("verified concurrent customer and tutor funding cases");
        bytes32 commitment = keccak256(abi.encode(
            keccak256("spark.v1.5.booking.verified-prefunding"), lessonCommitment, forms, LESSON_BACKING, fundingRef
        ));
        IInstalledBookingPrefunding.Proof memory proof;
        bytes32 message;
        proof.validThrough = START - 1;
        if (basis == DraftBasis.Registered) {
            funding = _evidence(commitment);
        } else {
            proof.sourceRole = app.applicationModule.SOURCE_ROLE();
            proof.sourceAuthorityId = _subject(SOURCE, proof.sourceRole);
            proof.disclosurePolicyId = app.disclosurePolicyId;
            message = keccak256(abi.encode(
                keccak256("PrefundingEvidence(uint256 packageId,bytes32 lessonId,bytes32 commitment,address verifier,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"),
                packageId, LESSON, commitment, VERIFIER, proof.sourceRole, proof.sourceAuthorityId,
                proof.disclosurePolicyId, proof.validThrough
            ));
            (proof.r, proof.vs) = _signEvidenceMessage("Spark DAO Prefunding Evidence", address(module), message, SOURCE_KEY);
            funding = uint256(message);
        }
        message = keccak256(abi.encode(
            keccak256("AdoptOrdinaryBookingDraft(bytes32 formId,uint128 requiredUnits,bytes32 fundingRef,uint256 fundingEvidenceId,address verifier,uint64 validThrough)"),
            formId, LESSON_BACKING, fundingRef, funding, VERIFIER, proof.validThrough
        ));
        (bytes32 r, bytes32 vs) = _signEvidenceMessage("Spark DAO Booking Draft", address(app.booking), message, COORDINATOR_KEY);
        if (basis == DraftBasis.AdoptedWithAmountControl) {
            vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
            vm.prank(VERIFIER);
            module.adoptOrdinaryBookingDraftWithPrefundingProof(
                lesson, place, LESSON_BACKING - 1, fundingRef, proof.validThrough, r, vs, proof
            );
            require(app.booking.getLesson(LESSON).packageId == 0 && funds.lessonReserved(LESSON) == 0, "failed draft was adopted");
        }
        vm.prank(VERIFIER);
        bytes32 adopted = basis == DraftBasis.Registered
            ? opening.adoptOrdinaryBookingDraft(lesson, place, LESSON_BACKING, fundingRef, funding, proof.validThrough, r, vs)
            : module.adoptOrdinaryBookingDraftWithPrefundingProof(
                lesson, place, LESSON_BACKING, fundingRef, proof.validThrough, r, vs, proof
            );
        require(adopted == formId, "wrong draft form adopted");
    }

    function _ordinaryRefundScenario(bytes32 formId)
        private view returns (SparkV15FundingCases.FundingScenario[] memory scenarios)
    {
        SparkV15FundingCases cases = SparkV15FundingCases(funds.materialBookingCoverage());
        scenarios = new SparkV15FundingCases.FundingScenario[](1);
        scenarios[0].forms = new bytes32[](1);
        scenarios[0].forms[0] = formId;
        scenarios[0].outcomes = new bytes32[](1);
        scenarios[0].outcomes[0] = keccak256("fixture no teaching with full original refund outstanding");
        scenarios[0].expenses = new SparkV15FundingCases.Expense[](1);
        scenarios[0].expenses[0].referenceId = cases.bookingExposureReference(formId, 0);
        scenarios[0].expenses[0].units = FEE;
    }

    function _signEvidenceMessage(string memory name, address verifyingContract, bytes32 message, uint256 signerKey)
        private
        view
        returns (bytes32 r, bytes32 vs)
    {
        bytes32 domain = keccak256(abi.encode(
            keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
            keccak256(bytes(name)), keccak256("1"), block.chainid, verifyingContract
        ));
        (uint8 v, bytes32 rr, bytes32 s) = vm.sign(signerKey, keccak256(abi.encodePacked(hex"1901", domain, message)));
        return (rr, bytes32(uint256(s) | ((uint256(v) - 27) << 255)));
    }

    function _finishTeaching(bytes32 formId, bool recordAttendance, bool recordFeedback) private {
        vm.warp(END);
        bytes32 end = keccak256("observed actual teaching end");
        uint256 evidenceId = _evidence(app.booking.teachingEndCommitment(LESSON, END, end));
        vm.prank(VERIFIER);
        app.booking.recordTeachingEnded(LESSON, END, end, evidenceId);
        vm.warp(END + 1);
        _reportTeaching(formId, recordAttendance, recordFeedback);
    }

    function _startObservation(bytes32 conflict) private view returns (SparkV15Booking.StartObservation memory) {
        address[] memory present = new address[](1);
        present[0] = STUDENT;
        return SparkV15Booking.StartObservation(
            START, true, present, keccak256("observed actual teaching start"), conflict
        );
    }

    function _recordLegacyStart(SparkV15Booking.StartObservation memory observation) private {
        SparkV15Booking booking = app.booking;
        uint256 evidenceId = _evidence(booking.teachingStartCommitment(LESSON, observation));
        vm.prank(VERIFIER);
        booking.recordTeachingStarted(LESSON, observation, evidenceId);
    }

    function _reportTeaching(bytes32 formId, bool recordAttendance, bool recordFeedback) private {
        SparkV15Booking booking = app.booking;
        bytes32 tutorReport = keccak256("tutor's completion report");
        uint256 evidenceId = _evidence(booking.tutorDeliveryCommitment(LESSON, true, tutorReport));
        vm.prank(TUTOR);
        booking.recordTutorDelivery(LESSON, true, tutorReport, evidenceId);
        if (recordAttendance) {
            bytes32 attendance = keccak256("student confirmed attendance");
            evidenceId = _evidence(booking.attendanceCommitment(formId, true, attendance));
            vm.prank(STUDENT);
            booking.recordAttendance(formId, true, attendance, evidenceId);
        }
        if (recordFeedback) {
            bytes32 feedback = keccak256("student confirmed complete service");
            SparkV15Booking.ServiceStatus delivered = SparkV15Booking.ServiceStatus.FullyDelivered;
            evidenceId = _evidence(booking.serviceFeedbackCommitment(formId, delivered, feedback, bytes32(0)));
            vm.prank(STUDENT);
            booking.recordServiceFeedback(formId, delivered, feedback, bytes32(0), evidenceId);
        }
    }

    function _approvePayment(bytes32 obligationId, uint128 amount, uint64 requestDeadline)
        private
        returns (uint256 requestId)
    {
        SparkV15Payments.ApprovalTerms memory terms =
            SparkV15Payments.ApprovalTerms(obligationId, EXECUTOR, amount, requestDeadline + 1 days, 0);
        bytes32 parameters = app.payments.approvalParameters(terms);
        bytes32 commitment = app.requests.commitmentFor(
            SparkV15.APP_ID,
            address(app.payments),
            SparkV15.RESPONSE_APPROVE_PAYMENT,
            parameters,
            SparkV15.APPROVAL_BURDEN,
            requestDeadline
        );
        uint256 stateId = _vestApproval(_registerApprovalObject(commitment));
        bytes32 sourceRole = app.applicationModule.SOURCE_ROLE();
        bytes32 sourceId = _subject(SOURCE, sourceRole);
        AVARequestAllocation.RequestInput memory input = AVARequestAllocation.RequestInput(
            stateId, address(app.payments), SparkV15.RESPONSE_APPROVE_PAYMENT, parameters, SparkV15.APPROVAL_BURDEN,
            requestDeadline
        );
        vm.prank(SOURCE);
        requestId = app.requests.createRequest(input, sourceRole, sourceId);
        bytes32 allocatorRole = app.applicationModule.ALLOCATOR_ROLE();
        bytes32 allocatorId = _subject(ALLOCATOR, allocatorRole);
        vm.prank(ALLOCATOR);
        app.requests.approve(requestId, allocatorRole, allocatorId);
        require(app.payments.getApproval(requestId).approver == address(0), "allocation already recorded App approval");
        vm.prank(ALLOCATOR);
        app.payments.recordApproval(requestId, terms);

        AVARequestAllocation.RequestRecord memory request = app.requests.getRequest(requestId);
        require(
            request.creator == SOURCE && request.allocator == ALLOCATOR && request.triggeredBy == ALLOCATOR,
            "wrong request actors"
        );
        require(
            request.input.recognisedStateId == stateId && request.consumed && request.completed, "request not completed"
        );
        SparkV15Payments.Approval memory approval = app.payments.getApproval(requestId);
        require(approval.approver == ALLOCATOR && approval.authorityId == allocatorId, "wrong App approval authority");
        require(
            keccak256(abi.encode(approval.terms)) == keccak256(abi.encode(terms)) && approval.paid == 0,
            "wrong unpaid approval scope"
        );
    }

    function _registerApprovalObject(bytes32 commitment) private returns (uint256) {
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        bytes32 subject = _subject(SOURCE, role);
        uint256 evidenceId = _evidence(keccak256(abi.encode(commitment, "wage approval support")));
        AVAGovernanceKernel.GovernedObjectInput memory input = AVAGovernanceKernel.GovernedObjectInput({
            appId: SparkV15.APP_ID,
            workflowKey: SparkV15.WORKFLOW,
            packageId: app.packageId,
            roleKey: role,
            objectTypeKey: SparkV15.OBJECT_PAYMENT_APPROVAL,
            objectCommitment: commitment,
            parentObjectId: 0,
            subjectId: subject,
            evidenceReceiptId: evidenceId,
            disclosurePolicyId: app.disclosurePolicyId,
            metadataHash: commitment,
            authorityId: subject,
            uri: "test:wage-approval"
        });
        vm.prank(SOURCE);
        return app.kernel.registerGovernedObject(input);
    }

    function _vestApproval(uint256 objectId) private returns (uint256 stateId) {
        bytes32 role = app.applicationModule.VERIFIER_ROLE();
        bytes32 subject = _subject(VERIFIER, role);
        AVAGovernanceKernel.RecognisedStateFormationInput memory formation =
            AVAGovernanceKernel.RecognisedStateFormationInput(
                objectId,
                role,
                subject,
                AVACoreTypes.Stage.Verification,
                AVACoreTypes.RecognisedStateStatus.Provisional,
                keccak256("verified wage approval formation"),
                "test:formation"
            );
        vm.prank(VERIFIER);
        stateId = app.kernel.formRecognisedState(formation);
        AVAGovernanceKernel.RecognisedStateTransitionInput memory transition =
            AVAGovernanceKernel.RecognisedStateTransitionInput(
                stateId,
                role,
                subject,
                AVACoreTypes.RecognisedStateStatus.Challengeable,
                keccak256("wage approval challengeable"),
                "test:challengeable"
            );
        vm.prank(VERIFIER);
        app.kernel.transitionRecognisedState(transition);
        transition.toStatus = AVACoreTypes.RecognisedStateStatus.Vested;
        transition.reasonHash = keccak256("wage approval vested");
        transition.reasonURI = "test:vesting";
        vm.prank(VERIFIER);
        app.kernel.vestRecognisedState(transition);
        AVACoreTypes.RecognisedStateRecord memory state = app.kernel.getRecognisedState(stateId);
        require(
            state.status == AVACoreTypes.RecognisedStateStatus.Vested && state.governedObjectId == objectId,
            "wrong vested state"
        );
    }

    function _rechargePayer() private returns (uint256 receiptId) {
        bytes32 subject = _subject(PROVIDER, funds.CREDIT_PROVIDER_ROLE());
        vm.prank(PROVIDER);
        bytes32 offer = funds.offerRecharge(
            SparkV15Funds.RechargeTerms(PAYER, FEE, FEE, EPOCH + 1 days, AGREEMENT), subject
        );
        token.mint(PAYER, FEE);
        vm.prank(PAYER);
        token.approve(address(funds), FEE);
        vm.prank(PAYER);
        receiptId = funds.recharge(offer);
        require(funds.getRechargeReceipt(receiptId).received == FEE, "recharge missing");
    }

    function _provideTerms(bytes32 formId, address recipient) private {
        uint256 evidence = _evidence(app.booking.provisionCommitment(formId, recipient, DOCUMENTS));
        vm.prank(COORDINATOR);
        app.booking.recordTermsProvision(formId, recipient, DOCUMENTS, evidence);
    }

    function _accept(bytes32 formId, SparkV15Booking.Acceptance role, address actor) private {
        vm.prank(actor);
        app.booking.acceptForm(formId, role);
    }

    function _evidence(bytes32 commitment) private returns (uint256) {
        return _registeredEvidence(commitment, keccak256("verified Spark lesson record"));
    }

    function _registeredEvidence(bytes32 commitment, bytes32 evidenceTypeHash) private returns (uint256) {
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        bytes32 subject = _subject(SOURCE, role);
        AVAEvidenceRegistry.EvidenceRegistrationInput memory input = AVAEvidenceRegistry.EvidenceRegistrationInput({
            appId: SparkV15.APP_ID,
            workflowKey: SparkV15.WORKFLOW,
            packageId: app.packageId,
            roleKey: role,
            subjectId: subject,
            commitment: commitment,
            evidenceTypeHash: evidenceTypeHash,
            disclosurePolicyId: app.disclosurePolicyId,
            authorityId: subject,
            uri: "test:lesson-record"
        });
        vm.prank(SOURCE);
        return registry.registerEvidence(input);
    }

    function _subject(address actor, bytes32 role) private view returns (bytes32) {
        return app.kernel.IDENTITY_REGISTRY().subjectOf(actor, SparkV15.APP_ID, role);
    }

    function _env(string memory name, address value) private {
        vm.setEnv(name, vm.toString(value));
    }
}
