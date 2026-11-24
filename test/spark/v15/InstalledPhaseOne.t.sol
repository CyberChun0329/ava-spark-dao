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
import {SparkV15CustomerRedress, SparkV15LessonRemedies} from "../../../src/apps/spark/v15/SparkV15LessonRemedies.sol";
import {
    SparkV15FundingCases,
    SparkV15MaterialProvisions,
    SparkV15ServiceReserve
} from "../../../src/apps/spark/v15/SparkV15MaterialProvisions.sol";
import {SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15PaymentTakeover} from "../../../src/apps/spark/v15/SparkV15PaymentTakeover.sol";
import {SparkV15Returns} from "../../../src/apps/spark/v15/SparkV15Returns.sol";
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
import {SparkV15TemporaryHolds} from "../../../src/apps/spark/v15/SparkV15TemporaryHolds.sol";
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

/// @notice In-process exercise of the shipped installers and the normal paid one-to-one entry points.
contract InstalledPhaseOneTest {
    enum BookingPath {
        Recorded,
        Signed,
        Withdrawn
    }

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
    address private constant ALTERNATE = address(0x7416);
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
    bytes32 private constant TAKEOVER_CONCERN = keccak256("retained tutor settlement matter");
    bytes32 private constant CORE_PARTNER_ROLE = keccak256("ava.spark.role.core-partner.v1.5");

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
        _install(true);
    }

    function _install(bool withMaterials) private {
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
        _env("SPARK_V15_ALTERNATIVE_CONTACT", ALTERNATE);
        _env("SPARK_V15_MATERIALS_DAO", withMaterials ? MATERIALS_DAO : address(0));
        _env("SPARK_V15_SERVICE_RESERVE", withMaterials ? SERVICE_RESERVE : address(0));
        app = new DeploySparkV15OnExistingCore().run();
        funds = app.payments.FUNDS();
        require(address(app.kernel) == address(core.kernel), "wrong installed Core");
        require(address(app.payments.REQUEST_ALLOCATION()) == address(core.requests), "wrong request allocation");
        require((funds.materialBookingCoverage().code.length != 0) == withMaterials, "wrong material coverage");
        require((funds.ordinaryBookingCoverage().code.length == 0) == withMaterials, "wrong ordinary coverage");
    }

    function testInstalledOverdueTakeoverRecordsIndependentNoticeWithoutChangingPartialWage() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        bytes32 obligation = _settle(formId, assessment);
        bytes32 termsId = _publishWageTakeoverTerms(formId);
        uint64 deadline = DUE + 3 days;
        uint256 approval = _approvePayment(obligation, WAGE, deadline);
        vm.warp(DUE);
        vm.prank(EXECUTOR);
        uint256 receipt = app.payments.pay(approval, 3);

        SparkV15PaymentTakeover.Input memory input = SparkV15PaymentTakeover.Input({
            caseId: bytes32(0),
            termsId: termsId,
            obligationId: obligation,
            takenOverAt: deadline,
            responsible: COORDINATOR,
            assignedAt: deadline,
            newActionDate: deadline + 2 days,
            progress: keccak256("three received, five remain"),
            notice: SparkV15ReviewContext.Notice(keccak256("notice delivered to provider and tutor"), deadline),
            unpaidAtDeadline: 5,
            unpaidAtTakeover: 5,
            cutoffSelection: SparkV15PaymentTakeover.CutoffSelection(false, bytes32(0), 0, bytes32(0)),
            settlementBasis: bytes32(0)
        });
        bytes32 actorAuthority = _subject(CORE_PARTNER, CORE_PARTNER_ROLE);
        vm.warp(deadline);
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        vm.prank(CORE_PARTNER);
        app.paymentTakeover.record(input, 0, actorAuthority);

        vm.warp(deadline + 1);
        input.takenOverAt = deadline + 1;
        input.assignedAt = deadline + 1;
        input.notice.sentAt = deadline + 1;
        uint256 proof = _evidence(app.paymentTakeover.takeoverCommitment(input, CORE_PARTNER));
        bytes32 wrongActorAuthority = _subject(COORDINATOR, app.booking.COORDINATOR_ROLE());
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        vm.prank(COORDINATOR);
        app.paymentTakeover.record(input, proof, wrongActorAuthority);
        vm.prank(CORE_PARTNER);
        bytes32 recordId = app.paymentTakeover.record(input, proof, actorAuthority);
        SparkV15PaymentTakeover.Record memory saved = app.paymentTakeover.get(recordId);
        require(saved.responsible == COORDINATOR && saved.newActionDate == deadline + 2 days,
            "actual assignment and date missing"
        );
        require(saved.takenOverAt == deadline + 1 && saved.evidenceId == proof, "notice evidence unavailable");
        require(saved.caseId == bytes32(0) && saved.termsId == termsId
            && saved.obligationId == obligation && saved.cutoff == deadline,
            "wrong governing payment"
        );
        require(app.payments.getObligation(obligation).terms.executionDeadline == deadline
            && app.payments.getObligation(obligation).paid == 3 && app.payments.getReceipt(receipt).amount == 3
            && token.balanceOf(TUTOR) == 3 && funds.paymentReserved(obligation) == 5, "changed payment"
        );
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        vm.prank(CORE_PARTNER);
        app.paymentTakeover.record(input, proof, actorAuthority);
        vm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        vm.prank(EXECUTOR);
        app.payments.pay(approval, 5);
    }

    function testInstalledOverdueTakeoverWaitsForFirstCompleteReleaseAndKeepsItsDeadline() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        bytes32 obligation = _settle(formId, assessment);
        bytes32 caseId = _retainWageForTakeover(formId, obligation);
        _fileWageTakeoverConcern(caseId, obligation);
        uint64 originalDeadline = DUE + 3 days;
        uint256 approval = _approvePayment(obligation, WAGE, originalDeadline + 10 days);
        vm.warp(originalDeadline - 2 days);
        bytes32 first = _holdWageForTakeover(caseId, obligation, "first formal hold");
        vm.warp(originalDeadline - 1 days);
        bytes32 overlap = _holdWageForTakeover(caseId, obligation, "overlapping formal hold");
        vm.warp(originalDeadline + 1 days);
        _liftWageForTakeover(first, obligation);
        _expectTakeoverRejected(caseId, WAGE);

        uint64 firstRelease = originalDeadline + 2 days;
        vm.warp(firstRelease);
        _liftWageForTakeover(overlap, obligation);
        vm.prank(EXECUTOR);
        app.payments.pay(approval, 3);
        vm.warp(firstRelease + 1);
        _holdWageForTakeover(caseId, obligation, "later formal hold");
        uint64 cutoff = firstRelease + 1 days;
        vm.warp(cutoff);
        _expectTakeoverRejected(caseId, 5);
        vm.warp(cutoff + 1);
        SparkV15PaymentTakeover.Input memory original = _takeoverInput(caseId, 5);
        original.cutoffSelection.originalExecution = true;
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        app.paymentTakeover.takeoverCommitment(original, CORE_PARTNER);
        SparkV15PaymentTakeover.Record memory saved = _recordWageTakeover(caseId, 5);
        require(saved.cutoff == cutoff && saved.obligationId == obligation, "a later hold restarted the window");
        require(app.payments.HOLDS().getStatus(obligation).active, "lost separate later hold");
        require(app.payments.getObligation(obligation).paid == 3 && token.balanceOf(TUTOR) == 3, "partial pay lost");
        require(app.payments.getObligation(obligation).terms.executionDeadline == originalDeadline,
            "formal release replaced the date on the form"
        );
    }

    function testInstalledOverdueTakeoverUsesEarlierVerifiedLawBeforeAnyCompleteRelease() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        assessment.tutor.schedule.dueAt = END + 2 days;
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        uint64 legal = END + 3 days;
        _verifyEarlierTakeoverDeadline(legal);
        bytes32 obligation = _settle(formId, assessment);
        bytes32 caseId = _retainWageForTakeover(formId, obligation);
        _fileWageTakeoverConcern(caseId, obligation);
        vm.warp(legal - 1);
        _holdWageForTakeover(caseId, obligation, "formal hold still in force at legal deadline");
        vm.warp(legal);
        _expectTakeoverRejected(caseId, WAGE);
        vm.warp(legal + 1);
        SparkV15PaymentTakeover.Record memory saved = _recordWageTakeover(caseId, WAGE);
        SparkV15Payments.Obligation memory payment = app.payments.getObligation(obligation);
        require(saved.cutoff == legal && saved.obligationId == obligation, "earlier applicable law lost");
        require(app.payments.HOLDS().getStatus(obligation).active && payment.paid == 0, "record changed payment");
        require(payment.terms.legalDeadline == legal && payment.terms.executionDeadline == DUE + 3 days,
            "record rewrote original deadlines"
        );
    }

    function testInstalledOverdueTakeoverCanBeFiledAfterFullOrdinaryPayment() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        bytes32 obligation = _settle(formId, assessment);
        bytes32 caseId = _retainWageForTakeover(formId, obligation);
        _fileWageTakeoverConcern(caseId, obligation);
        uint256 approval = _approvePayment(obligation, WAGE, DUE + 3 days);
        vm.warp(DUE + 1);
        bytes32 hold = _holdWageForTakeover(caseId, obligation, "formal hold after the due date");
        uint64 releaseAt = DUE + 6;
        vm.warp(releaseAt);
        _liftWageForTakeover(hold, obligation);

        uint64 cutoff = releaseAt + 1 days;
        vm.warp(cutoff + 1);
        SparkV15PaymentTakeover.Input memory input = _takeoverInput(caseId, WAGE);
        vm.warp(cutoff + 2);
        vm.prank(EXECUTOR);
        uint256 receiptId = app.payments.pay(approval, WAGE);

        uint256 proof = _evidence(app.paymentTakeover.takeoverCommitment(input, CORE_PARTNER));
        bytes32 authority = _subject(CORE_PARTNER, CORE_PARTNER_ROLE);
        vm.prank(CORE_PARTNER);
        bytes32 id = app.paymentTakeover.record(input, proof, authority);
        SparkV15PaymentTakeover.Record memory saved = app.paymentTakeover.get(id);
        require(saved.cutoff == cutoff && saved.takenOverAt == cutoff + 1 && saved.recordedAt == cutoff + 2,
            "filing did not preserve original takeover"
        );
        SparkV15Payments.PaymentReceipt memory receipt = app.payments.getReceipt(receiptId);
        require(receipt.amount == WAGE && receipt.paidAt == cutoff + 2 && receipt.promptCutoff == cutoff
            && !receipt.promptCutoffMet && token.balanceOf(TUTOR) == WAGE, "filing changed earlier real payment"
        );
    }

    function testInstalledOverdueTakeoverUsesOriginalCutoffAfterPromptPaymentAndActualReturn() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        bytes32 obligation = _settle(formId, assessment);
        bytes32 caseId = _retainWageForTakeover(formId, obligation);
        _fileWageTakeoverConcern(caseId, obligation);
        uint64 original = DUE + 3 days;
        uint256 approval = _approvePayment(obligation, WAGE, original);
        vm.warp(DUE + 1);
        bytes32 holdId = _holdWageForTakeover(caseId, obligation, "hold before original cutoff");
        uint64 releasedAt = DUE + 2;
        vm.warp(releasedAt);
        _liftWageForTakeover(holdId, obligation);
        vm.prank(EXECUTOR);
        uint256 receiptId = app.payments.pay(approval, WAGE);

        uint64 prompt = releasedAt + 1 days;
        vm.warp(prompt);
        SparkV15Payments.PaymentReceipt memory receipt = app.payments.getReceipt(receiptId);
        require(receipt.promptCutoff == prompt && receipt.promptCutoffMet, "prompt payment not made");
        require(app.payments.getObligation(obligation).paid == WAGE && token.balanceOf(TUTOR) == WAGE,
            "amount still unpaid at prompt cutoff"
        );
        require(token.balanceOf(address(funds)) == 192 && funds.paymentReserved(obligation) == 0, "wrong payout");

        vm.warp(prompt + 1);
        _returnWage(receiptId, 3);
        require(
            app.payments.getObligation(obligation).paid == 5 && token.balanceOf(TUTOR) == 5
                && token.balanceOf(address(funds)) == 195 && funds.paymentReserved(obligation) == 3,
            "return did not restore payment backing"
        );
        vm.warp(original);
        SparkV15PaymentTakeover.Input memory input = _takeoverInput(caseId, 3);
        input.cutoffSelection.originalExecution = true;
        bytes32 authority = _subject(CORE_PARTNER, CORE_PARTNER_ROLE);
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        vm.prank(CORE_PARTNER);
        app.paymentTakeover.record(input, 0, authority);

        vm.warp(original + 1);
        input = _takeoverInput(caseId, 3);
        input.cutoffSelection.originalExecution = true;
        uint256 proof = _evidence(app.paymentTakeover.takeoverCommitment(input, CORE_PARTNER));
        input.cutoffSelection.originalExecution = false;
        vm.expectRevert(SparkV15ReviewContext.InvalidEvidence.selector);
        vm.prank(CORE_PARTNER);
        app.paymentTakeover.record(input, proof, authority);
        input.cutoffSelection.originalExecution = true;
        vm.prank(CORE_PARTNER);
        bytes32 id = app.paymentTakeover.record(input, proof, authority);
        SparkV15PaymentTakeover.Record memory saved = app.paymentTakeover.get(id);
        require(saved.cutoff == original && saved.takenOverAt == original + 1, "wrong original cutoff");
        require(app.payments.getApproval(approval).paid == 5 && app.payments.getReceipt(receiptId).amount == WAGE
            && app.payments.getObligation(obligation).terms.executionDeadline == original
            && token.balanceOf(address(funds)) == 195, "filing changed the settled history"
        );
        vm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        vm.prank(EXECUTOR);
        app.payments.pay(approval, 3);
    }

    function testInstalledOverdueTakeoverFilesEarlierCompleteLiftAfterLaterRelease() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        bytes32 obligation = _settle(formId, assessment);
        bytes32 caseId = _retainWageForTakeover(formId, obligation);
        _fileWageTakeoverConcern(caseId, obligation);
        vm.warp(DUE + 1);
        bytes32 first = _holdWageForTakeover(caseId, obligation, "first overlapping hold");
        vm.warp(DUE + 2);
        bytes32 earlierRelease = _holdWageForTakeover(caseId, obligation, "second overlapping hold");
        vm.warp(DUE + 3);
        _liftWageForTakeover(first, obligation);
        uint64 releasedAt = DUE + 6;
        vm.warp(releasedAt);
        _liftWageForTakeover(earlierRelease, obligation);
        uint64 cutoff = releasedAt + 1 days;
        vm.warp(cutoff + 1);
        SparkV15PaymentTakeover.Input memory input = _takeoverInput(caseId, WAGE);

        vm.warp(cutoff + 2);
        bytes32 laterRelease = _holdWageForTakeover(caseId, obligation, "later hold");
        vm.warp(cutoff + 3);
        _liftWageForTakeover(laterRelease, obligation);
        bytes32 authority = _subject(CORE_PARTNER, CORE_PARTNER_ROLE);
        require(app.payments.HOLDS().getStatus(obligation).lastFullReleaseAt == cutoff + 3,
            "a later release did not replace the latest read"
        );
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        vm.prank(CORE_PARTNER);
        app.paymentTakeover.record(input, 0, authority);
        input.cutoffSelection = SparkV15PaymentTakeover.CutoffSelection(false, first, WAGE, bytes32(0));
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        app.paymentTakeover.takeoverCommitment(input, CORE_PARTNER);
        input.cutoffSelection.releasedHoldId = laterRelease;
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        app.paymentTakeover.takeoverCommitment(input, CORE_PARTNER);
        input.cutoffSelection.releasedHoldId = earlierRelease;
        uint256 proof = _evidence(app.paymentTakeover.takeoverCommitment(input, CORE_PARTNER));
        vm.prank(CORE_PARTNER);
        bytes32 id = app.paymentTakeover.record(input, proof, authority);
        SparkV15PaymentTakeover.Record memory saved = app.paymentTakeover.get(id);
        require(saved.cutoff == cutoff && saved.takenOverAt == cutoff + 1 && saved.recordedAt == cutoff + 3,
            "wrong historical prompt cutoff"
        );
        require(app.payments.getObligation(obligation).paid == 0 && funds.paymentReserved(obligation) == WAGE
            && token.balanceOf(TUTOR) == 0, "filing altered payment or reserve"
        );
    }

    function testInstalledOverdueTakeoverFilesReleaseAtTemporaryExpiryAfterLaterRelease() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        bytes32 obligation = _settle(formId, assessment);
        bytes32 caseId = _retainWageForTakeover(formId, obligation);
        _fileWageTakeoverConcern(caseId, obligation);
        uint256 approval = _approvePayment(obligation, WAGE, DUE + 3 days);

        vm.warp(DUE + 1);
        bytes32 termsId = app.cases.INTAKE().caseContext(caseId).termsId;
        bytes32 temporaryCase = _fileWageTakeoverConcern(termsId, keccak256("separate wage concern"), obligation);
        uint64 expiry = DUE + 6;
        bytes32 temporary = _temporarilyHoldWageForTakeover(temporaryCase, obligation, expiry);
        vm.warp(DUE + 2);
        bytes32 formal = _holdWageForTakeover(caseId, obligation, "formal hold on the original matter");
        vm.warp(DUE + 3);
        _liftWageForTakeover(formal, obligation);

        SparkV15PaymentHolds holds = app.payments.HOLDS();
        require(!holds.getFormalHold(formal).completelyReleased && holds.getStatus(obligation).active,
            "formal lift released an active temporary hold");
        vm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        vm.prank(EXECUTOR);
        app.payments.pay(approval, 3);

        vm.warp(expiry);
        vm.prank(EXECUTOR);
        uint256 receiptId = app.payments.pay(approval, 3);
        uint64 cutoff = expiry + 1 days;
        require(app.payments.getReceipt(receiptId).promptCutoff == cutoff
            && holds.getStatus(obligation).lastFullReleaseAt == expiry, "wrong release or prompt payment clock");

        vm.warp(cutoff + 1);
        SparkV15PaymentTakeover.Input memory input = _takeoverInput(caseId, 5);
        vm.warp(cutoff + 2);
        bytes32 later = _holdWageForTakeover(caseId, obligation, "later formal hold");
        vm.warp(cutoff + 3);
        _liftWageForTakeover(later, obligation);
        require(holds.getStatus(obligation).lastFullReleaseAt == cutoff + 3, "latest release was not overwritten");

        bytes32 authority = _subject(CORE_PARTNER, CORE_PARTNER_ROLE);
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        vm.prank(CORE_PARTNER);
        app.paymentTakeover.record(input, 0, authority);

        input.cutoffSelection = SparkV15PaymentTakeover.CutoffSelection(false, formal, WAGE, bytes32(0));
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        app.paymentTakeover.takeoverCommitment(input, CORE_PARTNER);
        input.cutoffSelection.releasedHoldId = later;
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        app.paymentTakeover.takeoverCommitment(input, CORE_PARTNER);

        input.cutoffSelection.releasedHoldId = formal;
        input.cutoffSelection.expiringTemporaryHoldId = temporary;
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(CORE_PARTNER);
        app.paymentTakeover.record(input, 0, authority);

        uint256 proof = _evidence(app.paymentTakeover.takeoverCommitment(input, CORE_PARTNER));
        input.cutoffSelection.unpaidAtRelease = 5;
        vm.expectRevert(SparkV15ReviewContext.InvalidEvidence.selector);
        vm.prank(CORE_PARTNER);
        app.paymentTakeover.record(input, proof, authority);

        input.cutoffSelection.unpaidAtRelease = WAGE;
        vm.prank(CORE_PARTNER);
        bytes32 id = app.paymentTakeover.record(input, proof, authority);
        SparkV15PaymentTakeover.Record memory saved = app.paymentTakeover.get(id);
        require(saved.cutoff == cutoff && saved.takenOverAt == cutoff + 1 && saved.recordedAt == cutoff + 3,
            "wrong historical takeover clock");
        require(app.payments.getObligation(obligation).paid == 3 && funds.paymentReserved(obligation) == 5
            && token.balanceOf(TUTOR) == 3 && token.balanceOf(address(funds)) == 197,
            "filing changed the actual payout or remaining reserve");
    }

    function _returnWage(uint256 receiptId, uint128 amount) private {
        SparkV15Returns returnsLedger = app.payments.RETURNS();
        SparkV15Returns.ReturnTerms memory terms =
            SparkV15Returns.ReturnTerms(receiptId, amount, keccak256("verified tutor wage return"));
        uint256 proof = _evidence(returnsLedger.returnEvidenceCommitment(terms));
        bytes32 authority = _subject(VERIFIER, app.applicationModule.VERIFIER_ROLE());
        vm.prank(VERIFIER);
        returnsLedger.authorisePaymentReturn(terms, proof, authority);
        vm.prank(TUTOR);
        token.approve(address(funds), amount);
        vm.prank(TUTOR);
        uint256 returnId = returnsLedger.returnPayment(terms, proof);
        SparkV15Returns.PaymentReturn memory returned = returnsLedger.getPaymentReturn(returnId);
        require(returned.terms.receiptId == receiptId && returned.terms.amount == amount
            && returned.returnedAt == block.timestamp, "return history missing"
        );
    }

    function _verifyEarlierTakeoverDeadline(uint64 legal) private {
        SparkV15SettlementOccurrences occurrences = app.settlement.ALTERNATIVES().OCCURRENCES();
        SparkV15SettlementOccurrences.TutorLegalScope memory scope = SparkV15SettlementOccurrences.TutorLegalScope(
            LESSON, bytes32(0), TUTOR, AGREEMENT, app.booking.getLesson(LESSON).terms.tutorPayTermsRef, START
        );
        SparkV15SettlementOccurrences.StatutoryTutorDeadline memory facts =
            SparkV15SettlementOccurrences.StatutoryTutorDeadline(
                scope, legal, true, keccak256("jurisdiction"), keccak256("wage law"),
                keccak256("confirmed statutory pay deadline for this agreement")
            );
        uint256 proof = _registeredEvidence(
            occurrences.earlierTutorDeadlineCommitment(facts, REVIEWER), occurrences.STATUTORY_TUTOR_DEADLINE_EVIDENCE_TYPE()
        );
        bytes32 reviewer = _subject(REVIEWER, app.applicationModule.VERIFIER_ROLE());
        vm.prank(REVIEWER);
        occurrences.verifyEarlierTutorDeadline(facts, proof, reviewer);
    }

    function _holdWageForTakeover(bytes32 caseId, bytes32 obligation, string memory reason)
        private
        returns (bytes32)
    {
        SparkV15PaymentHolds.HoldTerms memory terms = SparkV15PaymentHolds.HoldTerms(
            obligation, caseId, keccak256(bytes(reason)), DUE + 20 days, app.payments.getObligation(obligation).version
        );
        uint256 proof = _evidence(app.payments.HOLDS().formalHoldCommitment(terms, REVIEWER));
        bytes32 reviewer = _subject(REVIEWER, app.applicationModule.VERIFIER_ROLE());
        vm.prank(REVIEWER);
        return app.payments.imposeFormalHold(terms, proof, reviewer);
    }

    function _liftWageForTakeover(bytes32 holdId, bytes32 obligation) private {
        uint256 version = app.payments.getObligation(obligation).version;
        bytes32 disposition = keccak256("independently confirmed release");
        uint256 proof = _evidence(app.payments.HOLDS().formalLiftCommitment(holdId, disposition, version, REVIEWER));
        bytes32 reviewer = _subject(REVIEWER, app.applicationModule.VERIFIER_ROLE());
        vm.prank(REVIEWER);
        app.payments.liftFormalHold(holdId, disposition, version, proof, reviewer);
    }

    function _temporarilyHoldWageForTakeover(bytes32 caseId, bytes32 obligation, uint64 expiry)
        private
        returns (bytes32)
    {
        SparkV15PaymentHolds holds = app.payments.HOLDS();
        bytes32 termsId = app.cases.INTAKE().caseContext(caseId).termsId;
        uint64 handoffDeadline = expiry - 1;
        uint256 dates = _evidence(holds.temporaryHoldDeadlinesCommitment(termsId, expiry, handoffDeadline));
        holds.recordTemporaryHoldDeadlines(termsId, expiry, handoffDeadline, dates);

        SparkV15TemporaryHolds.Terms memory terms = SparkV15TemporaryHolds.Terms(
            obligation, caseId, keccak256("notice of an independent temporary hold"), uint64(block.timestamp) - 1,
            expiry, app.payments.getObligation(obligation).version
        );
        uint256 proof = _evidence(holds.temporaryHoldCommitment(terms, ALTERNATE));
        bytes32 authority = _subject(ALTERNATE, SparkV15.ALTERNATIVE_CONTACT_ROLE);
        vm.prank(ALTERNATE);
        return app.payments.imposeTemporaryHold(terms, proof, authority);
    }

    function _takeoverInput(bytes32 caseId, uint128 unpaid) private view returns (SparkV15PaymentTakeover.Input memory) {
        uint64 nowAt = uint64(block.timestamp);
        SparkV15ReviewContext.ConcernContext memory context = app.cases.INTAKE().caseContext(caseId);
        return SparkV15PaymentTakeover.Input({
            caseId: caseId,
            termsId: context.termsId,
            obligationId: context.obligationId,
            takenOverAt: nowAt,
            responsible: COORDINATOR,
            assignedAt: nowAt,
            newActionDate: nowAt + 2 days,
            progress: keccak256("progress verified and shared with the parties"),
            notice: SparkV15ReviewContext.Notice(keccak256("notice delivered to the case parties"), nowAt),
            unpaidAtDeadline: unpaid,
            unpaidAtTakeover: unpaid,
            cutoffSelection: SparkV15PaymentTakeover.CutoffSelection(false, bytes32(0), 0, bytes32(0)),
            settlementBasis: bytes32(0)
        });
    }

    function _expectTakeoverRejected(bytes32 caseId, uint128 unpaid) private {
        SparkV15PaymentTakeover.Input memory input = _takeoverInput(caseId, unpaid);
        bytes32 actorAuthority = _subject(CORE_PARTNER, CORE_PARTNER_ROLE);
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        vm.prank(CORE_PARTNER);
        app.paymentTakeover.record(input, 0, actorAuthority);
    }

    function _recordWageTakeover(bytes32 caseId, uint128 unpaid)
        private
        returns (SparkV15PaymentTakeover.Record memory)
    {
        SparkV15PaymentTakeover.Input memory input = _takeoverInput(caseId, unpaid);
        uint256 proof = _evidence(app.paymentTakeover.takeoverCommitment(input, CORE_PARTNER));
        bytes32 actorAuthority = _subject(CORE_PARTNER, CORE_PARTNER_ROLE);
        vm.prank(CORE_PARTNER);
        bytes32 id = app.paymentTakeover.record(input, proof, actorAuthority);
        return app.paymentTakeover.get(id);
    }

    function _fileWageTakeoverConcern(bytes32 caseId, bytes32 obligation) private {
        SparkV15ConcernIntake intake = app.cases.INTAKE();
        _fileWageTakeoverConcern(intake.caseContext(caseId).termsId, TAKEOVER_CONCERN, obligation);
    }

    function _fileWageTakeoverConcern(bytes32 termsId, bytes32 concernRef, bytes32 obligation)
        private
        returns (bytes32 caseId)
    {
        SparkV15ReviewContext.ConcernInput memory input;
        input.termsId = termsId;
        input.concernRef = concernRef;
        input.obligationId = obligation;
        input.receiver = COORDINATOR;
        input.subject = SparkV15ReviewContext.ConcernSubject.Tutor;
        input.claim = keccak256(abi.encode("request for independent review of the unpaid wage", concernRef));
        input.parties = new address[](2);
        input.parties[0] = PROVIDER;
        input.parties[1] = TUTOR;
        caseId = app.cases.caseIdFor(LESSON, concernRef);
        uint256 proof = _evidence(app.cases.evidenceCommitment(
            caseId, SparkV15ReviewActions.ACTION_RECEIVE_CONCERN, TUTOR, keccak256(abi.encode(input))
        ));
        SparkV15ConcernIntake intake = app.cases.INTAKE();
        vm.prank(TUTOR);
        intake.receiveConcern(input, proof);
    }

    function _publishWageTakeoverTerms(bytes32 formId) private returns (bytes32 termsId) {
        SparkV15ReviewContext.ReviewTerms memory terms;
        terms.lessonId = LESSON;
        terms.publication = DOCUMENTS;
        terms.governingForm = formId;
        terms.provider = PROVIDER;
        terms.coordinator = COORDINATOR;
        terms.alternativeContact = ALTERNATE;
        terms.leadAcademicTutor = ALLOCATOR;
        terms.namedReviewer = REVIEWER;
        terms.escalationContact = CORE_PARTNER;
        terms.replyPeriod = 1 days;
        terms.reviewDeadline = DUE;
        termsId = keccak256(abi.encode(terms));
        uint256 publication = _evidence(
            app.cases.evidenceCommitment(termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, PROVIDER, termsId)
        );
        bytes32 providerAuthority = _subject(PROVIDER, funds.CREDIT_PROVIDER_ROLE());
        SparkV15ConcernIntake intake = app.cases.INTAKE();
        vm.prank(PROVIDER);
        intake.publishContacts(terms, publication, providerAuthority);
    }

    function _retainWageForTakeover(bytes32 formId, bytes32 obligation) private returns (bytes32 caseId) {
        bytes32 termsId = _publishWageTakeoverTerms(formId);
        address[] memory parties = new address[](2);
        parties[0] = PROVIDER;
        parties[1] = TUTOR;
        SparkV15ReviewContext.OriginalInput memory original = SparkV15ReviewContext.OriginalInput({
            termsId: termsId,
            concernRef: TAKEOVER_CONCERN,
            obligationId: obligation,
            paymentCommitment: app.payments.getObligation(obligation).commitment,
            decider: VERIFIER,
            decidedAt: uint64(block.timestamp),
            outcome: app.settlement.getGroupSettlement(LESSON).basis,
            parties: parties
        });
        caseId = app.cases.caseIdFor(LESSON, original.concernRef);
        uint256 proof = _evidence(app.cases.evidenceCommitment(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, COORDINATOR, keccak256(abi.encode(original))
        ));
        bytes32 authority = _subject(COORDINATOR, app.booking.COORDINATOR_ROLE());
        vm.prank(COORDINATOR);
        app.cases.retainOriginal(original, proof, authority);
    }

    function testInstalledOrdinaryCreditUsesTheSameReservedExpense() public {
        _checkOrdinaryCompensation(true);
    }

    function testInstalledOrdinaryCreditKeepsTheLegacyPathForAnOpaqueInventory() public {
        _checkOrdinaryCompensation(false);
    }

    function _checkOrdinaryCompensation(bool typedInventory) private {
        _install(false);
        require(funds.materialProvisions() == address(0), "material provisions installed");
        SparkV15FundingCases coverage = SparkV15FundingCases(funds.ordinaryBookingCoverage());
        require(coverage.BOOKING() == app.booking && coverage.PAYMENTS() == app.payments, "wrong ordinary coverage");
        if (!typedInventory) coverage = SparkV15FundingCases(address(0));
        bytes32 formId = _bookWithChangeTerms(_assessment(), BookingPath.Recorded, bytes32(0), coverage);
        _teachWithReports(formId, true, false);
        SparkV15CustomerRedress redress = _recordOrdinaryCompensation(formId);

        uint256 reserved = funds.reservedUnits();
        uint256 lessonHold = funds.lessonReserved(LESSON);
        uint256 feeBalance = funds.lessonFeeBalance(LESSON);
        uint256 cash = token.balanceOf(address(funds));
        if (typedInventory) require(coverage.independentTeachingCosts(LESSON) == 38, "wrong original expenses");
        redress.issueCourseCredit(formId);

        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == FEE, "customer lacks usable credit");
        require(funds.compensationCreditRemaining(LESSON, PLACE) == FEE, "wrong retained credit");
        require(funds.creditBalance(funds.creditAccount(PAYER)) == 0, "credit changed the original payer balance");
        require(funds.lessonFeeBalance(LESSON) == feeBalance, "credit spent original fees");
        require(token.balanceOf(address(funds)) == cash, "credit moved vault cash");
        if (typedInventory) {
            require(funds.reservedUnits() == reserved, "same-purpose course credit reserved twice");
            require(funds.lessonReserved(LESSON) == lessonHold - FEE, "wrong same-purpose lesson backing");
            require(coverage.independentTeachingCosts(LESSON) == 18, "independent refund or wage disappeared");
        } else {
            require(funds.reservedUnits() == reserved + FEE, "opaque inventory was treated as same-purpose backing");
            require(funds.lessonReserved(LESSON) == lessonHold, "opaque inventory reduced the lesson hold");
        }
    }

    function _recordOrdinaryCompensation(bytes32 formId) private returns (SparkV15CustomerRedress redress) {
        SparkV15LessonRemedies remedies = SparkV15LessonRemedies(address(app.settlement.remedyPolicy()));
        redress = remedies.customerRedress();
        bytes32 feedback = keccak256("student received some of the agreed session");
        bytes32 missed = keccak256("administrative error prevented some agreed instruction");
        SparkV15Booking.ServiceStatus status = SparkV15Booking.ServiceStatus.PartiallyDelivered;
        uint256 evidence = _evidence(app.booking.serviceFeedbackCommitment(formId, status, feedback, missed));
        vm.prank(STUDENT);
        app.booking.recordServiceFeedback(formId, status, feedback, missed, evidence);
        SparkV15LessonRemedies.FaultFinding memory finding;
        finding.kind = SparkV15LessonRemedies.FaultKind.ProviderAdministrationError;
        finding.groundRef = missed;
        finding.affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        finding.affected[0] = SparkV15LessonRemedies.AffectedPlace(
            formId, SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered,
            SparkV15LessonRemedies.Participation.AttendedAsAgreed, 10, true, feedback
        );
        bytes32 matter = keccak256("ordinary partial delivery due to a provider error");
        bytes32 noDispute = keccak256("verified undisputed provider error");
        evidence = _evidence(remedies.providerFaultCommitment(formId, matter, finding, noDispute, COORDINATOR));
        vm.prank(COORDINATOR);
        remedies.recordUndisputedProviderFault(formId, matter, finding, noDispute, evidence);
        SparkV15CustomerRedress.RedressTerms memory terms = SparkV15CustomerRedress.RedressTerms(
            END + 7 days, END + 14 days, 0, 3 days, 0, 1 days, missed, DOCUMENTS
        );
        evidence = _evidence(redress.redressTermsCommitment(formId, terms));
        vm.prank(PROVIDER);
        redress.publishRedressTerms(formId, terms, evidence);
        vm.prank(CUSTOMER);
        redress.acceptStandardCompensation(formId);
        require(redress.getRedress(formId).acceptedBy == CUSTOMER, "compensation never accepted");
    }

    function testBookingOpeningMustBelongToItsBookingAndCanOnlyBeBoundOnceByInstaller() public {
        SparkV15BookingOpening installedOpening = app.booking.OPENING();
        require(installedOpening.BOOKING() == app.booking, "wrong installed Opening");
        bytes32 coordinatorRole = app.booking.COORDINATOR_ROLE();
        bytes32 verifierRole = app.booking.VERIFIER_ROLE();
        vm.prank(ADMIN);
        SparkV15Booking other = new SparkV15Booking(
            app.requests,
            ISparkV15BookingFunds(address(funds)),
            SparkV15.WORKFLOW,
            coordinatorRole,
            verifierRole,
            PROVIDER
        );
        vm.expectRevert(SparkV15Settlement.InvalidSettlementInstallation.selector);
        new SparkV15Settlement(other, app.payments);
        SparkV15BookingOpening otherOpening = new SparkV15BookingOpening(
            other, new SparkV15BookingPrefunding(other), new SparkV15TeachingEnd(other), new SparkV15CourseNotices(other)
        );
        vm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        vm.prank(COORDINATOR);
        other.bindOpening(otherOpening);
        vm.expectRevert(SparkV15Booking.InvalidLesson.selector);
        vm.prank(ADMIN);
        other.bindOpening(installedOpening);
        vm.prank(ADMIN);
        other.bindOpening(otherOpening);
        require(other.OPENING() == otherOpening, "Opening not bound");
        SparkV15Settlement settlement = new SparkV15Settlement(other, app.payments);
        require(settlement.BOOKING() == other, "Settlement did not install against bound Booking");
        vm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        vm.prank(ADMIN);
        other.bindOpening(otherOpening);
    }

    function testInstalledOrdinaryOneToOneThroughTutorReceipt() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        bytes32 obligationId = _settle(formId, assessment);
        _approveAndPayWage(obligationId);
    }

    function testInstalledIndependentNoticesEnableNoStartAbsenceOnlyAfterBothActorsRecord() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        assessment.route = SparkV15Settlement.Route.OneToOneAbsence;
        assessment.seats[0].disposition = SparkV15Settlement.SeatDisposition.VerifiedAbsence;
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        SparkV15Booking booking = app.booking;
        SparkV15BookingOpening opening = booking.OPENING();
        SparkV15CourseNotices notices = opening.COURSE_NOTICES();
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        uint256 nextEvidence = registry.nextEvidenceId();
        bytes32 receipt = keccak256("actual deliveries to the two separately scoped channels");
        address[] memory present = new address[](1);
        present[0] = STUDENT;
        vm.warp(EPOCH + 5);
        SparkV15CourseNotices.SourceProof memory studentProof = _noticeProof(
            notices, booking.studentNoticeCommitment(formId, EPOCH + 2, receipt), COORDINATOR, false
        );
        vm.prank(COORDINATOR);
        uint256 studentId = notices.recordStudentNoticeWithConsent(formId, EPOCH + 2, receipt, studentProof);
        SparkV15Booking.StudentNotice memory studentNotice = booking.getStudentNotice(formId);
        require(
            studentNotice.evidenceId == studentId && studentId != 0 && studentNotice.sender == COORDINATOR
                && studentNotice.authorityId == _subject(COORDINATOR, booking.COORDINATOR_ROLE())
                && studentNotice.deliveredAt == EPOCH + 2 && studentNotice.recordedAt == EPOCH + 5,
            "wrong student notice provenance or times"
        );
        require(booking.getTutorNotice(LESSON).evidenceId == 0, "first notice created a tutor notice");
        require(
            opening.startPermission(LESSON, false, START, present) == SparkV15Booking.StartPermission.Unverified,
            "one notice made starting permissible"
        );
        require(registry.nextEvidenceId() == nextEvidence, "student proof registered in Core");

        SparkV15SettlementAlternatives alternatives = app.settlement.ALTERNATIVES();
        SparkV15SettlementAlternatives.AbsenceFacts memory facts = SparkV15SettlementAlternatives.AbsenceFacts(
            formId, START, keccak256("otherwise ready, no attendance and no good reason"), bytes32(0),
            SparkV15SettlementAlternatives.AbsenceReason.NoGoodReason
        );
        vm.warp(END + 1);
        uint256 absenceEvidence = _evidence(alternatives.absenceCommitment(facts, VERIFIER));
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(VERIFIER);
        alternatives.recordOneToOneAbsence(facts, absenceEvidence);
        require(alternatives.getOneToOneAbsence(formId).evidenceId == 0, "missing tutor notice produced absence");
        SparkV15CourseNotices.SourceProof memory tutorProof = _noticeProof(
            notices, booking.tutorNoticeCommitment(LESSON, TUTOR_CHANNEL, EPOCH + 3, receipt), PROVIDER, true
        );
        vm.prank(PROVIDER);
        uint256 tutorId = notices.recordTutorNoticeWithConsent(LESSON, TUTOR_CHANNEL, EPOCH + 3, receipt, tutorProof);
        SparkV15Booking.TutorNotice memory tutorNotice = booking.getTutorNotice(LESSON);
        require(
            tutorNotice.evidenceId == tutorId && tutorId != studentId && tutorNotice.sender == PROVIDER
                && tutorNotice.channelRef == TUTOR_CHANNEL && tutorNotice.deliveredAt == EPOCH + 3
                && tutorNotice.recordedAt == END + 1,
            "wrong independent tutor notice provenance or times"
        );
        require(registry.nextEvidenceId() == absenceEvidence + 1, "tutor proof registered in Core");
        require(
            opening.startPermission(LESSON, false, START, present) == SparkV15Booking.StartPermission.Permitted,
            "two notices did not meet historic start conditions"
        );

        vm.prank(VERIFIER);
        alternatives.recordOneToOneAbsence(facts, absenceEvidence);
        SparkV15SettlementAlternatives.AbsenceRecord memory absence = alternatives.getOneToOneAbsence(formId);
        require(
            absence.evidenceId == absenceEvidence && absence.verifiedBy == VERIFIER && absence.verifiedAt == END + 1,
            "absence was not separately verified"
        );
        _settleNoticeAbsence(formId, assessment, studentId);
    }

    function _settleNoticeAbsence(
        bytes32 formId,
        SparkV15Settlement.GroupAssessment memory assessment,
        uint256 studentNoticeId
    ) private {
        SparkV15Settlement settlement = app.settlement;
        bytes32 proposal = settlement.proposalCommitment(LESSON, assessment);
        vm.prank(COORDINATOR);
        settlement.proposeOrdinaryGroup(LESSON, proposal);
        SparkV15Settlement.GroupPreview memory preview = settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        uint256 approvalEvidence = _evidence(preview.basis);
        uint256[] memory paymentEvidence = new uint256[](preview.payments.length);
        for (uint256 i; i < paymentEvidence.length; ++i) {
            paymentEvidence[i] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[i], preview.basis));
        }
        vm.prank(VERIFIER);
        settlement.approveOrdinaryGroup(LESSON, assessment, approvalEvidence, paymentEvidence);
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, formId);
        require(app.booking.getTeaching(LESSON).startedAt == 0 && seat.debited == 20, "absence invented teaching");
        require(seat.feeDue == 10 && seat.refundDue == 10 && seat.tutorPay == 4, "wrong absence amounts");
        require(seat.noticeEvidenceId == studentNoticeId, "settlement lost the original schedule notice");
    }

    function testInstalledIndependentCourseNoticesPreserveNormalTeachingAndActualWage() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        SparkV15Booking booking = app.booking;
        SparkV15CourseNotices notices = booking.OPENING().COURSE_NOTICES();
        bytes32 receipt = keccak256("delivered to the agreed channels");
        vm.warp(EPOCH + 5);
        SparkV15CourseNotices.SourceProof memory studentProof = _noticeProof(
            notices, booking.studentNoticeCommitment(formId, EPOCH + 2, receipt), COORDINATOR, false
        );
        vm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        vm.prank(STUDENT);
        notices.recordStudentNoticeWithConsent(formId, EPOCH + 2, receipt, studentProof);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(COORDINATOR);
        notices.recordTutorNoticeWithConsent(LESSON, TUTOR_CHANNEL, EPOCH + 2, receipt, studentProof);

        vm.prank(COORDINATOR);
        uint256 studentId = notices.recordStudentNoticeWithConsent(formId, EPOCH + 2, receipt, studentProof);
        SparkV15CourseNotices.SourceProof memory tutorProof = _noticeProof(
            notices, booking.tutorNoticeCommitment(LESSON, TUTOR_CHANNEL, EPOCH + 3, receipt), PROVIDER, true
        );
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(COORDINATOR);
        notices.recordTutorNoticeWithConsent(LESSON, TUTOR_CHANNEL, EPOCH + 3, receipt, tutorProof);
        vm.prank(PROVIDER);
        notices.recordTutorNoticeWithConsent(LESSON, TUTOR_CHANNEL, EPOCH + 3, receipt, tutorProof);
        vm.expectRevert(SparkV15Booking.InvalidNotice.selector);
        vm.prank(COORDINATOR);
        booking.recordStudentNotice(formId, EPOCH + 2, receipt, 1);

        _observeActualStart();
        _finishTeaching(formId, true, true);
        _approveAndPayWage(_settle(formId, assessment));
        require(
            app.settlement.getSeatSettlement(LESSON, formId).noticeEvidenceId == studentId,
            "normal settlement lost the original notice"
        );
    }

    function testInstalledLateVerificationOfTimelyOpeningNoticeSupportsOrdinarySettlement() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _openBeforeStudentNoticeVerification(bytes32(0));

        vm.warp(END + 2);
        SparkV15TeachingEnd teachingEnd = app.booking.OPENING().TEACHING_END();
        SparkV15SettlementOccurrences occurrences = app.settlement.ALTERNATIVES().OCCURRENCES();
        require(!occurrences.hasUsableLateOpeningNotices(LESSON), "missing proof already usable");
        bytes32 end = keccak256("witnessed actual teaching end");
        SparkV15TeachingEnd.Proof memory proof = _teachingEndProof(teachingEnd, end, VERIFIER, END + 5);
        vm.expectRevert(SparkV15Booking.InvalidTeaching.selector);
        vm.prank(VERIFIER);
        teachingEnd.recordOrdinaryTeachingEnded(LESSON, END, end, proof);

        uint256 noticeId = _verifyLateStudentNotice(formId, START - 12);
        SparkV15Booking.StudentNotice memory notice = app.booking.getStudentNotice(formId);
        require(notice.deliveredAt == START - 12 && notice.recordedAt == END + 2, "lost distinct notice times");
        require(occurrences.hasUsableLateOpeningNotices(LESSON), "late verification unavailable to settlement");
        vm.prank(VERIFIER);
        teachingEnd.recordOrdinaryTeachingEnded(LESSON, END, end, proof);

        SparkV15Booking.Teaching memory teaching = app.booking.getTeaching(LESSON);
        require(teaching.startedAt == START && teaching.startRecordedAt == START, "opening history changed");
        require(teaching.startPermission == SparkV15Booking.StartPermission.Unverified, "original judgement rewritten");
        require(teaching.endedAt == END && teaching.endRecordedAt == END + 2, "lost distinct end times");

        vm.warp(END + 3);
        _recordAdoptedTutorCompletion();
        require(app.booking.getTutorDelivery(LESSON).reportedAt == END + 3, "tutor completion not recorded");
        require(!app.settlement.getGroupSettlement(LESSON).complete, "tutor report settled the lesson");
        _approveAndPayWage(_settle(formId, assessment));
        require(app.settlement.getSeatSettlement(LESSON, formId).noticeEvidenceId == noticeId, "late evidence lost");
    }

    function testInstalledActuallyLateOpeningNoticeCannotSupportOrdinarySettlement() public {
        _requireLateNoticeDoesNotSettle(START + 1, bytes32(0));
    }

    function testInstalledLateVerificationDoesNotReverseAnExpressOpeningFinding() public {
        _requireLateNoticeDoesNotSettle(START - 12, keccak256("independent finding that opening conditions were not met"));
    }

    function _requireLateNoticeDoesNotSettle(uint64 deliveredAt, bytes32 conflict) private {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _openBeforeStudentNoticeVerification(conflict);
        vm.warp(START + 2);
        _verifyLateStudentNotice(formId, deliveredAt);
        _finishTeaching(formId, true, true);

        SparkV15Settlement settlement = app.settlement;
        bytes32 proposal = settlement.proposalCommitment(LESSON, assessment);
        vm.prank(COORDINATOR);
        settlement.proposeOrdinaryGroup(LESSON, proposal);
        uint256[] memory wageEvidence = new uint256[](0);
        vm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        vm.prank(VERIFIER);
        settlement.approveOrdinaryGroup(LESSON, assessment, 0, wageEvidence);
        SparkV15Booking.Teaching memory teaching = app.booking.getTeaching(LESSON);
        require(teaching.startedAt == START && teaching.endedAt == END, "actual occurrence lost");
        require(teaching.unmetConditionRef == conflict, "original finding overwritten");
        require(!app.settlement.getGroupSettlement(LESSON).complete && token.balanceOf(TUTOR) == 0, "rejected route paid");
    }

    function testInstalledRevokedLateOpeningNoticeBlocksSettlementButKeepsPriorCompletion() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _openBeforeStudentNoticeVerification(bytes32(0));
        vm.warp(START + 2);
        SparkV15Booking booking = app.booking;
        uint64 deliveredAt = START - 12;
        bytes32 receipt = keccak256("independently registered receipt of timely student notice");
        uint256 noticeId = _evidence(booking.studentNoticeCommitment(formId, deliveredAt, receipt));
        vm.prank(COORDINATOR);
        booking.recordStudentNotice(formId, deliveredAt, receipt, noticeId);
        _finishTeaching(formId, true, true);
        (uint256 approvalEvidence, uint256[] memory wageEvidence) = _prepareApprovalEvidence(formId, assessment);

        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        bytes32 authority = _subject(SOURCE, role);
        _allowSourceEvidenceLifecycle();
        vm.prank(SOURCE);
        registry.recordEvidenceLifecycle(
            noticeId, role, authority, AVACoreTypes.EvidenceLifecycleKind.Revoke, 0,
            keccak256("independent recall of student notice proof"), ""
        );

        require(!app.settlement.ALTERNATIVES().OCCURRENCES().hasUsableLateOpeningNotices(LESSON), "recalled proof still usable");
        vm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, approvalEvidence, wageEvidence);
        require(app.booking.getStudentNotice(formId).evidenceId == noticeId, "revocation erased notice history");
        require(app.booking.getTutorDelivery(LESSON).completed, "revocation erased the tutor report");
        require(app.booking.getTeaching(LESSON).endedAt == END, "revocation erased the actual end");
    }

    function _openBeforeStudentNoticeVerification(bytes32 conflict) private {
        vm.warp(START - 5);
        bytes32 receipt = keccak256("timely delivery to the tutor on the agreed channel");
        uint64 deliveredAt = START - 12;
        uint256 evidenceId = _evidence(app.booking.tutorNoticeCommitment(LESSON, TUTOR_CHANNEL, deliveredAt, receipt));
        vm.prank(PROVIDER);
        app.booking.recordTutorNotice(LESSON, TUTOR_CHANNEL, deliveredAt, receipt, evidenceId);

        vm.warp(START);
        _recordAdoptedStart(_startObservation(conflict));
        SparkV15Booking.Teaching memory teaching = app.booking.getTeaching(LESSON);
        SparkV15Booking.StartPermission expected = conflict == bytes32(0)
            ? SparkV15Booking.StartPermission.Unverified : SparkV15Booking.StartPermission.RequirementsNotMet;
        require(teaching.startPermission == expected, "wrong original opening judgement");
        require(teaching.startedAt == START && teaching.startEvidenceId != 0, "actual opening was not recorded");
    }

    function _verifyLateStudentNotice(bytes32 formId, uint64 deliveredAt) private returns (uint256 evidenceId) {
        SparkV15Booking booking = app.booking;
        SparkV15CourseNotices notices = booking.OPENING().COURSE_NOTICES();
        bytes32 receipt = keccak256("independently inspected student notice receipt");
        SparkV15CourseNotices.SourceProof memory proof = _noticeProof(
            notices, booking.studentNoticeCommitment(formId, deliveredAt, receipt), COORDINATOR, false
        );
        vm.prank(COORDINATOR);
        evidenceId = notices.recordStudentNoticeWithConsent(formId, deliveredAt, receipt, proof);
    }

    function _recordAdoptedTutorCompletion() private {
        SparkV15ServiceReports reports = app.booking.OPENING().SERVICE_REPORTS();
        bytes32 details = keccak256("tutor reports actual completion of the agreed teaching");
        bytes32 sourceRole = app.applicationModule.SOURCE_ROLE();
        SparkV15ServiceReports.SourceProof memory proof = SparkV15ServiceReports.SourceProof(
            sourceRole, _subject(SOURCE, sourceRole), app.disclosurePolicyId, END + 10, 0, 0
        );
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(SOURCE_KEY, reports.tutorDeliveryDigest(LESSON, details, proof));
        proof.r = r;
        proof.vs = bytes32(uint256(s) | ((uint256(v) - 27) << 255));
        vm.prank(TUTOR);
        reports.recordCompletedTutorDelivery(LESSON, details, proof);
    }

    function testInstalledCourseNoticeLifecycleSeparatesCoreAndAdoptedProofsFromDeliveryHistory() public {
        bytes32 formId = _book(_assessment());
        SparkV15Booking booking = app.booking;
        SparkV15CourseNotices notices = booking.OPENING().COURSE_NOTICES();
        bytes32 receipt = keccak256("delivered with independently checkable evidence");
        vm.warp(EPOCH + 5);
        SparkV15CourseNotices.SourceProof memory studentProof = _noticeProof(
            notices, booking.studentNoticeCommitment(formId, EPOCH + 2, receipt), COORDINATOR, false
        );
        vm.prank(COORDINATOR);
        uint256 studentId = notices.recordStudentNoticeWithConsent(formId, EPOCH + 2, receipt, studentProof);
        uint256 tutorId = _evidence(booking.tutorNoticeCommitment(LESSON, TUTOR_CHANNEL, EPOCH + 3, receipt));
        vm.prank(PROVIDER);
        booking.recordTutorNotice(LESSON, TUTOR_CHANNEL, EPOCH + 3, receipt, tutorId);
        (uint256 localTutorId,,) = notices.getAdoptedNoticeEvidence(SparkV15CourseNotices.NoticeKind.Tutor, LESSON);
        require(localTutorId == 0, "Core tutor proof was reclassified");
        bytes32 reason = keccak256("independent evidence check found unavailable proof");
        SparkV15CourseNotices.NoticeKind kind = SparkV15CourseNotices.NoticeKind.Student;
        AVACoreTypes.EvidenceLifecycleKind expire = AVACoreTypes.EvidenceLifecycleKind.Expire;
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(SOURCE);
        notices.recordNoticeEvidenceLifecycle(
            kind, formId, studentProof.sourceRole, studentProof.sourceAuthorityId, expire, 0, reason
        );
        _allowSourceEvidenceLifecycle();
        vm.prank(SOURCE);
        notices.recordNoticeEvidenceLifecycle(
            kind, formId, studentProof.sourceRole, studentProof.sourceAuthorityId, expire, 0, reason
        );
        (uint256 original, AVACoreTypes.EvidenceStatus status,) = notices.getAdoptedNoticeEvidence(kind, formId);
        require(original == studentId && status == AVACoreTypes.EvidenceStatus.Expired, "lost adopted status");
        uint256 packageId = app.packageId;
        vm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        notices.requireStudentNoticeEvidence(formId, studentId, packageId);
        notices.requireTutorNoticeEvidence(LESSON, tutorId, packageId);

        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        vm.prank(SOURCE);
        registry.recordEvidenceLifecycle(
            tutorId, studentProof.sourceRole, studentProof.sourceAuthorityId,
            AVACoreTypes.EvidenceLifecycleKind.Revoke, 0, reason, ""
        );
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        notices.requireTutorNoticeEvidence(LESSON, tutorId, packageId);
        require(booking.getStudentNotice(formId).deliveredAt == EPOCH + 2, "student history rewritten");
        require(booking.getTutorNotice(LESSON).deliveredAt == EPOCH + 3, "tutor history rewritten");
    }

    function _noticeProof(SparkV15CourseNotices notices, bytes32 commitment, address actor, bool tutor)
        private
        view
        returns (SparkV15CourseNotices.SourceProof memory proof)
    {
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        proof = SparkV15CourseNotices.SourceProof(role, _subject(SOURCE, role), app.disclosurePolicyId, END + 10, 0, 0);
        bytes32 schema = tutor
            ? keccak256("TutorNoticeEvidence(bytes32 commitment,uint256 packageId,address actor,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)")
            : keccak256("StudentNoticeEvidence(bytes32 commitment,uint256 packageId,address actor,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)");
        bytes32 message = keccak256(abi.encode(
            schema, commitment, app.packageId, actor, role, proof.sourceAuthorityId, proof.disclosurePolicyId, proof.validThrough
        ));
        (proof.r, proof.vs) = _signEvidenceMessage("Spark DAO Course Notice Evidence", address(notices), message, SOURCE_KEY);
    }

    function testOrdinaryPrefundingProofFirstUsedAtReserveAndChargesOriginalPayer() public {
        uint256 nextEvidenceId = app.kernel.EVIDENCE_REGISTRY().nextEvidenceId();
        (bytes32 formId, uint256 funding, SparkV15Funds.RechargeDebit[] memory debits) = _adoptPrefundedDraft(DraftBasis.AdoptedWithAmountControl);
        require(app.kernel.EVIDENCE_REGISTRY().nextEvidenceId() == nextEvidenceId, "prefunding registered in Core");

        SparkV15Booking.FundingCheck memory check = app.booking.getLesson(LESSON).prefunding;
        require(
            check.evidenceId == funding && check.checkedAt == EPOCH && check.reservedUnits == LESSON_BACKING
                && check.verifier == VERIFIER && check.authorityId == _subject(VERIFIER, app.booking.VERIFIER_ROLE()),
            "wrong funded scope or effective point"
        );
        (uint256 evidenceId, bytes32 sourceAuthorityId, uint256 disclosurePolicyId,
            AVACoreTypes.EvidenceStatus status,) = _prefundingModule().getAdoptedEvidence(LESSON);
        require(
            evidenceId == funding && sourceAuthorityId == _subject(SOURCE, app.applicationModule.SOURCE_ROLE())
                && disclosurePolicyId == app.disclosurePolicyId && status == AVACoreTypes.EvidenceStatus.Active,
            "missing independently adopted proof"
        );
        require(funds.lessonReserved(LESSON) == LESSON_BACKING, "prefunding is not held in the existing pool");
        require(funds.lessonFeeBalance(LESSON) == 0 && app.booking.getConfirmedForms(LESSON).length == 0, "premature commitment");
        vm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
        vm.prank(TUTOR);
        app.booking.signTeachingAgreement(LESSON);

        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        vm.warp(EPOCH + 2);
        _confirmWithAcceptances(formId, funding, debits, false);
        require(funds.creditBalance(funds.creditAccount(PAYER)) == 0, "original payer was not charged");
        require(funds.lessonFeeBalance(LESSON) == FEE, "wrong charge");
    }

    function testOrdinaryPrefundingLegacyDraftRetainsRegisteredBasisAndChargesOriginalPayer() public {
        (bytes32 formId, uint256 funding, SparkV15Funds.RechargeDebit[] memory debits) =
            _adoptPrefundedDraft(DraftBasis.Registered);
        (uint256 adopted,,,,) = _prefundingModule().getAdoptedEvidence(LESSON);
        require(adopted == 0 && app.booking.getLesson(LESSON).prefunding.evidenceId == funding, "wrong proof origin");
        require(funds.lessonReserved(LESSON) == LESSON_BACKING, "registered backing was not held");
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        vm.warp(EPOCH + 2);
        _confirmWithAcceptances(formId, funding, debits, false);
        require(funds.creditBalance(funds.creditAccount(PAYER)) == 0, "registered flow charged the wrong account");
    }

    function testRegisteredPrefundingRevocationBlocksNewCommitmentsAndPreservesTheReserve() public {
        (bytes32 formId, uint256 funding,) = _adoptPrefundedDraft(DraftBasis.Registered);
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        vm.prank(PROVIDER);
        app.booking.signTeachingAgreement(LESSON);
        vm.prank(TUTOR);
        app.booking.signTeachingAgreement(LESSON);
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        bytes32 role = app.booking.VERIFIER_ROLE();
        _allowEvidenceLifecycle(role);
        bytes32 authority = _subject(REVIEWER, role);
        vm.prank(REVIEWER);
        registry.recordEvidenceLifecycle(
            funding, role, authority, AVACoreTypes.EvidenceLifecycleKind.Revoke, 0,
            keccak256("review withdrew the registered funding proof"), ""
        );

        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(TUTOR);
        app.booking.acceptForm(formId, SparkV15Booking.Acceptance.Tutor);
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(CUSTOMER);
        app.booking.acceptForm(formId, SparkV15Booking.Acceptance.Customer);
        require(app.booking.getLesson(LESSON).prefunding.evidenceId == funding, "registered reference changed");
        require(app.booking.teachingAgreementSignedAt(LESSON, TUTOR) == EPOCH, "earlier teaching terms changed");
        require(!app.booking.getForm(formId).hasAcceptance, "failed commitment was recorded");
        require(funds.lessonReserved(LESSON) == LESSON_BACKING, "withdrawing proof released the reserve");
        require(funds.creditBalance(funds.creditAccount(PAYER)) == FEE, "payer credit changed");
    }

    function testRegisteredPrefundingReleaseBlocksConfirmationAndPreservesExistingAssents() public {
        (bytes32 formId, uint256 funding, SparkV15Funds.RechargeDebit[] memory debits) =
            _adoptPrefundedDraft(DraftBasis.Registered);
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        vm.prank(PROVIDER);
        app.booking.signTeachingAgreement(LESSON);
        vm.prank(TUTOR);
        app.booking.signTeachingAgreement(LESSON);
        _accept(formId, SparkV15Booking.Acceptance.Provider, PROVIDER);
        _accept(formId, SparkV15Booking.Acceptance.Tutor, TUTOR);
        _accept(formId, SparkV15Booking.Acceptance.Customer, CUSTOMER);
        _accept(formId, SparkV15Booking.Acceptance.Payer, PAYER);

        SparkV15ServiceReserve release = SparkV15MaterialProvisions(funds.materialProvisions()).SERVICE_RESERVE();
        bytes32 releaseRef = keccak256("verified provision released from the unconfirmed place");
        uint256 evidence = _evidence(release.releaseEvidenceCommitment(LESSON, 1, releaseRef, VERIFIER));
        bytes32 authority = _subject(VERIFIER, app.booking.VERIFIER_ROLE());
        vm.prank(VERIFIER);
        release.releaseBudget(LESSON, 1, releaseRef, evidence, authority);
        require(funds.lessonReserved(LESSON) == LESSON_BACKING - 1, "lesson backing was not reduced");
        require(app.kernel.EVIDENCE_REGISTRY().isEvidenceAvailableForPackage(funding, app.packageId), "proof changed");

        vm.expectRevert(SparkV15Booking.InvalidPrefunding.selector);
        vm.prank(COORDINATOR);
        app.booking.confirmPlace(formId, bytes32(0), 0, debits);
        (address tutor, uint64 acceptedAt) = app.booking.acceptances(formId, SparkV15Booking.Acceptance.Tutor);
        require(tutor == TUTOR && acceptedAt == EPOCH, "the original assent changed");
        require(app.booking.getForm(formId).confirmation.confirmedAt == 0, "place was confirmed");
        require(funds.creditBalance(funds.creditAccount(PAYER)) == FEE && funds.lessonFeeBalance(LESSON) == 0, "fee moved");
        require(token.balanceOf(address(funds)) == 200, "vault cash changed");
    }

    function testOrdinaryPrefundingInventoryConstrainsActualAuthorisedReserveRelease() public {
        (bytes32 formId,,) = _adoptPrefundedDraft(DraftBasis.AdoptedInventory);
        SparkV15FundingCases cases = SparkV15FundingCases(funds.materialBookingCoverage());
        SparkV15ServiceReserve release = SparkV15MaterialProvisions(funds.materialProvisions()).SERVICE_RESERVE();
        SparkV15FundingCases.FundingScenario[] memory scenarios = _ordinaryRefundScenario(formId);
        require(release.releasableProviderHold(LESSON) == LESSON_BACKING, "unexpected recorded inventory");
        scenarios[0].expenses[0].units = FEE - 1;
        vm.expectRevert(SparkV15FundingCases.InvalidFundingInventory.selector);
        cases.retainInventory(LESSON, scenarios);
        scenarios[0].expenses[0].units = FEE;
        cases.retainInventory(LESSON, scenarios);
        uint128 idle = LESSON_BACKING - FEE;
        require(cases.hasInventory(LESSON) && release.releasableProviderHold(LESSON) == idle, "refund not protected");

        bytes32 releaseRef = keccak256("verified provider backing idle outside the retained refund");
        bytes32 authority = _subject(VERIFIER, app.booking.VERIFIER_ROLE());
        uint256 tooMuch = _evidence(release.releaseEvidenceCommitment(LESSON, idle + 1, releaseRef, VERIFIER));
        vm.expectRevert(SparkV15ServiceReserve.InvalidReserveOperation.selector);
        vm.prank(VERIFIER);
        release.releaseBudget(LESSON, idle + 1, releaseRef, tooMuch, authority);
        require(funds.lessonReserved(LESSON) == LESSON_BACKING, "refused release reduced the hold");
        uint256 allowed = _evidence(release.releaseEvidenceCommitment(LESSON, idle, releaseRef, VERIFIER));
        vm.prank(VERIFIER);
        release.releaseBudget(LESSON, idle, releaseRef, allowed, authority);
        require(funds.lessonReserved(LESSON) == FEE && funds.reservedUnits() == FEE * 2, "wrong actual reserve release");
        require(token.balanceOf(address(funds)) == 200 && funds.lessonFeeBalance(LESSON) == 0, "release moved cash or fees");
    }

    function testInstalledStandaloneTermsLifecycleControlsLaterOriginalPayerDebit() public {
        (bytes32 formId,, SparkV15Funds.RechargeDebit[] memory debits) = _adoptPrefundedDraft(DraftBasis.Registered);
        _provideTerms(formId, CUSTOMER);
        SparkV15Booking booking = app.booking;
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        uint256 nextEvidence = registry.nextEvidenceId();
        vm.warp(EPOCH + 1);
        SparkV15Booking.TermsProvisionConsent memory consent = _signedTermsDelivery(formId, TUTOR);
        vm.prank(COORDINATOR);
        booking.recordTermsProvisionWithConsent(formId, TUTOR, DOCUMENTS, consent);
        require(registry.nextEvidenceId() == nextEvidence && booking.termsProvisionEvidence(formId, TUTOR) == 0,
            "signed delivery registered a Core receipt");

        vm.warp(EPOCH + 2);
        vm.prank(PROVIDER);
        booking.signTeachingAgreement(LESSON);
        vm.prank(TUTOR);
        booking.signTeachingAgreement(LESSON);
        _accept(formId, SparkV15Booking.Acceptance.Provider, PROVIDER);
        _accept(formId, SparkV15Booking.Acceptance.Tutor, TUTOR);
        _accept(formId, SparkV15Booking.Acceptance.Customer, CUSTOMER);
        _accept(formId, SparkV15Booking.Acceptance.Payer, PAYER);

        SparkV15BookingPrefunding prefunding = booking.PREFUNDING();
        bytes32 reason = keccak256("review of the exact delivered terms evidence");
        AVACoreTypes.EvidenceLifecycleKind revoke = AVACoreTypes.EvidenceLifecycleKind.Revoke;
        AVACoreTypes.EvidenceLifecycleKind supersede = AVACoreTypes.EvidenceLifecycleKind.Supersede;
        vm.warp(EPOCH + 3);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(SOURCE);
        prefunding.recordTermsEvidenceLifecycle(formId, TUTOR, consent.sourceRole, consent.sourceAuthorityId, revoke, 0, reason);

        bytes32 lifecycleRole = booking.VERIFIER_ROLE();
        _allowEvidenceLifecycle(lifecycleRole);
        bytes32 lifecycleAuthority = _subject(VERIFIER, lifecycleRole);
        uint256 beforeReview = vm.snapshotState();
        vm.prank(VERIFIER);
        prefunding.recordTermsEvidenceLifecycle(formId, TUTOR, lifecycleRole, lifecycleAuthority, revoke, 0, reason);
        require(prefunding.getStandaloneTermsEvidence(formId, TUTOR).lifecycleStatus == AVACoreTypes.EvidenceStatus.Revoked,
            "signed receipt did not retain its withdrawal");
        require(booking.hasTermsProvision(formId, TUTOR) && !booking.OPENING().hasUsableTermsProvision(formId, TUTOR, app.packageId),
            "withdrawal changed recorded history or left the receipt usable");
        vm.expectRevert(SparkV15Booking.InvalidConfirmation.selector);
        vm.prank(COORDINATOR);
        booking.confirmPlace(formId, bytes32(0), 0, debits);
        (address signer, uint64 acceptedAt) = booking.acceptances(formId, SparkV15Booking.Acceptance.Tutor);
        require(signer == TUTOR && acceptedAt == EPOCH + 2, "withdrawal erased valid earlier assent");
        require(booking.teachingAgreementSignedAt(LESSON, TUTOR) == EPOCH + 2, "withdrawal erased teaching agreement");
        require(funds.creditBalance(funds.creditAccount(PAYER)) == FEE && funds.lessonReserved(LESSON) == LESSON_BACKING,
            "failed confirmation altered payer credit or reservation");
        require(vm.revertToState(beforeReview));

        bytes32 evidenceType = keccak256("spark.v1.5.booking.receipt");
        uint256 otherRecipient = _registeredEvidence(booking.provisionCommitment(formId, CUSTOMER, DOCUMENTS), evidenceType);
        vm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        vm.prank(VERIFIER);
        prefunding.recordTermsEvidenceLifecycle(
            formId, TUTOR, lifecycleRole, lifecycleAuthority, supersede, otherRecipient, reason
        );
        bytes32 original = booking.provisionCommitment(formId, TUTOR, DOCUMENTS);
        uint256 replacement = _registeredEvidence(original, evidenceType);
        vm.prank(VERIFIER);
        prefunding.recordTermsEvidenceLifecycle(
            formId, TUTOR, lifecycleRole, lifecycleAuthority, supersede, replacement, reason
        );
        vm.warp(EPOCH + 4);
        uint256 laterReplacement = _registeredEvidence(original, evidenceType);
        vm.prank(VERIFIER);
        registry.recordEvidenceLifecycle(replacement, lifecycleRole, lifecycleAuthority, supersede, laterReplacement, reason, "");
        require(booking.OPENING().hasUsableTermsProvision(formId, TUTOR, app.packageId), "compatible successor not usable");
        vm.prank(COORDINATOR);
        booking.confirmPlace(formId, bytes32(0), 0, debits);
        require(funds.creditBalance(funds.creditAccount(PAYER)) == 0 && funds.lessonFeeBalance(LESSON) == FEE,
            "compatible delivery did not charge the original payer");
        SparkV15BookingPrefunding.AdoptedEvidence memory receipt = prefunding.getStandaloneTermsEvidence(formId, TUTOR);
        require(receipt.commitment == original && receipt.replacementCoreEvidenceId == replacement
            && receipt.lifecycleStatus == AVACoreTypes.EvidenceStatus.Superseded,
            "linking new receipts overwrote the original delivery");
    }

    function _signedTermsDelivery(bytes32 formId, address recipient)
        private
        view
        returns (SparkV15Booking.TermsProvisionConsent memory consent)
    {
        consent.sourceRole = app.applicationModule.SOURCE_ROLE();
        consent.sourceAuthorityId = _subject(SOURCE, consent.sourceRole);
        consent.disclosurePolicyId = app.disclosurePolicyId;
        bytes32 schema = keccak256(
            "TermsProvisionConsent(uint256 packageId,bytes32 formId,address recipient,bytes32 deliveryRef,address coordinator,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId)"
        );
        bytes32 message = keccak256(abi.encode(
            schema, app.packageId, formId, recipient, DOCUMENTS, COORDINATOR, consent.sourceRole,
            consent.sourceAuthorityId, consent.disclosurePolicyId
        ));
        (consent.r, consent.vs) = _signEvidenceMessage("Spark DAO Terms Delivery", address(app.booking), message, SOURCE_KEY);
    }

    function testOrdinaryPrefundingProofRevocationPreservesHoldAndBlocksUnformedCommitments() public {
        (bytes32 formId, uint256 funding, SparkV15Funds.RechargeDebit[] memory debits) = _adoptPrefundedDraft(DraftBasis.Adopted);
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        _invalidatePrefunding(AVACoreTypes.EvidenceLifecycleKind.Revoke, 0);

        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(TUTOR);
        app.booking.signTeachingAgreement(LESSON);
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(CUSTOMER);
        app.booking.acceptForm(formId, SparkV15Booking.Acceptance.Customer);
        bytes memory assents = bytes.concat(
            _signBookingConsent(formId, funding, 0, PROVIDER_KEY, false),
            _signBookingConsent(formId, funding, 1, TUTOR_KEY, false),
            _signBookingConsent(formId, funding, 2, CUSTOMER_KEY, false),
            _signBookingConsent(formId, funding, 3, PAYER_KEY, false)
        );
        bytes memory agreements = bytes.concat(
            _signBookingConsent(formId, funding, 0, PROVIDER_KEY, true),
            _signBookingConsent(formId, funding, 1, TUTOR_KEY, true)
        );
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(COORDINATOR);
        app.booking.confirmOrdinaryPlaceWithAcceptances(formId, debits, assents, agreements);
        require(app.booking.getLesson(LESSON).prefunding.evidenceId == funding, "original funding reference was erased");
        require(funds.lessonReserved(LESSON) == LESSON_BACKING && funds.lessonFeeBalance(LESSON) == 0, "hold changed");
        require(funds.creditBalance(funds.creditAccount(PAYER)) == FEE, "failed actions debited the payer");
    }

    function testOrdinaryPrefundingSupersessionDoesNotChargeUnderPreviouslyRecordedAssents() public {
        (bytes32 formId, uint256 funding, SparkV15Funds.RechargeDebit[] memory debits) = _adoptPrefundedDraft(DraftBasis.Adopted);
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);
        vm.prank(PROVIDER);
        app.booking.signTeachingAgreement(LESSON);
        vm.prank(TUTOR);
        app.booking.signTeachingAgreement(LESSON);
        _accept(formId, SparkV15Booking.Acceptance.Provider, PROVIDER);
        _accept(formId, SparkV15Booking.Acceptance.Tutor, TUTOR);
        _accept(formId, SparkV15Booking.Acceptance.Customer, CUSTOMER);
        _accept(formId, SparkV15Booking.Acceptance.Payer, PAYER);
        uint256 replacement = _registeredEvidence(
            keccak256("updated inventory evidence"),
            keccak256("spark.v1.5.booking.verified-prefunding")
        );
        _invalidatePrefunding(AVACoreTypes.EvidenceLifecycleKind.Supersede, replacement);

        (uint256 evidenceId,,, AVACoreTypes.EvidenceStatus status, uint256 replacementId) =
            _prefundingModule().getAdoptedEvidence(LESSON);
        require(
            evidenceId == funding && status == AVACoreTypes.EvidenceStatus.Superseded && replacementId == replacement,
            "missing original and replacement linkage"
        );
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(COORDINATOR);
        app.booking.confirmPlace(formId, bytes32(0), 0, debits);
        (address signer,) = app.booking.acceptances(formId, SparkV15Booking.Acceptance.Payer);
        require(signer == PAYER && funds.creditBalance(funds.creditAccount(PAYER)) == FEE, "recorded assent or balance changed");
        require(app.booking.getConfirmedForms(LESSON).length == 0, "superseding proof silently confirmed the booking");
    }

    function testIndependentFullServiceFeedbackFirstUsesSourceProofAndKeepsReceiptScope() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teachWithReports(formId, true, false);
        SparkV15ServiceReports reports = app.booking.OPENING().SERVICE_REPORTS();
        bytes32 received = keccak256("complete agreed service");
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        uint256 nextEvidence = registry.nextEvidenceId();
        uint64 adoptedAt = END + 2;
        vm.warp(adoptedAt);
        SparkV15ServiceReports.SourceProof memory proof = _fullServiceProof(reports, formId, received, adoptedAt + 1);
        vm.prank(STUDENT);
        uint256 evidenceId = reports.recordFullServiceFeedback(formId, received, proof);

        require(registry.nextEvidenceId() == nextEvidence, "feedback unexpectedly registered in Core");
        SparkV15Booking.ServiceFeedback memory feedback = app.booking.getServiceFeedback(formId);
        require(feedback.status == SparkV15Booking.ServiceStatus.FullyDelivered, "feedback not yet effective");
        require(feedback.reportedAt == adoptedAt && feedback.receivedRef == received, "incorrect report history");
        require(feedback.evidenceId == evidenceId && evidenceId != 0, "incorrect scoped reference");
        require(!app.settlement.getGroupSettlement(LESSON).complete, "report itself settled the lesson");

        SparkV15Booking booking = app.booking;
        vm.expectRevert(SparkV15Booking.InvalidReport.selector);
        vm.prank(STUDENT);
        booking.recordServiceFeedback(formId, SparkV15Booking.ServiceStatus.FullyDelivered, received, 0, nextEvidence);
        vm.warp(adoptedAt + 2); // The Source authorisation to adopt has expired. The adopted report remains effective.
        _approveAndPayWage(_settle(formId, assessment));
        require(app.settlement.getSeatSettlement(LESSON, formId).serviceFeedbackEvidenceId == evidenceId, "basis lost report scope");
    }

    function testIndependentFullServiceFeedbackRequiresActualStudentAndExactPostTeachingProof() public {
        bytes32 formId = _book(_assessment());
        SparkV15ServiceReports reports = app.booking.OPENING().SERVICE_REPORTS();
        bytes32 received = keccak256("complete agreed service");
        SparkV15ServiceReports.SourceProof memory proof = _fullServiceProof(reports, formId, received, END + 5);
        vm.expectRevert(SparkV15Booking.InvalidReport.selector);
        vm.prank(STUDENT);
        reports.recordFullServiceFeedback(formId, received, proof);

        _teachWithReports(formId, true, false);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(STUDENT);
        reports.recordFullServiceFeedback(formId, received, proof); // The proof named a different end reference.
        proof = _fullServiceProof(reports, formId, received, END + 2);
        vm.expectRevert(SparkV15Booking.UnauthorisedBookingActor.selector);
        vm.prank(COORDINATOR);
        reports.recordFullServiceFeedback(formId, received, proof);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(STUDENT);
        reports.recordFullServiceFeedback(formId, keccak256("different report"), proof);
        vm.warp(END + 3);
        vm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        vm.prank(STUDENT);
        reports.recordFullServiceFeedback(formId, received, proof);
        require(app.booking.getServiceFeedback(formId).reportedAt == 0, "failed proof created a report");

        SparkV15Booking booking = app.booking;
        SparkV15Booking.ServiceStatus partialService = SparkV15Booking.ServiceStatus.PartiallyDelivered;
        bytes32 missed = keccak256("agreed service omitted");
        uint256 registered = _evidence(booking.serviceFeedbackCommitment(formId, partialService, received, missed));
        vm.prank(STUDENT);
        booking.recordServiceFeedback(formId, partialService, received, missed, registered);
        proof = _fullServiceProof(reports, formId, received, END + 5);
        vm.expectRevert(SparkV15Booking.InvalidReport.selector);
        vm.prank(STUDENT);
        reports.recordFullServiceFeedback(formId, received, proof);
        require(booking.getServiceFeedback(formId).evidenceId == registered, "old contradictory report overwritten");
    }

    function testIndependentFullServiceFeedbackLifecycleRetainsReportAndBlocksLiveConsumption() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teachWithReports(formId, true, false);
        SparkV15ServiceReports reports = app.booking.OPENING().SERVICE_REPORTS();
        bytes32 received = keccak256("complete agreed service");
        SparkV15ServiceReports.SourceProof memory proof = _fullServiceProof(reports, formId, received, END + 5);
        vm.prank(STUDENT);
        uint256 evidenceId = reports.recordFullServiceFeedback(formId, received, proof);
        _prepareSettlement(formId, assessment);

        bytes32 reason = keccak256("basis replaced after independent check");
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(SOURCE);
        reports.recordFeedbackEvidenceLifecycle(
            formId, proof.sourceRole, proof.sourceAuthorityId, AVACoreTypes.EvidenceLifecycleKind.Revoke, 0, reason
        );
        _allowSourceEvidenceLifecycle();
        uint256 unrelated = _evidence(keccak256("unrelated attestation"));
        vm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        vm.prank(SOURCE);
        reports.recordFeedbackEvidenceLifecycle(
            formId, proof.sourceRole, proof.sourceAuthorityId, AVACoreTypes.EvidenceLifecycleKind.Supersede, unrelated, reason
        );
        uint256 replacement = _registeredEvidence(
            keccak256("revised service-feedback evidence"), keccak256("spark.v1.5.booking.service-feedback")
        );
        vm.prank(SOURCE);
        reports.recordFeedbackEvidenceLifecycle(
            formId, proof.sourceRole, proof.sourceAuthorityId, AVACoreTypes.EvidenceLifecycleKind.Supersede, replacement, reason
        );
        (uint256 stored, AVACoreTypes.EvidenceStatus status, uint256 replacementId) = reports.getAdoptedFeedbackEvidence(formId);
        require(stored == evidenceId && status == AVACoreTypes.EvidenceStatus.Superseded, "original basis not retained");
        require(replacementId == replacement, "incorrect supersession link");
        require(app.booking.getServiceFeedback(formId).receivedRef == received, "history was replaced");
        SparkV15Settlement settlement = app.settlement;
        vm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        require(!settlement.getGroupSettlement(LESSON).complete, "unavailable report settled lesson");
    }

    function _fullServiceProof(SparkV15ServiceReports reports, bytes32 formId, bytes32 received, uint64 validThrough)
        private returns (SparkV15ServiceReports.SourceProof memory proof)
    {
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        proof = SparkV15ServiceReports.SourceProof(role, _subject(SOURCE, role), app.disclosurePolicyId, validThrough, 0, 0);
        bytes32 digest = reports.fullServiceFeedbackDigest(formId, received, proof);
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(SOURCE_KEY, digest);
        proof.r = r;
        proof.vs = bytes32(uint256(s) | ((uint256(v) - 27) << 255));
    }

    function testPaidPlaceAdoptsSignedAcceptancesAndDebitsTheOriginalRecharge() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _bookWithAcceptances(assessment, BookingPath.Signed);
        assessment.seats[0].formId = formId;
        _teach(formId);
        _approveAndPayWage(_settle(formId, assessment));
    }

    function testWithdrawingUnusedBookingAssentLeavesTheRecordedRouteAvailable() public {
        _bookWithAcceptances(_assessment(), BookingPath.Withdrawn);
    }

    function testInstalledOrdinaryOneToOneFirstUsesSettlementConsent() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        SparkV15Settlement settlement = app.settlement;
        SparkV15Settlement.GroupPreview memory earlier = _prepareSettlement(formId, assessment);
        vm.warp(block.timestamp + 1);
        bytes32 sameProposal = settlement.proposalCommitment(LESSON, assessment);
        vm.prank(COORDINATOR);
        settlement.proposeOrdinaryGroup(LESSON, sameProposal);
        SparkV15Settlement.GroupPreview memory preview = settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        require(preview.basis != earlier.basis, "later proposal lost its identity");
        uint256[] memory wageEvidence = new uint256[](1);
        wageEvidence[0] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis));

        _expectConsentRejection(assessment, earlier.basis, SOURCE_KEY, wageEvidence, AVACoreTypes.NotAuthorised.selector);
        _expectConsentRejection(assessment, preview.basis, 0x7450, wageEvidence, AVACoreTypes.NotAuthorised.selector);
        _expectConsentRejection(assessment, preview.basis, VERIFIER_KEY, wageEvidence, SparkV15Booking.InvalidEvidence.selector);
        _expectConsentRejection(assessment, preview.basis, COORDINATOR_KEY, wageEvidence, SparkV15Booking.InvalidEvidence.selector);
        _expectConsentRejection(
            assessment, preview.basis, SOURCE_KEY, new uint256[](0), SparkV15Settlement.InvalidSettlementEvidence.selector
        );
        require(!settlement.getGroupSettlement(LESSON).complete, "rejected consent completed settlement");

        SparkV15BookingOpening.OrdinarySettlementConsent memory consent = _settlementConsent(preview.basis, SOURCE_KEY);
        vm.expectEmit(true, true, true, true, address(settlement));
        emit OrdinarySettlementConsented(LESSON, preview.basis, SOURCE, consent.sourceAuthorityId);
        vm.prank(VERIFIER);
        settlement.approveOrdinaryOneToOneWithConsent(LESSON, assessment, consent, wageEvidence);
        bytes32 obligationId = _settledObligation(formId, assessment.route, preview.basis, 0);
        require(app.payments.getObligation(obligationId).evidenceId == wageEvidence[0], "independent wage evidence lost");
        SparkV15SettlementAlternatives alternatives = settlement.ALTERNATIVES();
        (bytes32 retained,) = alternatives.retainedPayment(preview.payments[0], app.packageId);
        require(retained == obligationId, "registered wage not retained");
        _allowSourceEvidenceLifecycle();
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        vm.prank(SOURCE);
        registry.recordEvidenceLifecycle(
            wageEvidence[0], consent.sourceRole, consent.sourceAuthorityId,
            AVACoreTypes.EvidenceLifecycleKind.Revoke, 0, keccak256("source withdrew the evidence"), ""
        );
        uint256 packageId = app.packageId;
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        alternatives.retainedPayment(preview.payments[0], packageId);
        _approveAndPayWage(obligationId);
    }

    function testInstalledOrdinaryWageFirstUsesSeparateExactProofAndPays() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teachWithAttendanceOption(formId, false);
        (SparkV15SettlementOccurrences.LocalOneToOneRecords memory records,
            SparkV15SettlementOccurrences.SignedAttendance memory attendance) = _localRecords(formId, assessment);
        SparkV15Settlement.GroupPreview memory preview =
            app.settlement.previewOrdinaryOneToOneWithLocalAttendance(LESSON, assessment, VERIFIER, records, attendance);
        SparkV15BookingOpening.OrdinarySettlementConsent memory consent = _settlementConsent(preview.basis, SOURCE_KEY);
        bytes32 commitment = app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis);
        uint64 validThrough = uint64(block.timestamp + 30 minutes);
        SparkV15BookingOpening.OrdinaryWageEvidence memory wage =
            _wageConsent(commitment, app.packageId, validThrough, SOURCE_KEY);
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        uint256 nextEvidenceId = registry.nextEvidenceId();
        _assertInvalidWageProofs(assessment, consent, records, attendance, commitment, validThrough);

        vm.expectRevert(SparkV15Payments.InvalidObligation.selector);
        vm.prank(VERIFIER);
        app.payments.establishAdoptedWage(preview.payments[0], preview.basis, app.packageId);
        vm.record();
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryOneToOneWithAdoptedWage(LESSON, assessment, consent, wage, records, attendance);
        uint256 settlementWrites = _nonzeroWrittenWords(address(app.settlement));
        emit log_named_uint("Ordinary adopted wage approval settlement storage words updated", settlementWrites);
        bytes32 obligationId = _settledObligation(formId, assessment.route, preview.basis, 0);
        SparkV15Settlement.SeatSettlement memory snapshot = _assertOrdinarySeatSnapshot(formId, obligationId);
        SparkV15Payments.Obligation memory obligation = app.payments.getObligation(obligationId);
        require(registry.nextEvidenceId() == nextEvidenceId, "unexpected Core registration");
        require(obligation.evidenceId == 0 && obligation.commitment == commitment, "wrong adopted obligation");
        require(app.booking.getAttendance(formId).attended, "signed attendance not adopted");
        vm.expectRevert(SparkV15SettlementOccurrences.InvalidLocalOneToOneRecords.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryOneToOneWithAdoptedWage(LESSON, assessment, consent, wage, records, attendance);
        vm.warp(validThrough + 1);
        _checkAdoptedEvidenceLifecycle(obligationId, wage, preview.payments[0]);
        SparkV15Payments.ApprovalTerms memory terms =
            SparkV15Payments.ApprovalTerms(obligationId, EXECUTOR, WAGE, DUE + 1 days, 0);
        vm.prank(ALLOCATOR);
        _payApprovedWage(obligationId, app.payments.grantOrdinaryWageApproval(terms));
        require(
            keccak256(abi.encode(app.settlement.getSeatSettlement(LESSON, formId))) == keccak256(abi.encode(snapshot)),
            "retained assessment changed after source revocation and payment"
        );
        require(settlementWrites <= 19, "ordinary approval rewrote immutable seat fields");
    }

    function _assertOrdinarySeatSnapshot(bytes32 formId, bytes32 obligationId)
        private
        view
        returns (SparkV15Settlement.SeatSettlement memory snapshot)
    {
        SparkV15Settlement.SeatSettlement memory expected;
        expected.formId = formId;
        expected.placeId = PLACE;
        expected.debitAccount = funds.creditAccount(PAYER);
        expected.debitOwner = PAYER;
        expected.normalFee = FEE;
        expected.debited = FEE;
        expected.feeDue = FEE;
        expected.tutorPay = WAGE;
        expected.tutorNetPay = WAGE;
        expected.disposition = SparkV15Settlement.SeatDisposition.OrdinaryFee;
        expected.noticeEvidenceId = app.booking.getStudentNotice(formId).evidenceId;
        expected.serviceFeedbackEvidenceId = app.booking.getServiceFeedback(formId).evidenceId;
        expected.serviceAvailabilityRef = keccak256("verified available service on the agreed place");
        expected.tutorObligationId = obligationId;
        snapshot = app.settlement.getSeatSettlement(LESSON, formId);
        require(keccak256(abi.encode(snapshot)) == keccak256(abi.encode(expected)), "ordinary seat assessment changed");
    }

    function testInstalledOrdinaryTeachingStartAdoptsIndependentEvidenceAtItsActualEntry() public {
        bytes32 formId = _book(_assessment());
        _recordStartNotices(formId);
        vm.warp(START + 2);
        SparkV15Booking.StartObservation memory observation = _startObservation(bytes32(0));
        SparkV15TeachingEnd occurrenceModule = app.booking.OPENING().TEACHING_END();
        SparkV15TeachingEnd.Proof memory proof = _teachingStartProof(occurrenceModule, observation, START + 3);
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        uint256 nextEvidence = registry.nextEvidenceId();
        vm.prank(VERIFIER);
        occurrenceModule.recordOrdinaryTeachingStarted(LESSON, observation, proof);
        SparkV15Booking.Teaching memory readback = app.booking.getTeaching(LESSON);
        require(readback.startedAt == START && readback.startRecordedAt == START + 2, "lost actual or record time");
        require(readback.startPermission == SparkV15Booking.StartPermission.Permitted, "wrong permission");
        require(readback.startEvidenceId != 0 && readback.providerWentAhead, "start evidence or provider missing");
        address[] memory students = app.booking.getStudentsTakingLesson(LESSON);
        require(students.length == 1 && students[0] == STUDENT, "actual students lost");
        require(registry.nextEvidenceId() == nextEvidence, "start also registered a Core record");
        occurrenceModule.requireStartAvailable(LESSON, readback.startEvidenceId, app.packageId);
        this.finishAfterAdoptedStart(formId);
    }

    function finishAfterAdoptedStart(bytes32 formId) external {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        assessment.seats[0].formId = formId;
        _recordEndFromCurrentStart();
        vm.warp(END + 1);
        _reportTeaching(formId, true, true);
        _approveAndPayWage(_settle(formId, assessment));
    }

    function testInstalledSignedStartClosesTheSameLiveRescheduleAtTheSameClock() public {
        (bytes32 formId, bytes32 changeId) = this.preparePendingRescheduleAtStart();
        SparkV15BookingChanges changes = SparkV15BookingChanges(address(app.booking.bookingChanges()));
        vm.warp(START + 2);
        uint256 beforeStart = vm.snapshotState();
        require(app.booking.getTeaching(LESSON).startedAt == 0, "fixture already started");
        vm.prank(COORDINATOR);
        changes.finalizeArrangement(changeId);
        (,,, uint64 finalizedAt,,) = changes.getAgreement(changeId);
        require(finalizedAt == START + 2, "pre-start control could not really finalize at the same clock");
        require(vm.revertToState(beforeStart), "pre-start control snapshot missing");

        uint256 beforeLegacy = vm.snapshotState();
        _recordLegacyStart(_startObservation(bytes32(0)));
        _assertPendingRescheduleBlocked(changes, changeId);
        require(vm.revertToState(beforeLegacy), "old start control snapshot missing");

        require(block.timestamp == START + 2, "clock differed between branches");
        require(app.booking.getForm(formId).confirmation.debitedUnits == FEE, "lost exact debit");
        _recordAdoptedStart(_startObservation(bytes32(0)));
        _assertPendingRescheduleBlocked(changes, changeId);
        this.changeCurrentStartLifecycle(
            AVACoreTypes.EvidenceLifecycleKind.Revoke, AVACoreTypes.EvidenceStatus.Revoked
        );
        _assertPendingRescheduleBlocked(changes, changeId);
        _recordEndFromCurrentStart();
        require(app.booking.getTeaching(LESSON).endedAt == END, "start proof recall blocked the later physical end");
    }

    function _assertPendingRescheduleBlocked(SparkV15BookingChanges changes, bytes32 changeId) private {
        SparkV15Booking.Teaching memory teaching = app.booking.getTeaching(LESSON);
        require(teaching.startedAt == START && teaching.startRecordedAt == START + 2, "canonical start not recorded");
        require(teaching.startPermission == SparkV15Booking.StartPermission.Permitted, "teaching permission changed");
        vm.expectRevert(SparkV15BookingChanges.InvalidChange.selector);
        vm.prank(COORDINATOR);
        changes.finalizeArrangement(changeId);
        (,,, uint64 finalizedAt,,) = changes.getAgreement(changeId);
        require(finalizedAt == 0 && !changes.hasFinalizedArrangement(LESSON), "blocked reschedule became effective");
    }

    function preparePendingRescheduleAtStart() external returns (bytes32 formId, bytes32 changeId) {
        SparkV15BookingChanges changes = SparkV15BookingChanges(address(app.booking.bookingChanges()));
        SparkV15BookingChanges.ChangeTerms memory terms;
        terms.reschedule = SparkV15BookingChanges.Window(
            SparkV15BookingChanges.ClockMode.Fixed, START + 2 days, SparkV15BookingChanges.ClockMode.None, 0
        );
        formId = _bookWithChangeTerms(_assessment(), BookingPath.Recorded, changes.changeTermsCommitment(terms));
        changes.admitChangeTerms(formId, terms);
        _recordStartNotices(formId);
        vm.warp(EPOCH + 2);

        SparkV15BookingChanges.ArrangementTerms memory next;
        next.startsAt = START + 1 days;
        next.endsAt = END + 1 days;
        next.effectiveAt = START + 30 minutes;
        next.timeZoneRef = keccak256("UTC");
        bytes32 contact = keccak256("contact with parties about moving the lesson");
        uint256 proposal = _evidence(changes.proposalCommitment(LESSON, next, EPOCH + 2, contact));
        vm.prank(COORDINATOR);
        changeId = changes.proposeArrangement(LESSON, next, EPOCH + 2, contact, proposal);
        vm.prank(PAYER);
        changes.acceptPlace(changeId, formId);
        vm.prank(TUTOR);
        changes.acceptTutor(changeId);
        vm.prank(PROVIDER);
        changes.acceptProvider(changeId);
        vm.prank(COORDINATOR);
        changes.recordAgreement(changeId);

        vm.warp(EPOCH + 3);
        bytes32 notice = keccak256("delivered the proposed alternate schedule to the student");
        uint256 studentEvidence = _evidence(changes.studentChangeNoticeCommitment(changeId, formId, EPOCH + 3, notice));
        vm.prank(COORDINATOR);
        changes.recordStudentChangeNotice(changeId, formId, EPOCH + 3, notice, studentEvidence);
    }

    function testInstalledStartEvidenceLifecycleRejectsPreviouslySupportedSettlement() public {
        bytes32 formId = this.bookAndAdoptStart();
        _recordEndFromCurrentStart();
        vm.warp(END + 1);
        _reportTeaching(formId, true, true);
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        assessment.seats[0].formId = formId;
        (uint256 approvalEvidence, uint256[] memory wageEvidence) = _prepareApprovalEvidence(formId, assessment);
        _checkStartEffectOnSettlement(
            assessment, approvalEvidence, wageEvidence,
            AVACoreTypes.EvidenceLifecycleKind.Revoke, AVACoreTypes.EvidenceStatus.Revoked
        );
        _checkStartEffectOnSettlement(
            assessment, approvalEvidence, wageEvidence,
            AVACoreTypes.EvidenceLifecycleKind.Expire, AVACoreTypes.EvidenceStatus.Expired
        );
        _checkStartEffectOnSettlement(
            assessment, approvalEvidence, wageEvidence,
            AVACoreTypes.EvidenceLifecycleKind.Supersede, AVACoreTypes.EvidenceStatus.Superseded
        );
    }

    function _checkStartEffectOnSettlement(
        SparkV15Settlement.GroupAssessment memory assessment,
        uint256 approvalEvidence,
        uint256[] memory wageEvidence,
        AVACoreTypes.EvidenceLifecycleKind kind,
        AVACoreTypes.EvidenceStatus status
    ) private {
        uint256 snapshot = vm.snapshotState();
        this.changeCurrentStartLifecycle(kind, status);
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, approvalEvidence, wageEvidence);
        require(!app.settlement.getGroupSettlement(LESSON).complete, "unavailable start evidence approved settlement");
        SparkV15Booking.Teaching memory actual = app.booking.getTeaching(LESSON);
        require(actual.startedAt == START && actual.endedAt == END, "lost actual interval after evidence decision");
        require(vm.revertToState(snapshot), "missing settlement snapshot");
    }

    function bookAndAdoptStart() external returns (bytes32 formId) {
        formId = _book(_assessment());
        _recordStartNotices(formId);
        vm.warp(START + 2);
        _recordAdoptedStart(_startObservation(bytes32(0)));
    }

    function changeCurrentStartLifecycle(
        AVACoreTypes.EvidenceLifecycleKind kind, AVACoreTypes.EvidenceStatus expected
    ) external {
        SparkV15TeachingEnd occurrenceModule = app.booking.OPENING().TEACHING_END();
        (uint256 original, bytes32 source, uint256 disclosure, AVACoreTypes.EvidenceStatus prior,) =
            occurrenceModule.getAdoptedStartEvidence(LESSON);
        require(prior == AVACoreTypes.EvidenceStatus.Active && original != 0, "signed start is not active");
        require(source == _subject(SOURCE, app.applicationModule.SOURCE_ROLE()), "wrong starting source");
        require(disclosure == app.disclosurePolicyId, "wrong starting disclosure policy");
        bytes32 role = app.applicationModule.VERIFIER_ROLE();
        bytes32 authority = _subject(REVIEWER, role);
        bytes32 reason = keccak256("independent decision on initial actual starting evidence");
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(REVIEWER);
        occurrenceModule.recordStartEvidenceLifecycle(LESSON, role, authority, kind, 0, reason);
        _allowEvidenceLifecycle(role);
        uint256 replacement;
        if (kind == AVACoreTypes.EvidenceLifecycleKind.Supersede) {
            bytes32 alternateObservation = keccak256("recognised correction to the opening evidence");
            replacement = _registeredEvidence(
                app.booking.teachingStartCommitment(LESSON, _startObservation(alternateObservation)),
                occurrenceModule.START_EVIDENCE_TYPE()
            );
        }
        vm.prank(REVIEWER);
        occurrenceModule.recordStartEvidenceLifecycle(LESSON, role, authority, kind, replacement, reason);
        (uint256 retained,,, AVACoreTypes.EvidenceStatus latest, uint256 linkedReplacement) =
            occurrenceModule.getAdoptedStartEvidence(LESSON);
        require(retained == original && latest == expected && linkedReplacement == replacement, "wrong lifecycle");
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        occurrenceModule.requireStartAvailable(LESSON, original, app.packageId);
    }

    function testInstalledSignedStartBindsExactObservationAndKeepsConflictingFacts() public {
        bytes32 formId = _book(_assessment());
        _recordStartNotices(formId);
        vm.warp(START + 2);
        bytes32 conflict = keccak256("verified contradiction to the recorded opening permission");
        SparkV15Booking.StartObservation memory observation = _startObservation(conflict);
        SparkV15TeachingEnd occurrenceModule = app.booking.OPENING().TEACHING_END();
        SparkV15TeachingEnd.Proof memory proof = _teachingStartProof(occurrenceModule, observation, START + 3);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(COORDINATOR);
        occurrenceModule.recordOrdinaryTeachingStarted(LESSON, observation, proof);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(VERIFIER);
        occurrenceModule.recordOrdinaryTeachingStarted(LESSON, _startObservation(bytes32(0)), proof);
        require(app.booking.getTeaching(LESSON).startedAt == 0, "wrong observation recorded a start");
        vm.warp(START + 4);
        vm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        vm.prank(VERIFIER);
        occurrenceModule.recordOrdinaryTeachingStarted(LESSON, observation, proof);

        _recordAdoptedStart(observation);
        SparkV15Booking.Teaching memory teaching = app.booking.getTeaching(LESSON);
        require(teaching.startedAt == START && teaching.providerWentAhead, "lost physical start");
        require(teaching.unmetConditionRef == conflict, "lost conflicting evidence");
        require(teaching.startPermission == SparkV15Booking.StartPermission.Unverified, "disagreement became permit");
    }

    function testInstalledOrdinaryTeachingEndAdoptsIndependentEvidenceBeforeReportsAndPayment() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _startTeaching(formId);
        vm.warp(END + 2);
        SparkV15TeachingEnd teachingEnd = app.booking.OPENING().TEACHING_END();
        bytes32 occurrenceRef = keccak256("observed actual teaching end");
        SparkV15TeachingEnd.Proof memory proof = _teachingEndProof(teachingEnd, occurrenceRef, VERIFIER, END + 3);
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        uint256 nextEvidenceId = registry.nextEvidenceId();

        vm.prank(VERIFIER);
        teachingEnd.recordOrdinaryTeachingEnded(LESSON, END, occurrenceRef, proof);

        SparkV15Booking.Teaching memory teaching = app.booking.getTeaching(LESSON);
        require(teaching.endedAt == END && teaching.endRecordedAt == END + 2, "lost actual or recording time");
        require(teaching.endEvidenceId != 0, "missing end evidence");
        require(registry.nextEvidenceId() == nextEvidenceId, "adoption also registered Core evidence");
        teachingEnd.requireAvailable(LESSON, teaching.endEvidenceId, app.packageId);

        vm.warp(END + 4);
        _reportTeaching(formId, true, true);
        require(app.booking.getTutorDelivery(LESSON).reportedAt == END + 4, "expected early independent tutor report");
        require(app.booking.getServiceFeedback(formId).reportedAt == END + 4, "expected separate student feedback");
        require(!app.settlement.getGroupSettlement(LESSON).complete, "reports must precede settlement");
        _approveAndPayWage(_settle(formId, assessment));
    }

    function testInstalledOrdinaryTeachingEndRequiresCurrentVerifierAndExactUnexpiredProof() public {
        bytes32 formId = _book(_assessment());
        _startTeaching(formId);
        vm.warp(END + 2);
        SparkV15TeachingEnd teachingEnd = app.booking.OPENING().TEACHING_END();
        bytes32 occurrenceRef = keccak256("observed actual teaching end");
        SparkV15TeachingEnd.Proof memory proof = _teachingEndProof(teachingEnd, occurrenceRef, VERIFIER, END + 3);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(COORDINATOR);
        teachingEnd.recordOrdinaryTeachingEnded(LESSON, END, occurrenceRef, proof);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(VERIFIER);
        teachingEnd.recordOrdinaryTeachingEnded(LESSON, END + 1, occurrenceRef, proof);
        vm.warp(END + 4);
        vm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        vm.prank(VERIFIER);
        teachingEnd.recordOrdinaryTeachingEnded(LESSON, END, occurrenceRef, proof);
        require(app.booking.getTeaching(LESSON).endedAt == 0, "rejected proof recorded an end");

        proof = _teachingEndProof(teachingEnd, occurrenceRef, VERIFIER, END + 5);
        vm.prank(VERIFIER);
        teachingEnd.recordOrdinaryTeachingEnded(LESSON, END, occurrenceRef, proof);
        vm.expectRevert(SparkV15Booking.InvalidTeaching.selector);
        vm.prank(VERIFIER);
        teachingEnd.recordOrdinaryTeachingEnded(LESSON, END, occurrenceRef, proof);
    }

    function testInstalledRecalledTeachingEndBlocksSettlementButRetainsEarlyReportsAndOccurrence() public {
        _assertUnavailableAdoptedEnd(AVACoreTypes.EvidenceLifecycleKind.Revoke, AVACoreTypes.EvidenceStatus.Revoked);
    }

    function testInstalledExpiredTeachingEndBlocksSettlement() public {
        _assertUnavailableAdoptedEnd(AVACoreTypes.EvidenceLifecycleKind.Expire, AVACoreTypes.EvidenceStatus.Expired);
    }

    function testInstalledSupersededTeachingEndLinksCoreReplacementWithoutReactivatingOriginal() public {
        _assertUnavailableAdoptedEnd(
            AVACoreTypes.EvidenceLifecycleKind.Supersede, AVACoreTypes.EvidenceStatus.Superseded
        );
    }

    function _assertUnavailableAdoptedEnd(AVACoreTypes.EvidenceLifecycleKind kind, AVACoreTypes.EvidenceStatus status)
        private
    {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _recordAdoptedEnd(formId);
        vm.warp(END + 1);
        _reportTeaching(formId, true, true);
        (uint256 approvalEvidence, uint256[] memory wageEvidence) = _prepareApprovalEvidence(formId, assessment);
        this.checkAdoptedTeachingEndLifecycle(kind, status);
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, approvalEvidence, wageEvidence);
        require(!app.settlement.getGroupSettlement(LESSON).complete, "inactive ending basis completed settlement");
        require(app.booking.getTeaching(LESSON).endedAt == END, "lifecycle rewrote actual end");
        require(app.booking.getTutorDelivery(LESSON).reportedAt == END + 1, "lifecycle rewrote existing report");
    }

    function _prepareApprovalEvidence(bytes32 formId, SparkV15Settlement.GroupAssessment memory assessment)
        private
        returns (uint256 approvalEvidence, uint256[] memory wageEvidence)
    {
        SparkV15Settlement.GroupPreview memory preview = _prepareSettlement(formId, assessment);
        approvalEvidence = _evidence(preview.basis);
        wageEvidence = new uint256[](1);
        wageEvidence[0] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis));
    }

    function checkAdoptedTeachingEndLifecycle(
        AVACoreTypes.EvidenceLifecycleKind kind,
        AVACoreTypes.EvidenceStatus status
    ) external {
        SparkV15TeachingEnd teachingEnd = app.booking.OPENING().TEACHING_END();
        (uint256 evidenceId, bytes32 source, uint256 disclosure, AVACoreTypes.EvidenceStatus initial, uint256 prior) =
            teachingEnd.getAdoptedEvidence(LESSON);
        require(evidenceId == app.booking.getTeaching(LESSON).endEvidenceId && prior == 0, "wrong original evidence");
        require(source == _subject(SOURCE, app.applicationModule.SOURCE_ROLE()), "wrong proof source");
        require(disclosure == app.disclosurePolicyId, "wrong proof disclosure");
        require(initial == AVACoreTypes.EvidenceStatus.Active, "first-use signature deadline expired served evidence");
        bytes32 reviewerRole = app.applicationModule.VERIFIER_ROLE();
        bytes32 reviewerAuthority = _subject(REVIEWER, reviewerRole);
        bytes32 reason = keccak256("separate lifecycle decision on the ending basis");
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(REVIEWER);
        teachingEnd.recordEvidenceLifecycle(LESSON, reviewerRole, reviewerAuthority, kind, 0, reason);

        _allowEvidenceLifecycle(reviewerRole);
        uint256 replacement;
        if (kind == AVACoreTypes.EvidenceLifecycleKind.Supersede) {
            uint256 unrelated = _evidence(keccak256("independent evidence of unrelated form support"));
            vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
            vm.prank(REVIEWER);
            teachingEnd.recordEvidenceLifecycle(LESSON, reviewerRole, reviewerAuthority, kind, unrelated, reason);
            replacement = _registeredEvidence(
                app.booking.teachingEndCommitment(LESSON, END, keccak256("later improved occurrence record")),
                teachingEnd.EVIDENCE_TYPE()
            );
        }
        vm.prank(REVIEWER);
        teachingEnd.recordEvidenceLifecycle(LESSON, reviewerRole, reviewerAuthority, kind, replacement, reason);
        (uint256 afterId,,, AVACoreTypes.EvidenceStatus latest, uint256 linkedReplacement) =
            teachingEnd.getAdoptedEvidence(LESSON);
        require(afterId == evidenceId && latest == status && linkedReplacement == replacement, "lost lifecycle effect");
        if (replacement != 0) {
            uint256 packageId = app.packageId;
            app.kernel.EVIDENCE_REGISTRY().requireUsableEvidenceReferenceForPackage(replacement, packageId);
            vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
            teachingEnd.requireAvailable(LESSON, replacement, packageId);
        }
    }

    function testInstalledRevokedCoreEndRemainsSubjectToCoreLifecycleAndKeepsOccurrence() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        (uint256 approvalEvidence, uint256[] memory wageEvidence) = _prepareApprovalEvidence(formId, assessment);
        SparkV15TeachingEnd teachingEnd = app.booking.OPENING().TEACHING_END();
        (uint256 adoptedId,,,,) = teachingEnd.getAdoptedEvidence(LESSON);
        require(adoptedId == 0, "Core evidence looked like an adopted proof");
        uint256 coreId = app.booking.getTeaching(LESSON).endEvidenceId;
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        bytes32 reviewerRole = app.applicationModule.VERIFIER_ROLE();
        bytes32 reviewerAuthority = _subject(REVIEWER, reviewerRole);
        _allowEvidenceLifecycle(reviewerRole);
        vm.prank(REVIEWER);
        registry.recordEvidenceLifecycle(
            coreId, reviewerRole, reviewerAuthority, AVACoreTypes.EvidenceLifecycleKind.Revoke, 0,
            keccak256("independent recall of Core end evidence"), ""
        );
        vm.expectPartialRevert(AVACoreTypes.InvalidState.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, approvalEvidence, wageEvidence);
        require(!app.settlement.getGroupSettlement(LESSON).complete, "revoked Core evidence completed settlement");
        require(app.booking.getTeaching(LESSON).endedAt == END, "Core revocation rewrote observed end");
    }

    function testInstalledRemedyReadsAdoptedEndBeforeOrdinarySettlement() public {
        bytes32 formId = _book(_assessment());
        _recordAdoptedEnd(formId);
        vm.warp(END + 1);
        _recordProviderFault(formId);
    }

    function testInstalledConsentCannotTreatAnOperativeProviderFaultAsOrdinaryFullFee() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        SparkV15Settlement.GroupPreview memory preview = _prepareSettlement(formId, assessment);
        uint256[] memory wageEvidence = new uint256[](1);
        wageEvidence[0] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis));
        _recordProviderFault(formId);
        uint256 reserved = funds.reservedUnits();
        _expectConsentRejection(
            assessment, preview.basis, SOURCE_KEY, wageEvidence, SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector
        );
        require(!app.settlement.getGroupSettlement(LESSON).complete, "provider fault settled at full fee");
        require(funds.reservedUnits() == reserved, "rejected settlement changed reserves");
    }

    function testInstalledRegisteredSettlementUsesAssessedProviderRefundAndPaysTutor() public {
        SparkV15Settlement.GroupAssessment memory assessment = _assessment();
        bytes32 formId = _book(assessment);
        assessment.seats[0].formId = formId;
        _teach(formId);
        _recordProviderFault(formId);
        bytes32 refund = _payProviderFaultRefund(formId);

        SparkV15Settlement.GroupPreview memory preview = _prepareSettlement(formId, assessment);
        uint256 approval = _evidence(preview.basis);
        uint256[] memory wageEvidence = new uint256[](1);
        wageEvidence[0] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis));
        _expectConsentRejection(
            assessment, preview.basis, SOURCE_KEY, wageEvidence, SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector
        );
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, approval, wageEvidence);

        SparkV15Settlement.SeatSettlement memory seat = app.settlement.getSeatSettlement(LESSON, formId);
        require(seat.debited == 20 && seat.feeDue == 12, "registered settlement ignored assessed fee");
        require(seat.refundDue == 8 && seat.refundAlreadyReceived == 8, "wrong retained refund");
        require(seat.refundObligationId == refund && seat.debitAccount == funds.creditAccount(PAYER), "wrong refund");
        require(funds.paymentReserved(refund) == 0 && funds.creditBalance(seat.debitAccount) == 8, "duplicate refund");
        require(seat.tutorNetPay == WAGE && funds.paymentReserved(seat.tutorObligationId) == WAGE, "wage lost");

        uint256 wageApproval = _approvePayment(seat.tutorObligationId, WAGE, DUE);
        require(app.payments.getObligation(seat.tutorObligationId).paid == 0, "approval paid the wage");
        vm.warp(DUE);
        vm.prank(EXECUTOR);
        uint256 receiptId = app.payments.pay(wageApproval, WAGE);
        SparkV15Payments.PaymentReceipt memory receipt = app.payments.getReceipt(receiptId);
        require(receipt.amount == WAGE && receipt.recipient == TUTOR, "wrong wage receipt");
        require(token.balanceOf(TUTOR) == WAGE && token.balanceOf(address(funds)) == 192, "wrong actual cash movement");
        require(funds.creditBalance(seat.debitAccount) == 8, "payment changed original refund");
    }

    function testInstalledEarlyProviderStartSettlesVerifiedServiceAndPaysBothObligations() public {
        (SparkV15Settlement.GroupAssessment memory assessment, bytes32 formId) = _earlyProviderStartAssessment();
        SparkV15Settlement.GroupPreview memory preview = app.settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        require(preview.totalTutorPay == 5 && preview.netTutorPay == 5, "incorrect verified tutor amount");
        require(preview.payments.length == 2, "independent refund and tutor obligations required");
        require(preview.payments[0].amount == 7 && preview.payments[1].amount == 5, "incorrect exceptional amounts");

        uint256 approvalEvidence = _evidence(preview.basis);
        uint256[] memory paymentEvidence = new uint256[](2);
        paymentEvidence[0] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis));
        paymentEvidence[1] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[1], preview.basis));
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, approvalEvidence, paymentEvidence);

        SparkV15Settlement.GroupSettlement memory result = app.settlement.getGroupSettlement(LESSON);
        require(result.complete && result.basis == preview.basis && result.approver == VERIFIER, "final approval lost");
        require(result.route == SparkV15Settlement.Route.ProviderStartedEarly, "final route lost");
        SparkV15Settlement.SeatSettlement memory seat = app.settlement.getSeatSettlement(LESSON, formId);
        bytes32 payerAccount = funds.creditAccount(PAYER);
        require(seat.debited == 20 && seat.feeDue == 13 && seat.tutorPay == 5, "wrong retained assessment");
        require(seat.refundDue == 7 && seat.refundAlreadyReceived == 0, "assessment credited money before payment");
        require(seat.debitOwner == PAYER && seat.debitAccount == payerAccount, "wrong original debit");
        require(seat.refundObligationId != bytes32(0) && seat.tutorObligationId != bytes32(0), "obligations missing");
        require(funds.paymentReserved(seat.refundObligationId) == 7, "refund not backed");
        require(funds.paymentReserved(seat.tutorObligationId) == 5, "wage not backed");
        require(funds.creditBalance(payerAccount) == 0 && token.balanceOf(TUTOR) == 0, "settlement paid");

        uint256 refundApproval = _approvePayment(seat.refundObligationId, 7, END + 2);
        require(app.payments.getObligation(seat.refundObligationId).paid == 0, "approval restored credit");
        vm.prank(EXECUTOR);
        uint256 refundReceiptId = app.payments.pay(refundApproval, 7);
        SparkV15Payments.PaymentReceipt memory refundReceipt = app.payments.getReceipt(refundReceiptId);
        require(refundReceipt.creditAccount == payerAccount && refundReceipt.recipient == PAYER, "wrong refund account");
        require(refundReceipt.amount == 7 && refundReceipt.executor == EXECUTOR, "refund not performed");
        require(funds.creditBalance(payerAccount) == 7 && funds.creditBalance(funds.creditAccount(CUSTOMER)) == 0,
            "original credit not restored"
        );
        require(token.balanceOf(address(funds)) == 200 && token.balanceOf(TUTOR) == 0, "credit refund moved tokens");

        uint256 wageApproval = _approvePayment(seat.tutorObligationId, 5, DUE);
        vm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        vm.prank(EXECUTOR);
        app.payments.pay(wageApproval, 5);
        vm.warp(DUE);
        vm.prank(EXECUTOR);
        uint256 wageReceiptId = app.payments.pay(wageApproval, 5);
        SparkV15Payments.PaymentReceipt memory wageReceipt = app.payments.getReceipt(wageReceiptId);
        require(wageReceipt.recipient == TUTOR && wageReceipt.creditAccount == bytes32(0), "wrong wage transfer");
        require(wageReceipt.amount == 5 && wageReceipt.executor == EXECUTOR, "wage not performed");
        require(token.balanceOf(TUTOR) == 5 && token.balanceOf(address(funds)) == 195, "wrong cash movement");
        require(app.payments.getObligation(seat.refundObligationId).paid == 7, "refund net ledger wrong");
        require(app.payments.getObligation(seat.tutorObligationId).paid == 5, "wage net ledger wrong");
    }

    function testInstalledEarlyProviderStartRequiresExactIndependentApprovalAndUnheldFee() public {
        (SparkV15Settlement.GroupAssessment memory assessment, bytes32 formId) = _earlyProviderStartAssessment();
        SparkV15Settlement.GroupPreview memory preview = app.settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        uint256 approvalEvidence = _evidence(preview.basis);
        uint256[] memory paymentEvidence = new uint256[](2);
        paymentEvidence[0] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis));
        paymentEvidence[1] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[1], preview.basis));
        uint256 wrongScope = _evidence(keccak256("different proposed service assessment"));
        uint256 reservedBefore = funds.reservedUnits();

        vm.expectRevert(SparkV15BookingOpening.InvalidSettlementEvidence.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, wrongScope, paymentEvidence);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(PROVIDER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, approvalEvidence, paymentEvidence);

        bytes32 caseId = _holdFeeForEarlyProviderStart(formId);
        vm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, approvalEvidence, paymentEvidence);
        require(!app.settlement.hasSeatSettlement(LESSON, formId), "held fee settled");
        require(funds.reservedUnits() == reservedBefore, "blocked assessment changed shared funding");

        vm.warp(END + 2);
        SparkV15SettlementAlternatives alternatives = app.settlement.ALTERNATIVES();
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("fee decision notified to the concerned parties"), END + 2);
        bytes32 disposition = keccak256("fee hold fully lifted without changing the verified valuation");
        uint256 liftEvidence = _evidence(alternatives.feeLiftCommitment(caseId, disposition, notice, REVIEWER));
        bytes32 reviewer = _subject(REVIEWER, app.applicationModule.VERIFIER_ROLE());
        vm.prank(REVIEWER);
        alternatives.liftFeeHold(caseId, disposition, notice, liftEvidence, reviewer);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, approvalEvidence, paymentEvidence);
        require(app.settlement.getSeatSettlement(LESSON, formId).feeDue == 13, "fee changed when hold lifted");
    }

    function _earlyProviderStartAssessment()
        private
        returns (SparkV15Settlement.GroupAssessment memory assessment, bytes32 formId)
    {
        assessment = _assessment();
        formId = _book(assessment);
        _recordConfirmedUnpermittedTeaching(formId);
        assessment.seats[0].formId = formId;
        assessment.seats[0].serviceAvailabilityRef = keccak256("verified partial teaching under the agreed provider terms");
        assessment.route = SparkV15Settlement.Route.ProviderStartedEarly;
        assessment.seats[0].disposition = SparkV15Settlement.SeatDisposition.ProviderStartedEarly;
        assessment.verificationRef = app.settlement.ALTERNATIVES().OCCURRENCES().encodeProviderStartedEarlyAmounts(13, 5);
        assessment.clearanceRef = keccak256("independent under-terms valuation and scope check");
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

    function _recordConfirmedUnpermittedTeaching(bytes32 formId) private {
        vm.warp(START);
        // The provider proceeded although the agreed start notices had not been delivered.
        bytes32 unmet = keccak256("separate verified finding of missing agreed start notices");
        _recordLegacyStart(_startObservation(unmet));
        SparkV15Booking.Teaching memory teaching = app.booking.getTeaching(LESSON);
        require(teaching.startPermission == SparkV15Booking.StartPermission.RequirementsNotMet, "start permitted");
        require(teaching.providerWentAhead && teaching.unmetConditionRef == unmet, "actual violation missing");
        _finishTeaching(formId, true, false);
    }

    function _recordProviderFault(bytes32 formId) private {
        SparkV15LessonRemedies remedies = SparkV15LessonRemedies(address(app.settlement.remedyPolicy()));
        SparkV15LessonRemedies.FaultFinding memory finding;
        finding.kind = SparkV15LessonRemedies.FaultKind.ProviderAdministrationError;
        finding.groundRef = keccak256("provider handled the agreed administrative support incorrectly");
        finding.affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        finding.affected[0] = SparkV15LessonRemedies.AffectedPlace(
            formId, SparkV15LessonRemedies.TeachingReceived.FullyDelivered,
            SparkV15LessonRemedies.Participation.AttendedAsAgreed, 8, false, keccak256("verified loss of agreed support")
        );
        bytes32 matter = keccak256("undisputed provider error");
        bytes32 noDispute = keccak256("separate check of acceptable basis and no dispute");
        uint256 evidence = _evidence(remedies.providerFaultCommitment(formId, matter, finding, noDispute, COORDINATOR));
        vm.prank(COORDINATOR);
        bytes32 caseId = remedies.recordUndisputedProviderFault(formId, matter, finding, noDispute, evidence);
        require(remedies.getFault(caseId, 1).originalLessonAt == END, "remedy used the wrong occurrence clock");
        require(!app.settlement.getGroupSettlement(LESSON).complete, "remedy required earlier settlement");
    }

    function _payProviderFaultRefund(bytes32 formId) private returns (bytes32 refund) {
        SparkV15LessonRemedies remedies = SparkV15LessonRemedies(address(app.settlement.remedyPolicy()));
        SparkV15CustomerRedress redress = remedies.customerRedress();
        SparkV15CustomerRedress.RedressTerms memory terms = SparkV15CustomerRedress.RedressTerms(
            END + 7 days, END + 14 days, 0, 3 days, 0, 1 days, keccak256("agreed support"), DOCUMENTS
        );
        uint256 evidenceId = _evidence(redress.redressTermsCommitment(formId, terms));
        vm.prank(PROVIDER);
        redress.publishRedressTerms(formId, terms, evidenceId);
        vm.prank(CUSTOMER);
        redress.requestDirectRefund(formId);
        SparkV15CustomerRedress.RefundBasis cause = SparkV15CustomerRedress.RefundBasis.DirectRequest;
        (SparkV15CustomerRedress.RefundAssessment memory assessed, SparkV15Payments.PaymentTerms memory payment) =
            redress.previewRefund(formId, cause, VERIFIER);
        require(assessed.finalFee == 12 && assessed.principal == 8, "wrong provider refund assessment");
        require(payment.originalDebitAccount == funds.creditAccount(PAYER) && payment.recipient == PAYER, "wrong payer");
        evidenceId = _evidence(assessed.basis);
        bytes32 authority = _subject(VERIFIER, app.payments.VERIFIER_ROLE());
        vm.prank(VERIFIER);
        uint256 index = redress.assessRefund(formId, cause, evidenceId, authority);
        evidenceId = _evidence(app.payments.paymentEvidenceCommitment(payment, assessed.basis));
        vm.prank(VERIFIER);
        refund = redress.establishRefundPayment(formId, index, evidenceId);
        uint256 approval = _approvePayment(refund, 8, END + 2);
        vm.prank(EXECUTOR);
        uint256 receiptId = app.payments.pay(approval, 8);
        SparkV15Payments.PaymentReceipt memory receipt = app.payments.getReceipt(receiptId);
        require(receipt.amount == 8 && receipt.creditAccount == payment.originalDebitAccount, "refund not restored");
        require(token.balanceOf(address(funds)) == 200 && token.balanceOf(TUTOR) == 0, "refund moved tokens");
    }

    function _recordAdoptedEnd(bytes32 formId) private {
        _startTeaching(formId);
        _recordEndFromCurrentStart();
    }

    function _recordEndFromCurrentStart() private {
        vm.warp(END);
        SparkV15TeachingEnd teachingEnd = app.booking.OPENING().TEACHING_END();
        bytes32 occurrenceRef = keccak256("observed actual teaching end");
        SparkV15TeachingEnd.Proof memory proof = _teachingEndProof(teachingEnd, occurrenceRef, VERIFIER, END);
        vm.prank(VERIFIER);
        teachingEnd.recordOrdinaryTeachingEnded(LESSON, END, occurrenceRef, proof);
    }

    function _teachingEndProof(
        SparkV15TeachingEnd teachingEnd,
        bytes32 occurrenceRef,
        address verifier,
        uint64 validThrough
    ) private view returns (SparkV15TeachingEnd.Proof memory proof) {
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        bytes32 authority = _subject(SOURCE, role);
        bytes32 commitment = app.booking.teachingEndCommitment(LESSON, END, occurrenceRef);
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256("Spark DAO Teaching End Evidence"),
                keccak256("1"),
                block.chainid,
                address(teachingEnd)
            )
        );
        bytes32 message = keccak256(
            abi.encode(
                keccak256("TeachingEndEvidence(uint256 packageId,bytes32 lessonId,bytes32 commitment,address verifier,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"),
                app.packageId, LESSON, commitment, verifier, role, authority, app.disclosurePolicyId, validThrough
            )
        );
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(SOURCE_KEY, keccak256(abi.encodePacked(hex"1901", domain, message)));
        return SparkV15TeachingEnd.Proof(
            role, authority, app.disclosurePolicyId, validThrough, r, bytes32(uint256(s) | ((uint256(v) - 27) << 255))
        );
    }

    function _assertInvalidWageProofs(
        SparkV15Settlement.GroupAssessment memory assessment,
        SparkV15BookingOpening.OrdinarySettlementConsent memory consent,
        SparkV15SettlementOccurrences.LocalOneToOneRecords memory records,
        SparkV15SettlementOccurrences.SignedAttendance memory attendance,
        bytes32 commitment,
        uint64 validThrough
    ) private {
        uint256 packageId = app.packageId;
        uint256 held = funds.lessonReserved(LESSON);
        SparkV15BookingOpening.OrdinaryWageEvidence memory proof =
            _wageConsent(commitment, packageId, validThrough, VERIFIER_KEY);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryOneToOneWithAdoptedWage(LESSON, assessment, consent, proof, records, attendance);

        bytes32 role = app.applicationModule.SOURCE_ROLE();
        AVAIdentityRegistry identities = app.kernel.IDENTITY_REGISTRY();
        vm.prank(ADMIN);
        identities.assignSubject(
            VERIFIER, SparkV15.APP_ID, role, keccak256("verifier also assigned Source"), "test:interested-source"
        );
        proof = _wageConsent(commitment, packageId, validThrough, VERIFIER_KEY);
        vm.expectRevert(SparkV15Settlement.InterestedSettlementActor.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryOneToOneWithAdoptedWage(LESSON, assessment, consent, proof, records, attendance);

        proof = _wageConsent(commitment, packageId + 1, validThrough, SOURCE_KEY);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryOneToOneWithAdoptedWage(LESSON, assessment, consent, proof, records, attendance);

        proof = _wageConsent(keccak256("other exact wage terms"), packageId, validThrough, SOURCE_KEY);
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryOneToOneWithAdoptedWage(LESSON, assessment, consent, proof, records, attendance);

        proof.r = consent.r;
        proof.vs = consent.vs;
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryOneToOneWithAdoptedWage(LESSON, assessment, consent, proof, records, attendance);

        proof = _wageConsent(commitment, packageId, uint64(block.timestamp - 1), SOURCE_KEY);
        vm.expectRevert(SparkV15Booking.InvalidEvidence.selector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryOneToOneWithAdoptedWage(LESSON, assessment, consent, proof, records, attendance);
        require(!app.settlement.getGroupSettlement(LESSON).complete, "invalid proof completed settlement");
        require(funds.lessonReserved(LESSON) == held, "invalid proof consumed backing");
    }

    function _checkAdoptedEvidenceLifecycle(
        bytes32 obligationId,
        SparkV15BookingOpening.OrdinaryWageEvidence memory proof,
        SparkV15Payments.PaymentTerms memory terms
    ) private {
        SparkV15Settlement settlement = app.settlement;
        SparkV15SettlementAlternatives alternatives = settlement.ALTERNATIVES();
        uint256 packageId = app.packageId;
        (bytes32 retained, uint256 received) = alternatives.retainedPayment(terms, packageId);
        require(retained == obligationId && received == 0, "retention lost an effective adopted proof");
        require(
            settlement.adoptedWageEvidenceStatus(obligationId) == AVACoreTypes.EvidenceStatus.Active,
            "adoption window was treated as a post-adoption expiry"
        );
        bytes32 reason = keccak256("source withdrew the adopted evidence");
        AVACoreTypes.EvidenceLifecycleKind kind = AVACoreTypes.EvidenceLifecycleKind.Revoke;
        vm.expectPartialRevert(AVACoreTypes.NotAuthorised.selector);
        vm.prank(SOURCE);
        settlement.recordOrdinaryWageEvidenceLifecycle(obligationId, proof.sourceRole, proof.sourceAuthorityId, kind, reason);
        _allowSourceEvidenceLifecycle();
        vm.prank(SOURCE);
        settlement.recordOrdinaryWageEvidenceLifecycle(obligationId, proof.sourceRole, proof.sourceAuthorityId, kind, reason);
        require(
            settlement.adoptedWageEvidenceStatus(obligationId) == AVACoreTypes.EvidenceStatus.Revoked,
            "missing proof revocation"
        );
        vm.expectRevert(SparkV15SettlementAlternatives.InvalidEvidence.selector);
        alternatives.retainedPayment(terms, packageId);
    }

    function _allowSourceEvidenceLifecycle() private {
        _allowEvidenceLifecycle(app.applicationModule.SOURCE_ROLE());
    }

    function _allowEvidenceLifecycle(bytes32 role) private {
        AVAAuthorityMatrix matrix = app.kernel.AUTHORITY_MATRIX();
        vm.prank(ADMIN);
        matrix.setPermission(SparkV15.APP_ID, role, AVACoreTypes.ACTION_RECORD_EVIDENCE_LIFECYCLE, true);
    }

    function _wageConsent(bytes32 commitment, uint256 packageId, uint64 validThrough, uint256 signingKey)
        private
        view
        returns (SparkV15BookingOpening.OrdinaryWageEvidence memory consent)
    {
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        bytes32 authority = _subject(vm.addr(signingKey), role);
        bytes32 message = keccak256(abi.encode(
            keccak256("OrdinaryWageEvidence(bytes32 commitment,uint256 packageId,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"),
            commitment, packageId, role, authority, app.disclosurePolicyId, validThrough
        ));
        (bytes32 r, bytes32 vs) = _signSettlementMessage("Spark DAO Ordinary Wage Evidence", message, signingKey);
        return SparkV15BookingOpening.OrdinaryWageEvidence(role, authority, app.disclosurePolicyId, validThrough, r, vs);
    }

    function _localRecords(bytes32 formId, SparkV15Settlement.GroupAssessment memory assessment)
        private view returns (SparkV15SettlementOccurrences.LocalOneToOneRecords memory records,
            SparkV15SettlementOccurrences.SignedAttendance memory attendance)
    {
        SparkV15Booking.Teaching memory teaching = app.booking.getTeaching(LESSON);
        records.formId = formId;
        records.validThrough = uint64(block.timestamp + 1 hours);
        records.studentReportRef = keccak256("student's completed lesson report");
        records.coordinatorReportRef = keccak256("coordinator's verification of completion");
        bytes32 studentMessage = keccak256(abi.encode(
            keccak256("StudentCompletion(bytes32 lessonId,bytes32 formId,uint64 endedAt,uint256 endEvidenceId,bytes32 reportRef,uint64 validThrough)"),
            LESSON, formId, teaching.endedAt, teaching.endEvidenceId, records.studentReportRef, records.validThrough
        ));
        bytes32 coordinatorMessage = keccak256(abi.encode(
            keccak256("CoordinatorCompletionAndProposal(bytes32 lessonId,bytes32 formId,uint64 endedAt,uint256 endEvidenceId,bytes32 reportRef,uint64 validThrough,bytes32 proposalCommitment,bytes32 authorityId)"),
            LESSON, formId, teaching.endedAt, teaching.endEvidenceId, records.coordinatorReportRef, records.validThrough,
            app.settlement.proposalCommitment(LESSON, assessment), _subject(COORDINATOR, app.booking.COORDINATOR_ROLE())
        ));
        string memory domain = "Spark DAO One-to-One Settlement Records";
        (records.studentR, records.studentVS) = _signSettlementMessage(domain, studentMessage, STUDENT_KEY);
        (records.coordinatorR, records.coordinatorVS) = _signSettlementMessage(domain, coordinatorMessage, COORDINATOR_KEY);
        attendance.reportRef = keccak256("student's affirmative attendance report");
        attendance.validThrough = records.validThrough;
        bytes32 attendanceMessage = keccak256(abi.encode(
            keccak256("StudentAttendance(bytes32 lessonId,bytes32 formId,uint64 endedAt,uint256 endEvidenceId,bool attended,bytes32 reportRef,uint64 validThrough)"),
            LESSON, formId, teaching.endedAt, teaching.endEvidenceId, true, attendance.reportRef, attendance.validThrough
        ));
        (attendance.r, attendance.vs) = _signSettlementMessage(domain, attendanceMessage, STUDENT_KEY);
    }

    function _signSettlementMessage(string memory name, bytes32 message, uint256 signingKey)
        private view returns (bytes32 r, bytes32 vs)
    {
        bytes32 domain = keccak256(abi.encode(
            keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
            keccak256(bytes(name)), keccak256("1"), block.chainid, app.settlement
        ));
        (uint8 v, bytes32 recovery, bytes32 s) =
            vm.sign(signingKey, keccak256(abi.encodePacked(hex"1901", domain, message)));
        return (recovery, bytes32(uint256(s) | ((uint256(v) - 27) << 255)));
    }

    function _expectConsentRejection(
        SparkV15Settlement.GroupAssessment memory assessment,
        bytes32 basis,
        uint256 signingKey,
        uint256[] memory wageEvidence,
        bytes4 errorSelector
    ) private {
        SparkV15BookingOpening.OrdinarySettlementConsent memory consent = _settlementConsent(basis, signingKey);
        vm.expectPartialRevert(errorSelector);
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryOneToOneWithConsent(LESSON, assessment, consent, wageEvidence);
    }

    function _settlementConsent(bytes32 basis, uint256 signingKey)
        private
        view
        returns (SparkV15BookingOpening.OrdinarySettlementConsent memory consent)
    {
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        bytes32 authority = _subject(SOURCE, role);
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256("Spark DAO Ordinary Settlement"),
                keccak256("1"),
                block.chainid,
                app.settlement
            )
        );
        bytes32 message = keccak256(
            abi.encode(
                keccak256(
                    "OrdinarySettlementConsent(uint256 packageId,bytes32 lessonId,bytes32 basis,address approver,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId)"
                ),
                app.packageId,
                LESSON,
                basis,
                VERIFIER,
                role,
                authority,
                app.disclosurePolicyId
            )
        );
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(signingKey, keccak256(abi.encodePacked(hex"1901", domain, message)));
        bytes32 vs = bytes32(uint256(s) | ((uint256(v) - 27) << 255));
        return SparkV15BookingOpening.OrdinarySettlementConsent(role, authority, app.disclosurePolicyId, r, vs);
    }

    function _approveAndPayWage(bytes32 obligationId) private {
        _payApprovedWage(obligationId, this.approveWage(obligationId));
    }

    function _payApprovedWage(bytes32 obligationId, uint256 requestId) private {
        SparkV15Payments.Obligation memory unpaid = app.payments.getObligation(obligationId);
        require(unpaid.destination == TUTOR && unpaid.terms.dueAt == DUE, "wrong wage destination or date");
        require(unpaid.correctAmount == WAGE && unpaid.paid == 0, "wage not outstanding");
        require(token.balanceOf(TUTOR) == 0 && token.balanceOf(address(funds)) == 200, "approval moved cash");
        require(funds.paymentReserved(obligationId) == WAGE && funds.reservedUnits() == 78, "wrong unpaid backing");

        vm.warp(DUE);
        vm.prank(EXECUTOR);
        uint256 receiptId = app.payments.pay(requestId, WAGE);
        this.assertWageReceipt(obligationId, requestId, receiptId);
    }

    function assertWageReceipt(bytes32 obligationId, uint256 requestId, uint256 receiptId) external view {
        SparkV15Payments.PaymentReceipt memory receipt = app.payments.getReceipt(receiptId);
        require(receipt.obligationId == obligationId && receipt.approvalRequestId == requestId, "wrong receipt scope");
        require(
            receipt.executor == EXECUTOR && receipt.recipient == TUTOR && receipt.creditAccount == bytes32(0),
            "wrong receipt actors"
        );
        require(receipt.amount == WAGE && receipt.paidAt == DUE, "wrong receipt amount or date");
        require(app.payments.getApproval(requestId).paid == WAGE, "approval balance unchanged");
        require(app.payments.getObligation(obligationId).paid == WAGE, "obligation balance unchanged");
        require(token.balanceOf(TUTOR) == WAGE && token.balanceOf(address(funds)) == 192, "wage did not transfer");
        require(funds.paymentReserved(obligationId) == 0 && funds.reservedUnits() == 70, "wage backing not consumed");
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

    function _book(SparkV15Settlement.GroupAssessment memory assessment) private returns (bytes32 formId) {
        return _bookWithAcceptances(assessment, BookingPath.Recorded);
    }

    function _bookWithAcceptances(SparkV15Settlement.GroupAssessment memory assessment, BookingPath path)
        private
        returns (bytes32 formId)
    {
        return _bookWithChangeTerms(assessment, path, bytes32(0));
    }

    function _bookWithChangeTerms(
        SparkV15Settlement.GroupAssessment memory assessment, BookingPath path, bytes32 changeTermsRef
    ) private returns (bytes32 formId) {
        return _bookWithChangeTerms(assessment, path, changeTermsRef, SparkV15FundingCases(address(0)));
    }

    function _bookWithChangeTerms(
        SparkV15Settlement.GroupAssessment memory assessment,
        BookingPath path,
        bytes32 changeTermsRef,
        SparkV15FundingCases coverage
    ) private returns (bytes32 formId)
    {
        SparkV15Booking.LessonTerms memory lesson = _ordinaryLessonTerms(assessment);
        vm.prank(COORDINATOR);
        app.booking.publishLesson(lesson);

        SparkV15Funds.RechargeDebit[] memory debits = new SparkV15Funds.RechargeDebit[](1);
        debits[0] = SparkV15Funds.RechargeDebit(_rechargePayer(), FEE);
        SparkV15Booking.PlaceTerms memory place = _ordinaryPlaceTerms(debits);
        place.changeTermsRef = changeTermsRef;
        vm.prank(COORDINATOR);
        formId = app.booking.publishForm(LESSON, place);
        _provideTerms(formId, CUSTOMER);
        _provideTerms(formId, TUTOR);

        token.mint(PROVIDER, 180);
        vm.prank(PROVIDER);
        require(token.transfer(address(funds), 180), "provider backing transfer failed");
        bytes32[] memory forms = new bytes32[](1);
        forms[0] = formId;
        bytes32 inventory = keccak256("verified concurrent customer and tutor funding cases");
        SparkV15FundingCases.FundingScenario[] memory scenarios;
        if (address(coverage) != address(0)) {
            scenarios = _ordinaryCompensationScenarios(coverage, formId, forms);
            inventory = coverage.inventoryReference(LESSON, scenarios);
        }
        uint256 funding = _evidence(app.booking.prefundingCommitment(LESSON, forms, LESSON_BACKING, inventory));
        vm.record();
        vm.prank(VERIFIER);
        app.booking.verifyPrefunding(LESSON, forms, LESSON_BACKING, inventory, funding);
        uint256 written = _nonzeroWrittenWords(address(app.booking));
        if (address(coverage) != address(0)) coverage.retainInventory(LESSON, scenarios);
        emit log_named_uint("Single-place prefunding Booking storage words updated", written);
        require(written <= 5, "single-place prefunding stored a duplicate plan");
        require(funds.lessonReserved(LESSON) == LESSON_BACKING, "prefunding not reserved");
        bytes32[] memory plan = app.booking.getPlannedForms(LESSON);
        require(plan.length == 1 && plan[0] == formId, "funded form missing from plan");
        require(app.booking.getConfirmedForms(LESSON).length == 0, "prefunding confirmed a form");
        (bytes32 fundedForm, uint64 confirmedAt) = app.booking.getStudentConfirmation(LESSON, STUDENT);
        require(fundedForm == formId && confirmedAt == 0, "premature confirmation or wrong form");
        (fundedForm, confirmedAt) = app.booking.getStudentConfirmation(LESSON, PAYER);
        require(fundedForm == 0 && confirmedAt == 0, "credit payer treated as the funded student");

        vm.warp(EPOCH + 1);
        if (path != BookingPath.Recorded) {
            _confirmWithAcceptances(formId, funding, debits, path == BookingPath.Withdrawn);
        }
        if (path != BookingPath.Signed) {
            vm.prank(PROVIDER);
            app.booking.signTeachingAgreement(LESSON);
            vm.prank(TUTOR);
            app.booking.signTeachingAgreement(LESSON);
            _accept(formId, SparkV15Booking.Acceptance.Provider, PROVIDER);
            _accept(formId, SparkV15Booking.Acceptance.Tutor, TUTOR);
            _accept(formId, SparkV15Booking.Acceptance.Customer, CUSTOMER);
            _accept(formId, SparkV15Booking.Acceptance.Payer, PAYER);
            vm.prank(COORDINATOR);
            app.booking.confirmPlace(formId, bytes32(0), 0, debits);
        }
        require(app.booking.getForm(formId).confirmation.debitedUnits == FEE, "form not charged");
        require(funds.creditBalance(place.creditAccount) == 0, "wrong debit account balance");
        bytes32[] memory confirmed = app.booking.getConfirmedForms(LESSON);
        require(confirmed.length == 1 && confirmed[0] == formId, "confirmed form missing from plan");
        (fundedForm, confirmedAt) = app.booking.getStudentConfirmation(LESSON, STUDENT);
        require(fundedForm == formId && confirmedAt == EPOCH + 1, "wrong student confirmation");
    }

    function _nonzeroWrittenWords(address account) private returns (uint256 count) {
        (, bytes32[] memory writes) = vm.accesses(account);
        for (uint256 i; i < writes.length; ++i) {
            if (vm.load(account, writes[i]) == bytes32(0)) continue;
            bool first = true;
            for (uint256 j; j < i; ++j) {
                if (writes[j] == writes[i]) {
                    first = false;
                    break;
                }
            }
            if (first) ++count;
        }
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

    function _ordinaryCompensationScenarios(
        SparkV15FundingCases coverage,
        bytes32 formId,
        bytes32[] memory forms
    ) private pure returns (SparkV15FundingCases.FundingScenario[] memory scenarios) {
        scenarios = new SparkV15FundingCases.FundingScenario[](1);
        scenarios[0].teachingBegan = true;
        scenarios[0].forms = forms;
        scenarios[0].outcomes = new bytes32[](1);
        scenarios[0].outcomes[0] = coverage.deliveryOutcome(
            formId, uint8(SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered)
        );
        scenarios[0].expenses = new SparkV15FundingCases.Expense[](3);
        scenarios[0].expenses[0].referenceId = coverage.bookingExposureReference(formId, 0);
        scenarios[0].expenses[0].units = 10;
        scenarios[0].expenses[1].referenceId = coverage.bookingExposureReference(formId, 1);
        scenarios[0].expenses[1].units = FEE;
        scenarios[0].expenses[2].referenceId = keccak256("separately agreed teacher wage");
        scenarios[0].expenses[2].units = WAGE;
    }

    function _invalidatePrefunding(AVACoreTypes.EvidenceLifecycleKind kind, uint256 replacement) private {
        bytes32 role = app.booking.VERIFIER_ROLE();
        _allowEvidenceLifecycle(role);
        bytes32 authority = _subject(REVIEWER, role);
        IInstalledBookingPrefunding module = _prefundingModule();
        vm.prank(REVIEWER);
        module.recordEvidenceLifecycle(LESSON, role, authority, kind, replacement, keccak256("independent basis review"));
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

    function _confirmWithAcceptances(
        bytes32 formId, uint256 funding, SparkV15Funds.RechargeDebit[] memory debits, bool withdraw
    ) private {
        IOrdinaryBookingAcceptances entry = IOrdinaryBookingAcceptances(address(app.booking));
        bytes memory three = bytes.concat(
            _signBookingConsent(formId, funding, 0, PROVIDER_KEY, false),
            _signBookingConsent(formId, funding, 1, TUTOR_KEY, false),
            _signBookingConsent(formId, funding, 2, CUSTOMER_KEY, false)
        );
        bytes memory agreements = bytes.concat(
            _signBookingConsent(formId, funding, 0, PROVIDER_KEY, true),
            _signBookingConsent(formId, funding, 1, TUTOR_KEY, true)
        );
        vm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
        vm.prank(COORDINATOR);
        entry.confirmOrdinaryPlaceWithAcceptances(formId, debits, three, agreements);
        require(app.booking.getForm(formId).confirmation.confirmedAt == 0, "a required assent is missing");
        require(funds.creditBalance(funds.creditAccount(PAYER)) == FEE, "failed confirmation debited payer");
        bytes memory all = bytes.concat(three, _signBookingConsent(formId, funding, 3, PAYER_KEY, false));
        require(app.booking.teachingAgreementSignedAt(LESSON, TUTOR) == 0, "unsigned adoption appeared on chain");
        if (withdraw) {
            SparkV15BookingOpening opening = app.booking.OPENING();
            vm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
            vm.prank(COORDINATOR);
            opening.withdrawUnusedBookingAcceptance(formId, SparkV15Booking.Acceptance.Tutor);
            vm.prank(TUTOR);
            opening.withdrawUnusedBookingAcceptance(formId, SparkV15Booking.Acceptance.Tutor);
            vm.expectRevert(SparkV15Booking.InvalidAcceptance.selector);
            vm.prank(COORDINATOR);
            entry.confirmOrdinaryPlaceWithAcceptances(formId, debits, all, agreements);
            require(funds.creditBalance(funds.creditAccount(PAYER)) == FEE, "withdrawal failed to block debit");
            return;
        }
        vm.prank(COORDINATOR);
        entry.confirmOrdinaryPlaceWithAcceptances(formId, debits, all, agreements);
        (address payer, uint64 adoptedAt) = app.booking.acceptances(formId, SparkV15Booking.Acceptance.Payer);
        require(payer == PAYER && adoptedAt == block.timestamp, "wrong first-adoption readback");
        require(app.booking.teachingAgreementSignedAt(LESSON, TUTOR) == adoptedAt, "tutor agreement adoption missing");
        require(app.booking.teachingAgreementSignedAt(LESSON, PROVIDER) == adoptedAt, "provider agreement adoption missing");
    }

    function _signBookingConsent(bytes32 formId, uint256 funding, uint8 role, uint256 key, bool teaching)
        private
        returns (bytes memory)
    {
        bytes32 domain = keccak256(abi.encode(
            keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
            keccak256("Spark DAO Booking Acceptance"), keccak256("1"), block.chainid, address(app.booking)
        ));
        bytes32 typehash = teaching
            ? keccak256("AdoptTeachingAgreement(bytes32 formId,uint256 fundingEvidenceId,uint8 role)")
            : keccak256("AdoptBookingAcceptance(bytes32 formId,uint256 fundingEvidenceId,uint8 role)");
        bytes32 message = keccak256(abi.encode(typehash, formId, funding, role));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, keccak256(abi.encodePacked(hex"1901", domain, message)));
        return abi.encodePacked(r, bytes32(uint256(s) | ((uint256(v) - 27) << 255)));
    }

    function _teach(bytes32 formId) private {
        _teachWithAttendanceOption(formId, true);
    }

    function _teachWithAttendanceOption(bytes32 formId, bool recordAttendance) private {
        _teachWithReports(formId, recordAttendance, true);
    }

    function _teachWithReports(bytes32 formId, bool recordAttendance, bool recordFeedback) private {
        _startTeaching(formId);
        _finishTeaching(formId, recordAttendance, recordFeedback);
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

    function _recordStartNotices(bytes32 formId) private {
        SparkV15Booking booking = app.booking;
        bytes32 notice = keccak256("verified delivery on the agreed channels");
        uint256 evidenceId = _evidence(booking.studentNoticeCommitment(formId, EPOCH + 1, notice));
        vm.prank(COORDINATOR);
        booking.recordStudentNotice(formId, EPOCH + 1, notice, evidenceId);
        evidenceId = _evidence(booking.tutorNoticeCommitment(LESSON, TUTOR_CHANNEL, EPOCH + 1, notice));
        vm.prank(COORDINATOR);
        booking.recordTutorNotice(LESSON, TUTOR_CHANNEL, EPOCH + 1, notice, evidenceId);
    }

    function _startObservation(bytes32 conflict) private view returns (SparkV15Booking.StartObservation memory) {
        address[] memory present = new address[](1);
        present[0] = STUDENT;
        return SparkV15Booking.StartObservation(
            START, true, present, keccak256("observed actual teaching start"), conflict
        );
    }

    function _startTeaching(bytes32 formId) private {
        _recordStartNotices(formId);
        _observeActualStart();
    }

    function _observeActualStart() private {
        vm.warp(START);
        _recordLegacyStart(_startObservation(bytes32(0)));
        require(
            app.booking.getTeaching(LESSON).startPermission == SparkV15Booking.StartPermission.Permitted,
            "start not permitted"
        );
    }

    function _recordLegacyStart(SparkV15Booking.StartObservation memory observation) private {
        SparkV15Booking booking = app.booking;
        uint256 evidenceId = _evidence(booking.teachingStartCommitment(LESSON, observation));
        vm.prank(VERIFIER);
        booking.recordTeachingStarted(LESSON, observation, evidenceId);
    }

    function _recordAdoptedStart(SparkV15Booking.StartObservation memory observation) private {
        SparkV15TeachingEnd occurrenceModule = app.booking.OPENING().TEACHING_END();
        SparkV15TeachingEnd.Proof memory proof =
            _teachingStartProof(occurrenceModule, observation, uint64(block.timestamp + 1));
        vm.prank(VERIFIER);
        occurrenceModule.recordOrdinaryTeachingStarted(LESSON, observation, proof);
    }

    function _teachingStartProof(
        SparkV15TeachingEnd occurrenceModule,
        SparkV15Booking.StartObservation memory observation,
        uint64 validThrough
    ) private view returns (SparkV15TeachingEnd.Proof memory) {
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        bytes32 authority = _subject(SOURCE, role);
        bytes32 commitment = app.booking.teachingStartCommitment(LESSON, observation);
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256("Spark DAO Teaching Start Evidence"), keccak256("1"), block.chainid, address(occurrenceModule)
            )
        );
        bytes32 message = keccak256(
            abi.encode(
                keccak256("TeachingStartEvidence(uint256 packageId,bytes32 lessonId,bytes32 commitment,address verifier,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"),
                app.packageId, LESSON, commitment, VERIFIER, role, authority, app.disclosurePolicyId, validThrough
            )
        );
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(SOURCE_KEY, keccak256(abi.encodePacked(hex"1901", domain, message)));
        return SparkV15TeachingEnd.Proof(
            role, authority, app.disclosurePolicyId, validThrough, r, bytes32(uint256(s) | ((uint256(v) - 27) << 255))
        );
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

    function _settle(bytes32 formId, SparkV15Settlement.GroupAssessment memory assessment)
        private
        returns (bytes32 obligationId)
    {
        SparkV15Settlement.GroupPreview memory preview = _prepareSettlement(formId, assessment);
        uint256 approvalEvidence = _evidence(preview.basis);
        uint256[] memory paymentEvidence = new uint256[](1);
        paymentEvidence[0] = _evidence(app.payments.paymentEvidenceCommitment(preview.payments[0], preview.basis));
        vm.prank(VERIFIER);
        app.settlement.approveOrdinaryGroup(LESSON, assessment, approvalEvidence, paymentEvidence);
        return _settledObligation(formId, assessment.route, preview.basis, approvalEvidence);
    }

    function _prepareSettlement(bytes32 formId, SparkV15Settlement.GroupAssessment memory assessment)
        private
        returns (SparkV15Settlement.GroupPreview memory preview)
    {
        SparkV15Settlement settlement = app.settlement;
        SparkV15SettlementAlternatives alternatives = settlement.ALTERNATIVES();
        bytes32 report = keccak256("the agreed one-to-one lesson was completed");
        uint256 studentEvidence = _evidence(alternatives.completionCommitment(formId, report, STUDENT));
        vm.prank(STUDENT);
        alternatives.recordOneToOneCompletion(formId, report, studentEvidence);
        bytes32 proposal = settlement.proposalCommitment(LESSON, assessment);
        vm.prank(COORDINATOR);
        settlement.proposeOrdinaryGroup(LESSON, proposal);
        require(alternatives.studentCompletion(formId) == studentEvidence, "student confirmation missing");
        require(alternatives.coordinatorCompletion(formId) == 0, "phantom coordinator confirmation");
        SparkV15Settlement.GroupSettlement memory empty;
        require(
            keccak256(abi.encode(settlement.getGroupSettlement(LESSON))) == keccak256(abi.encode(empty)),
            "phantom final settlement"
        );
        vm.expectRevert(SparkV15Settlement.OrdinaryGroupConditionsNotMet.selector);
        settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);

        uint256 coordinatorEvidence = _evidence(alternatives.completionCommitment(formId, report, COORDINATOR));
        vm.prank(COORDINATOR);
        alternatives.recordOneToOneCompletion(formId, report, coordinatorEvidence);
        require(alternatives.coordinatorCompletion(formId) == coordinatorEvidence, "coordinator confirmation missing");
        preview = settlement.previewOrdinaryGroup(LESSON, assessment, VERIFIER);
        require(preview.payments.length == 1 && preview.totalTutorPay == WAGE, "wrong settlement preview");
    }

    function _settledObligation(bytes32 formId, SparkV15Settlement.Route route, bytes32 basis, uint256 approvalEvidence)
        private
        view
        returns (bytes32 obligationId)
    {
        SparkV15Settlement settlement = app.settlement;
        SparkV15Settlement.GroupSettlement memory result = settlement.getGroupSettlement(LESSON);
        require(result.complete && result.basis == basis && result.route == route, "wrong final settlement");
        require(result.approver == VERIFIER && result.evidenceId == approvalEvidence, "wrong final authority");
        SparkV15Settlement.GroupSettlement memory tranche = settlement.getSettlementTranche(basis);
        require(keccak256(abi.encode(result)) == keccak256(abi.encode(tranche)), "final tranche differs");
        SparkV15Settlement.SeatSettlement memory seat = settlement.getSeatSettlement(LESSON, formId);
        require(seat.debited == FEE && seat.feeDue == FEE && seat.tutorPay == WAGE, "wrong single-seat settlement");
        require(seat.refundObligationId == bytes32(0) && seat.tutorObligationId != bytes32(0), "wrong obligations");
        return seat.tutorObligationId;
    }

    function approveWage(bytes32 obligationId) external returns (uint256 requestId) {
        return _approvePayment(obligationId, WAGE, DUE);
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
