// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {DeployAVACore} from "@ava-protocol/contracts/script/DeployAVACore.s.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVAGovernanceKernel} from "@ava-protocol/contracts/src/core/AVAGovernanceKernel.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {DeploySparkV15OnExistingCore} from "../../../script/DeploySparkV15OnExistingCore.s.sol";
import {SparkV15} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {SparkV15Booking} from "../../../src/apps/spark/v15/SparkV15Booking.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {SparkV15LessonRemedies, SparkV15CustomerRedress} from "../../../src/apps/spark/v15/SparkV15LessonRemedies.sol";
import {
    SparkV15FundingCases,
    SparkV15MaterialProvisions
} from "../../../src/apps/spark/v15/SparkV15MaterialProvisions.sol";
import {SparkV15Materials} from "../../../src/apps/spark/v15/SparkV15Materials.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15PaymentTakeover} from "../../../src/apps/spark/v15/SparkV15PaymentTakeover.sol";
import {SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {
    SparkV15ReviewActions,
    SparkV15ReviewContext,
    SparkV15ConcernIntake
} from "../../../src/apps/spark/v15/SparkV15ReviewCases.sol";
import {SparkV15Settlement} from "../../../src/apps/spark/v15/SparkV15Settlement.sol";
import {MockERC20} from "../mocks/MockERC20.sol";

interface OriginalB1Vm {
    function chainId(uint256 value) external;
    function warp(uint256 value) external;
    function setEnv(string calldata name, string calldata value) external;
    function toString(address value) external pure returns (string memory);
    function prank(address actor) external;
    function expectRevert(bytes4 selector) external;
}

/// @notice In-process contract comparison to the archived B1 run-04 business inputs.
contract InstalledOriginalB1Test {
    OriginalB1Vm private constant vm = OriginalB1Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address private constant ADMIN = 0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266;
    address private constant SOURCE = 0x70997970C51812dc3A010C7d01b50e0d17dc79C8;
    address private constant VERIFIER = 0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC;
    address private constant REVIEWER = 0x15d34AAf54267DB7D7c367839AAf71A00a2C6A65;
    address private constant PROVIDER = 0x9965507D1a55bcC2695C58ba16FB37d819B0A4dc;
    address private constant COORDINATOR = 0x976EA74026E726554dB657fA54763abd0C3a0aa9;
    address private constant PARTNER = 0x14dC79964da2C08b23698B3D3cc7Ca32193d9955;
    address private constant EXECUTOR = 0x23618e81E3f5cdF7f54C3d65f7FBc0aBf5B21E8f;
    address private constant TUTOR = 0xa0Ee7A142d267C1f36714E4a8F75612F20a79720;
    address private constant T_PAYER = 0xBcd4042DE499D14e55001CcbB24a551F3b954096;
    address private constant T_CUSTOMER = 0x71bE63f3384f5fb98995898A86B02Fb2426c5788;
    address private constant T_STUDENT = 0xFABB0ac9d68B0B445fB7357272Ff202C5651694a;
    address private constant M_CUSTOMER = 0x1CBd3b2770909D4e10f157cABC84C7264073C9Ec;
    address private constant M_FIRST_HOLDER = 0xdF3e18d64BC6A983f673Ab319CCaE4f1a57C7097;
    address private constant MATERIALS_DAO = 0xcd3B766CCDd6AE721141F452C550Ca635964ce71;
    address private constant SERVICE_RESERVE = 0x2546BcD3c84621e976D8185a91A922aE77ECEc30;

    uint64 private constant T_START = 1795437133;
    uint64 private constant T_END = T_START + 100;
    uint64 private constant T_TRIGGER = 1795437236;
    uint64 private constant M_START = 1795437737;
    uint64 private constant M_END = M_START + 10;
    uint64 private constant M_APPROVAL_EXPIRY = M_END + 900;
    bytes32 private constant T100 = bytes32(uint256(100));
    bytes32 private constant M42 = bytes32(uint256(42));
    bytes32 private constant T_SEAT = keccak256("T100 one-to-one seat");
    bytes32 private constant M_SEAT = keccak256("M42 material seat");
    bytes32 private constant MAIN = bytes32(uint256(7));
    bytes32 private constant OTHER = bytes32(uint256(8));
    bytes32 private constant DOCS = keccak256("verified contractual terms");
    bytes32 private constant CHANNEL = keccak256("agreed tutor channel");
    bytes32 private constant MISSED = keccak256("the remaining agreed teaching was missed");

    DeploySparkV15OnExistingCore.Deployment private app;
    MockERC20 private token;
    SparkV15Booking private booking;
    SparkV15Funds private funds;
    SparkV15Payments private payments;
    SparkV15LessonRemedies private remedies;
    SparkV15CustomerRedress private redress;
    SparkV15Materials private materials;
    SparkV15MaterialProvisions private provisions;
    SparkV15FundingCases private funding;
    bytes32 private tForm;
    bytes32 private mForm;
    bytes32 private refund;
    bytes32 private first;
    bytes32 private second;

    event Checkpoint(string stage, uint256 cash, uint256 reserved, uint256 tHold, uint256 mHold, uint256 mBeyond);

    function setUp() public {
        vm.chainId(31337);
        vm.warp(T_START - 2410);
        DeployAVACore.Deployment memory core = new DeployAVACore().run(ADMIN);
        token = new MockERC20("Fixture USD", "TUSD", 6);
        _env("AVA_ROOT_ADMIN", ADMIN);
        _env("AVA_EXISTING_KERNEL", address(core.kernel));
        _env("AVA_EXISTING_REQUESTS", address(core.requests));
        _env("SPARK_V15_TOKEN", address(token));
        _env("SPARK_V15_COURSE_PROVIDER", PROVIDER);
        _env("SPARK_V15_BOOKING_COORDINATOR", COORDINATOR);
        _env("SPARK_V15_CORE_PARTNER", PARTNER);
        _env("SPARK_V15_SOURCE", SOURCE);
        _env("SPARK_V15_VERIFIER", VERIFIER);
        _env("SPARK_V15_ALLOCATOR", PROVIDER);
        _env("SPARK_V15_REVIEWER", REVIEWER);
        _env("SPARK_V15_ALTERNATIVE_CONTACT", EXECUTOR);
        _env("SPARK_V15_MATERIALS_DAO", MATERIALS_DAO);
        _env("SPARK_V15_SERVICE_RESERVE", SERVICE_RESERVE);
        app = new DeploySparkV15OnExistingCore().run();
        booking = app.booking;
        payments = app.payments;
        funds = payments.FUNDS();
        remedies = SparkV15LessonRemedies(address(app.settlement.remedyPolicy()));
        redress = remedies.customerRedress();
        provisions = SparkV15MaterialProvisions(funds.materialProvisions());
        materials = provisions.MATERIALS();
        funding = provisions.FUNDING_CASES();
        require(app.requests == core.requests && address(booking.FUNDS()) == address(funds), "installed shared vault");
        require(funds.materialBookingCoverage() == address(funding), "installed booking coverage");
    }

    function testOriginalB1ContractSequence() public {
        _bookT100();
        _reachT100AcceptedRedress();
        _bookM42();
        _establishM42Entitlements();

        vm.warp(1795437752);
        uint256 oldApproval = _approve(first, 2, M_APPROVAL_EXPIRY);
        vm.warp(1795437760);
        uint256 nextApproval = _approve(second, 4, M_APPROVAL_EXPIRY);
        _checkpoint("both unpaid material approvals", 202, 198);
        require(funds.lessonReserved(T100) == 8 && funds.lessonFeeBalance(T100) == 2, "T100 backing");
        require(funds.lessonReserved(M42) == 182 && funds.paymentReserved(refund) == 2, "M42 and refund backing");
        require(funds.paymentReserved(first) == 2 && funds.paymentReserved(second) == 4, "material backing");
        require(funding.independentTeachingCosts(M42) == 124, "M42 independent costs");
        _materialProtection(12);

        vm.warp(1795437764);
        vm.prank(PROVIDER);
        redress.issueCourseCredit(tForm);
        require(funds.compensationCreditRemaining(T100, T_SEAT) == 4, "T100 accepted course credit");
        require(funds.creditBalance(funds.creditAccount(T_CUSTOMER)) == 4, "T100 credit in customer account");
        _checkpoint("T100 course credit issued", 202, 202);

        vm.warp(1795437774);
        uint256 oldReceipt = _pay(oldApproval, first, 2, M_FIRST_HOLDER, bytes32(0));
        require(provisions.getMaterialReceipt(oldReceipt).verifiedAt == 0, "transfer alone did not verify");
        _checkpoint("first material payment", 200, 200);
        _materialProtection(12);

        vm.warp(1795437778);
        _verify(oldReceipt, first);
        vm.warp(1795437779);
        _checkpoint("first receipt available before second payment", 200, 200);
        _materialProtection(10);
        require(provisions.paymentProtection(M42, second, 4) == 6, "proposed second material protection");
        require(funds.paymentReserved(second) == 4, "unspent second assignment");
        _assertLiveApproval(nextApproval, second, 4, PARTNER);
        uint256 nextReceipt = _pay(nextApproval, second, 4, PARTNER, bytes32(0));
        require(funds.paymentReserved(second) == 0, "second assignment was consumed");
        require(provisions.getMaterialReceipt(nextReceipt).verifiedAt == 0, "second transfer alone did not verify");
        _checkpoint("second material payment", 196, 196);

        vm.warp(1795437782);
        _verify(nextReceipt, second);
        _materialProtection(6);
        require(token.balanceOf(M_FIRST_HOLDER) == 2 && token.balanceOf(PARTNER) == 4, "actual material balances");
        _checkpoint("both material receipts recognised", 196, 196);
        _payT100Refund();
        require(provisions.getMaterialReceipt(oldReceipt).verifiedAt == 1795437778, "first receipt changed");
        require(provisions.getMaterialReceipt(nextReceipt).verifiedAt == 1795437782, "second receipt changed");
    }

    function testInstalledMaterialTakeoverUsesTheChargedFormAndKeepsTheDelegatedReceipt() public {
        _bookT100();
        _reachT100AcceptedRedress();
        _bookM42();
        bytes32 scope = _recordM42Scope();
        vm.prank(M_FIRST_HOLDER);
        provisions.agreeMaterialRecipient(scope, M_CUSTOMER);
        first = _entitlement(scope, M_FIRST_HOLDER, M_CUSTOMER, 2);
        second = _entitlement(scope, PARTNER, PARTNER, 4);
        bytes32 termsId = _publishReviewContacts(M42, mForm, M_END + 20_000);
        bytes32 unrelatedTerms = _publishReviewContacts(M42, tForm, M_END + 20_000);

        vm.warp(1795437752);
        uint256 approval = _approve(first, 2, M_APPROVAL_EXPIRY);
        vm.warp(1795437764);
        vm.prank(PROVIDER);
        redress.issueCourseCredit(tForm);
        vm.warp(1795437774);
        uint256 receipt = _pay(approval, first, 1, M_CUSTOMER, bytes32(0));
        vm.warp(1795437778);
        _verify(receipt, first);
        uint64 deadline = M_END + 1000;
        vm.warp(deadline + 1);

        SparkV15PaymentTakeover.Input memory input;
        input.termsId = unrelatedTerms;
        input.obligationId = first;
        input.takenOverAt = deadline + 1;
        input.responsible = COORDINATOR;
        input.assignedAt = deadline + 1;
        input.newActionDate = deadline + 110;
        input.progress = keccak256("one paid to the designated wallet and one overdue");
        input.notice = SparkV15ReviewContext.Notice(keccak256("notified the materials payer and holder"), deadline + 1);
        input.unpaidAtDeadline = 1;
        input.unpaidAtTakeover = 1;
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        app.paymentTakeover.takeoverCommitment(input, PARTNER);

        input.termsId = termsId;
        input.unpaidAtTakeover = 3;
        vm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        app.paymentTakeover.takeoverCommitment(input, PARTNER);
        input.unpaidAtTakeover = 1;
        uint256 proof = _evidence(app.paymentTakeover.takeoverCommitment(input, PARTNER));
        bytes32 authority = _subject(PARTNER, keccak256("ava.spark.role.core-partner.v1.5"));
        vm.prank(PARTNER);
        bytes32 id = app.paymentTakeover.record(input, proof, authority);
        SparkV15PaymentTakeover.Record memory saved = app.paymentTakeover.get(id);
        SparkV15Payments.Obligation memory item = payments.getObligation(first);
        require(saved.obligationId == first && saved.cutoff == deadline, "wrong materials clock or part");
        require(item.beneficiary == M_FIRST_HOLDER && item.destination == M_CUSTOMER, "entitlement or collection changed");
        require(item.paid == 1 && funds.paymentReserved(first) == 1, "takeover changed the original unpaid share");
        require(funds.paymentReserved(second) == 4 && token.balanceOf(address(funds)) == 201, "shared backing changed");
        require(payments.getReceipt(receipt).recipient == M_CUSTOMER && payments.getApproval(approval).paid == 1,
            "takeover changed actual receipt or approval"
        );
    }

    function _bookT100() private {
        vm.warp(T_START - 2400);
        _publishLesson(T100, T_SEAT, T_START, T_END, bytes32(0));
        SparkV15Funds.RechargeDebit[] memory debit = _recharge(T_PAYER, T_START - 200);
        tForm = _publishForm(T100, T_SEAT, T_CUSTOMER, T_PAYER, T_STUDENT, bytes32(0), debit);
        _provideTerms(tForm, T_CUSTOMER);
        token.mint(PROVIDER, 194);
        vm.prank(PROVIDER);
        require(token.transfer(address(funds), 194), "original provider deposit");
        _verifyPrefunding(T100, tForm, 6, DOCS);
        vm.warp(T_START - 2300);
        _signAndConfirm(T100, tForm, T_CUSTOMER, T_PAYER, debit);
        _publishRedress(tForm, T_END);
        _checkpoint("T100 confirmed", 198, 10);
    }

    function _reachT100AcceptedRedress() private {
        _teach(T100, tForm, T_STUDENT, T_START, T_END);
        uint256 proof = _evidence(booking.tutorDeliveryCommitment(T100, false, DOCS));
        vm.prank(TUTOR);
        booking.recordTutorDelivery(T100, false, DOCS, proof);
        proof = _evidence(booking.attendanceCommitment(tForm, true, DOCS));
        vm.prank(T_STUDENT);
        booking.recordAttendance(tForm, true, DOCS, proof);
        SparkV15Booking.ServiceStatus status = SparkV15Booking.ServiceStatus.PartiallyDelivered;
        proof = _evidence(booking.serviceFeedbackCommitment(tForm, status, DOCS, MISSED));
        vm.prank(T_STUDENT);
        booking.recordServiceFeedback(tForm, status, DOCS, MISSED, proof);
        _recordT100Fault();

        SparkV15CustomerRedress.RefundBasis route = SparkV15CustomerRedress.RefundBasis.OriginalRelief;
        (SparkV15CustomerRedress.RefundAssessment memory assessment, SparkV15Payments.PaymentTerms memory terms) =
            redress.previewRefund(tForm, route, VERIFIER);
        require(assessment.principal == 2 && assessment.grossCreditRestoration == 2, "T100 original refund assessment");
        require(terms.recipient == T_PAYER && terms.originalDebitAmount == 4, "T100 original payer and debit");
        require(terms.originalDebitAccount == funds.creditAccount(T_PAYER), "T100 original debit account");
        require(terms.dueAt == 1795523636 && terms.executionDeadline == 1795696436, "T100 original refund clock");
        proof = _evidence(assessment.basis);
        bytes32 authority = _subject(VERIFIER, booking.VERIFIER_ROLE());
        vm.prank(VERIFIER);
        uint256 index = redress.assessRefund(tForm, route, proof, authority);
        proof = _evidence(payments.paymentEvidenceCommitment(terms, assessment.basis));
        vm.prank(VERIFIER);
        refund = redress.establishRefundPayment(tForm, index, proof);
        vm.warp(1795437237);
        vm.prank(T_CUSTOMER);
        redress.acceptStandardCompensation(tForm);
        require(redress.getRedress(tForm).acceptedBy == T_CUSTOMER, "T100 customer accepted compensation");
        require(funds.compensationCreditRemaining(T100, T_SEAT) == 0, "acceptance alone did not issue credit");
        require(funds.lessonReserved(T100) == 8 && funds.paymentReserved(refund) == 2, "T100 separate refund backing");
        _assertRefundStatus(0);
        _checkpoint("T100 refund established and standard compensation accepted", 198, 10);
    }

    function _recordT100Fault() private {
        bytes32 concernRef = keccak256("T100 partial delivery concern");
        bytes32 caseId = app.cases.caseIdFor(T100, concernRef);
        SparkV15ConcernIntake intake = app.cases.INTAKE();
        bytes32 termsId = _publishReviewContacts(T100, tForm, T_END + 20_000);

        address[] memory parties = new address[](3);
        parties[0] = T_STUDENT;
        parties[1] = T_CUSTOMER;
        parties[2] = TUTOR;
        SparkV15ReviewContext.ConcernInput memory concern = SparkV15ReviewContext.ConcernInput(
            termsId,
            concernRef,
            bytes32(0),
            COORDINATOR,
            SparkV15ReviewContext.ConcernSubject.StudentService,
            SparkV15ReviewContext.AlternativeGround.None,
            keccak256("student reported missed agreed teaching"),
            tForm,
            parties
        );
        uint256 proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_RECEIVE_CONCERN, T_STUDENT, keccak256(abi.encode(concern))
        );
        vm.prank(T_STUDENT);
        intake.receiveConcern(concern, proof);

        SparkV15LessonRemedies.AffectedPlace[] memory affected = new SparkV15LessonRemedies.AffectedPlace[](1);
        affected[0] = SparkV15LessonRemedies.AffectedPlace(
            tForm,
            SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered,
            SparkV15LessonRemedies.Participation.AttendedAsAgreed,
            2,
            true,
            keccak256("verified partial teaching and agreed attendance")
        );
        SparkV15LessonRemedies.FaultFinding memory finding = SparkV15LessonRemedies.FaultFinding(
            SparkV15LessonRemedies.FaultKind.MissedAgreedTeaching,
            true,
            TUTOR,
            DOCS,
            T_END,
            MISSED,
            keccak256("tutor was consulted"),
            keccak256("tutor had the opportunity to respond"),
            keccak256("student report and agreed preparation verified"),
            affected
        );
        bytes32 outcome = remedies.faultOutcome(caseId, finding);
        SparkV15ReviewContext.InitialInput memory initial = SparkV15ReviewContext.InitialInput(
            SparkV15ReviewContext.DisputedFinding.Fault,
            outcome,
            keccak256("missed agreed teaching attributable to the tutor"),
            keccak256("independent verification of tutor and student records")
        );
        vm.warp(T_END + 2);
        proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, REVIEWER, keccak256(abi.encode(initial))
        );
        bytes32 authority = _subject(REVIEWER, booking.VERIFIER_ROLE());
        vm.prank(REVIEWER);
        app.cases.decideInitial(caseId, initial, proof, authority);
        SparkV15ReviewContext.OriginalInput memory original = SparkV15ReviewContext.OriginalInput(
            termsId, concernRef, bytes32(0), bytes32(0), REVIEWER, T_END + 2, outcome, parties
        );
        proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, REVIEWER, keccak256(abi.encode(original))
        );
        vm.prank(REVIEWER);
        app.cases.retainOriginal(original, proof, authority);

        vm.warp(T_TRIGGER);
        vm.prank(REVIEWER);
        remedies.recordFault(caseId, finding);
        require(remedies.isOperative(caseId, 1) && remedies.placeFaultCase(tForm) == caseId, "T100 recognised finding");
    }

    function _publishReviewContacts(bytes32 lesson, bytes32 form, uint64 reviewDeadline)
        private
        returns (bytes32 termsId)
    {
        SparkV15ReviewContext.ReviewTerms memory publication = SparkV15ReviewContext.ReviewTerms(
            lesson, DOCS, form, PROVIDER, COORDINATOR, EXECUTOR, REVIEWER, VERIFIER, PARTNER, 0, 300, 0, reviewDeadline, 0
        );
        termsId = keccak256(abi.encode(publication));
        uint256 proof = _caseEvidence(termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, PROVIDER, termsId);
        bytes32 authority = _subject(PROVIDER, funds.CREDIT_PROVIDER_ROLE());
        SparkV15ConcernIntake intake = app.cases.INTAKE();
        vm.prank(PROVIDER);
        intake.publishContacts(publication, proof, authority);
    }

    function _bookM42() private {
        SparkV15Materials.HolderShare[] memory holders = new SparkV15Materials.HolderShare[](2);
        holders[0] = SparkV15Materials.HolderShare(M_FIRST_HOLDER, 1);
        holders[1] = SparkV15Materials.HolderShare(PARTNER, 2);
        SparkV15Materials.MaterialTerms[] memory bundle = new SparkV15Materials.MaterialTerms[](2);
        bundle[0] = SparkV15Materials.MaterialTerms(MAIN, 5, holders, new address[](0));
        bundle[1] = SparkV15Materials.MaterialTerms(OTHER, 5, holders, new address[](0));
        bytes32 bundleRef = keccak256("M42 material bundle");
        SparkV15Materials.Terms memory annex = SparkV15Materials.Terms(
            M42,
            bundleRef,
            PROVIDER,
            DOCS,
            DOCS,
            DOCS,
            M_END + 100,
            M_END + 1000,
            100,
            bundle,
            new SparkV15Materials.PriceRow[](0)
        );
        bytes32 annexRef = materials.termsCommitment(annex);
        _publishLesson(M42, M_SEAT, M_START, M_END, annexRef);
        vm.prank(M_FIRST_HOLDER);
        materials.acceptTerms(annexRef);
        vm.prank(PARTNER);
        materials.acceptTerms(annexRef);
        vm.prank(PROVIDER);
        materials.adoptTerms(annex);

        SparkV15Funds.RechargeDebit[] memory debit = _recharge(M_CUSTOMER, M_START);
        mForm = _publishForm(M42, M_SEAT, M_CUSTOMER, M_CUSTOMER, M_CUSTOMER, bundleRef, debit);
        _publishRedress(mForm, M_END);
        SparkV15FundingCases.FundingScenario[] memory scenarios = _mScenarios(annexRef);
        bytes32 inventoryRef = funding.inventoryReference(M42, scenarios);
        _verifyPrefunding(M42, mForm, 184, inventoryRef);
        _checkpoint("M42 prefunded before agreement", 202, 198);
        vm.prank(PROVIDER);
        funding.retainInventory(M42, scenarios);
        require(keccak256(abi.encode(funding.getScenarios(M42))) == keccak256(abi.encode(scenarios)), "M42 inventory");
        _provideTerms(mForm, M_CUSTOMER);
        _signAndConfirm(M42, mForm, M_CUSTOMER, M_CUSTOMER, debit);
        _checkpoint("M42 confirmed", 202, 198);

        _provision(
            MAIN, keccak256("M42 verified estimate 0x0000000000000000000000000000000000000000000000000000000000000007")
        );
        _provision(
            OTHER, keccak256("M42 verified estimate 0x0000000000000000000000000000000000000000000000000000000000000008")
        );
        require(provisions.provisioningNeed(M42) == 12, "M42 original two estimates");
    }

    function _mScenarios(bytes32 annexRef) private view returns (SparkV15FundingCases.FundingScenario[] memory result) {
        SparkV15FundingCases.Expense memory refundExposure = _exposure(0, 4);
        SparkV15FundingCases.Expense memory creditExposure = _exposure(1, 120);
        SparkV15FundingCases.Expense memory discountExposure = _exposure(2, 60);
        SparkV15FundingCases.Expense memory main = _materialExpense(MAIN, annexRef, keccak256("M42 main estimate"));
        SparkV15FundingCases.Expense memory other = _materialExpense(OTHER, annexRef, keccak256("M42 other estimate"));
        result = new SparkV15FundingCases.FundingScenario[](5);
        result[0] = _scenario(true, keccak256("M42 taught without relief"), 2);
        result[0].expenses[0] = main;
        result[0].expenses[1] = other;
        result[1] = _scenario(false, keccak256("M42 no-fault cancellation before delivery"), 1);
        result[1].expenses[0] = refundExposure;
        result[2] = _scenario(true, keccak256("M42 taught with full refund only"), 3);
        result[2].expenses[0] = refundExposure;
        result[2].expenses[1] = main;
        result[2].expenses[2] = other;
        result[3] = _scenario(true, keccak256("M42 taught with accepted standard compensation"), 4);
        result[3].expenses[0] = refundExposure;
        result[3].expenses[1] = creditExposure;
        result[3].expenses[2] = main;
        result[3].expenses[3] = other;
        result[4] = _scenario(false, keccak256("M42 no delivery with accepted standard compensation"), 3);
        result[4].expenses[0] = refundExposure;
        result[4].expenses[1] = creditExposure;
        result[4].expenses[2] = discountExposure;
    }

    function _exposure(uint8 category, uint128 units) private view returns (SparkV15FundingCases.Expense memory) {
        return SparkV15FundingCases.Expense(
            funding.bookingExposureReference(mForm, category),
            bytes32(0),
            bytes32(0),
            bytes32(0),
            units,
            new SparkV15FundingCases.MaterialPortion[](0)
        );
    }

    function _materialExpense(bytes32 material, bytes32 annexRef, bytes32 estimate)
        private
        view
        returns (SparkV15FundingCases.Expense memory)
    {
        SparkV15FundingCases.MaterialPortion[] memory portions = new SparkV15FundingCases.MaterialPortion[](1);
        portions[0] = SparkV15FundingCases.MaterialPortion(mForm, 6);
        return SparkV15FundingCases.Expense(estimate, bytes32(0), material, annexRef, 6, portions);
    }

    function _scenario(bool taught, bytes32 outcome, uint256 expenseCount)
        private
        view
        returns (SparkV15FundingCases.FundingScenario memory)
    {
        bytes32[] memory outcomes = new bytes32[](1);
        outcomes[0] = outcome;
        return SparkV15FundingCases.FundingScenario(
            taught, _onlyForm(mForm), outcomes, new SparkV15FundingCases.Expense[](expenseCount)
        );
    }

    function _establishM42Entitlements() private {
        bytes32 scope = _recordM42Scope();
        first = _entitlement(scope, M_FIRST_HOLDER, M_FIRST_HOLDER, 2);
        _checkpoint("M42 first entitlement", 202, 198);
        second = _entitlement(scope, PARTNER, PARTNER, 4);
        _checkpoint("M42 second entitlement", 202, 198);
    }

    function _recordM42Scope() private returns (bytes32 scope) {
        _teach(M42, mForm, M_CUSTOMER, M_START, M_END);
        SparkV15Materials.UseCheck memory use = SparkV15Materials.UseCheck(
            mForm,
            MAIN,
            M_START,
            M_END,
            SparkV15Materials.UseSource.LessonRecord,
            DOCS,
            keccak256("M42 verified dated use"),
            false,
            false,
            bytes32(0)
        );
        uint256 proof = _materialEvidence(materials.ACTION_VERIFY_USE(), abi.encode(use));
        vm.prank(COORDINATOR);
        materials.verifyUse(use, proof);

        vm.warp(M_END + 1);
        SparkV15Materials.GrossInput memory gross = SparkV15Materials.GrossInput(
            M42, MAIN, bytes32(0), keccak256("M42 original main charge"), M_END + 1, _onlyForm(mForm)
        );
        proof = _materialEvidence(materials.ACTION_RECORD_GROSS(), abi.encode(gross));
        vm.prank(COORDINATOR);
        scope = materials.recordGross(gross, proof);
        require(materials.getHistoricalCharge(scope, mForm).amount == 6, "M42 original gross charge");
        _checkpoint("M42 recorded actual gross", 202, 198);
    }

    function _entitlement(bytes32 scope, address holder, address recipient, uint128 expected)
        private
        returns (bytes32 obligationId)
    {
        SparkV15MaterialProvisions.EntitlementInput memory input = SparkV15MaterialProvisions.EntitlementInput(
            scope, holder, recipient, uint64(block.timestamp), M_END + 1100, keccak256("M42 verified holder shares")
        );
        (SparkV15Payments.PaymentTerms memory terms, bytes32 basis) = provisions.previewEntitlement(input, VERIFIER);
        require(terms.amount == expected && terms.recipient == recipient, "M42 entitlement amount and recipient");
        bytes32 schedule =
            keccak256(abi.encode(keccak256("spark.v1.5.material-schedule"), basis, input.verifiedAt, true));
        uint256 proof = _evidence(payments.paymentEvidenceCommitment(terms, schedule));
        bytes32 authority = _subject(VERIFIER, booking.VERIFIER_ROLE());
        vm.prank(VERIFIER);
        return provisions.establishEntitlement(input, proof, authority);
    }

    function _provideTerms(bytes32 formId, address customer) private {
        _recordProvisionOfTerms(formId, customer);
        _recordProvisionOfTerms(formId, TUTOR);
    }

    function _recordProvisionOfTerms(bytes32 formId, address recipient) private {
        uint256 proof = _evidence(booking.provisionCommitment(formId, recipient, DOCS));
        vm.prank(COORDINATOR);
        booking.recordTermsProvision(formId, recipient, DOCS, proof);
    }

    function _publishLesson(bytes32 id, bytes32 seat, uint64 start, uint64 end, bytes32 annexRef) private {
        bool materialLesson = id == M42;
        uint64 wageDue = start + 30 days;
        SparkV15Settlement.RefundTerms memory refundTerms = SparkV15Settlement.RefundTerms(
            DOCS,
            SparkV15Settlement.PaymentSchedule(end + 1, materialLesson ? end + 4 days : wageDue + 4 days, 0, 1 days)
        );
        SparkV15Settlement.TutorSeatTerms[] memory tutorSeats = new SparkV15Settlement.TutorSeatTerms[](1);
        tutorSeats[0] = SparkV15Settlement.TutorSeatTerms(seat, materialLesson ? 0 : 8, materialLesson ? 0 : 2);
        SparkV15Settlement.TutorPayTerms memory tutorPay = SparkV15Settlement.TutorPayTerms(
            DOCS, TUTOR, SparkV15Settlement.PaymentSchedule(wageDue, wageDue + 3 days, 0, 1 days), tutorSeats
        );
        SparkV15Booking.LessonTerms memory terms = SparkV15Booking.LessonTerms({
            lessonId: id,
            provider: PROVIDER,
            tutor: TUTOR,
            coordinator: COORDINATOR,
            startsAt: start,
            endsAt: end,
            rosterLockAt: 0,
            rosterRef: bytes32(0),
            timeZoneRef: keccak256("UTC"),
            tutorNoticeChannelRef: CHANNEL,
            tutorFee: materialLesson ? 0 : 2,
            tutorAgreementRef: DOCS,
            serviceTermsRef: app.settlement.refundTermsCommitment(id, refundTerms),
            tutorPayTermsRef: app.settlement.tutorPayTermsCommitment(id, tutorPay),
            providerResponsibilitiesRef: DOCS,
            tutorResponsibilitiesRef: DOCS,
            startTermsRef: DOCS,
            documentsRef: DOCS,
            materialsTermsRef: annexRef
        });
        vm.prank(COORDINATOR);
        booking.publishLesson(terms);
    }

    function _publishForm(
        bytes32 lessonId,
        bytes32 seat,
        address customer,
        address payer,
        address student,
        bytes32 bundleRef,
        SparkV15Funds.RechargeDebit[] memory debits
    ) private returns (bytes32) {
        bool materialLesson = lessonId == M42;
        SparkV15Booking.PlaceTerms memory terms = SparkV15Booking.PlaceTerms({
            placeId: seat,
            customer: customer,
            customerRepresentative: address(0),
            payer: payer,
            student: student,
            creditAccount: funds.creditAccount(payer),
            studentNoticeChannelRef: DOCS,
            normalFee: materialLesson ? 120 : 4,
            payableFee: 4,
            discountBasis: materialLesson ? keccak256("M42 agreed discount") : bytes32(0),
            rechargeDebitsHash: keccak256(abi.encode(debits)),
            materialsBundleRef: bundleRef,
            materialPayer: materialLesson ? PROVIDER : address(0),
            changeTermsRef: bytes32(0),
            remedyDiscountId: bytes32(0)
        });
        vm.prank(COORDINATOR);
        return booking.publishForm(lessonId, terms);
    }

    function _recharge(address payer, uint64 returnThrough)
        private
        returns (SparkV15Funds.RechargeDebit[] memory debit)
    {
        bytes32 authority = _subject(PROVIDER, funds.CREDIT_PROVIDER_ROLE());
        vm.prank(PROVIDER);
        bytes32 offer = funds.offerRecharge(SparkV15Funds.RechargeTerms(payer, 4, 4, returnThrough, DOCS), authority);
        token.mint(payer, 4);
        vm.prank(payer);
        token.approve(address(funds), 4);
        vm.prank(payer);
        uint256 receipt = funds.recharge(offer);
        debit = new SparkV15Funds.RechargeDebit[](1);
        debit[0] = SparkV15Funds.RechargeDebit(receipt, 4);
    }

    function _verifyPrefunding(bytes32 lessonId, bytes32 formId, uint128 amount, bytes32 ref) private {
        bytes32[] memory forms = _onlyForm(formId);
        uint256 proof = _evidence(booking.prefundingCommitment(lessonId, forms, amount, ref));
        vm.prank(VERIFIER);
        booking.verifyPrefunding(lessonId, forms, amount, ref, proof);
    }

    function _signAndConfirm(
        bytes32 lessonId,
        bytes32 formId,
        address customer,
        address payer,
        SparkV15Funds.RechargeDebit[] memory debits
    ) private {
        vm.prank(PROVIDER);
        booking.signTeachingAgreement(lessonId);
        vm.prank(TUTOR);
        booking.signTeachingAgreement(lessonId);
        vm.prank(PROVIDER);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Provider);
        vm.prank(TUTOR);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Tutor);
        vm.prank(customer);
        booking.acceptForm(formId, SparkV15Booking.Acceptance.Customer);
        if (customer != payer) {
            vm.prank(payer);
            booking.acceptForm(formId, SparkV15Booking.Acceptance.Payer);
        }
        vm.prank(COORDINATOR);
        booking.confirmPlace(formId, bytes32(0), 0, debits);
        require(booking.getForm(formId).confirmation.debitedUnits == 4, "original account debited four");
        require(funds.creditBalance(funds.creditAccount(payer)) == 0, "credit spent only from original account");
    }

    function _publishRedress(bytes32 formId, uint64 end) private {
        SparkV15CustomerRedress.RedressTerms memory terms = SparkV15CustomerRedress.RedressTerms(
            end + 7 days, end + 14 days, 1 days, 3 days, 0, 2 days, keccak256("original agreed teaching"), DOCS
        );
        uint256 proof = _evidence(redress.redressTermsCommitment(formId, terms));
        vm.prank(PROVIDER);
        redress.publishRedressTerms(formId, terms, proof);
    }

    function _provision(bytes32 material, bytes32 sourceRef) private {
        SparkV15MaterialProvisions.ProvisionInput memory input =
            SparkV15MaterialProvisions.ProvisionInput(mForm, material, 6, sourceRef);
        uint256 proof = _evidence(provisions.provisionEvidenceCommitment(input, VERIFIER));
        bytes32 authority = _subject(VERIFIER, booking.VERIFIER_ROLE());
        vm.prank(VERIFIER);
        provisions.recordProvision(input, proof, authority);
    }

    function _teach(bytes32 lessonId, bytes32 formId, address student, uint64 start, uint64 end) private {
        uint64 noticeAt = uint64(block.timestamp);
        uint256 proof = _evidence(booking.studentNoticeCommitment(formId, noticeAt, DOCS));
        vm.prank(COORDINATOR);
        booking.recordStudentNotice(formId, noticeAt, DOCS, proof);
        proof = _evidence(booking.tutorNoticeCommitment(lessonId, CHANNEL, noticeAt, DOCS));
        vm.prank(COORDINATOR);
        booking.recordTutorNotice(lessonId, CHANNEL, noticeAt, DOCS, proof);

        address[] memory attending = new address[](1);
        attending[0] = student;
        SparkV15Booking.StartObservation memory observation =
            SparkV15Booking.StartObservation(start, true, attending, DOCS, bytes32(0));
        proof = _evidence(booking.teachingStartCommitment(lessonId, observation));
        vm.warp(start);
        vm.prank(VERIFIER);
        booking.recordTeachingStarted(lessonId, observation, proof);
        proof = _evidence(booking.teachingEndCommitment(lessonId, end, DOCS));
        vm.warp(end);
        vm.prank(VERIFIER);
        booking.recordTeachingEnded(lessonId, end, DOCS, proof);
    }

    function _approve(bytes32 obligationId, uint128 amount, uint64 through) private returns (uint256 requestId) {
        SparkV15Payments.ApprovalTerms memory terms =
            SparkV15Payments.ApprovalTerms(obligationId, EXECUTOR, amount, through, 0);
        bytes32 parameters = payments.approvalParameters(terms);
        bytes32 commitment = app.requests
            .commitmentFor(
                SparkV15.APP_ID,
                address(payments),
                SparkV15.RESPONSE_APPROVE_PAYMENT,
                parameters,
                SparkV15.APPROVAL_BURDEN,
                through
            );
        uint256 stateId = _vest(_registerApproval(commitment));
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        bytes32 authority = _subject(SOURCE, role);
        AVARequestAllocation.RequestInput memory input = AVARequestAllocation.RequestInput(
            stateId, address(payments), SparkV15.RESPONSE_APPROVE_PAYMENT, parameters, SparkV15.APPROVAL_BURDEN, through
        );
        vm.prank(SOURCE);
        requestId = app.requests.createRequest(input, role, authority);
        role = app.applicationModule.ALLOCATOR_ROLE();
        authority = _subject(PROVIDER, role);
        vm.prank(PROVIDER);
        app.requests.approve(requestId, role, authority);
        AVARequestAllocation.RequestRecord memory allocated = app.requests.getRequest(requestId);
        require(
            allocated.allocator == PROVIDER && !allocated.consumed && !allocated.completed,
            "allocation before App adoption"
        );
        vm.prank(PROVIDER);
        payments.recordApproval(requestId, terms);
        AVARequestAllocation.RequestRecord memory complete = app.requests.getRequest(requestId);
        require(
            complete.input.recognisedStateId == stateId && complete.consumed && complete.completed,
            "Core consumed scope"
        );
        SparkV15Payments.Approval memory approval = payments.getApproval(requestId);
        require(
            approval.approver == PROVIDER && approval.paid == 0 && approval.authorityId == authority,
            "unpaid App approval"
        );
        require(keccak256(abi.encode(approval.terms)) == keccak256(abi.encode(terms)), "App adoption preserves scope");
    }

    function _registerApproval(bytes32 commitment) private returns (uint256) {
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        bytes32 authority = _subject(SOURCE, role);
        uint256 evidenceId = _evidence(commitment);
        AVAGovernanceKernel.GovernedObjectInput memory input = AVAGovernanceKernel.GovernedObjectInput({
            appId: SparkV15.APP_ID,
            workflowKey: SparkV15.WORKFLOW,
            packageId: app.packageId,
            roleKey: role,
            objectTypeKey: SparkV15.OBJECT_PAYMENT_APPROVAL,
            objectCommitment: commitment,
            parentObjectId: 0,
            subjectId: authority,
            evidenceReceiptId: evidenceId,
            disclosurePolicyId: app.disclosurePolicyId,
            metadataHash: commitment,
            authorityId: authority,
            uri: "local:spark-v15/b1-approval"
        });
        vm.prank(SOURCE);
        return app.kernel.registerGovernedObject(input);
    }

    function _vest(uint256 objectId) private returns (uint256 stateId) {
        bytes32 role = app.applicationModule.VERIFIER_ROLE();
        bytes32 authority = _subject(VERIFIER, role);
        AVAGovernanceKernel.RecognisedStateFormationInput memory formation =
            AVAGovernanceKernel.RecognisedStateFormationInput(
                objectId,
                role,
                authority,
                AVACoreTypes.Stage.Verification,
                AVACoreTypes.RecognisedStateStatus.Provisional,
                keccak256("B1 approval accepted"),
                "local:spark-v15/b1-recognition"
            );
        vm.prank(VERIFIER);
        stateId = app.kernel.formRecognisedState(formation);
        AVAGovernanceKernel.RecognisedStateTransitionInput memory transition =
            AVAGovernanceKernel.RecognisedStateTransitionInput(
                stateId,
                role,
                authority,
                AVACoreTypes.RecognisedStateStatus.Challengeable,
                keccak256("challengeable"),
                "local:spark-v15/m42-challengeable"
            );
        vm.prank(VERIFIER);
        app.kernel.transitionRecognisedState(transition);
        transition.toStatus = AVACoreTypes.RecognisedStateStatus.Vested;
        transition.reasonHash = keccak256("B1 approval vested");
        transition.reasonURI = "local:spark-v15/b1-vesting";
        vm.prank(VERIFIER);
        app.kernel.vestRecognisedState(transition);
    }

    function _assertLiveApproval(uint256 requestId, bytes32 obligationId, uint128 amount, address holder) private view {
        SparkV15Payments.Obligation memory item = payments.getObligation(obligationId);
        SparkV15Payments.Approval memory approval = payments.getApproval(requestId);
        SparkV15PaymentHolds.Status memory hold = app.holds.getStatus(obligationId);
        require(approval.terms.obligationId == obligationId && approval.terms.executor == EXECUTOR, "payment scope");
        require(approval.stoppedAt == 0 && approval.beneficiaryVersion == item.beneficiaryVersion, "current approval");
        require(item.beneficiary == holder && item.destination == holder, "current receivable destination");
        require(
            item.correctAmount - item.paid == amount && approval.terms.ceiling - item.paid == amount, "unpaid amount"
        );
        require(!hold.active && hold.activeFormalHolds == 0 && hold.firstFullReleaseAt == 0, "no effective hold");
        require(block.timestamp > item.eligibleFrom && block.timestamp < item.terms.executionDeadline, "eligible clock");
        require(block.timestamp <= approval.terms.validThrough, "approval current at execution");
    }

    function _pay(uint256 requestId, bytes32 obligationId, uint128 amount, address holder, bytes32 account)
        private
        returns (uint256 receiptId)
    {
        vm.prank(EXECUTOR);
        receiptId = payments.pay(requestId, amount);
        SparkV15Payments.PaymentReceipt memory receipt = payments.getReceipt(receiptId);
        require(receipt.obligationId == obligationId && receipt.approvalRequestId == requestId, "actual receipt scope");
        require(
            receipt.executor == EXECUTOR && receipt.recipient == holder && receipt.creditAccount == account,
            "receipt actors"
        );
        require(receipt.amount == amount && receipt.paidAt == block.timestamp, "receipt amount and payment time");
        require(payments.getApproval(requestId).paid == amount, "approval consumed by actual execution");
    }

    function _verify(uint256 receiptId, bytes32 obligationId) private {
        uint64 nowAt = uint64(block.timestamp);
        uint256 proof = _evidence(provisions.receiptEvidenceCommitment(receiptId, nowAt, VERIFIER));
        bytes32 authority = _subject(VERIFIER, booking.VERIFIER_ROLE());
        vm.prank(VERIFIER);
        provisions.verifyMaterialReceipt(receiptId, nowAt, proof, authority);
        SparkV15MaterialProvisions.MaterialReceipt memory receipt = provisions.getMaterialReceipt(receiptId);
        require(
            receipt.obligationId == obligationId && receipt.verifiedAt == nowAt, "recognised receipt time and scope"
        );
        require(
            receipt.paidAt < nowAt && receipt.verifiedBy == VERIFIER && receipt.evidenceId == proof,
            "independent verification"
        );
    }

    function _payT100Refund() private {
        SparkV15Payments.PaymentTerms memory terms = payments.getObligation(refund).terms;
        uint256 approval = _approve(refund, 2, terms.executionDeadline);
        vm.warp(terms.dueAt);
        bytes32 original = funds.creditAccount(T_PAYER);
        require(funds.creditBalance(original) == 0, "original account before refund");
        _pay(approval, refund, 2, T_PAYER, original);
        require(funds.creditBalance(original) == 2 && funds.paymentReserved(refund) == 0, "original account restored");
        require(funds.creditBalance(funds.creditAccount(T_CUSTOMER)) == 4, "the customer retains the separate credit");
        require(funds.compensationCreditRemaining(T100, T_SEAT) == 4, "seat retains the separate credit");
        _assertRefundStatus(2);
        _checkpoint("T100 original account refund", 196, 196);
    }

    function _assertRefundStatus(uint256 expectedReceived) private view {
        (uint256 assessments, uint256 amount, uint256 received) = redress.refundStatus(tForm);
        require(assessments == 1 && amount == 2 && received == expectedReceived, "T100 refund status");
    }

    function _materialProtection(uint256 expected) private view {
        require(provisions.paymentProtection(M42, bytes32(0), 0) == expected, "M42 material protection at observation");
    }

    function _checkpoint(string memory stage, uint256 expectedCash, uint256 expectedReserved) private {
        uint256 cash = token.balanceOf(address(funds));
        uint256 reserved = funds.reservedUnits();
        uint256 beyond = provisions.MATERIAL_BACKING().requiredBeyondLessonHold(M42, bytes32(0), 0, false);
        emit Checkpoint(stage, cash, reserved, funds.lessonReserved(T100), funds.lessonReserved(M42), beyond);
        require(cash == expectedCash && reserved == expectedReserved && beyond == 0, stage);
    }

    function _onlyForm(bytes32 formId) private pure returns (bytes32[] memory result) {
        result = new bytes32[](1);
        result[0] = formId;
    }

    function _caseEvidence(bytes32 subject, bytes32 action, address actor, bytes32 payload) private returns (uint256) {
        return _evidence(app.cases.evidenceCommitment(subject, action, actor, payload));
    }

    function _materialEvidence(bytes32 action, bytes memory payload) private returns (uint256) {
        return _evidence(materials.operationEvidenceCommitment(M42, action, COORDINATOR, keccak256(payload)));
    }

    function _evidence(bytes32 commitment) private returns (uint256) {
        AVAEvidenceRegistry registry = app.kernel.EVIDENCE_REGISTRY();
        bytes32 role = app.applicationModule.SOURCE_ROLE();
        bytes32 authority = _subject(SOURCE, role);
        AVAEvidenceRegistry.EvidenceRegistrationInput memory input = AVAEvidenceRegistry.EvidenceRegistrationInput({
            appId: SparkV15.APP_ID,
            workflowKey: SparkV15.WORKFLOW,
            packageId: app.packageId,
            roleKey: role,
            subjectId: authority,
            commitment: commitment,
            evidenceTypeHash: keccak256("independently verified synthetic course fact"),
            disclosurePolicyId: app.disclosurePolicyId,
            authorityId: authority,
            uri: "local:spark-v15/compensation-browser"
        });
        vm.prank(SOURCE);
        return registry.registerEvidence(input);
    }

    function _subject(address actor, bytes32 role) private view returns (bytes32) {
        return app.kernel.IDENTITY_REGISTRY().subjectOf(actor, SparkV15.APP_ID, role);
    }

    function _env(string memory key, address value) private {
        vm.setEnv(key, vm.toString(value));
    }
}
