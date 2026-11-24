// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {SparkV15, SparkV15ApplicationModule} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {ISparkV15BookingFunds, SparkV15Booking, SparkV15BookingOpening} from "../../../src/apps/spark/v15/SparkV15Booking.sol";
import {SparkV15BookingPrefunding} from "../../../src/apps/spark/v15/SparkV15BookingPrefunding.sol";
import {SparkV15CourseNotices} from "../../../src/apps/spark/v15/SparkV15CourseNotices.sol";
import {SparkV15TeachingEnd} from "../../../src/apps/spark/v15/SparkV15TeachingEnd.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {
    SparkV15MaterialBacking,
    SparkV15MaterialProvisions,
    SparkV15ObservedMaterialReceipts
} from "../../../src/apps/spark/v15/SparkV15MaterialProvisions.sol";
import {SparkV15MaterialRights} from "../../../src/apps/spark/v15/SparkV15MaterialRights.sol";
import {ISparkV15MaterialInterests, SparkV15Materials, SparkV15MaterialsUse} from "../../../src/apps/spark/v15/SparkV15Materials.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15PaymentObservations} from "../../../src/apps/spark/v15/SparkV15PaymentObservations.sol";
import {ISparkV15AdoptedDispositions, SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {SparkV15Returns} from "../../../src/apps/spark/v15/SparkV15Returns.sol";
import {SparkV15TemporaryHolds} from "../../../src/apps/spark/v15/SparkV15TemporaryHolds.sol";
import {
    SparkV15ConcernIntake,
    SparkV15ReviewCases,
    SparkV15ReviewContext,
    SparkV15ReviewActions
} from "../../../src/apps/spark/v15/SparkV15ReviewCases.sol";
import {IERC20} from "../../../src/apps/spark/legacy/interfaces/IERC20.sol";
import {RequestAllocationFixture} from "../../helpers/RequestAllocationFixture.sol";
import {MockERC20} from "../mocks/MockERC20.sol";

interface MaterialRightsChain {
    function roll(uint256 blockNumber) external;
    function setBlockhash(uint256 blockNumber, bytes32 blockHash) external;
    function expectRevert(bytes calldata reason) external;
}

contract MaterialRightsTest is RequestAllocationFixture {
    MaterialRightsChain private constant CHAIN =
        MaterialRightsChain(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint64 private constant EPOCH = 1_000_000;
    bytes32 private constant LESSON = bytes32(uint256(42));
    bytes32 private constant MATERIAL = bytes32(uint256(7));
    bytes32 private constant RULES = keccak256("published rights transfer terms");
    bytes32 private constant TEACHING = keccak256("agreed teaching services");
    address private constant DAO = address(0x7801);
    address private constant PROVIDER = address(0x7802);
    address private constant COORDINATOR = address(0x7803);
    address private constant TUTOR = address(0x7804);
    address private constant OUTGOING = address(0x7805);
    address private constant INCOMING = address(0x7806);
    address private constant SECOND = address(0x7807);
    address private constant OTHER = address(0x7808);
    address private constant STUDENT = address(0x7809);
    address private constant EXECUTOR = address(0x7810);
    address private constant STUDENT_B = address(0x7811);
    address private constant HOLD_REVIEWER = address(0x7812);
    address private constant DELEGATE = address(0x7813);

    SparkV15Booking private booking;
    SparkV15Materials private materials;
    SparkV15MaterialRights private rights;
    SparkV15Funds private funds;
    SparkV15MaterialProvisions private provisions;
    SparkV15Payments private payments;
    SparkV15ReviewCases private cases;
    SparkV15ConcernIntake private intake;
    MockERC20 private token;
    bytes32 private formId;
    bytes32 private otherForm;
    bytes32 private materialCaseTermsId;

    function setUp() public {
        requestVm.warp(EPOCH + 1);
        _setUpRequestAllocation(
            SparkV15.APP_ID,
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR),
            SparkV15.OBJECT_PAYMENT_APPROVAL
        );
        token = new MockERC20("Materials rights cash", "MAT", 6);
        payments = new SparkV15Payments(requestAllocation, IERC20(address(token)), REQUEST_WORKFLOW, ROLE_VERIFIER);
        payments.bindHolds(
            new SparkV15PaymentHolds(address(payments), requestAllocation, REQUEST_WORKFLOW, ROLE_VERIFIER)
        );
        funds = payments.FUNDS();
        booking = new SparkV15Booking(
            requestAllocation,
            ISparkV15BookingFunds(address(payments.FUNDS())),
            REQUEST_WORKFLOW,
            ROLE_SOURCE,
            ROLE_VERIFIER,
            PROVIDER
        );
        booking.bindOpening(new SparkV15BookingOpening(
            booking, new SparkV15BookingPrefunding(booking), new SparkV15TeachingEnd(booking), new SparkV15CourseNotices(booking)
        ));
        cases = new SparkV15ReviewCases(payments, ROLE_SOURCE);
        intake = new SparkV15ConcernIntake(payments, ROLE_SOURCE, cases);
        cases.bindIntake(intake);
        materials = new SparkV15Materials(booking, cases);
        materials.bindMaterialUse(new SparkV15MaterialsUse(materials));
        rights = new SparkV15MaterialRights(materials, DAO);
        require(address(rights).code.length <= 24_576, "rights runtime too large");
        require(address(rights.COLLECTION_READER()).code.length <= 24_576, "collection reader runtime too large");
        materials.bindMaterialInterests(ISparkV15MaterialInterests(address(rights)));
        provisions = new SparkV15MaterialProvisions(materials, payments);
        provisions.bindMaterialBacking(new SparkV15MaterialBacking(provisions, materials, booking, payments));
        funds.bindMaterialProvisions(address(provisions));
        provisions.bindMaterialRights(address(rights));
        identityRegistry.assignSubject(PROVIDER, SparkV15.APP_ID, ROLE_ALLOCATOR, _actorId(PROVIDER), "test:provider");
        identityRegistry.assignSubject(
            HOLD_REVIEWER, SparkV15.APP_ID, ROLE_VERIFIER, _actorId(HOLD_REVIEWER), "test:hold reviewer"
        );
        identityRegistry.assignSubject(
            COORDINATOR, SparkV15.APP_ID, ROLE_SOURCE, _actorId(COORDINATOR), "test:coordinator"
        );
        identityRegistry.assignSubject(
            address(booking), SparkV15.APP_ID, funds.BOOKING_ROLE(), _actorId(address(booking)), "test:booking"
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, booking.ACTION_COORDINATE_BOOKING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, materials.ACTION_VERIFY_USE(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, materials.ACTION_RECORD_GROSS(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, booking.ACTION_VERIFY_PREFUNDING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, booking.ACTION_VERIFY_TEACHING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, funds.BOOKING_ROLE(), funds.ACTION_MANAGE_LESSON_FUNDS(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, rights.ACTION_VERIFY_TRANSFER(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, rights.ACTION_VERIFY_TRANSFER_COLLECTION(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, provisions.ACTION_VERIFY_ENTITLEMENT(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_FORMAL_HOLD, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_LIFT_HOLD, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_AUTHORISE_PAYMENT_RETURN, true);
        _adoptLessonTerms();
    }

    function testAppointmentUsesSettledEarlierUseRatherThanCurrentNominalShares() public {
        bytes32 scope = _settledScope();
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 36);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 37);
        _verifyTransfer(transfer);
        _expectPortions(scope, EPOCH + 37, 5, 0, 3, 2);
        require(rights.unitsAt(LESSON, MATERIAL, OUTGOING, EPOCH + 37, EPOCH + 37) == 0, "nominal seller");
        require(rights.unitsAt(LESSON, MATERIAL, INCOMING, EPOCH + 37, EPOCH + 37) == 5, "nominal buyer");
        bytes32 caseId = _materialConcern(scope);
        _appointMaterialActor(caseId, OUTGOING, true);
        _appointMaterialActor(caseId, INCOMING, false);
        require(
            cases.getAppointment(caseId, SparkV15ReviewContext.AppointmentPurpose.InitialDecision, 0).input.handler
                == INCOMING,
            "disinterested appointee missing"
        );
    }

    function testOmissionAppointmentUsesTheMatchingOriginalCharge() public {
        _book(10);
        _teach();
        requestVm.warp(EPOCH + 33);
        _recordUse(EPOCH + 33);
        requestVm.warp(EPOCH + 34);
        bytes32[] memory forms = new bytes32[](1);
        forms[0] = formId;
        bytes32 scope = _recordGross(bytes32(0), EPOCH + 34, keccak256("exact seat charge"), forms);
        bytes32 caseId = _materialCase(scope, bytes32(0), true, false);
        _appointMaterialActor(caseId, OUTGOING, true);
        _appointMaterialActor(caseId, INCOMING, false);
        require(
            cases.getAppointment(caseId, SparkV15ReviewContext.AppointmentPurpose.InitialDecision, 0).input.handler
                == INCOMING,
            "eligible omission appointee missing"
        );
    }

    function testRetainedGrossReviewRechecksAssignmentAfterAppointment() public {
        bytes32 scope = _settledScope();
        bytes32 caseId = _materialCase(scope, bytes32(0), false, true);
        _appointMaterialReviewer(caseId, INCOMING, false);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 36);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 37);
        _verifyTransfer(transfer);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.Affirmed,
            outcome: keccak256("retained gross affirmed"),
            reasons: keccak256("independent review reasons"),
            approvalRequestId: 0
        });
        uint256 proof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, INCOMING, keccak256(abi.encode(review)));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(INCOMING);
        cases.decideReview(caseId, review, proof, _caseAuthority(INCOMING));
        require(cases.getCase(caseId).review.decidedAt == 0, "conflicted retained review recorded");
    }

    function testAppointmentUsesUnsettledEarlierUseAssignment() public {
        _book(10);
        _teach();
        requestVm.warp(EPOCH + 33);
        _recordUse(EPOCH + 33);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 34);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 35);
        _verifyTransfer(transfer);
        requestVm.warp(EPOCH + 36);
        bytes32 scope = _recordGross(bytes32(0), EPOCH + 36, keccak256("earlier use first charged after transfer"));
        _expectPortions(scope, EPOCH + 36, 5, 0, 3, 2);
        require(rights.unitsAt(LESSON, MATERIAL, OUTGOING, EPOCH + 36, EPOCH + 36) == 0, "nominal seller");
        require(rights.unitsAt(LESSON, MATERIAL, INCOMING, EPOCH + 36, EPOCH + 36) == 5, "nominal buyer");
        bytes32 caseId = _materialConcern(scope);
        _appointMaterialActor(caseId, OUTGOING, true);
        _appointMaterialActor(caseId, INCOMING, false);
    }

    function testAppointmentRejectsAcquirerWhenSettledBalanceWasAssigned() public {
        bytes32 scope = _settledScope();
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 36);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 37);
        _verifyTransfer(transfer);
        _expectPortions(scope, EPOCH + 37, 0, 5, 3, 2);
        require(rights.unitsAt(LESSON, MATERIAL, OUTGOING, EPOCH + 37, EPOCH + 37) == 0, "nominal seller");
        require(rights.unitsAt(LESSON, MATERIAL, INCOMING, EPOCH + 37, EPOCH + 37) == 5, "nominal buyer");
        bytes32 caseId = _materialConcern(scope);
        _appointMaterialActor(caseId, INCOMING, true);
        _appointMaterialActor(caseId, OUTGOING, false);
        require(
            cases.getAppointment(caseId, SparkV15ReviewContext.AppointmentPurpose.InitialDecision, 0).input.handler
                == OUTGOING,
            "seller should be eligible after assigning unpaid balance"
        );
    }

    function testAppointmentAllowsOutgoingHolderAfterFullCollectionBeforeTransfer() public {
        bytes32 scope = _settledScope();
        bytes32 obligation = _establishEntitlement(scope, OUTGOING, EPOCH + 34);
        uint256 approval = _approveMaterial(obligation, 5);
        requestVm.warp(EPOCH + 51);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 5);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 54);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 55);
        _verifyTransfer(transfer);
        _expectPortions(scope, EPOCH + 55, 5, 0, 3, 2);
        require(payments.getObligation(obligation).paid == 5, "prior collection missing");
        bytes32 caseId = _materialConcern(scope);
        _appointMaterialActor(caseId, OUTGOING, false);
        require(
            cases.getAppointment(caseId, SparkV15ReviewContext.AppointmentPurpose.InitialDecision, 0).input.handler
                == OUTGOING,
            "fully collected predecessor has no unpaid balance"
        );
    }

    function testInitialDecisionRechecksSettledBalanceAssignedAfterAppointment() public {
        bytes32 scope = _settledScope();
        bytes32 caseId = _materialConcern(scope);
        _appointMaterialActor(caseId, INCOMING, false);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 36);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 37);
        _verifyTransfer(transfer);
        _expectPortions(scope, EPOCH + 37, 0, 5, 3, 2);
        SparkV15ReviewContext.InitialInput memory finding = SparkV15ReviewContext.InitialInput({
            issue: SparkV15ReviewContext.DisputedFinding.OtherDisputedFact,
            outcome: keccak256("material revenue finding"),
            reasons: keccak256("verified revenue evidence"),
            support: bytes32(0)
        });
        uint256 proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, INCOMING, keccak256(abi.encode(finding))
        );
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(INCOMING);
        cases.decideInitial(caseId, finding, proof, _caseAuthority(INCOMING));
        require(cases.getCase(caseId).initial.decidedAt == 0, "conflicted finding recorded");
    }

    function testFutureEffectiveAssignmentDoesNotConflictUntilItsEffectiveTime() public {
        bytes32 scope = _settledScope();
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 40);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        _verifyTransfer(transfer);
        bytes32 caseId = _materialConcern(scope);
        _appointMaterialActor(caseId, INCOMING, false);
        requestVm.warp(EPOCH + 40);
        _expectPortions(scope, EPOCH + 40, 0, 5, 3, 2);
        SparkV15ReviewContext.InitialInput memory finding = SparkV15ReviewContext.InitialInput({
            issue: SparkV15ReviewContext.DisputedFinding.OtherDisputedFact,
            outcome: keccak256("material revenue finding"),
            reasons: keccak256("verified revenue evidence"),
            support: bytes32(0)
        });
        uint256 proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, INCOMING, keccak256(abi.encode(finding))
        );
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(INCOMING);
        cases.decideInitial(caseId, finding, proof, _caseAuthority(INCOMING));
    }

    function testReviewRechecksSettledBalanceAssignedAfterAppointment() public {
        bytes32 scope = _settledScope();
        bytes32 caseId = _materialConcern(scope);
        _appointMaterialReviewer(caseId, INCOMING, false);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 36);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 37);
        _verifyTransfer(transfer);
        _expectPortions(scope, EPOCH + 37, 0, 5, 3, 2);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.Affirmed,
            outcome: keccak256("material revenue affirmed"),
            reasons: keccak256("independent review reasons"),
            approvalRequestId: 0
        });
        uint256 proof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, INCOMING, keccak256(abi.encode(review)));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(INCOMING);
        cases.decideReview(caseId, review, proof, _caseAuthority(INCOMING));
        require(cases.getCase(caseId).review.decidedAt == 0, "conflicted review recorded");
    }

    function testReviewCannotUseARevokedTransferAsEvidenceOfDisinterest() public {
        bytes32 scope = _settledScope();
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 36);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 37);
        uint256 transferEvidenceId = rights.getTransfer(_verifyTransfer(transfer)).evidenceId;
        bytes32 caseId = _materialConcern(scope);
        _appointMaterialReviewer(caseId, OUTGOING, false);

        requestVm.warp(EPOCH + 38);
        _revokeEvidence(transferEvidenceId);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.Affirmed,
            outcome: keccak256("material revenue affirmed"),
            reasons: keccak256("independent review reasons"),
            approvalRequestId: 0
        });
        uint256 proof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, OUTGOING, keccak256(abi.encode(review)));
        CHAIN.expectRevert(
            abi.encodeWithSelector(SparkV15MaterialRights.UnavailableCaseRightsEvidence.selector, transferEvidenceId)
        );
        requestVm.prank(OUTGOING);
        cases.decideReview(caseId, review, proof, _caseAuthority(OUTGOING));
        require(cases.getCase(caseId).review.decidedAt == 0, "review recorded with revoked rights basis");
    }

    function testUnavailableMaterialIntakeStillAllowsNeutralReviewDisposition() public {
        bytes32 caseId = _materialConcern(_settledScope());
        _revokeEvidence(intake.getConcern(caseId).intake.evidenceId);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.EvidenceUnavailable,
            outcome: bytes32(0),
            reasons: keccak256("the material complaint source is no longer available"),
            approvalRequestId: 0
        });
        requestVm.prank(HOLD_REVIEWER);
        cases.decideReview(caseId, review, 0, _actorId(HOLD_REVIEWER));
        require(cases.getReview(caseId).input.disposition == review.disposition, "neutral review missing");
        require(cases.getAdoptedDisposition(caseId).adoptedAt == 0, "neutral review changed the charge");
    }

    function testAppointmentDistinguishesOriginalChargeFromLaterShortfall() public {
        _book(10);
        _teach();
        requestVm.warp(EPOCH + 33);
        bytes32 original = _recordGross(bytes32(0), EPOCH + 33, keccak256("original before later use evidence"));
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 34);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 35);
        _verifyTransfer(transfer);
        _recordUse(EPOCH + 35);
        requestVm.warp(EPOCH + 36);
        bytes32 shortfall = _recordGross(original, EPOCH + 36, keccak256("later positive shortfall"));
        _expectPortions(original, EPOCH + 36, 0, 0, 0, 0);
        _expectPortions(shortfall, EPOCH + 36, 0, 5, 3, 2);
        bytes32 originalCase = _materialConcern(original);
        bytes32 shortfallCase = _materialConcern(shortfall);
        _appointMaterialActor(originalCase, INCOMING, false);
        _appointMaterialActor(shortfallCase, INCOMING, true);
        require(
            cases.getAppointment(originalCase, SparkV15ReviewContext.AppointmentPurpose.InitialDecision, 0).input
                    .handler == INCOMING,
            "original scope appointment missing"
        );

        bytes32 payment = _establishEntitlement(shortfall, INCOMING, EPOCH + 36);
        bytes32 mismatchedCase = _materialConcern(original, payment);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.Affirmed,
            outcome: keccak256("purported review of a different charge"),
            reasons: keccak256("independent review reasons"),
            approvalRequestId: 0
        });
        uint256 proof = _caseEvidence(
            mismatchedCase, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, HOLD_REVIEWER, keccak256(abi.encode(review))
        );
        requestVm.expectRevert(SparkV15MaterialProvisions.InvalidCaseChargeScope.selector);
        requestVm.prank(HOLD_REVIEWER);
        cases.decideReview(mismatchedCase, review, proof, _actorId(HOLD_REVIEWER));

        bytes32 paymentCase = _materialConcern(bytes32(0), payment);
        _appointMaterialActor(paymentCase, INCOMING, true);
    }

    function testMatchingRetainedChargeAllowsInitialAndIndependentReview() public {
        bytes32 scope = _settledScope();
        bytes32 payment = _establishEntitlement(scope, OUTGOING, EPOCH + 34);
        _materialConcern(scope);
        bytes32 caseId = _candidateRetainedGrossCase(scope, payment);
        (bytes32 resolved, uint256 proof) = materials.MATERIAL_USE().retainedGrossScope(caseId, LESSON);
        require(resolved == scope && proof != 0, "matching retained scope missing");
        _candidateAssertNormalHandling(caseId);
    }

    function testMatchingOmittedChargeAllowsInitialAndIndependentReview() public {
        (bytes32 scope,) = _candidateSingleSeatCharges();
        bytes32 payment = _establishEntitlement(scope, OUTGOING, EPOCH + 35);
        bytes32 caseId = _materialCase(scope, payment, true, false);
        require(
            provisions.MATERIAL_BACKING().caseOmissionScope(LESSON, formId, materials.useMatter(formId, MATERIAL))
                == scope,
            "matching omission scope missing"
        );
        _candidateAssertNormalHandling(caseId);
    }

    function testAdoptedExactOmissionCorrectionChangesSingleSeatAndSubsequentEntitlement() public {
        (bytes32 first, bytes32 second) = _candidateSingleSeatCharges();
        bytes32 caseId = _materialCase(first, bytes32(0), true, false);
        (uint256 originalProof, uint256 reviewProof) = _decideCorrectedGross(caseId, first, 10, 8);
        bytes32 originalSource = materials.getChargeScope(first).sourceRef;
        materials.bindGrossReview(caseId, first, 10, 8);
        (uint128 beforeAdoption, bool pending) = materials.activeScopeGrossAt(first, formId, EPOCH + 36);
        require(beforeAdoption == 10 && !pending, "unadopted result changed the original gross");

        requestVm.warp(EPOCH + 37);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, materials.ACTION_VERIFY_ATTRIBUTION(), true);
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("adopted correction delivered"), EPOCH + 37);
        bytes32 partiesHash = intake.getConcern(caseId).intake.partiesHash;
        uint256 adoption = _caseEvidence(
            caseId,
            SparkV15ReviewActions.ACTION_ADOPT_CORRECTION,
            COORDINATOR,
            keccak256(abi.encode(notice, originalProof, reviewProof, partiesHash, partiesHash))
        );
        requestVm.prank(COORDINATOR);
        cases.adoptCorrection(caseId, notice, adoption, _actorId(COORDINATOR));
        (, pending) = materials.activeScopeGrossAt(first, formId, EPOCH + 37);
        require(pending, "adoption skipped verified seat attribution");
        SparkV15Materials.GrossAttributionInput memory attribution = SparkV15Materials.GrossAttributionInput(
            caseId, formId, 10, 8, EPOCH + 37, keccak256("verified affected seat and corrected gross")
        );
        uint256 proof = _evidence(materials.operationEvidenceCommitment(
            LESSON, materials.ACTION_VERIFY_ATTRIBUTION(), COORDINATOR, keccak256(abi.encode(attribution))
        ));
        requestVm.prank(COORDINATOR);
        materials.recordGrossAttribution(attribution, proof);
        (uint128 revised, bool waiting) = materials.activeScopeGrossAt(first, formId, EPOCH + 37);
        (uint128 unaffected, bool otherWaiting) = materials.activeScopeGrossAt(second, otherForm, EPOCH + 37);
        require(revised == 8 && !waiting && unaffected == 10 && !otherWaiting, "correction escaped its exact seat");
        require(materials.getHistoricalCharge(first, formId).amount == 10, "historical gross was rewritten");
        require(materials.getChargeScope(first).sourceRef == originalSource, "historical source was replaced");
        require(materials.getGrossAttribution(caseId, formId).input.sourceRef == attribution.sourceRef);

        bytes32 obligation = _establishEntitlement(first, OUTGOING, EPOCH + 37);
        require(payments.getObligation(obligation).correctAmount == 4, "entitlement did not use the revised gross");
        require(funds.paymentReserved(obligation) == 4, "cash reserve did not use the revised gross");
        uint256 approval = _approveMaterial(obligation, 4);
        requestVm.warp(EPOCH + 50);
        requestVm.prank(EXECUTOR);
        uint256 receipt = payments.pay(approval, 4);
        require(token.balanceOf(OUTGOING) == 4 && payments.getReceipt(receipt).amount == 4, "wrong amount paid");
    }

    function testSeatOmissionDoesNotAttributeAWholeGroupGrossCorrection() public {
        bytes32 groupScope = _settledScope(20, true);
        bytes32 caseId = _materialCase(groupScope, bytes32(0), true, false);
        _decideCorrectedGross(caseId, groupScope, 20, 18);
        requestVm.expectRevert(SparkV15Materials.InvalidGrossReview.selector);
        materials.bindGrossReview(caseId, groupScope, 20, 18);
    }

    function testUnresolvedOmittedChargeKeepsNeutralReview() public {
        _book(10);
        bytes32 caseId = _materialCase(bytes32(0), bytes32(0), true, false);
        (bool recognised, bool interested) = provisions.caseChargeInterest(
            caseId, LESSON, materials.useMatter(formId, MATERIAL), bytes32(0), formId, INCOMING
        );
        require(!recognised && !interested, "unestablished charge was manufactured");
        _appointMaterialReviewer(caseId, INCOMING, false);
        _revokeEvidence(intake.getConcern(caseId).intake.evidenceId);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.EvidenceUnavailable,
            outcome: bytes32(0),
            reasons: keccak256("identified use still requires available evidence"),
            approvalRequestId: 0
        });
        requestVm.prank(INCOMING);
        cases.decideReview(caseId, review, 0, _caseAuthority(INCOMING));
        require(cases.getReview(caseId).input.disposition == review.disposition, "neutral handling lost");
        require(cases.getAdoptedDisposition(caseId).adoptedAt == 0, "neutral result changed an entitlement");
        require(materials.originalFor(formId, MATERIAL) == bytes32(0), "complaint created a material charge");
    }

    function testConsentingWalletsMoveOnlyTheirSharesAtTheEffectiveTimeAndAfterRecording() public {
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 10);
        bytes32 commitment = rights.transferCommitment(transfer);
        requestVm.warp(EPOCH + 3);
        requestVm.prank(OUTGOING);
        rights.acceptTransfer(commitment);
        uint256 proof = _evidence(rights.transferEvidenceCommitment(commitment, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15MaterialRights.InvalidTransfer.selector);
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransfer(transfer, proof, _authority(ROLE_VERIFIER));

        requestVm.warp(EPOCH + 4);
        requestVm.prank(INCOMING);
        rights.acceptTransfer(commitment);
        requestVm.warp(EPOCH + 12);
        requestVm.prank(VERIFIER_ACTOR);
        require(rights.verifyTransfer(transfer, proof, _authority(ROLE_VERIFIER)) == commitment, "transfer identity");

        require(rights.unitsAt(LESSON, MATERIAL, OUTGOING, EPOCH + 9, EPOCH + 12) == 5, "early rights changed");
        require(rights.unitsAt(LESSON, MATERIAL, OUTGOING, EPOCH + 11, EPOCH + 11) == 5, "evidence leaked backwards");
        require(rights.unitsAt(LESSON, MATERIAL, OUTGOING, EPOCH + 10, EPOCH + 12) == 0, "seller retained units");
        require(rights.unitsAt(LESSON, MATERIAL, INCOMING, EPOCH + 10, EPOCH + 12) == 5, "buyer lacks units");
        require(rights.unitsAt(LESSON, MATERIAL, OTHER, EPOCH + 12, EPOCH + 12) == 2, "other holder changed");
        SparkV15MaterialRights.Transfer memory saved = rights.getTransfer(commitment);
        require(saved.terms.effectiveAt == EPOCH + 10 && saved.recordedAt == EPOCH + 12, "distinct dates lost");
        require(
            saved.evidenceId == proof && saved.verifiedBy == VERIFIER_ACTOR
                && saved.authorityId == _authority(ROLE_VERIFIER),
            "verification basis lost"
        );
    }

    function testEarlierVerifiedUseDefaultsToFirstActualUseDespiteLaterShareTransfer() public {
        _book(10);
        _teach();
        requestVm.warp(EPOCH + 33);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 34);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 35);
        _verifyTransfer(transfer);
        _recordUse(EPOCH + 35);
        requestVm.warp(EPOCH + 36);
        bytes32 scope = _recordGross(bytes32(0), EPOCH + 36, keccak256("original charge after transfer"));
        _expectPortions(scope, EPOCH + 36, 5, 0, 3, 2);
        require(rights.unitsAt(LESSON, MATERIAL, OUTGOING, EPOCH + 36, EPOCH + 36) == 0, "outgoing units active");
    }

    function testUseAfterTwoDisjointSameTimeTransfersPaysTheNewHolders() public {
        _book(10);
        requestVm.warp(EPOCH + 3);
        SparkV15MaterialRights.TransferTerms memory first = _transfer(EPOCH + 10);
        _acceptTransfer(first);
        _verifyTransfer(first);
        SparkV15MaterialRights.TransferTerms memory second = _transfer(EPOCH + 10);
        second.sourceRef = keccak256("a separate signed DAO buyback");
        second.kind = SparkV15MaterialRights.TransferKind.DaoBuyback;
        second.transferor = SECOND;
        second.transferee = DAO;
        second.units = 3;
        _acceptTransfer(second);
        _verifyTransfer(second);

        _teach();
        requestVm.warp(EPOCH + 33);
        _recordUse(EPOCH + 33);
        requestVm.warp(EPOCH + 34);
        bytes32 scope = _recordGross(bytes32(0), EPOCH + 34, keccak256("use after two transfers"));
        _expectPortions(scope, EPOCH + 34, 0, 5, 0, 2);
        require(rights.holderPortion(scope, DAO, EPOCH + 34, EPOCH + 34) == 3, "buyback allocation lost");
    }

    function testFirstUseEvaluatesExactAmountsAfterThePartialOwnershipTransfer() public {
        _book(5, 50);
        requestVm.warp(EPOCH + 3);
        SparkV15MaterialRights.TransferTerms memory deal = _transfer(EPOCH + 10);
        deal.transferee = SECOND;
        deal.units = 1;
        _acceptTransfer(deal);
        _verifyTransfer(deal);

        _teach();
        requestVm.warp(EPOCH + 33);
        _recordUse(EPOCH + 33);
        requestVm.warp(EPOCH + 34);
        bytes32 scope = _recordGross(bytes32(0), EPOCH + 34, keccak256("five units after the partial transfer"));
        _expectPortions(scope, EPOCH + 34, 2, 0, 2, 1);
    }

    function testAnAcquiringCoordinatorCannotVerifyUseInTheirOwnMaterial() public {
        _book(10);
        requestVm.warp(EPOCH + 3);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 10);
        transfer.transferee = COORDINATOR;
        _acceptTransfer(transfer);
        _verifyTransfer(transfer);
        _teach();
        requestVm.warp(EPOCH + 33);
        require(rights.isEconomicHolder(LESSON, MATERIAL, COORDINATOR), "current economic interest absent");
        _observeUse(formId, EPOCH + 33, true);
    }

    function testEarlierUseAgreementAssignsFutureShortfallSeparatelyFromTheSettledOriginal() public {
        _book(10);
        _teach();
        requestVm.warp(EPOCH + 33);
        bytes32 original = _recordGross(bytes32(0), EPOCH + 33, keccak256("original before late use evidence"));
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 34);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 35);
        _verifyTransfer(transfer);
        _recordUse(EPOCH + 35);
        requestVm.warp(EPOCH + 36);
        bytes32 supplement = _recordGross(original, EPOCH + 36, keccak256("separate positive shortfall"));
        _expectPortions(original, EPOCH + 36, 0, 0, 0, 0);
        _expectPortions(supplement, EPOCH + 36, 0, 5, 3, 2);
        require(materials.getChargeScope(supplement).originalScopeId == original, "shortfall scope lost");
    }

    function testSettledUncollectedAssignsOnlyTheUnpaidBalanceAndRequiresNewApproval() public {
        bytes32 scope = _settledScope();
        requestVm.prank(OUTGOING);
        provisions.agreeMaterialRecipient(scope, DELEGATE);
        bytes32 prior = _establishEntitlement(scope, OUTGOING, DELEGATE, EPOCH + 34);
        uint256 oldApproval = _approveMaterial(prior, 5);
        requestVm.warp(EPOCH + 51);
        requestVm.prank(EXECUTOR);
        uint256 priorReceipt = payments.pay(oldApproval, 2);

        requestVm.warp(EPOCH + 52);
        _returnFromDelegate(priorReceipt, 1, keccak256("one unit returned before the transfer"));
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 54);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 55);
        _verifyTransfer(transfer);
        _expectPortions(scope, EPOCH + 55, 1, 4, 3, 2);
        require(rights.holderPortion(scope, OUTGOING, EPOCH + 53, EPOCH + 55) == 5, "prior posting repriced");
        require(payments.getReceipt(priorReceipt).recipient == DELEGATE, "historical receipt overwritten");
        require(payments.RETURNS().receiptBeneficiary(priorReceipt) == OUTGOING, "agreed recipient replaced holder");

        requestVm.expectRevert(SparkV15MaterialProvisions.InvalidEntitlement.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(oldApproval, 1);
        bytes32 successor = _establishEntitlement(scope, INCOMING, EPOCH + 55);
        require(successor != prior && funds.paymentReserved(prior) == 0, "old reserve still charged");
        SparkV15Payments.Obligation memory predecessor = payments.getObligation(prior);
        require(
            predecessor.terms.amount == 5 && predecessor.correctAmount == 1 && predecessor.paid == 1,
            "old principal history"
        );
        require(payments.getObligation(successor).firstApprovalRequestId == 0, "old approval inherited");

        uint256 newApproval = _approveMaterial(successor, 4);
        requestVm.prank(EXECUTOR);
        payments.pay(newApproval, 4);
        require(token.balanceOf(DELEGATE) == 1 && token.balanceOf(INCOMING) == 4, "wrong actual receipts");
        require(token.balanceOf(address(funds)) == 5, "unrelated shares spent");

        requestVm.warp(EPOCH + 56);
        _returnFromDelegate(priorReceipt, 1, keccak256("last prior unit returned after the transfer"));
        _expectPortions(scope, EPOCH + 56, 1, 4, 3, 2);
        require(payments.getObligation(prior).paid == 0, "later return did not reopen the predecessor part");
    }

    function testMaterialPaymentUsesCorrectedDestinationAndKeepsTheHoldersEarlierReceipt() public {
        bytes32 scope = _settledScope();
        requestVm.prank(OUTGOING);
        provisions.agreeMaterialRecipient(scope, DELEGATE);
        bytes32 obligation = _establishEntitlement(scope, OUTGOING, DELEGATE, EPOCH + 34);
        uint256 oldApproval = _approveMaterial(obligation, 5);
        requestVm.warp(EPOCH + 51);
        requestVm.prank(EXECUTOR);
        uint256 oldReceipt = payments.pay(oldApproval, 2);

        address newDestination = address(0x7820);
        _correctMaterialDestination(scope, obligation, newDestination);
        require(payments.retainedByBeneficiary(obligation, OUTGOING) == 2, "earlier net receipt lost");
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(oldApproval, 1);

        _verifyOrderedMaterialReceipt(oldReceipt, EPOCH + 53);
        uint256 newApproval = _approveMaterial(obligation, 5);
        requestVm.prank(EXECUTOR);
        uint256 newReceipt = payments.pay(newApproval, 3);
        require(provisions.getMaterialReceipt(newReceipt).verifiedAt == 0, "execution also verified the receipt");
        requestVm.warp(EPOCH + 54);
        _verifyOrderedMaterialReceipt(newReceipt, EPOCH + 54);

        require(token.balanceOf(DELEGATE) == 2 && token.balanceOf(newDestination) == 3, "wrong actual destinations");
        require(token.balanceOf(address(funds)) == 5 && funds.paymentReserved(obligation) == 0, "wrong remaining backing");
        require(payments.getReceipt(oldReceipt).recipient == DELEGATE, "original destination overwritten");
        require(payments.getReceipt(newReceipt).recipient == newDestination, "new destination missing");
        require(payments.RETURNS().receiptBeneficiary(newReceipt) == OUTGOING, "holder changed");
        require(payments.retainedByBeneficiary(obligation, OUTGOING) == 5, "net receipts did not add up");

        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 55);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 56);
        _verifyTransfer(transfer);
        _expectPortions(scope, EPOCH + 56, 5, 0, 3, 2);
    }

    function testReturnInTransferSecondNeedsEvidenceBeforeTheSuccessorCanCollectIt() public {
        bytes32 scope = _settledScope();
        requestVm.prank(OUTGOING);
        provisions.agreeMaterialRecipient(scope, DELEGATE);
        bytes32 prior = _establishEntitlement(scope, OUTGOING, DELEGATE, EPOCH + 34);
        uint256 approval = _approveMaterial(prior, 5);
        requestVm.warp(EPOCH + 51);
        requestVm.prank(EXECUTOR);
        uint256 receipt = payments.pay(approval, 2);

        requestVm.warp(EPOCH + 52);
        _returnFromDelegate(receipt, 1, keccak256("return before assent in the transfer second"));
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 52);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 53);
        bytes32 id = _verifyTransfer(transfer);

        (uint256 known, uint256 pending) = rights.readHolderAmounts(scope, INCOMING, EPOCH + 53, EPOCH + 53, false, 0);
        require(known == 3 && pending == 1, "only the ordered return should be pending");
        _expectPortions(scope, EPOCH + 53, 1, 3, 3, 2);

        requestVm.warp(EPOCH + 54);
        SparkV15MaterialRights.SeatCollection[] memory seats = new SparkV15MaterialRights.SeatCollection[](1);
        seats[0] = SparkV15MaterialRights.SeatCollection(formId, 1);
        SparkV15MaterialRights.CollectionInput memory input = SparkV15MaterialRights.CollectionInput(
            id, scope, receipt, OUTGOING, keccak256("verified return and effective transfer order"), seats
        );
        identityRegistry.assignSubject(INCOMING, SparkV15.APP_ID, ROLE_VERIFIER, _actorId(INCOMING), "test:acquirer");
        uint256 conflictedProof = _evidence(rights.collectionEvidenceCommitment(input, INCOMING));
        requestVm.expectRevert(SparkV15MaterialRights.InvalidTransfer.selector);
        requestVm.prank(INCOMING);
        rights.verifyTransferCollection(input, conflictedProof, _actorId(INCOMING));

        uint256 proof = _evidence(rights.collectionEvidenceCommitment(input, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransferCollection(input, proof, _authority(ROLE_VERIFIER));
        _expectPortions(scope, EPOCH + 54, 1, 4, 3, 2);
        (known, pending) = rights.readHolderAmounts(scope, INCOMING, EPOCH + 53, EPOCH + 53, false, 0);
        require(known == 3 && pending == 1, "later verification changed the prior read");

        bytes32 successor = _establishEntitlement(scope, INCOMING, EPOCH + 54);
        approval = _approveMaterial(successor, 4);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 4);
        require(token.balanceOf(DELEGATE) == 1 && token.balanceOf(INCOMING) == 4, "wrong net and successor receipts");
        require(funds.paymentReserved(prior) == 0 && token.balanceOf(address(funds)) == 5, "wrong remaining backing");
    }

    function testFullReturnInTransferSecondCanVerifyZeroCollected() public {
        bytes32 scope = _settledScope();
        requestVm.prank(OUTGOING);
        provisions.agreeMaterialRecipient(scope, DELEGATE);
        bytes32 prior = _establishEntitlement(scope, OUTGOING, DELEGATE, EPOCH + 34);
        uint256 approval = _approveMaterial(prior, 5);
        requestVm.warp(EPOCH + 51);
        requestVm.prank(EXECUTOR);
        uint256 receipt = payments.pay(approval, 1);

        requestVm.warp(EPOCH + 52);
        _returnFromDelegate(receipt, 1, keccak256("last unit returned before assent"));
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 52);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 53);
        bytes32 id = _verifyTransfer(transfer);
        (uint256 known, uint256 pending) = rights.readHolderAmounts(scope, INCOMING, EPOCH + 53, EPOCH + 53, false, 0);
        require(known == 4 && pending == 1, "full return should remain pending before verification");

        requestVm.warp(EPOCH + 54);
        SparkV15MaterialRights.CollectionInput memory input = SparkV15MaterialRights.CollectionInput(
            id, scope, receipt, OUTGOING, keccak256("verified no earlier cash remained"),
            new SparkV15MaterialRights.SeatCollection[](0)
        );
        uint256 proof = _evidence(rights.collectionEvidenceCommitment(input, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransferCollection(input, proof, _authority(ROLE_VERIFIER));
        _expectPortions(scope, EPOCH + 54, 0, 5, 3, 2);
        (SparkV15MaterialRights.CollectionRecord memory saved, uint128 retained) =
            rights.getTransferCollection(id, scope, receipt, formId);
        require(saved.evidenceId == proof && retained == 0, "zero retained amount was not verified");
    }

    function testTransferCollectionUsesWholeReturnsInTheirExecutionOrder() public {
        bytes32 scope = _settledScope();
        requestVm.prank(OUTGOING);
        provisions.agreeMaterialRecipient(scope, DELEGATE);
        bytes32 prior = _establishEntitlement(scope, OUTGOING, DELEGATE, EPOCH + 34);
        uint256 approval = _approveMaterial(prior, 5);
        requestVm.warp(EPOCH + 51);
        requestVm.prank(EXECUTOR);
        uint256 receipt = payments.pay(approval, 5);

        requestVm.warp(EPOCH + 52);
        _returnFromDelegate(receipt, 3, keccak256("three units returned before assent"));
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 52);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        bytes32 id = _verifyTransfer(transfer);

        SparkV15MaterialRights.SeatCollection[] memory seats = new SparkV15MaterialRights.SeatCollection[](1);
        seats[0] = SparkV15MaterialRights.SeatCollection(formId, 4);
        SparkV15MaterialRights.CollectionInput memory input = SparkV15MaterialRights.CollectionInput(
            id, scope, receipt, OUTGOING, keccak256("claimed retained cash at the transfer"), seats
        );
        uint256 proof = _evidence(rights.collectionEvidenceCommitment(input, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15MaterialRights.InvalidTransfer.selector);
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransferCollection(input, proof, _authority(ROLE_VERIFIER));

        _returnFromDelegate(receipt, 1, keccak256("one unit returned after the effective transfer"));
        requestVm.warp(EPOCH + 53);
        requestVm.expectRevert(SparkV15MaterialRights.InvalidTransfer.selector);
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransferCollection(input, proof, _authority(ROLE_VERIFIER));

        input.seats[0].amount = 2;
        proof = _evidence(rights.collectionEvidenceCommitment(input, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransferCollection(input, proof, _authority(ROLE_VERIFIER));
        _expectPortions(scope, EPOCH + 53, 2, 3, 3, 2);

        bytes32 successor = _establishEntitlement(scope, INCOMING, EPOCH + 53);
        approval = _approveMaterial(successor, 3);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 3);
        require(token.balanceOf(DELEGATE) == 1 && token.balanceOf(INCOMING) == 3, "wrong actual receipts");
        require(funds.paymentReserved(prior) == 1 && token.balanceOf(address(funds)) == 6, "later return lost");
    }

    function testAlreadySettledIncomeUsesTheSettledDispositionRatherThanTheEarlierUseException() public {
        bytes32 scope = _settledScope();
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 36);
        transfer.unsettledEarlierUse = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 37);
        _verifyTransfer(transfer);
        _expectPortions(scope, EPOCH + 37, 5, 0, 3, 2);
    }

    function testVerifiedSameSecondReceiptLeavesOnlyTheUncertainPartPending() public {
        (bytes32 scope, bytes32 predecessor, uint256 receipt) = _payBeforeRecordingSameSecondTransfer(2);
        requestVm.warp(EPOCH + 53);
        _verifyOrderedMaterialReceipt(receipt, EPOCH + 53);

        (uint256 known, uint256 pending) = rights.readHolderAmounts(scope, INCOMING, EPOCH + 53, EPOCH + 53, false, 0);
        require(known == 3 && pending == 2, "wrong determined and pending assignment");
        bytes32 successor = _establishEntitlement(scope, INCOMING, EPOCH + 53);
        SparkV15Payments.Obligation memory original = payments.getObligation(predecessor);
        require(original.correctAmount == 2 && original.paid == 2, "rebasing decided the pending receipt");
        require(funds.paymentReserved(successor) == 3, "known assignment was not backed");

        uint256 approval = _approveMaterial(successor, 3);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 3);
        bytes32 independent = _establishEntitlement(scope, SECOND, EPOCH + 53);
        approval = _approveMaterial(independent, 3);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 3);
        require(token.balanceOf(OUTGOING) == 2 && token.balanceOf(INCOMING) == 3, "actual right payments changed");
        require(token.balanceOf(SECOND) == 3 && token.balanceOf(address(funds)) == 2, "independent money changed");
    }

    function testLateVerifiedSameSecondReceiptLimitsAnExistingSuccessorApproval() public {
        (bytes32 scope,, uint256 receipt) = _payBeforeRecordingSameSecondTransfer(2);
        bytes32 successor = _establishEntitlement(scope, INCOMING, EPOCH + 52);
        uint256 approval = _approveMaterial(successor, 5);
        requestVm.warp(EPOCH + 53);
        _verifyOrderedMaterialReceipt(receipt, EPOCH + 53);
        require(rights.holderPortion(scope, INCOMING, EPOCH + 52, EPOCH + 52) == 5, "later verification backdated");
        require(rights.holderPortion(scope, INCOMING, EPOCH + 53, EPOCH + 53) == 3, "pending amount still payable");

        requestVm.expectRevert(SparkV15MaterialProvisions.InvalidEntitlement.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 5);
        require(payments.getApproval(approval).paid == 0 && funds.paymentReserved(successor) == 5, "refusal mutated funds");
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 3);
        require(token.balanceOf(INCOMING) == 3 && token.balanceOf(address(funds)) == 5, "determined part did not reach payee");
        require(funds.paymentReserved(successor) == 2, "unresolved portion lost backing");
        require(payments.getApproval(approval).paid == 3, "approval lost the actual paid amount");
    }

    function testSameSecondPendingAmountStillConflictsInItsOwnMaterialCase() public {
        (bytes32 scope,, uint256 receipt) = _payBeforeRecordingSameSecondTransfer(5);
        requestVm.warp(EPOCH + 53);
        _verifyOrderedMaterialReceipt(receipt, EPOCH + 53);
        (uint256 known, uint256 pending) = rights.readHolderAmounts(scope, INCOMING, EPOCH + 53, EPOCH + 53, false, 0);
        require(known == 0 && pending == 5, "case must have no presently payable successor amount");
        bytes32 caseId = _materialConcern(scope);
        _appointMaterialActor(caseId, INCOMING, true);
        _appointMaterialActor(caseId, OUTGOING, false);
        require(
            cases.getAppointment(caseId, SparkV15ReviewContext.AppointmentPurpose.InitialDecision, 0).input.handler
                == OUTGOING,
            "fully collected holder could not handle the same case"
        );
    }

    function _payBeforeRecordingSameSecondTransfer(uint128 amount)
        private
        returns (bytes32 scope, bytes32 predecessor, uint256 receipt)
    {
        scope = _settledScope();
        predecessor = _establishEntitlement(scope, OUTGOING, EPOCH + 34);
        uint256 approval = _approveMaterial(predecessor, 5);
        requestVm.warp(EPOCH + 51);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 51);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.prank(EXECUTOR);
        receipt = payments.pay(approval, amount);
        requestVm.warp(EPOCH + 52);
        _verifyTransfer(transfer);
    }

    function _verifyOrderedMaterialReceipt(uint256 receipt, uint64 atTime) private {
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, provisions.ACTION_VERIFY_MATERIAL_RECEIPT(), true
        );
        uint256 proof = _evidence(provisions.receiptEvidenceCommitment(receipt, atTime, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        provisions.verifyMaterialReceipt(receipt, atTime, proof, _authority(ROLE_VERIFIER));
    }

    function testObservedCashUsesVerifiedQualificationAndTheOriginalTransferCutoff() public {
        bytes32 scope = _settledScope();
        bytes32 prior = _establishEntitlement(scope, OUTGOING, EPOCH + 34);
        SparkV15PaymentObservations observations =
            new SparkV15PaymentObservations(address(payments), requestAllocation, ROLE_VERIFIER);
        payments.bindPaymentObservations(address(observations));
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, observations.ACTION_VERIFY_OBSERVATION(), true);
        token.mint(PROVIDER, 2);
        requestVm.warp(EPOCH + 51);
        SparkV15PaymentObservations.Transfer memory cash = _outsideCash(PROVIDER, OUTGOING, EPOCH + 51, 20);

        requestVm.warp(EPOCH + 52);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 54);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 55);
        _verifyTransfer(transfer);
        _expectPortions(scope, EPOCH + 55, 0, 5, 3, 2);

        requestVm.warp(EPOCH + 56);
        SparkV15PaymentObservations.PaymentTerms memory terms = SparkV15PaymentObservations.PaymentTerms(
            prior, OUTGOING, cash, EPOCH + 52, keccak256("exact independently observed material payment"), PROVIDER
        );
        uint256 proof = _evidence(observations.paymentEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        bytes32 receipt = observations.verifyPayment(terms, proof, _authority(ROLE_VERIFIER));
        require(observations.getPaymentObservation(receipt).qualifies, "outside payment was not qualified");
        _expectPortions(scope, EPOCH + 56, 2, 3, 3, 2);
        _expectPortions(scope, EPOCH + 55, 0, 5, 3, 2);

        requestVm.warp(EPOCH + 57);
        SparkV15PaymentObservations.ReturnTerms memory returned = SparkV15PaymentObservations.ReturnTerms(
            receipt,
            _outsideCash(OUTGOING, PROVIDER, EPOCH + 57, 22),
            EPOCH + 57,
            keccak256("verified later external return")
        );
        proof = _evidence(observations.returnEvidenceCommitment(returned));
        requestVm.prank(VERIFIER_ACTOR);
        observations.verifyReturn(returned, proof, _authority(ROLE_VERIFIER));
        require(payments.retainedByBeneficiary(prior, OUTGOING) == 0, "external return not deducted");
        _expectPortions(scope, EPOCH + 57, 2, 3, 3, 2);

        _revokeEvidence(proof);
        bytes32 caseId = _materialConcern(scope);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.Affirmed,
            outcome: keccak256("observed material payment and return"),
            reasons: keccak256("independent review reasons"),
            approvalRequestId: 0
        });
        uint256 reviewProof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, HOLD_REVIEWER, keccak256(abi.encode(review))
        );
        CHAIN.expectRevert(
            abi.encodeWithSelector(SparkV15ObservedMaterialReceipts.UnavailableCaseReceiptEvidence.selector, proof)
        );
        requestVm.prank(HOLD_REVIEWER);
        cases.decideReview(caseId, review, reviewProof, _actorId(HOLD_REVIEWER));
    }

    function testExistingAcquirerNeedsNewVerificationAndApprovalForTheIncreasedPrincipal() public {
        bytes32 scope = _settledScope();
        bytes32 original = _establishEntitlement(scope, OUTGOING, EPOCH + 34);
        bytes32 acquirer = _establishEntitlement(scope, SECOND, EPOCH + 34);
        uint256 oldApproval = _approveMaterial(acquirer, 3);

        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 36);
        transfer.transferee = SECOND;
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 37);
        bytes32 transferId = _verifyTransfer(transfer);
        _expectPortions(scope, EPOCH + 37, 0, 0, 8, 2);
        require(payments.getObligation(acquirer).correctAmount == 3, "recognition silently changed principal");
        uint256 version = payments.getObligation(acquirer).version;
        uint256 proof =
            _evidence(provisions.entitlementIncreaseCommitment(acquirer, 8, version, transferId, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        provisions.reviseEstablishedEntitlement(acquirer, 8, transferId, proof, _authority(ROLE_VERIFIER));
        require(
            funds.paymentReserved(acquirer) == 8 && funds.paymentReserved(original) == 0, "wrong backed continuation"
        );
        require(payments.getObligation(acquirer).terms.amount == 3, "initial amount overwritten");

        requestVm.warp(EPOCH + 51);
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(oldApproval, 8);
        uint256 newApproval = _approveMaterial(acquirer, 8);
        requestVm.prank(EXECUTOR);
        payments.pay(newApproval, 8);
        require(token.balanceOf(SECOND) == 8 && token.balanceOf(OUTGOING) == 0, "new actual recipient or amount");
    }

    function testTheNamedMaterialObligationEstablishesItsUnpaidBeneficiaryInterest() public {
        bytes32 scope = _settledScope();
        requestVm.prank(OUTGOING);
        provisions.agreeMaterialRecipient(scope, DELEGATE);
        bytes32 obligation = _establishEntitlement(scope, OUTGOING, DELEGATE, EPOCH + 34);
        SparkV15Payments.Obligation memory payment = payments.getObligation(obligation);
        require(payment.beneficiary == OUTGOING && payment.destination == DELEGATE, "payment roles were conflated");
        require(payment.correctAmount == 5 && payment.paid == 0, "wrong current outstanding");
        bytes32 otherObligation = _establishEntitlement(scope, OTHER, EPOCH + 34);
        payments.bindReviewCases(ISparkV15AdoptedDispositions(address(cases)));
        bytes32 caseId = _materialCase(payment.terms.paymentPart, obligation, false, false, OUTGOING);
        bytes32 otherPart = payments.getObligation(otherObligation).terms.paymentPart;
        bytes32 otherCase = _materialCase(otherPart, otherObligation, false, false, OUTGOING);
        (bool chargeKnown,) =
            provisions.caseChargeInterest(caseId, LESSON, payment.terms.paymentPart, obligation, bytes32(0), OUTGOING);
        require(cases.isPaymentConcern(caseId, LESSON, obligation) && !chargeKnown, "distinct payment and charge scope");

        bytes32 alternateRole = SparkV15.ALTERNATIVE_CONTACT_ROLE;
        bytes32 alternateId = _authority(alternateRole);
        identityRegistry.assignSubject(OUTGOING, SparkV15.APP_ID, alternateRole, alternateId, "test:published contact");
        authorityMatrix.setPermission(SparkV15.APP_ID, alternateRole, SparkV15.ACTION_TEMPORARY_HOLD, true);
        _enrolCaseActor(DELEGATE);
        requestVm.warp(EPOCH + 35);
        SparkV15PaymentHolds holds = payments.HOLDS();
        uint256 deadlinesProof =
            _evidence(holds.temporaryHoldDeadlinesCommitment(materialCaseTermsId, EPOCH + 39, EPOCH + 37));
        holds.recordTemporaryHoldDeadlines(materialCaseTermsId, EPOCH + 39, EPOCH + 37, deadlinesProof);
        bytes32 notice = keccak256("verified notice for the separately identifiable unpaid part");
        SparkV15TemporaryHolds.Terms memory temporary =
            SparkV15TemporaryHolds.Terms(obligation, caseId, notice, EPOCH + 34, EPOCH + 39, payment.version);
        uint256 proof = _evidence(payments.HOLDS().temporaryHoldCommitment(temporary, OUTGOING));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(OUTGOING);
        payments.imposeTemporaryHold(temporary, proof, alternateId);

        SparkV15PaymentHolds.HoldTerms memory formal =
            SparkV15PaymentHolds.HoldTerms(obligation, caseId, notice, EPOCH + 45, payment.version);
        proof = _evidence(payments.HOLDS().formalHoldCommitment(formal, OUTGOING));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(OUTGOING);
        payments.imposeFormalHold(formal, proof, _caseAuthority(OUTGOING));
        require(!payments.HOLDS().getStatus(obligation).active, "own material payment changed on recusal");

        temporary.obligationId = otherObligation;
        temporary.caseId = otherCase;
        temporary.expectedVersion = payments.getObligation(otherObligation).version;
        proof = _evidence(payments.HOLDS().temporaryHoldCommitment(temporary, OUTGOING));
        requestVm.prank(OUTGOING);
        bytes32 otherHold = payments.imposeTemporaryHold(temporary, proof, alternateId);
        require(payments.HOLDS().getTemporaryHold(otherHold).amount == 2, "independent part was not held");

        proof = _evidence(payments.HOLDS().formalHoldCommitment(formal, HOLD_REVIEWER));
        requestVm.prank(HOLD_REVIEWER);
        bytes32 holdId = payments.imposeFormalHold(formal, proof, _actorId(HOLD_REVIEWER));
        require(payments.HOLDS().getFormalHold(holdId).amount == 5, "wrong formally held amount");
        requestVm.warp(EPOCH + 36);
        uint256 version = payments.getObligation(obligation).version;
        bytes32 disposition = keccak256("independent determination of the identified part");
        proof = _evidence(payments.HOLDS().formalLiftCommitment(holdId, disposition, version, OUTGOING));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(OUTGOING);
        payments.liftFormalHold(holdId, disposition, version, proof, _caseAuthority(OUTGOING));
        proof = _evidence(payments.HOLDS().formalLiftCommitment(holdId, disposition, version, DELEGATE));
        requestVm.prank(DELEGATE);
        payments.liftFormalHold(holdId, disposition, version, proof, _caseAuthority(DELEGATE));
        require(!payments.HOLDS().getStatus(obligation).active, "legitimate lift did not release the payment");
        require(payments.HOLDS().getStatus(otherObligation).active, "separate temporary hold changed");

        uint256 approval = _approveMaterial(obligation, 5);
        requestVm.warp(EPOCH + 51);
        requestVm.prank(EXECUTOR);
        uint256 receiptId = payments.pay(approval, 5);
        require(payments.RETURNS().receiptBeneficiary(receiptId) == OUTGOING, "beneficiary history changed");
        require(token.balanceOf(DELEGATE) == 5 && token.balanceOf(OUTGOING) == 0, "wrong actual material payment");
    }

    function testAnActivePredecessorHoldContinuesOverTheAssignedShare() public {
        bytes32 scope = _settledScope();
        bytes32 prior = _establishEntitlement(scope, OUTGOING, EPOCH + 34);
        payments.bindReviewCases(ISparkV15AdoptedDispositions(address(cases)));
        bytes32 caseId = _materialConcern(scope, prior);
        requestVm.warp(EPOCH + 35);
        bytes32 holdId = _hold(prior, caseId);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 36);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 37);
        _verifyTransfer(transfer);
        require(rights.holderPortion(scope, INCOMING, EPOCH + 37, EPOCH + 37) == 5, "succession absent");
        require(rights.holderPortionWithoutHeldPredecessors(scope, INCOMING, EPOCH + 37) == 0, "hold lost");
        require(rights.holderPortionWithoutHeldPredecessors(scope, OTHER, EPOCH + 37) == 2, "another holder held");

        bytes32 successor = _establishEntitlement(scope, INCOMING, EPOCH + 37);
        require(payments.getObligation(prior).correctAmount == 0, "predecessor principal not rebased");
        uint256 approval = _approveMaterial(successor, 5);
        requestVm.warp(EPOCH + 51);
        requestVm.expectRevert(SparkV15MaterialProvisions.InvalidEntitlement.selector);
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 5);

        requestVm.warp(EPOCH + 52);
        uint256 version = payments.getObligation(prior).version;
        bytes32 disposition = keccak256("release supported by the follow-through finding");
        uint256 proof = _evidence(payments.HOLDS().formalLiftCommitment(holdId, disposition, version, INCOMING));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(INCOMING);
        payments.liftFormalHold(holdId, disposition, version, proof, _caseAuthority(INCOMING));

        proof = _evidence(payments.HOLDS().formalLiftCommitment(holdId, disposition, version, OUTGOING));
        requestVm.prank(OUTGOING);
        payments.liftFormalHold(holdId, disposition, version, proof, _caseAuthority(OUTGOING));
        require(rights.holderPortionWithoutHeldPredecessors(scope, INCOMING, EPOCH + 52) == 5, "valid lift not read");
        requestVm.prank(EXECUTOR);
        payments.pay(approval, 5);
        require(token.balanceOf(INCOMING) == 5, "successor still unpaid");
    }

    function testAnAmbiguousGroupReceiptRequiresVerifiedSeatAttributionWithoutBlockingOtherHolders() public {
        bytes32 scope = _settledScope(20, true);
        bytes32 prior = _establishEntitlement(scope, OUTGOING, EPOCH + 34);
        uint256 approval = _approveMaterial(prior, 10);
        requestVm.warp(EPOCH + 51);
        requestVm.prank(EXECUTOR);
        uint256 receipt = payments.pay(approval, 3);

        requestVm.warp(EPOCH + 52);
        SparkV15MaterialRights.TransferTerms memory transfer = _transfer(EPOCH + 54);
        transfer.settledUncollected = SparkV15MaterialRights.Assignment(1, 1);
        _acceptTransfer(transfer);
        requestVm.warp(EPOCH + 55);
        bytes32 id = _verifyTransfer(transfer);
        requestVm.expectRevert(SparkV15MaterialRights.MaterialAllocationPending.selector);
        rights.holderPortion(scope, INCOMING, EPOCH + 55, EPOCH + 55);
        require(rights.holderPortion(scope, SECOND, EPOCH + 55, EPOCH + 55) == 6, "other holder paused");
        bytes32 independent = _establishEntitlement(scope, SECOND, EPOCH + 55);
        require(funds.paymentReserved(independent) == 6, "another holder could not continue");

        SparkV15MaterialRights.SeatCollection[] memory seats = new SparkV15MaterialRights.SeatCollection[](2);
        seats[0] = SparkV15MaterialRights.SeatCollection(formId, 2);
        seats[1] = SparkV15MaterialRights.SeatCollection(otherForm, 2);
        SparkV15MaterialRights.CollectionInput memory input = SparkV15MaterialRights.CollectionInput(
            id, scope, receipt, OUTGOING, keccak256("matched prior group receipt"), seats
        );
        uint256 proof = _evidence(rights.collectionEvidenceCommitment(input, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15MaterialRights.InvalidTransfer.selector);
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransferCollection(input, proof, _authority(ROLE_VERIFIER));

        requestVm.warp(EPOCH + 56);
        input.seats[1].amount = 1;
        proof = _evidence(rights.collectionEvidenceCommitment(input, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransferCollection(input, proof, _authority(ROLE_VERIFIER));
        _expectPortions(scope, EPOCH + 56, 3, 7, 6, 4);
        (SparkV15MaterialRights.CollectionRecord memory saved, uint128 paidAtSeat) =
            rights.getTransferCollection(id, scope, receipt, otherForm);
        require(saved.verifiedAt == EPOCH + 56 && paidAtSeat == 1, "wrong seat receipt retained");
        requestVm.expectRevert(SparkV15MaterialRights.MaterialAllocationPending.selector);
        rights.holderPortion(scope, INCOMING, EPOCH + 55, EPOCH + 55);
    }

    function testBuybackRequiresTheNamedDaoAndFreshUnexpiredConsent() public {
        SparkV15MaterialRights.TransferTerms memory wrongDao = _transfer(EPOCH + 10);
        wrongDao.kind = SparkV15MaterialRights.TransferKind.DaoBuyback;
        _acceptTransfer(wrongDao);
        _rejectTransfer(wrongDao);

        SparkV15MaterialRights.TransferTerms memory expired = _transfer(EPOCH + 10);
        expired.kind = SparkV15MaterialRights.TransferKind.DaoBuyback;
        expired.transferee = DAO;
        expired.acceptThrough = EPOCH + 2;
        requestVm.warp(EPOCH + 3);
        _acceptTransfer(expired);
        _rejectTransfer(expired);

        SparkV15MaterialRights.TransferTerms memory buyback = expired;
        buyback.acceptThrough = EPOCH + 10;
        _acceptTransfer(buyback);
        _verifyTransfer(buyback);
        _rejectTransfer(buyback);
        requestVm.warp(EPOCH + 10);
        require(rights.unitsAt(LESSON, MATERIAL, DAO, EPOCH + 10, EPOCH + 10) == 5, "DAO acquired no share");
        require(rights.unitsAt(LESSON, MATERIAL, PROVIDER, EPOCH + 10, EPOCH + 10) == 0, "provider acquired DAO share");
    }

    function _candidateSingleSeatCharges() private returns (bytes32 firstScope, bytes32 secondScope) {
        _book(20);
        _teach();
        requestVm.warp(EPOCH + 33);
        _recordUseFor(formId, EPOCH + 33);
        _recordUseFor(otherForm, EPOCH + 33);
        bytes32[] memory forms = new bytes32[](1);
        forms[0] = formId;
        requestVm.warp(EPOCH + 34);
        firstScope = _recordGross(bytes32(0), EPOCH + 34, keccak256("candidate first single-seat charge"), forms);
        forms[0] = otherForm;
        requestVm.warp(EPOCH + 35);
        secondScope = _recordGross(bytes32(0), EPOCH + 35, keccak256("candidate second single-seat charge"), forms);
        require(firstScope != secondScope, "separate seat scopes collapsed");
    }

    function _candidateRetainedGrossCase(bytes32 scope, bytes32 obligationId) private returns (bytes32 caseId) {
        bytes32 concernRef = keccak256(abi.encode("candidate retained charge", scope, obligationId));
        caseId = cases.caseIdFor(LESSON, concernRef);
        _retainCaseGross(scope, obligationId, concernRef);
        require(intake.caseContext(caseId).evidenceId == 0, "retained fixture added a complaint");
    }

    function _retainCaseGross(bytes32 scope, bytes32 obligationId, bytes32 concernRef) private returns (uint256 proof) {
        address[] memory parties = new address[](2);
        parties[0] = STUDENT;
        parties[1] = COORDINATOR;
        SparkV15Materials.ChargeScope memory charge = materials.getChargeScope(scope);
        SparkV15ReviewContext.OriginalInput memory original = SparkV15ReviewContext.OriginalInput({
            termsId: materialCaseTermsId,
            concernRef: concernRef,
            obligationId: obligationId,
            paymentCommitment: cases.requirePaymentScope(LESSON, booking.getLesson(LESSON).packageId, obligationId),
            decider: charge.assessedBy,
            decidedAt: charge.identifiedAt,
            outcome: materials.grossReviewBasis(scope, charge.total),
            parties: parties
        });
        bytes32 caseId = cases.caseIdFor(LESSON, original.concernRef);
        proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(original))
        );
        requestVm.prank(VERIFIER_ACTOR);
        cases.retainOriginal(original, proof, _authority(ROLE_VERIFIER));
    }

    function _decideCorrectedGross(bytes32 caseId, bytes32 scope, uint256 oldGross, uint256 newGross)
        private
        returns (uint256 originalProof, uint256 reviewProof)
    {
        originalProof = _retainCaseGross(scope, bytes32(0), intake.getConcern(caseId).concernRef);
        requestVm.warp(EPOCH + 36);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.CorrectionRequired,
            outcome: materials.grossReviewOutcome(caseId, scope, oldGross, newGross),
            reasons: keccak256("independently verified scope and gross correction"),
            approvalRequestId: 0
        });
        reviewProof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, HOLD_REVIEWER, keccak256(abi.encode(review))
        );
        requestVm.prank(HOLD_REVIEWER);
        cases.decideReview(caseId, review, reviewProof, _actorId(HOLD_REVIEWER));
    }

    function _correctMaterialDestination(bytes32 scope, bytes32 obligation, address destination) private {
        requestVm.warp(EPOCH + 52);
        bytes32 caseId = _materialConcern(scope, obligation);
        uint256 originalProof = _retainCaseGross(scope, obligation, intake.getConcern(caseId).concernRef);
        SparkV15Payments.Obligation memory original = payments.getObligation(obligation);
        SparkV15Payments.PaymentRevision memory revision = SparkV15Payments.PaymentRevision(
            obligation, original.correctAmount, original.beneficiary, destination, original.version
        );
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput(
            SparkV15ReviewContext.ReviewDisposition.CorrectionRequired,
            keccak256(abi.encode(
                keccak256("spark.v1.5.revise-payment"), block.chainid, address(payments), caseId, revision, original.commitment
            )),
            keccak256("verified change of collecting wallet for the same holder"),
            0
        );
        uint256 reviewProof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, HOLD_REVIEWER, keccak256(abi.encode(review))
        );
        requestVm.prank(HOLD_REVIEWER);
        cases.decidePaymentRevision(caseId, review, revision, reviewProof, _actorId(HOLD_REVIEWER));

        requestVm.warp(EPOCH + 53);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, true);
        bytes32 role = payments.caseEffectRole();
        authorityMatrix.setPermission(SparkV15.APP_ID, role, payments.ACTION_APPLY_CASE_EFFECT(), true);
        identityRegistry.assignSubject(address(cases), SparkV15.APP_ID, role, _authority(role), "test:case effects");
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("corrected payment destination notified"), EPOCH + 53);
        bytes32 partiesHash = intake.getConcern(caseId).intake.partiesHash;
        uint256 adoptionProof = _caseEvidence(
            caseId,
            SparkV15ReviewActions.ACTION_ADOPT_CORRECTION,
            COORDINATOR,
            keccak256(abi.encode(notice, originalProof, reviewProof, partiesHash, partiesHash))
        );
        requestVm.prank(COORDINATOR);
        cases.adoptPaymentRevision(caseId, notice, adoptionProof, _actorId(COORDINATOR), revision);
    }

    function _candidateAssertNormalHandling(bytes32 caseId) private {
        _appointMaterialActor(caseId, INCOMING, false);
        SparkV15ReviewContext.InitialInput memory initial = SparkV15ReviewContext.InitialInput({
            issue: SparkV15ReviewContext.DisputedFinding.OtherDisputedFact,
            outcome: keccak256("candidate matching-scope finding"),
            reasons: keccak256("candidate matching-scope evidence"),
            support: bytes32(0)
        });
        uint256 proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, INCOMING, keccak256(abi.encode(initial))
        );
        requestVm.prank(INCOMING);
        cases.decideInitial(caseId, initial, proof, _caseAuthority(INCOMING));
        require(cases.getCase(caseId).initial.decider == INCOMING, "qualified initial handler rejected");

        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.Affirmed,
            outcome: initial.outcome,
            reasons: keccak256("candidate independent confirmation"),
            approvalRequestId: 0
        });
        proof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, INCOMING, keccak256(abi.encode(review)));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(INCOMING);
        cases.decideReview(caseId, review, proof, _caseAuthority(INCOMING));
        require(cases.getReview(caseId).decidedAt == 0, "initial handler reviewed their own decision");

        proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, HOLD_REVIEWER, keccak256(abi.encode(review))
        );
        requestVm.prank(HOLD_REVIEWER);
        cases.decideReview(caseId, review, proof, _actorId(HOLD_REVIEWER));
        require(cases.getReview(caseId).reviewer == HOLD_REVIEWER, "independent review rejected");
        require(cases.getAdoptedDisposition(caseId).adoptedAt == 0, "affirmation applied an unrequested correction");
    }

    function _materialConcern(bytes32 scope) private returns (bytes32 caseId) {
        return _materialConcern(scope, bytes32(0));
    }

    function _materialConcern(bytes32 scope, bytes32 obligationId) private returns (bytes32 caseId) {
        return _materialCase(scope, obligationId, false, false);
    }

    function _materialCase(bytes32 scope, bytes32 obligationId, bool omission, bool retained)
        private
        returns (bytes32 caseId)
    {
        return _materialCase(scope, obligationId, omission, retained, OTHER);
    }

    function _materialCase(bytes32 scope, bytes32 obligationId, bool omission, bool retained, address alternate)
        private
        returns (bytes32 caseId)
    {
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, true
        );
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR, true
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, true);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, true
        );
        if (materialCaseTermsId == bytes32(0)) {
            _enrolCaseActor(OUTGOING);
            _enrolCaseActor(INCOMING);
        }
        SparkV15ReviewContext.ReviewTerms memory terms = SparkV15ReviewContext.ReviewTerms({
            lessonId: LESSON,
            publication: keccak256("published case routes"),
            governingForm: formId,
            provider: VERIFIER_ACTOR,
            coordinator: COORDINATOR,
            alternativeContact: alternate,
            leadAcademicTutor: TUTOR,
            namedReviewer: HOLD_REVIEWER,
            escalationContact: EXECUTOR,
            replyDate: 0,
            replyPeriod: 10,
            replyLegalDeadline: 0,
            reviewDeadline: EPOCH + 100,
            reviewLegalDeadline: 0
        });
        bytes32 termsId = keccak256(abi.encode(terms));
        uint256 proof;
        if (materialCaseTermsId == bytes32(0)) {
            proof = _caseEvidence(termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, VERIFIER_ACTOR, termsId);
            requestVm.prank(VERIFIER_ACTOR);
            intake.publishContacts(terms, proof, _authority(ROLE_VERIFIER));
            materialCaseTermsId = termsId;
        }
        address[] memory parties = new address[](2);
        parties[0] = STUDENT;
        parties[1] = COORDINATOR;
        SparkV15ReviewContext.ConcernInput memory concern = SparkV15ReviewContext.ConcernInput({
            termsId: termsId,
            concernRef: keccak256(abi.encode("material revenue concern", scope, obligationId)),
            obligationId: obligationId,
            receiver: COORDINATOR,
            subject: omission
                ? SparkV15ReviewContext.ConcernSubject.MaterialOmission
                : SparkV15ReviewContext.ConcernSubject.RevenueShare,
            alternativeGround: SparkV15ReviewContext.AlternativeGround.None,
            claim: keccak256("disputed material revenue"),
            subjectRef: omission ? materials.useMatter(formId, MATERIAL) : scope,
            parties: parties
        });
        caseId = cases.caseIdFor(LESSON, concern.concernRef);
        if (retained) {
            SparkV15Materials.ChargeScope memory charge = materials.getChargeScope(scope);
            SparkV15ReviewContext.OriginalInput memory original = SparkV15ReviewContext.OriginalInput({
                termsId: termsId,
                concernRef: concern.concernRef,
                obligationId: bytes32(0),
                paymentCommitment: bytes32(0),
                decider: charge.assessedBy,
                decidedAt: charge.identifiedAt,
                outcome: materials.grossReviewBasis(scope, charge.total),
                parties: parties
            });
            proof = _caseEvidence(
                caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(original))
            );
            requestVm.prank(VERIFIER_ACTOR);
            cases.retainOriginal(original, proof, _authority(ROLE_VERIFIER));
            return caseId;
        }
        proof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_RECEIVE_CONCERN, STUDENT, keccak256(abi.encode(concern))
        );
        requestVm.prank(STUDENT);
        intake.receiveConcern(concern, proof);
    }

    function _enrolCaseActor(address actor) private {
        identityRegistry.assignSubject(actor, SparkV15.APP_ID, ROLE_VERIFIER, _caseAuthority(actor), "test:case actor");
    }

    function _caseAuthority(address actor) private pure returns (bytes32) {
        return keccak256(abi.encode("material case actor", actor));
    }

    function _caseEvidence(bytes32 subject, bytes32 action, address actor, bytes32 payload) private returns (uint256) {
        return _evidence(cases.evidenceCommitment(subject, action, actor, payload));
    }

    function _revokeEvidence(uint256 evidenceId) private {
        requestVm.prank(SOURCE_ACTOR);
        evidenceRegistry.recordEvidenceLifecycle(
            evidenceId,
            ROLE_SOURCE,
            _authority(ROLE_SOURCE),
            AVACoreTypes.EvidenceLifecycleKind.Revoke,
            0,
            keccak256("the relied-on evidence became unavailable"),
            "test:material-case-evidence-revoked"
        );
    }

    function _appointMaterialActor(bytes32 caseId, address actor, bool conflicted) private {
        SparkV15ReviewContext.AppointmentInput memory appointment = SparkV15ReviewContext.AppointmentInput({
            purpose: SparkV15ReviewContext.AppointmentPurpose.InitialDecision,
            handler: actor,
            handlerAuthorityId: _caseAuthority(actor),
            recusedActor: TUTOR,
            disclosure: SparkV15ReviewContext.Notice(keccak256("recusal disclosed"), uint64(block.timestamp))
        });
        address[] memory parties = new address[](2);
        parties[0] = STUDENT;
        parties[1] = COORDINATOR;
        uint256 proof = _caseEvidence(
            caseId,
            SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR,
            VERIFIER_ACTOR,
            keccak256(abi.encode(appointment, keccak256(abi.encode(parties))))
        );
        if (conflicted) requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(VERIFIER_ACTOR);
        cases.appoint(caseId, appointment, proof, _authority(ROLE_VERIFIER));
    }

    function _appointMaterialReviewer(bytes32 caseId, address actor, bool conflicted) private {
        SparkV15ReviewContext.AppointmentInput memory appointment = SparkV15ReviewContext.AppointmentInput({
            purpose: SparkV15ReviewContext.AppointmentPurpose.IndependentReview,
            handler: actor,
            handlerAuthorityId: _caseAuthority(actor),
            recusedActor: address(0),
            disclosure: SparkV15ReviewContext.Notice(bytes32(0), 0)
        });
        address[] memory parties = new address[](2);
        parties[0] = STUDENT;
        parties[1] = COORDINATOR;
        uint256 proof = _caseEvidence(
            caseId,
            SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR,
            VERIFIER_ACTOR,
            keccak256(abi.encode(appointment, keccak256(abi.encode(parties))))
        );
        if (conflicted) requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(VERIFIER_ACTOR);
        cases.appoint(caseId, appointment, proof, _authority(ROLE_VERIFIER));
    }

    function _transfer(uint64 effectiveAt) private pure returns (SparkV15MaterialRights.TransferTerms memory terms) {
        terms.lessonId = LESSON;
        terms.material = MATERIAL;
        terms.publishedTermsRef = RULES;
        terms.sourceRef = keccak256("signed transfer document");
        terms.transferor = OUTGOING;
        terms.transferee = INCOMING;
        terms.units = 5;
        terms.effectiveAt = effectiveAt;
        terms.acceptThrough = effectiveAt;
        terms.kind = SparkV15MaterialRights.TransferKind.Voluntary;
        terms.unsettledEarlierUse = SparkV15MaterialRights.Assignment(0, 1);
        terms.settledUncollected = SparkV15MaterialRights.Assignment(0, 1);
        terms.laterShortfall = SparkV15MaterialRights.Assignment(1, 1);
    }

    function _adoptLessonTerms() private {
        SparkV15Materials.HolderShare[] memory holders = new SparkV15Materials.HolderShare[](3);
        holders[0] = SparkV15Materials.HolderShare(OUTGOING, 5);
        holders[1] = SparkV15Materials.HolderShare(SECOND, 3);
        holders[2] = SparkV15Materials.HolderShare(OTHER, 2);
        SparkV15Materials.MaterialTerms[] memory items = new SparkV15Materials.MaterialTerms[](1);
        items[0] = SparkV15Materials.MaterialTerms(MATERIAL, 10, holders, new address[](0));
        SparkV15Materials.Terms memory terms = SparkV15Materials.Terms(
            LESSON,
            TEACHING,
            PROVIDER,
            TEACHING,
            TEACHING,
            RULES,
            EPOCH + 50,
            EPOCH + 90,
            100,
            items,
            new SparkV15Materials.PriceRow[](0)
        );
        bytes32 commitment = materials.termsCommitment(terms);
        SparkV15Booking.LessonTerms memory lesson;
        lesson.lessonId = LESSON;
        lesson.provider = PROVIDER;
        lesson.tutor = TUTOR;
        lesson.coordinator = COORDINATOR;
        lesson.startsAt = EPOCH + 30;
        lesson.endsAt = EPOCH + 32;
        lesson.rosterLockAt = EPOCH + 28;
        lesson.rosterRef = TEACHING;
        lesson.timeZoneRef = keccak256("UTC");
        lesson.tutorNoticeChannelRef = TEACHING;
        lesson.tutorFee = 1;
        lesson.tutorAgreementRef = TEACHING;
        lesson.serviceTermsRef = TEACHING;
        lesson.tutorPayTermsRef = TEACHING;
        lesson.providerResponsibilitiesRef = TEACHING;
        lesson.tutorResponsibilitiesRef = TEACHING;
        lesson.startTermsRef = TEACHING;
        lesson.documentsRef = TEACHING;
        lesson.materialsTermsRef = commitment;
        requestVm.prank(COORDINATOR);
        booking.publishLesson(lesson);
        for (uint256 i; i < holders.length; ++i) {
            requestVm.prank(holders[i].holder);
            materials.acceptTerms(commitment);
        }
        requestVm.prank(PROVIDER);
        materials.adoptTerms(terms);
    }

    function _publishPlace(address student, uint256 seat, uint128 normalFee) private returns (bytes32) {
        SparkV15Booking.PlaceTerms memory place;
        place.placeId = bytes32(seat);
        place.customer = student;
        place.student = student;
        place.payer = student;
        place.creditAccount = funds.creditAccount(student);
        place.studentNoticeChannelRef = TEACHING;
        place.normalFee = normalFee;
        place.discountBasis = TEACHING;
        place.materialsBundleRef = TEACHING;
        place.materialPayer = PROVIDER;
        requestVm.prank(COORDINATOR);
        return booking.publishForm(LESSON, place);
    }

    function _book(uint128 backing) private {
        _book(backing, 100);
    }

    function _book(uint128 backing, uint128 normalFee) private {
        formId = _publishPlace(STUDENT, 1, normalFee);
        otherForm = _publishPlace(STUDENT_B, 2, normalFee);
        bytes32[] memory forms = _forms();
        token.mint(address(funds), backing);
        uint256 prefunding = _evidence(booking.prefundingCommitment(LESSON, forms, backing, TEACHING));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, forms, backing, TEACHING, prefunding);
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(LESSON);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(LESSON);
        _confirmPlace(formId, STUDENT);
        _confirmPlace(otherForm, STUDENT_B);
    }

    function _confirmPlace(bytes32 form, address student) private {
        _provideTerms(form, student);
        _provideTerms(form, TUTOR);
        requestVm.prank(PROVIDER);
        booking.acceptForm(form, SparkV15Booking.Acceptance.Provider);
        requestVm.prank(TUTOR);
        booking.acceptForm(form, SparkV15Booking.Acceptance.Tutor);
        requestVm.prank(student);
        booking.acceptForm(form, SparkV15Booking.Acceptance.Customer);
        uint256 proof = _evidence(booking.fullDiscountCommitment(form, TEACHING));
        requestVm.prank(COORDINATOR);
        booking.confirmPlace(form, TEACHING, proof, new SparkV15Funds.RechargeDebit[](0));
    }

    function _provideTerms(bytes32 form, address recipient) private {
        uint256 proof = _evidence(booking.provisionCommitment(form, recipient, TEACHING));
        requestVm.prank(COORDINATOR);
        booking.recordTermsProvision(form, recipient, TEACHING, proof);
    }

    function _teach() private {
        requestVm.warp(EPOCH + 22);
        uint256 proof = _evidence(booking.studentNoticeCommitment(formId, EPOCH + 22, TEACHING));
        requestVm.prank(COORDINATOR);
        booking.recordStudentNotice(formId, EPOCH + 22, TEACHING, proof);
        proof = _evidence(booking.studentNoticeCommitment(otherForm, EPOCH + 22, TEACHING));
        requestVm.prank(COORDINATOR);
        booking.recordStudentNotice(otherForm, EPOCH + 22, TEACHING, proof);
        proof = _evidence(booking.tutorNoticeCommitment(LESSON, TEACHING, EPOCH + 22, TEACHING));
        requestVm.prank(COORDINATOR);
        booking.recordTutorNotice(LESSON, TEACHING, EPOCH + 22, TEACHING, proof);
        requestVm.warp(EPOCH + 28);
        proof = _evidence(booking.rosterLockCommitment(LESSON, TEACHING));
        requestVm.prank(COORDINATOR);
        booking.lockRoster(LESSON, TEACHING, proof);
        requestVm.warp(EPOCH + 30);
        address[] memory attending = new address[](2);
        attending[0] = STUDENT;
        attending[1] = STUDENT_B;
        SparkV15Booking.StartObservation memory start =
            SparkV15Booking.StartObservation(EPOCH + 30, true, attending, keccak256("actual start"), bytes32(0));
        proof = _evidence(booking.teachingStartCommitment(LESSON, start));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingStarted(LESSON, start, proof);
        requestVm.warp(EPOCH + 32);
        proof = _evidence(booking.teachingEndCommitment(LESSON, EPOCH + 32, TEACHING));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingEnded(LESSON, EPOCH + 32, TEACHING, proof);
    }

    function _recordUse(uint64 checkedAt) private {
        _recordUseFor(formId, checkedAt);
    }

    function _recordUseFor(bytes32 form, uint64 checkedAt) private {
        _observeUse(form, checkedAt, false);
    }

    function _observeUse(bytes32 form, uint64 checkedAt, bool expectedConflict) private {
        SparkV15Materials.UseCheck memory useCheck = SparkV15Materials.UseCheck(
            form,
            MATERIAL,
            EPOCH + 30,
            checkedAt,
            SparkV15Materials.UseSource.LessonRecord,
            TEACHING,
            keccak256("checked student received teaching with this material"),
            false,
            false,
            bytes32(0)
        );
        uint256 proof = _evidence(
            materials.operationEvidenceCommitment(
                LESSON, materials.ACTION_VERIFY_USE(), COORDINATOR, keccak256(abi.encode(useCheck))
            )
        );
        if (expectedConflict) requestVm.expectRevert(SparkV15Materials.InvalidMaterialsAuthority.selector);
        requestVm.prank(COORDINATOR);
        materials.verifyUse(useCheck, proof);
    }

    function _settledScope() private returns (bytes32) {
        return _settledScope(10, false);
    }

    function _settledScope(uint128 backing, bool bothUsed) private returns (bytes32) {
        _book(backing);
        _teach();
        requestVm.warp(EPOCH + 33);
        _recordUse(EPOCH + 33);
        if (bothUsed) _recordUseFor(otherForm, EPOCH + 33);
        requestVm.warp(EPOCH + 34);
        return _recordGross(bytes32(0), EPOCH + 34, keccak256("settled charge"));
    }

    function _hold(bytes32 obligation, bytes32 caseId) private returns (bytes32) {
        SparkV15PaymentHolds.HoldTerms memory hold = SparkV15PaymentHolds.HoldTerms(
            obligation,
            caseId,
            keccak256("dated hold notice"),
            EPOCH + 89,
            payments.getObligation(obligation).version
        );
        uint256 proof = _evidence(payments.HOLDS().formalHoldCommitment(hold, HOLD_REVIEWER));
        requestVm.prank(HOLD_REVIEWER);
        return payments.imposeFormalHold(hold, proof, _actorId(HOLD_REVIEWER));
    }

    function _recordGross(bytes32 original, uint64 identifiedAt, bytes32 source) private returns (bytes32) {
        return _recordGross(original, identifiedAt, source, _forms());
    }

    function _recordGross(bytes32 original, uint64 identifiedAt, bytes32 source, bytes32[] memory forms)
        private
        returns (bytes32)
    {
        SparkV15Materials.GrossInput memory input =
            SparkV15Materials.GrossInput(LESSON, MATERIAL, original, source, identifiedAt, forms);
        uint256 proof = _evidence(
            materials.operationEvidenceCommitment(
                LESSON, materials.ACTION_RECORD_GROSS(), COORDINATOR, keccak256(abi.encode(input))
            )
        );
        requestVm.prank(COORDINATOR);
        return materials.recordGross(input, proof);
    }

    function _forms() private view returns (bytes32[] memory forms) {
        forms = new bytes32[](2);
        forms[0] = formId;
        forms[1] = otherForm;
    }

    function _expectPortions(
        bytes32 scope,
        uint64 nowAt,
        uint256 outgoing,
        uint256 incoming,
        uint256 second,
        uint256 other
    ) private view {
        require(rights.holderPortion(scope, OUTGOING, nowAt, nowAt) == outgoing, "outgoing payout");
        require(rights.holderPortion(scope, INCOMING, nowAt, nowAt) == incoming, "incoming payout");
        require(rights.holderPortion(scope, SECOND, nowAt, nowAt) == second, "second holder payout");
        require(rights.holderPortion(scope, OTHER, nowAt, nowAt) == other, "other holder payout");
    }

    function _acceptTransfer(SparkV15MaterialRights.TransferTerms memory transfer) private {
        bytes32 transferId = rights.transferCommitment(transfer);
        requestVm.prank(transfer.transferor);
        rights.acceptTransfer(transferId);
        requestVm.prank(transfer.transferee);
        rights.acceptTransfer(transferId);
    }

    function _verifyTransfer(SparkV15MaterialRights.TransferTerms memory transfer) private returns (bytes32) {
        bytes32 transferId = rights.transferCommitment(transfer);
        uint256 proof = _evidence(rights.transferEvidenceCommitment(transferId, VERIFIER_ACTOR));
        requestVm.prank(VERIFIER_ACTOR);
        return rights.verifyTransfer(transfer, proof, _authority(ROLE_VERIFIER));
    }

    function _rejectTransfer(SparkV15MaterialRights.TransferTerms memory transfer) private {
        bytes32 transferId = rights.transferCommitment(transfer);
        uint256 proof = _evidence(rights.transferEvidenceCommitment(transferId, VERIFIER_ACTOR));
        requestVm.expectRevert(SparkV15MaterialRights.InvalidTransfer.selector);
        requestVm.prank(VERIFIER_ACTOR);
        rights.verifyTransfer(transfer, proof, _authority(ROLE_VERIFIER));
    }

    function _establishEntitlement(bytes32 scope, address holder, uint64 verifiedAt) private returns (bytes32) {
        return _establishEntitlement(scope, holder, holder, verifiedAt);
    }

    function _establishEntitlement(bytes32 scope, address holder, address recipient, uint64 verifiedAt)
        private
        returns (bytes32)
    {
        SparkV15MaterialProvisions.EntitlementInput memory input = SparkV15MaterialProvisions.EntitlementInput(
            scope, holder, recipient, verifiedAt, 0, keccak256("verified material share")
        );
        (SparkV15Payments.PaymentTerms memory terms, bytes32 basis) =
            provisions.previewEntitlement(input, VERIFIER_ACTOR);
        bytes32 schedule = keccak256(abi.encode(keccak256("spark.v1.5.material-schedule"), basis, verifiedAt, true));
        uint256 proof = _evidence(payments.paymentEvidenceCommitment(terms, schedule));
        requestVm.prank(VERIFIER_ACTOR);
        return provisions.establishEntitlement(input, proof, _authority(ROLE_VERIFIER));
    }

    function _approveMaterial(bytes32 obligation, uint128 amount) private returns (uint256 requestId) {
        SparkV15Payments.ApprovalTerms memory terms =
            SparkV15Payments.ApprovalTerms(obligation, EXECUTOR, amount, EPOCH + 85, 0);
        bytes32 parameters = payments.approvalParameters(terms);
        uint256 status = _createRequestState(
            address(payments), SparkV15.RESPONSE_APPROVE_PAYMENT, parameters, SparkV15.APPROVAL_BURDEN, EPOCH + 84
        );
        requestId = _createRequest(
            AVARequestAllocation.RequestInput(
                status,
                address(payments),
                SparkV15.RESPONSE_APPROVE_PAYMENT,
                parameters,
                SparkV15.APPROVAL_BURDEN,
                EPOCH + 84
            )
        );
        requestVm.startPrank(PROVIDER);
        requestAllocation.approve(requestId, ROLE_ALLOCATOR, _actorId(PROVIDER));
        payments.recordApproval(requestId, terms);
        requestVm.stopPrank();
    }

    function _returnFromDelegate(uint256 receiptId, uint128 amount, bytes32 sourceRef) private {
        SparkV15Returns returnsLedger = payments.RETURNS();
        SparkV15Returns.ReturnTerms memory terms = SparkV15Returns.ReturnTerms(receiptId, amount, sourceRef);
        uint256 proof = _evidence(returnsLedger.returnEvidenceCommitment(terms));
        requestVm.prank(VERIFIER_ACTOR);
        returnsLedger.authorisePaymentReturn(terms, proof, _authority(ROLE_VERIFIER));
        requestVm.startPrank(DELEGATE);
        token.approve(address(funds), amount);
        returnsLedger.returnPayment(terms, proof);
        requestVm.stopPrank();
    }

    function _outsideCash(address from, address to, uint64 occurredAt, uint64 blockNumber)
        private
        returns (SparkV15PaymentObservations.Transfer memory)
    {
        CHAIN.roll(blockNumber);
        requestVm.prank(from);
        require(token.transfer(to, 2), "actual external wallet transfer failed");
        CHAIN.roll(blockNumber + 1);
        bytes32 blockHash = keccak256(abi.encode("local observed payment block", blockNumber));
        CHAIN.setBlockhash(blockNumber, blockHash);
        return SparkV15PaymentObservations.Transfer(
            keccak256(abi.encode("local outside transfer", blockNumber)),
            blockHash,
            blockNumber,
            0,
            occurredAt,
            from,
            to,
            2
        );
    }

    function _actorId(address actor) private pure returns (bytes32) {
        return keccak256(abi.encode("materials rights actor", actor));
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
                evidenceTypeHash: keccak256("spark.materials.rights.verified"),
                disclosurePolicyId: requestPolicyId,
                authorityId: _authority(ROLE_SOURCE),
                uri: "test:verified-materials-transfer"
            })
        );
    }
}
