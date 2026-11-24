// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15, SparkV15ApplicationModule} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {ISparkV15BookingChanges, ISparkV15BookingFunds, SparkV15Booking, SparkV15BookingOpening} from "../../../src/apps/spark/v15/SparkV15Booking.sol";
import {SparkV15BookingChanges} from "../../../src/apps/spark/v15/SparkV15BookingChanges.sol";
import {SparkV15BookingPrefunding} from "../../../src/apps/spark/v15/SparkV15BookingPrefunding.sol";
import {SparkV15CourseNotices} from "../../../src/apps/spark/v15/SparkV15CourseNotices.sol";
import {SparkV15TeachingEnd} from "../../../src/apps/spark/v15/SparkV15TeachingEnd.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {SparkV15Materials, SparkV15MaterialsUse} from "../../../src/apps/spark/v15/SparkV15Materials.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15Payments} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {
    SparkV15ReviewCases,
    SparkV15ReviewContext,
    SparkV15ReviewActions,
    SparkV15ConcernIntake
} from "../../../src/apps/spark/v15/SparkV15ReviewCases.sol";
import {IERC20} from "../../../src/apps/spark/legacy/interfaces/IERC20.sol";
import {RequestAllocationFixture} from "../../helpers/RequestAllocationFixture.sol";
import {MockERC20} from "../mocks/MockERC20.sol";

contract MaterialsGrossTest is RequestAllocationFixture {
    uint64 private constant EPOCH = 1_000_000;
    uint64 private constant START = EPOCH + 2;
    uint64 private constant END = EPOCH + 3;
    bytes32 private constant LESSON = bytes32(uint256(42));
    bytes32 private constant PLACE_A = bytes32(uint256(1));
    bytes32 private constant PLACE_B = bytes32(uint256(2));
    bytes32 private constant MAIN = bytes32(uint256(7));
    bytes32 private constant AUXILIARY = bytes32(uint256(8));
    bytes32 private constant BUNDLE = keccak256("signed materials bundle");
    bytes32 private constant AGREEMENT = keccak256("signed teaching services agreement");
    bytes32 private constant TUTOR_CHANNEL = keccak256("signed tutor notice channel");
    bytes32 private constant DOCUMENTS = keccak256("provided terms and course documents");
    address private constant PROVIDER = address(0x7601);
    address private constant TUTOR = address(0x7602);
    address private constant COORDINATOR = address(0x7603);
    address private constant HOLDER = address(0x7604);
    address private constant CUSTOMER_A = address(0x7605);
    address private constant CUSTOMER_B = address(0x7606);
    address private constant REVIEWER = address(0x7607);
    address private constant BACKUP = address(0x7608);
    address private constant REPLACEMENT = address(0x7609);

    MockERC20 private token;
    SparkV15Funds private funds;
    SparkV15Booking private booking;
    SparkV15Payments private payments;
    SparkV15ReviewCases private cases;
    SparkV15ConcernIntake private intake;
    SparkV15Materials private materials;

    function setUp() public {
        requestVm.warp(EPOCH - 4);
        _setUpRequestAllocation(
            SparkV15.APP_ID,
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR),
            SparkV15.OBJECT_PAYMENT_APPROVAL
        );
        token = new MockERC20("Local materials token", "MAT", 6);
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
        intake = new SparkV15ConcernIntake(payments, ROLE_SOURCE, cases);
        cases.bindIntake(intake);
        materials = new SparkV15Materials(booking, cases);
        materials.bindMaterialUse(new SparkV15MaterialsUse(materials));
        require(address(materials).code.length <= 24_576, "materials runtime too large");
        require(address(materials.MATERIAL_USE()).code.length <= 24_576, "materials evidence runtime too large");
        identityRegistry.assignSubject(
            COORDINATOR, SparkV15.APP_ID, ROLE_SOURCE, _actorId(COORDINATOR), "test:coordinator"
        );
        identityRegistry.assignSubject(
            address(booking), SparkV15.APP_ID, funds.BOOKING_ROLE(), _actorId(address(booking)), "test:booking"
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, booking.ACTION_COORDINATE_BOOKING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, booking.ACTION_VERIFY_PREFUNDING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, booking.ACTION_VERIFY_TEACHING(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, funds.BOOKING_ROLE(), funds.ACTION_MANAGE_LESSON_FUNDS(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, materials.ACTION_CHECK_COMBINATIONS(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, materials.ACTION_VERIFY_USE(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, materials.ACTION_RECORD_GROSS(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, materials.ACTION_VERIFY_ATTRIBUTION(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, materials.ACTION_VERIFY_REVIEW_FOLLOW_UP(), true);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_SOURCE, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, true);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, true
        );
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, true
        );
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, true);
        identityRegistry.assignSubject(PROVIDER, SparkV15.APP_ID, ROLE_VERIFIER, _actorId(PROVIDER), "test:provider");
        identityRegistry.assignSubject(REVIEWER, SparkV15.APP_ID, ROLE_VERIFIER, _actorId(REVIEWER), "test:reviewer");
    }

    function testOnlyTheExactAdoptedAnnexLicensesACurrentForm() public {
        SparkV15Materials.Terms memory terms = _standardTerms();
        bytes32 commitment = _publishLesson(terms);
        bytes32 formA = _publishForm(PLACE_A, CUSTOMER_A, PROVIDER);
        bytes32 mismatchedPayer = _publishForm(PLACE_B, CUSTOMER_B, CUSTOMER_B);
        require(!materials.licensedForm(formA, MAIN), "terms licensed before adoption");

        requestVm.expectRevert(SparkV15Materials.InvalidMaterialsTerms.selector);
        requestVm.prank(PROVIDER);
        materials.adoptTerms(terms);

        requestVm.prank(HOLDER);
        materials.acceptTerms(commitment);
        terms.contactRef = keccak256("different contact details");
        requestVm.expectRevert(SparkV15Materials.InvalidMaterialsTerms.selector);
        requestVm.prank(PROVIDER);
        materials.adoptTerms(terms);
        terms.contactRef = keccak256("agreed payment contact");

        requestVm.prank(PROVIDER);
        materials.adoptTerms(terms);
        require(materials.licensedForm(formA, MAIN), "exact annex did not license the material");
        require(!materials.licensedForm(formA, AUXILIARY), "unlicensed material accepted");
        require(!materials.licensedForm(mismatchedPayer, MAIN), "different payer accepted");
        bytes32 current = _publishForm(PLACE_B, CUSTOMER_B, PROVIDER);
        require(materials.licensedForm(current, MAIN), "current licensed version unavailable");
        require(!materials.licensedForm(mismatchedPayer, MAIN), "superseded form used");
    }

    function testEffectiveReplacementListsAndReportsMaterialsAndVerifiedUseStaysIndependent() public {
        SparkV15BookingChanges changes = new SparkV15BookingChanges(booking, payments);
        booking.bindBookingChanges(ISparkV15BookingChanges(address(changes)));
        bytes32[] memory forms = _prepareGroup(_otherTerms());
        requestVm.prank(TUTOR);
        materials.listExpectedMaterials(LESSON, 3);
        _replaceTutor(changes, forms);
        _notifyOriginalArrangement(forms);

        requestVm.expectRevert(SparkV15Materials.InvalidMaterialsUse.selector);
        requestVm.prank(TUTOR);
        materials.listExpectedMaterials(LESSON, 2);
        requestVm.prank(REPLACEMENT);
        materials.listExpectedMaterials(LESSON, 2);
        _teachAfterNotices(forms, false);
        require(booking.getTeaching(LESSON).startPermission == SparkV15Booking.StartPermission.Permitted);

        requestVm.expectRevert(SparkV15Materials.InvalidMaterialsUse.selector);
        requestVm.prank(TUTOR);
        materials.reportMaterialsUsed(LESSON, 1);
        requestVm.prank(REPLACEMENT);
        materials.reportMaterialsUsed(LESSON, 2);
        (uint256 originalExpected,, uint64 originalListedAt, uint64 originalReportedAt) =
            materials.MATERIAL_USE().tutorMaterialsReports(LESSON);
        require(originalExpected == 3 && originalListedAt == EPOCH - 2 && originalReportedAt == 0);
        (uint256 expected, uint256 reported, uint64 listedAt, uint64 reportedAt) =
            materials.MATERIAL_USE().replacementTutorMaterialsReports(LESSON, REPLACEMENT);
        require(expected == 2 && reported == 2 && listedAt == EPOCH && reportedAt == EPOCH + 4);

        SparkV15Materials.UseCheck memory cited = _check(forms[0], MAIN, 4);
        cited.citeTutorReport = true;
        cited.resolveReportOmission = true;
        _verify(cited, 0);
        _verify(_check(forms[1], MAIN, 4), 0);
        requestVm.warp(EPOCH + 5);
        bytes32 gross = _record(_gross(bytes32(0), 5, "verified after replacement", forms), 0);
        require(materials.getChargeScope(gross).total == 8, "reports alone changed verified gross");
    }

    function testM1ZeroRowDoesNotBlockEarlierVerifiedPositiveOnAnotherSeat() public {
        bytes32[] memory forms = _bookAndTeach(false);
        _verify(_check(forms[0], MAIN, 4), 0);
        _verify(_check(forms[1], MAIN, 4), 0);
        requestVm.warp(EPOCH + 5);
        bytes32 original = _record(_gross(bytes32(0), 5, "original", forms), 0);
        require(materials.getHistoricalCharge(original, forms[0]).amount == 4, "A original gross");
        require(materials.getHistoricalCharge(original, forms[1]).amount == 4, "B original gross");

        requestVm.warp(EPOCH + 6);
        SparkV15Materials.UseCheck memory aUse = _check(forms[0], AUXILIARY, 6);
        uint256 aUseEvidence = _materialEvidence(materials.ACTION_VERIFY_USE(), abi.encode(aUse));
        requestVm.warp(EPOCH + 7);
        SparkV15Materials.GrossInput memory aClaim = _gross(original, 7, "A was identified earlier", _one(forms[0]));
        uint256 aClaimEvidence = _materialEvidence(materials.ACTION_RECORD_GROSS(), abi.encode(aClaim));
        SparkV15Materials.GrossInput memory duplicateB = _gross(original, 7, "earlier B claim", _one(forms[1]));
        uint256 duplicateEvidence = _materialEvidence(materials.ACTION_RECORD_GROSS(), abi.encode(duplicateB));
        SparkV15Materials.UseCheck memory earlyB = _check(forms[1], AUXILIARY, 7);
        uint256 earlyBEvidence = _materialEvidence(materials.ACTION_VERIFY_USE(), abi.encode(earlyB));

        requestVm.warp(EPOCH + 8);
        _verify(_check(forms[1], AUXILIARY, 8), 0);
        requestVm.warp(EPOCH + 9);
        bytes32 bClaim = _record(_gross(original, 9, "B recorded first", forms), 0);
        SparkV15Materials.ChargeRow memory bZeroAtA = materials.getHistoricalCharge(bClaim, forms[0]);
        require(bZeroAtA.present && bZeroAtA.amount == 0, "B supplement did not retain A's explicit zero");
        require(materials.getHistoricalCharge(bClaim, forms[1]).amount == 1, "B shortfall");

        _verify(aUse, aUseEvidence);
        bytes32 recordedA = _record(aClaim, aClaimEvidence);
        require(materials.getHistoricalCharge(recordedA, forms[0]).amount == 1, "A shortfall blocked by B zero");
        require(materials.getChargeScope(recordedA).identifiedAt == EPOCH + 7, "A business time lost");
        require(materials.getChargeScope(recordedA).recordedAt == EPOCH + 9, "A archival time lost");
        (uint256 atSeven, uint256 cap) = materials.activeLessonGrossAt(LESSON, EPOCH + 7);
        require(atSeven == 9 && cap == 20, "A and B times or normal fees were conflated");
        (uint256 atNine,) = materials.activeLessonGrossAt(LESSON, EPOCH + 9);
        require(atNine == 10, "once-only per-seat gross");

        _verify(earlyB, earlyBEvidence);
        requestVm.expectRevert(SparkV15Materials.OutOfOrderMaterialCharge.selector);
        _record(duplicateB, duplicateEvidence);
        requestVm.warp(EPOCH + 10);
        require(
            _record(_gross(original, 10, "duplicate B amount", _one(forms[1])), 0) == bytes32(0),
            "duplicate positive B issued"
        );
        require(
            _record(_gross(original, 10, "duplicate A amount", _one(forms[0])), 0) == bytes32(0),
            "duplicate positive A issued"
        );
    }

    function testNonstandardOptionChecksOneNormalFeePerSeatAcrossAllMaterials() public {
        SparkV15Materials.Terms memory terms = _otherTerms();
        terms.otherPrices[1].charges[0] = 21;
        bytes32[] memory forms = _prepareGroup(terms);
        uint256[] memory pricesA = materials.bookingMaterialPrices(LESSON, PLACE_A, 100);
        uint256[] memory pricesB = materials.bookingMaterialPrices(LESSON, PLACE_B, 100);
        require(pricesA[0] == 21 && pricesA[1] == 0, "highest adopted prices for A");
        require(pricesB[0] == 5 && pricesB[1] == 0, "price schedule leaked between places");
        SparkV15Materials.CombinationSeat[][] memory options = new SparkV15Materials.CombinationSeat[][](1);
        options[0] = new SparkV15Materials.CombinationSeat[](2);
        options[0][0] = SparkV15Materials.CombinationSeat(forms[0], 3);
        options[0][1] = SparkV15Materials.CombinationSeat(forms[1], 1);
        SparkV15Materials.CombinationInput memory check = SparkV15Materials.CombinationInput(
            LESSON, EPOCH, keccak256("authorised rates would charge 25 over a capped base of 200"), options
        );
        requestVm.warp(EPOCH);
        uint256 proof = _materialEvidence(materials.ACTION_CHECK_COMBINATIONS(), abi.encode(check));
        requestVm.expectRevert(SparkV15Materials.MaterialsCapExceeded.selector);
        requestVm.prank(COORDINATOR);
        materials.recordCombinationCheck(check, proof);
    }

    function testM2AdoptedGrossAwaitsAttributionOnlyForItsUnverifiedPlaces() public {
        bytes32[] memory forms = _bookAndTeach(true);
        _verify(_check(forms[0], MAIN, 4), 0);
        requestVm.warp(EPOCH + 5);
        bytes32 original = _record(_gross(bytes32(0), 5, "original scope A and B", forms), 0);
        require(materials.getScopeForms(original).length == 2, "omitted B was dropped from scope");
        require(!materials.getHistoricalCharge(original, forms[1]).present, "B was not originally charged");
        (uint256 originalGross, uint256 cap) = materials.activeLessonGrossAt(LESSON, EPOCH + 5);
        require(originalGross == 4 && cap == 10, "unused B entered original gross or cap");

        bytes32 caseId = _reviewAndAdopt(original, forms[0], 5);
        _assertScope(original, forms[0], 8, 4, false);
        _assertScope(original, forms[0], 9, 4, true);
        _assertScope(original, forms[1], 9, 0, true);
        (uint256 reviewedGross,) = materials.activeLessonGrossAt(LESSON, EPOCH + 9);
        require(reviewedGross == 5, "whole-scope reviewed gross not used in cap");

        _attribute(caseId, forms[1], 0, 0, 9);
        _assertScope(original, forms[1], 9, 0, false);
        requestVm.warp(EPOCH + 10);
        _verify(_check(forms[1], MAIN, 10), 0);
        bytes32 bClaim = _record(_gross(original, 10, "verified B while A is pending", forms), 0);
        require(materials.getHistoricalCharge(bClaim, forms[1]).amount == 4, "pending A blocked B");
        require(materials.getHistoricalCharge(bClaim, forms[0]).amount == 0, "pending A was allocated");

        requestVm.warp(EPOCH + 11);
        _attribute(caseId, forms[0], 4, 5, 11);
        _verify(_check(forms[0], AUXILIARY, 11), 0);
        _assertScope(original, forms[0], 10, 4, true);
        _assertScope(original, forms[0], 11, 5, false);
        require(materials.getHistoricalCharge(original, forms[0]).amount == 4, "historical charge overwritten");
        requestVm.warp(EPOCH + 12);
        require(
            _record(_gross(original, 12, "A actual use rechecked", _one(forms[0])), 0) == bytes32(0),
            "revision issued a duplicate shortfall"
        );
        (uint256 active, uint256 currentCap) = materials.activeLessonGrossAt(LESSON, EPOCH + 12);
        require(active == 9 && currentCap == 20, "gross cap diverged from effective seat charge");
    }

    function testM2ReductionRequiresNewUseEvidenceCompatibleWithTheAdoptedReview() public {
        bytes32[] memory forms = _bookAndTeach(true);
        uint256 oldUse = _verify(_check(forms[0], MAIN, 4), 0);
        requestVm.warp(EPOCH + 5);
        bytes32 original = _record(_gross(bytes32(0), 5, "original A charge", forms), 0);
        bytes32 caseId = _reviewAndAdopt(original, forms[0], 3);
        _attribute(caseId, forms[0], 4, 3, 9);
        _attribute(caseId, forms[1], 0, 0, 9);
        _assertScope(original, forms[0], 9, 3, false);

        requestVm.warp(EPOCH + 10);
        SparkV15Materials.GrossInput memory candidate = _gross(original, 10, "stale facts", _one(forms[0]));
        require(_record(candidate, 0) == bytes32(0), "stale use revived a reduced amount");

        requestVm.warp(EPOCH + 11);
        uint256 newUse = _verify(_check(forms[0], AUXILIARY, 11), 0);
        candidate = _gross(original, 11, "unlinked new facts", _one(forms[0]));
        require(_record(candidate, 0) == bytes32(0), "unlinked use revived a reduced amount");

        SparkV15Materials.ReviewFollowUp memory followUp = SparkV15Materials.ReviewFollowUp({
            caseId: caseId,
            formId: forms[0],
            useEvidenceId: oldUse,
            sourceRef: keccak256("verified later use resolves the review basis"),
            checkedAt: EPOCH + 11
        });
        uint256 proof = _materialEvidence(materials.ACTION_VERIFY_REVIEW_FOLLOW_UP(), abi.encode(followUp));
        requestVm.expectRevert(SparkV15Materials.InvalidGrossReview.selector);
        requestVm.prank(COORDINATOR);
        materials.verifyReviewFollowUp(followUp, proof);
        followUp.useEvidenceId = newUse;
        proof = _materialEvidence(materials.ACTION_VERIFY_REVIEW_FOLLOW_UP(), abi.encode(followUp));
        requestVm.prank(COORDINATOR);
        materials.verifyReviewFollowUp(followUp, proof);

        requestVm.warp(EPOCH + 12);
        candidate = _gross(original, 12, "new verified compatible use", _one(forms[0]));
        bytes32 supplement = _record(candidate, 0);
        require(
            materials.getHistoricalCharge(supplement, forms[0]).amount == 2, "use recheck did not apply corrected basis"
        );
    }

    function _reviewAndAdopt(bytes32 original, bytes32 formId, uint256 revised) private returns (bytes32 caseId) {
        SparkV15ReviewContext.ReviewTerms memory terms = SparkV15ReviewContext.ReviewTerms({
            lessonId: LESSON,
            publication: keccak256("published ordinary and alternative materials contacts"),
            governingForm: formId,
            provider: PROVIDER,
            coordinator: COORDINATOR,
            alternativeContact: BACKUP,
            leadAcademicTutor: VERIFIER_ACTOR,
            namedReviewer: REVIEWER,
            escalationContact: BACKUP,
            replyDate: 0,
            replyPeriod: 10,
            replyLegalDeadline: 0,
            reviewDeadline: EPOCH + 18,
            reviewLegalDeadline: 0
        });
        bytes32 termsId = keccak256(abi.encode(terms));
        uint256 publication = _caseEvidence(termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, PROVIDER, termsId);
        requestVm.prank(PROVIDER);
        intake.publishContacts(terms, publication, _actorId(PROVIDER));

        bytes32 concernRef = keccak256("material gross correction after undercounted use");
        caseId = cases.caseIdFor(LESSON, concernRef);
        address[] memory parties = new address[](2);
        parties[0] = HOLDER;
        parties[1] = PROVIDER;
        SparkV15ReviewContext.ConcernInput memory concern = SparkV15ReviewContext.ConcernInput({
            termsId: termsId,
            concernRef: concernRef,
            obligationId: bytes32(0),
            receiver: COORDINATOR,
            subject: SparkV15ReviewContext.ConcernSubject.MaterialOmission,
            alternativeGround: SparkV15ReviewContext.AlternativeGround.None,
            claim: keccak256("source supports an omitted material use"),
            subjectRef: original,
            parties: parties
        });
        uint256 intakeProof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_RECEIVE_CONCERN, HOLDER, keccak256(abi.encode(concern)));
        requestVm.prank(HOLDER);
        intake.receiveConcern(concern, intakeProof);

        SparkV15ReviewContext.OriginalInput memory old = SparkV15ReviewContext.OriginalInput({
            termsId: termsId,
            concernRef: concernRef,
            obligationId: bytes32(0),
            paymentCommitment: bytes32(0),
            decider: COORDINATOR,
            decidedAt: EPOCH + 5,
            outcome: materials.grossReviewBasis(original, 4),
            parties: parties
        });
        uint256 originalProof = _caseEvidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(old))
        );
        requestVm.prank(VERIFIER_ACTOR);
        cases.retainOriginal(old, originalProof, _authority(ROLE_VERIFIER));

        requestVm.warp(EPOCH + 8);
        SparkV15ReviewContext.ReviewInput memory result = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.CorrectionRequired,
            outcome: materials.grossReviewOutcome(caseId, original, 4, revised),
            reasons: keccak256("independent review identified the corrected amount"),
            approvalRequestId: 0
        });
        uint256 reviewProof =
            _caseEvidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(result)));
        requestVm.prank(REVIEWER);
        cases.decideReview(caseId, result, reviewProof, _actorId(REVIEWER));
        materials.bindGrossReview(caseId, original, 4, revised);
        (uint256 unadoptedGross,) = materials.activeLessonGrossAt(LESSON, EPOCH + 8);
        require(unadoptedGross == 4, "unadopted review changed gross");

        requestVm.warp(EPOCH + 9);
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("all parties notified"), EPOCH + 9);
        bytes32 partiesHash = keccak256(abi.encode(parties));
        uint256 adoptionProof = _caseEvidence(
            caseId,
            SparkV15ReviewActions.ACTION_ADOPT_CORRECTION,
            COORDINATOR,
            keccak256(abi.encode(notice, originalProof, reviewProof, partiesHash, partiesHash))
        );
        requestVm.prank(COORDINATOR);
        cases.adoptCorrection(caseId, notice, adoptionProof, _actorId(COORDINATOR));
    }

    function _attribute(bytes32 caseId, bytes32 formId, uint128 previous, uint128 revised, uint64 time) private {
        SparkV15Materials.GrossAttributionInput memory input = SparkV15Materials.GrossAttributionInput(
            caseId,
            formId,
            previous,
            revised,
            EPOCH + time,
            keccak256(abi.encode("verified case and seat", formId, revised))
        );
        uint256 proof = _materialEvidence(materials.ACTION_VERIFY_ATTRIBUTION(), abi.encode(input));
        requestVm.prank(COORDINATOR);
        materials.recordGrossAttribution(input, proof);
    }

    function _assertScope(bytes32 scope, bytes32 formId, uint64 time, uint128 expected, bool pending) private view {
        (uint128 amount, bool waiting) = materials.activeScopeGrossAt(scope, formId, EPOCH + time);
        require(amount == expected && waiting == pending, "unexpected attributed seat gross");
    }

    function _caseEvidence(bytes32 subject, bytes32 action, address actor, bytes32 payload) private returns (uint256) {
        return _evidence(cases.evidenceCommitment(subject, action, actor, payload));
    }

    function _standardTerms() private pure returns (SparkV15Materials.Terms memory terms) {
        SparkV15Materials.MaterialTerms[] memory lines = new SparkV15Materials.MaterialTerms[](1);
        SparkV15Materials.HolderShare[] memory holders = new SparkV15Materials.HolderShare[](1);
        holders[0] = SparkV15Materials.HolderShare(HOLDER, 1);
        lines[0] = SparkV15Materials.MaterialTerms(MAIN, 6, holders, new address[](0));
        terms = SparkV15Materials.Terms({
            lessonId: LESSON,
            bundleRef: BUNDLE,
            payer: PROVIDER,
            contactRef: keccak256("agreed payment contact"),
            licenceRef: keccak256("use licensed only in this lesson"),
            sharesAndAdjustmentsRef: keccak256("agreed shares and adjustments"),
            paymentDue: EPOCH + 20,
            paymentDeadline: EPOCH + 20,
            rateDenominator: 100,
            materials: lines,
            otherPrices: new SparkV15Materials.PriceRow[](0)
        });
    }

    function _otherTerms() private pure returns (SparkV15Materials.Terms memory terms) {
        terms = _standardTerms();
        terms.rateDenominator = 0;
        SparkV15Materials.HolderShare[] memory holders = terms.materials[0].holders;
        terms.materials = new SparkV15Materials.MaterialTerms[](2);
        terms.materials[0] = SparkV15Materials.MaterialTerms(MAIN, 0, holders, new address[](0));
        terms.materials[1] = SparkV15Materials.MaterialTerms(AUXILIARY, 0, holders, new address[](0));
        terms.otherPrices = new SparkV15Materials.PriceRow[](4);
        for (uint256 i; i < 2; ++i) {
            bytes32 placeId = i == 0 ? PLACE_A : PLACE_B;
            uint128[] memory alone = new uint128[](1);
            alone[0] = 4;
            uint128[] memory together = new uint128[](2);
            together[0] = 5;
            terms.otherPrices[i * 2] = SparkV15Materials.PriceRow(placeId, 100, 1, alone);
            terms.otherPrices[i * 2 + 1] = SparkV15Materials.PriceRow(placeId, 100, 3, together);
        }
    }

    function _bookAndTeach(bool singlePlaceOptions) private returns (bytes32[] memory forms) {
        forms = _prepareGroup(_otherTerms());
        _teach(forms, singlePlaceOptions);
    }

    function _prepareGroup(SparkV15Materials.Terms memory agreement) private returns (bytes32[] memory forms) {
        bytes32 terms = _publishLesson(agreement);
        requestVm.prank(HOLDER);
        materials.acceptTerms(terms);
        requestVm.prank(PROVIDER);
        materials.adoptTerms(agreement);
        forms = new bytes32[](2);
        forms[0] = _publishForm(PLACE_A, CUSTOMER_A, PROVIDER);
        forms[1] = _publishForm(PLACE_B, CUSTOMER_B, PROVIDER);
        _confirm(forms);
    }

    function _confirm(bytes32[] memory forms) private {
        bytes32 inventory = keccak256("actual available tokens for local lesson");
        token.mint(address(funds), 200);
        uint256 prefunding = _evidence(booking.prefundingCommitment(LESSON, forms, 120, inventory));
        requestVm.prank(VERIFIER_ACTOR);
        booking.verifyPrefunding(LESSON, forms, 120, inventory, prefunding);
        requestVm.warp(EPOCH - 2);
        requestVm.prank(PROVIDER);
        booking.signTeachingAgreement(LESSON);
        requestVm.prank(TUTOR);
        booking.signTeachingAgreement(LESSON);
        for (uint256 i; i < forms.length; ++i) {
            bytes32 id = forms[i];
            address customer = booking.getForm(id).terms.customer;
            _provide(id, customer);
            _provide(id, TUTOR);
            requestVm.prank(PROVIDER);
            booking.acceptForm(id, SparkV15Booking.Acceptance.Provider);
            requestVm.prank(TUTOR);
            booking.acceptForm(id, SparkV15Booking.Acceptance.Tutor);
            requestVm.prank(customer);
            booking.acceptForm(id, SparkV15Booking.Acceptance.Customer);
            bytes32 discount = keccak256("funded full discount");
            uint256 discountEvidence = _evidence(booking.fullDiscountCommitment(id, discount));
            requestVm.prank(COORDINATOR);
            booking.confirmPlace(id, discount, discountEvidence, new SparkV15Funds.RechargeDebit[](0));
        }
    }

    function _teach(bytes32[] memory forms, bool omitB) private {
        _notifyOriginalArrangement(forms);
        requestVm.prank(TUTOR);
        materials.listExpectedMaterials(LESSON, 3);
        _teachAfterNotices(forms, omitB);
        requestVm.prank(TUTOR);
        materials.reportMaterialsUsed(LESSON, 1);
    }

    function _notifyOriginalArrangement(bytes32[] memory forms) private {
        requestVm.warp(EPOCH);
        bytes32 notice = keccak256("delivered on each agreed channel");
        for (uint256 i; i < forms.length; ++i) {
            uint256 proof = _evidence(booking.studentNoticeCommitment(forms[i], EPOCH, notice));
            requestVm.prank(COORDINATOR);
            booking.recordStudentNotice(forms[i], EPOCH, notice, proof);
        }
        uint256 tutorProof = _evidence(booking.tutorNoticeCommitment(LESSON, TUTOR_CHANNEL, EPOCH, notice));
        requestVm.prank(COORDINATOR);
        booking.recordTutorNotice(LESSON, TUTOR_CHANNEL, EPOCH, notice, tutorProof);
    }

    function _teachAfterNotices(bytes32[] memory forms, bool omitB) private {
        requestVm.warp(EPOCH + 1);
        bytes32 roster = keccak256("verified final roster");
        uint256 rosterProof = _evidence(booking.rosterLockCommitment(LESSON, roster));
        requestVm.prank(COORDINATOR);
        booking.lockRoster(LESSON, roster, rosterProof);
        _checkCombinations(forms, omitB);

        requestVm.warp(START);
        address[] memory students = new address[](2);
        students[0] = CUSTOMER_A;
        students[1] = CUSTOMER_B;
        SparkV15Booking.StartObservation memory start =
            SparkV15Booking.StartObservation(START, true, students, keccak256("actual opening"), bytes32(0));
        uint256 startProof = _evidence(booking.teachingStartCommitment(LESSON, start));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingStarted(LESSON, start, startProof);
        requestVm.warp(END);
        bytes32 ended = keccak256("actual end");
        uint256 endProof = _evidence(booking.teachingEndCommitment(LESSON, END, ended));
        requestVm.prank(VERIFIER_ACTOR);
        booking.recordTeachingEnded(LESSON, END, ended, endProof);
        requestVm.warp(EPOCH + 4);
    }

    function _replaceTutor(SparkV15BookingChanges changes, bytes32[] memory forms) private {
        requestVm.warp(EPOCH - 1);
        SparkV15BookingChanges.ArrangementTerms memory next;
        next.startsAt = START;
        next.endsAt = END;
        next.effectiveAt = EPOCH;
        next.timeZoneRef = keccak256("UTC");
        next.replacement = SparkV15BookingChanges.ReplacementTerms(
            REPLACEMENT, 100, keccak256("replacement agreement"), keccak256("replacement pay"), DOCUMENTS,
            keccak256("replacement duties"), DOCUMENTS, TUTOR_CHANNEL
        );
        bytes32 contact = keccak256("actual replacement contact");
        uint256 proof = _evidence(changes.proposalCommitment(LESSON, next, EPOCH - 1, contact));
        requestVm.prank(COORDINATOR);
        bytes32 changeId = changes.proposeArrangement(LESSON, next, EPOCH - 1, contact, proof);
        requestVm.prank(PROVIDER);
        changes.signReplacementAgreement(changeId);
        requestVm.prank(REPLACEMENT);
        changes.signReplacementAgreement(changeId);
        requestVm.prank(REPLACEMENT);
        changes.acceptTutor(changeId);
        requestVm.prank(PROVIDER);
        changes.acceptProvider(changeId);
        for (uint256 i; i < forms.length; ++i) {
            address payer = booking.getForm(forms[i]).terms.payer;
            requestVm.prank(payer);
            changes.acceptPlace(changeId, forms[i]);
        }
        requestVm.prank(COORDINATOR);
        changes.recordAgreement(changeId);
        bytes32 notice = keccak256("received replacement arrangement");
        for (uint256 i; i < forms.length; ++i) {
            proof = _evidence(changes.studentChangeNoticeCommitment(changeId, forms[i], EPOCH - 1, notice));
            requestVm.prank(COORDINATOR);
            changes.recordStudentChangeNotice(changeId, forms[i], EPOCH - 1, notice, proof);
        }
        proof = _evidence(changes.tutorChangeNoticeCommitment(changeId, TUTOR_CHANNEL, EPOCH - 1, notice));
        requestVm.prank(PROVIDER);
        changes.recordTutorChangeNotice(changeId, TUTOR_CHANNEL, EPOCH - 1, notice, proof);
        requestVm.prank(COORDINATOR);
        changes.finalizeArrangement(changeId);
    }

    function _checkCombinations(bytes32[] memory forms, bool omitB) private {
        SparkV15Materials.CombinationSeat[][] memory options = new SparkV15Materials.CombinationSeat[][](omitB ? 6 : 4);
        for (uint256 i; i < 4; ++i) {
            options[i] = new SparkV15Materials.CombinationSeat[](2);
            options[i][0] = SparkV15Materials.CombinationSeat(forms[0], (i & 1) == 0 ? 1 : 3);
            options[i][1] = SparkV15Materials.CombinationSeat(forms[1], (i & 2) == 0 ? 1 : 3);
        }
        if (omitB) {
            options[4] = new SparkV15Materials.CombinationSeat[](1);
            options[5] = new SparkV15Materials.CombinationSeat[](1);
            options[4][0] = SparkV15Materials.CombinationSeat(forms[0], 1);
            options[5][0] = SparkV15Materials.CombinationSeat(forms[0], 3);
        }
        SparkV15Materials.CombinationInput memory check =
            SparkV15Materials.CombinationInput(LESSON, EPOCH + 1, keccak256("signed prospective options"), options);
        uint256 proof = _materialEvidence(materials.ACTION_CHECK_COMBINATIONS(), abi.encode(check));
        requestVm.prank(COORDINATOR);
        materials.recordCombinationCheck(check, proof);
    }

    function _provide(bytes32 formId, address recipient) private {
        uint256 proof = _evidence(booking.provisionCommitment(formId, recipient, DOCUMENTS));
        requestVm.prank(COORDINATOR);
        booking.recordTermsProvision(formId, recipient, DOCUMENTS, proof);
    }

    function _check(bytes32 formId, bytes32 material, uint64 knownAt)
        private
        pure
        returns (SparkV15Materials.UseCheck memory)
    {
        return SparkV15Materials.UseCheck({
            formId: formId,
            material: material,
            usedAt: START,
            checkedAt: EPOCH + knownAt,
            source: SparkV15Materials.UseSource.LessonRecord,
            serviceRef: keccak256("recognised delivered teaching"),
            sourceRef: keccak256(abi.encode("verifiable lesson record", formId, material, knownAt)),
            citeTutorReport: false,
            resolveReportOmission: false,
            appointmentCaseId: bytes32(0)
        });
    }

    function _verify(SparkV15Materials.UseCheck memory check, uint256 proof) private returns (uint256) {
        if (proof == 0) proof = _materialEvidence(materials.ACTION_VERIFY_USE(), abi.encode(check));
        requestVm.prank(COORDINATOR);
        materials.verifyUse(check, proof);
        return proof;
    }

    function _gross(bytes32 original, uint64 time, string memory source, bytes32[] memory forms)
        private
        pure
        returns (SparkV15Materials.GrossInput memory)
    {
        return SparkV15Materials.GrossInput(LESSON, MAIN, original, keccak256(bytes(source)), EPOCH + time, forms);
    }

    function _record(SparkV15Materials.GrossInput memory input, uint256 proof) private returns (bytes32) {
        if (proof == 0) proof = _materialEvidence(materials.ACTION_RECORD_GROSS(), abi.encode(input));
        requestVm.prank(COORDINATOR);
        return materials.recordGross(input, proof);
    }

    function _one(bytes32 item) private pure returns (bytes32[] memory only) {
        only = new bytes32[](1);
        only[0] = item;
    }

    function _materialEvidence(bytes32 action, bytes memory payload) private returns (uint256) {
        return _evidence(materials.operationEvidenceCommitment(LESSON, action, COORDINATOR, keccak256(payload)));
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
                evidenceTypeHash: keccak256("spark.materials.verified.source"),
                disclosurePolicyId: requestPolicyId,
                authorityId: _authority(ROLE_SOURCE),
                uri: "test:verified-materials-facts"
            })
        );
    }

    function _publishLesson(SparkV15Materials.Terms memory terms) private returns (bytes32 commitment) {
        commitment = materials.termsCommitment(terms);
        SparkV15Booking.LessonTerms memory lesson;
        lesson.lessonId = LESSON;
        lesson.provider = PROVIDER;
        lesson.tutor = TUTOR;
        lesson.coordinator = COORDINATOR;
        lesson.startsAt = START;
        lesson.endsAt = END;
        lesson.rosterLockAt = EPOCH + 1;
        lesson.rosterRef = keccak256("signed group roster");
        lesson.timeZoneRef = keccak256("UTC");
        lesson.tutorNoticeChannelRef = TUTOR_CHANNEL;
        lesson.tutorFee = 100;
        lesson.tutorAgreementRef = AGREEMENT;
        lesson.serviceTermsRef = DOCUMENTS;
        lesson.tutorPayTermsRef = AGREEMENT;
        lesson.providerResponsibilitiesRef = DOCUMENTS;
        lesson.tutorResponsibilitiesRef = AGREEMENT;
        lesson.startTermsRef = DOCUMENTS;
        lesson.documentsRef = DOCUMENTS;
        lesson.materialsTermsRef = commitment;
        requestVm.prank(COORDINATOR);
        booking.publishLesson(lesson);
    }

    function _publishForm(bytes32 placeId, address customer, address materialPayer) private returns (bytes32 form) {
        SparkV15Booking.PlaceTerms memory place;
        place.placeId = placeId;
        place.customer = customer;
        place.payer = customer;
        place.student = customer;
        place.creditAccount = funds.creditAccount(customer);
        place.studentNoticeChannelRef = keccak256(abi.encode("signed student notice channel", customer));
        place.normalFee = 100;
        place.payableFee = 0;
        place.discountBasis = keccak256("signed full discount");
        place.materialsBundleRef = BUNDLE;
        place.materialPayer = materialPayer;
        SparkV15BookingChanges changes = SparkV15BookingChanges(address(booking.bookingChanges()));
        SparkV15BookingChanges.ChangeTerms memory changeTerms;
        if (address(changes) != address(0)) place.changeTermsRef = changes.changeTermsCommitment(changeTerms);
        requestVm.prank(COORDINATOR);
        form = booking.publishForm(LESSON, place);
        if (address(changes) != address(0)) changes.admitChangeTerms(form, changeTerms);
    }

    function _actorId(address actor) private pure returns (bytes32) {
        return keccak256(abi.encode("material actor", actor));
    }
}
