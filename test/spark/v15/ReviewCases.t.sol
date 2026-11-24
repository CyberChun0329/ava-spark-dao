// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {SparkV15, SparkV15ApplicationModule} from "../../../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {
    ISparkV15AdoptedDispositions,
    SparkV15Payments
} from "../../../src/apps/spark/v15/SparkV15Payments.sol";
import {SparkV15PaymentHolds} from "../../../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15Funds} from "../../../src/apps/spark/v15/SparkV15Funds.sol";
import {SparkV15Returns} from "../../../src/apps/spark/v15/SparkV15Returns.sol";
import {SparkV15TemporaryHolds} from "../../../src/apps/spark/v15/SparkV15TemporaryHolds.sol";
import {
    SparkV15ReviewCases,
    SparkV15ConcernIntake,
    SparkV15ReviewContext,
    SparkV15ReviewActions
} from "../../../src/apps/spark/v15/SparkV15ReviewCases.sol";
import {IERC20} from "../../../src/apps/spark/legacy/interfaces/IERC20.sol";
import {RequestAllocationFixture} from "../../helpers/RequestAllocationFixture.sol";
import {MockERC20} from "../mocks/MockERC20.sol";

interface ReviewSnapshotVm {
    function snapshotState() external returns (uint256);
    function revertToState(uint256 snapshotId) external returns (bool);
}

contract ReviewCasesTest is RequestAllocationFixture {
    uint64 private constant EPOCH = 1_000_000;
    bytes32 private constant LESSON = keccak256("reviewed lesson");
    bytes32 private constant CONCERN = keccak256("registered concern reference");
    address private constant COORDINATOR = address(0x8101);
    address private constant ALTERNATIVE = address(0x8102);
    address private constant LEAD_TUTOR = address(0x8103);
    address private constant REVIEWER = address(0x8104);
    address private constant ESCALATION = address(0x8105);
    address private constant CONTRIBUTOR = address(0x8106);
    address private constant STUDENT = address(0x8107);
    address private constant CORE_PARTNER = address(0x8108);
    address private constant SUBSTITUTE = address(0x8109);

    SparkV15Payments private payments;
    SparkV15ReviewCases private cases;
    SparkV15ConcernIntake private intake;

    function setUp() public {
        requestVm.warp(EPOCH);
        _setUpRequestAllocation(
            SparkV15.APP_ID,
            new SparkV15ApplicationModule(REQUEST_WORKFLOW, ROLE_SOURCE, ROLE_VERIFIER, ROLE_ALLOCATOR),
            SparkV15.OBJECT_PAYMENT_APPROVAL
        );
        MockERC20 token = new MockERC20("Spark fixture USD", "TUSD", 6);
        payments = new SparkV15Payments(requestAllocation, IERC20(address(token)), REQUEST_WORKFLOW, ROLE_VERIFIER);
        payments.bindHolds(
            new SparkV15PaymentHolds(address(payments), requestAllocation, REQUEST_WORKFLOW, ROLE_VERIFIER)
        );
        cases = new SparkV15ReviewCases(payments, ROLE_SOURCE);
        intake = new SparkV15ConcernIntake(payments, ROLE_SOURCE, cases);
        cases.bindIntake(intake);
        require(
            address(cases).code.length <= 24_576 && address(intake).code.length <= 24_576, "oversized review runtime"
        );
        authorityMatrix.setPermission(
            SparkV15.APP_ID, ROLE_VERIFIER, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, true
        );
        _grantCaseAction(SparkV15ReviewActions.ACTION_ACKNOWLEDGE_CONCERN);
        _grantCaseAction(SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN);
        _grantCaseAction(SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR);
        _grantCaseAction(SparkV15ReviewActions.ACTION_DECIDE_INITIAL);
        _grantCaseAction(SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL);
        _grantCaseAction(SparkV15ReviewActions.ACTION_DECIDE_REVIEW);
        _grantCaseAction(SparkV15ReviewActions.ACTION_ADOPT_CORRECTION);
        _grantCaseAction(SparkV15ReviewActions.ACTION_ESCALATE_CASE);
        _grantCaseAction(SparkV15.ACTION_ESTABLISH_PAYMENT);
        _enrol(COORDINATOR);
        _enrol(ALTERNATIVE);
        _enrol(LEAD_TUTOR);
        _enrol(CORE_PARTNER);
        _enrol(SUBSTITUTE);
        _enrol(REVIEWER);
        _enrol(ESCALATION);
    }

    function testApprovalStopAdoptionIsAtomicAndKeepsARealPartialReceipt() public {
        bytes32 termsId = _publishTerms(true);
        bytes32 obligationId = _establishPayment();
        bytes32 caseId = cases.caseIdFor(LESSON, CONCERN);
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        bytes32 partiesHash = keccak256(abi.encode(parties));
        SparkV15ReviewContext.OriginalInput memory original = SparkV15ReviewContext.OriginalInput({
            termsId: termsId,
            concernRef: CONCERN,
            obligationId: obligationId,
            paymentCommitment: payments.getObligation(obligationId).commitment,
            decider: LEAD_TUTOR,
            decidedAt: EPOCH,
            outcome: keccak256("initial decision to permit payment"),
            parties: parties
        });
        uint256 originalProof = _evidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(original))
        );
        requestVm.prank(VERIFIER_ACTOR);
        cases.retainOriginal(original, originalProof, _authority(ROLE_VERIFIER));
        uint256 requestId = _recordPaymentApproval(obligationId);

        requestVm.warp(EPOCH + 20);
        requestVm.prank(STUDENT);
        uint256 receiptId = payments.pay(requestId, 2);
        requestVm.warp(EPOCH + 21);
        bytes32 outcome = payments.stopApprovalOutcome(caseId, requestId);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.CorrectionRequired,
            outcome: outcome,
            reasons: keccak256("independent review found the unpaid approval must be stopped"),
            approvalRequestId: requestId
        });
        uint256 reviewProof =
            _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(review)));
        requestVm.prank(REVIEWER);
        cases.decideReview(caseId, review, reviewProof, _businessAuthority(REVIEWER));

        requestVm.warp(EPOCH + 22);
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("the decision was notified to all original parties"), EPOCH + 22);
        uint256 adoptionProof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_ADOPT_CORRECTION,
            COORDINATOR,
            keccak256(abi.encode(notice, originalProof, reviewProof, partiesHash, bytes32(0)))
        );
        bytes32 coordinatorAuthority = _businessAuthority(COORDINATOR);
        requestVm.prank(COORDINATOR);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        cases.adoptCorrection(caseId, notice, adoptionProof, coordinatorAuthority);
        requestVm.prank(COORDINATOR);
        requestVm.expectRevert();
        cases.adoptApprovalStop(caseId, notice, adoptionProof, coordinatorAuthority, requestId);
        require(cases.getAdoptedDisposition(caseId).adoptedAt == 0, "failed payment callback left an adoption");

        bytes32 effectRole = payments.caseEffectRole();
        authorityMatrix.setPermission(SparkV15.APP_ID, effectRole, payments.ACTION_APPLY_CASE_EFFECT(), true);
        identityRegistry.assignSubject(
            address(cases), SparkV15.APP_ID, effectRole, _authority(effectRole), "test:case-effects"
        );
        requestVm.prank(COORDINATOR);
        cases.adoptApprovalStop(caseId, notice, adoptionProof, coordinatorAuthority, requestId);
        (bytes32 target, bytes32 adoptedOutcome, uint64 adoptedAt) = cases.adoptedPaymentEffect(caseId);
        require(target == obligationId && adoptedOutcome == outcome && adoptedAt == EPOCH + 22, "atomic case output");
        require(payments.getApproval(requestId).stoppedByCase == caseId, "approval effect not applied");
        require(payments.getReceipt(receiptId).amount == 2, "prior receipt was not retained");
        requestVm.prank(STUDENT);
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        payments.pay(requestId, 3);
    }

    function testAdoptedPayeeCorrectionDoesNotCreditEarlierReceiptsOrCarryApprovalAcrossTheSameDestination() public {
        bytes32 termsId = _publishTerms(true);
        bytes32 obligationId = _establishPayment(true);
        bytes32 caseId = cases.caseIdFor(LESSON, CONCERN);
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        SparkV15Payments.Obligation memory originalPayment = payments.getObligation(obligationId);
        SparkV15ReviewContext.OriginalInput memory original = SparkV15ReviewContext.OriginalInput({
            termsId: termsId,
            concernRef: CONCERN,
            obligationId: obligationId,
            paymentCommitment: originalPayment.commitment,
            decider: LEAD_TUTOR,
            decidedAt: EPOCH,
            outcome: keccak256("original payee decision"),
            parties: parties
        });
        uint256 originalProof = _evidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(original))
        );
        requestVm.prank(VERIFIER_ACTOR);
        cases.retainOriginal(original, originalProof, _authority(ROLE_VERIFIER));
        uint256 requestId = _recordPaymentApproval(obligationId);
        requestVm.warp(EPOCH + 20);
        requestVm.prank(STUDENT);
        uint256 previousReceipt = payments.pay(requestId, 2);

        requestVm.warp(EPOCH + 21);
        SparkV15Payments.PaymentRevision memory revision = SparkV15Payments.PaymentRevision({
            obligationId: obligationId,
            correctAmount: 7,
            beneficiary: SUBSTITUTE,
            destination: originalPayment.terms.recipient,
            expectedVersion: payments.getObligation(obligationId).version
        });
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.CorrectionRequired,
            outcome: bytes32(0),
            reasons: keccak256("the same agreed collecting destination holds funds for a different payee"),
            approvalRequestId: 0
        });
        ++revision.expectedVersion;
        review.outcome = _paymentRevisionOutcome(caseId, revision, originalPayment.commitment);
        uint256 forwardVersionProof =
            _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(review)));
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        requestVm.prank(REVIEWER);
        cases.decidePaymentRevision(caseId, review, revision, forwardVersionProof, _businessAuthority(REVIEWER));
        require(cases.reviewedPaymentRevision(caseId) == bytes32(0), "no decision for a future version");

        --revision.expectedVersion;
        review.outcome = _paymentRevisionOutcome(caseId, revision, originalPayment.commitment);
        uint256 reviewProof =
            _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(review)));
        requestVm.prank(REVIEWER);
        cases.decidePaymentRevision(caseId, review, revision, reviewProof, _businessAuthority(REVIEWER));
        require(cases.reviewedPaymentRevision(caseId) == review.outcome, "payment revision not exposed");

        requestVm.warp(EPOCH + 22);
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("correction delivered to the parties"), EPOCH + 22);
        uint256 adoptionProof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_ADOPT_CORRECTION,
            COORDINATOR,
            keccak256(abi.encode(notice, originalProof, reviewProof, keccak256(abi.encode(parties)), bytes32(0)))
        );
        bytes32 role = payments.caseEffectRole();
        authorityMatrix.setPermission(SparkV15.APP_ID, role, payments.ACTION_APPLY_CASE_EFFECT(), true);
        identityRegistry.assignSubject(address(cases), SparkV15.APP_ID, role, _authority(role), "test:case-effects");
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        requestVm.prank(COORDINATOR);
        cases.adoptCorrection(caseId, notice, adoptionProof, _businessAuthority(COORDINATOR));
        _checkUnadoptedRevisionAfterLaterReceipt(caseId, notice, adoptionProof, revision, requestId);
        requestVm.prank(COORDINATOR);
        cases.adoptPaymentRevision(caseId, notice, adoptionProof, _businessAuthority(COORDINATOR), revision);

        SparkV15Payments.Obligation memory corrected = payments.getObligation(obligationId);
        require(
            corrected.terms.amount == originalPayment.terms.amount && corrected.correctAmount == 7, "assessment history"
        );
        require(
            corrected.beneficiary == SUBSTITUTE && corrected.destination == originalPayment.terms.recipient, "party"
        );
        require(corrected.paid == 0 && payments.getReceipt(previousReceipt).amount == 2, "previous recipient counted");
        require(
            payments.retainedByBeneficiary(obligationId, originalPayment.terms.recipient) == 2,
            "previous history vanished"
        );
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(STUDENT);
        payments.pay(requestId, 1);

        _payCorrectedObligationAndReturnOldReceipt(obligationId, requestId, previousReceipt);
    }

    function _paymentRevisionOutcome(
        bytes32 caseId,
        SparkV15Payments.PaymentRevision memory revision,
        bytes32 commitment
    ) private view returns (bytes32) {
        return keccak256(
            abi.encode(keccak256("spark.v1.5.revise-payment"), block.chainid, address(payments), caseId, revision, commitment)
        );
    }

    function _checkUnadoptedRevisionAfterLaterReceipt(
        bytes32 caseId,
        SparkV15ReviewContext.Notice memory notice,
        uint256 adoptionProof,
        SparkV15Payments.PaymentRevision memory revision,
        uint256 approvalId
    ) private {
        ReviewSnapshotVm snapshots = ReviewSnapshotVm(address(requestVm));
        uint256 state = snapshots.snapshotState();
        requestVm.prank(STUDENT);
        payments.pay(approvalId, 1);
        require(payments.getObligation(revision.obligationId).paid == 3, "intervening payment actually executed");
        requestVm.expectRevert(SparkV15Payments.InvalidObligation.selector);
        requestVm.prank(COORDINATOR);
        cases.adoptPaymentRevision(caseId, notice, adoptionProof, _businessAuthority(COORDINATOR), revision);
        require(cases.getAdoptedDisposition(caseId).adoptedAt == 0, "stale basis did not leave an adopted disposition");
        require(snapshots.revertToState(state), "restore reviewed version for adoption");
    }

    function _payCorrectedObligationAndReturnOldReceipt(bytes32 obligationId, uint256 oldApproval, uint256 oldReceipt)
        private
    {
        SparkV15Funds funds = payments.FUNDS();
        MockERC20 token = MockERC20(address(payments.TOKEN()));
        SparkV15Returns returnsEngine = payments.RETURNS();
        token.mint(address(funds), 4);
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, funds.ACTION_REPLENISH_PAYMENT_BACKING(), true);
        requestVm.prank(VERIFIER_ACTOR);
        funds.replenishPaymentBacking(obligationId, 4, _authority(ROLE_VERIFIER));

        uint256 correctedApproval = _recordPaymentApproval(obligationId, 7);
        requestVm.warp(EPOCH + 23);
        requestVm.prank(STUDENT);
        uint256 correctedReceipt = payments.pay(correctedApproval, 7);
        require(token.balanceOf(STUDENT) == 9, "collector actually received corrected payment");
        require(returnsEngine.receiptBeneficiary(oldReceipt) == STUDENT, "initial beneficial receipt retained");
        require(returnsEngine.receiptBeneficiary(correctedReceipt) == SUBSTITUTE, "corrected beneficial receipt");
        require(payments.getReceipt(correctedReceipt).recipient == STUDENT, "agreed collecting destination");

        requestVm.warp(EPOCH + 24);
        SparkV15Returns.ReturnTerms memory terms =
            SparkV15Returns.ReturnTerms(oldReceipt, 1, keccak256("verified and agreed return of the prior receipt"));
        uint256 proof = _registerCommitment(returnsEngine.returnEvidenceCommitment(terms));
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, SparkV15.ACTION_AUTHORISE_PAYMENT_RETURN, true);
        requestVm.prank(VERIFIER_ACTOR);
        returnsEngine.authorisePaymentReturn(terms, proof, _authority(ROLE_VERIFIER));
        requestVm.prank(STUDENT);
        token.approve(address(funds), 1);
        requestVm.prank(STUDENT);
        uint256 returnId = returnsEngine.returnPayment(terms, proof);
        require(returnsEngine.getPaymentReturn(returnId).terms.receiptId == oldReceipt, "return linked to initial receipt");
        require(token.balanceOf(STUDENT) == 8 && token.balanceOf(address(funds)) == 1, "actual return to vault");
        require(payments.retainedByBeneficiary(obligationId, STUDENT) == 1, "old beneficiary retains only net receipts");
        require(payments.getObligation(obligationId).paid == 7, "old return leaves corrected beneficiary net unchanged");
        require(payments.getApproval(oldApproval).paid == 1, "old approval records its own net receipt");
        require(payments.getApproval(correctedApproval).paid == 7, "corrected approval records its own net receipt");
    }

    function testUnavailableSourceKeepsTheHistoryAndAllowsOnlyNeutralDisposition() public {
        bytes32 caseId = _fileStudentConcern(_publishTerms(true), _parties(STUDENT, COORDINATOR), bytes32(0));
        uint256 filedProof = intake.getConcern(caseId).intake.evidenceId;
        _revokeEvidence(filedProof);
        require(!cases.reviewSourceAvailable(caseId), "unavailable source presented as usable");
        require(intake.getConcern(caseId).intake.raisedBy == STUDENT, "the accepted complaint was lost");
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.Affirmed,
            outcome: keccak256("unsupported merits"),
            reasons: keccak256("insufficient available material"),
            approvalRequestId: 0
        });
        requestVm.prank(REVIEWER);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        cases.decideReview(caseId, review, 0, _businessAuthority(REVIEWER));

        review.disposition = SparkV15ReviewContext.ReviewDisposition.EvidenceUnavailable;
        review.outcome = bytes32(0);
        requestVm.prank(REVIEWER);
        cases.decideReview(caseId, review, 0, _businessAuthority(REVIEWER));
        require(cases.getReview(caseId).input.disposition == review.disposition, "neutral outcome not retained");
        require(cases.getAdoptedDisposition(caseId).adoptedAt == 0, "neutral outcome became an adoption");
        (SparkV15ReviewContext.DeadlineProgress reply, SparkV15ReviewContext.DeadlineProgress resolution) =
            intake.getProgress(caseId);
        require(reply == SparkV15ReviewContext.DeadlineProgress.Pending, "the unanswered complaint was changed");
        require(resolution == SparkV15ReviewContext.DeadlineProgress.CompletedOnTime, "neutral completion inaccessible");
    }

    function testOnlyThePublishedAlternativeContactCanTemporarilyHoldTheConcernedPayment() public {
        payments.bindReviewCases(ISparkV15AdoptedDispositions(address(cases)));
        bytes32 termsId = _publishTerms(true);
        bytes32 obligationId = _establishPayment();
        uint256 approvalId = _recordPaymentApproval(obligationId);
        bytes32 caseId = _fileStudentConcern(termsId, _parties(STUDENT, COORDINATOR), obligationId);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, SparkV15.ALTERNATIVE_CONTACT_ROLE, SparkV15.ACTION_TEMPORARY_HOLD, true
        );
        bytes32 otherAuthority = keccak256("unpublished temporary-contact role");
        bytes32 publishedAuthority = keccak256("published temporary-contact role");
        identityRegistry.assignSubject(
            SUBSTITUTE, SparkV15.APP_ID, SparkV15.ALTERNATIVE_CONTACT_ROLE, otherAuthority, "test:another-contact"
        );
        identityRegistry.assignSubject(
            ALTERNATIVE, SparkV15.APP_ID, SparkV15.ALTERNATIVE_CONTACT_ROLE, publishedAuthority, "test:published-contact"
        );

        requestVm.warp(EPOCH + 20);
        SparkV15TemporaryHolds.Terms memory hold = SparkV15TemporaryHolds.Terms({
            obligationId: obligationId,
            caseId: caseId,
            noticeHash: keccak256("matched complaint about a separately identifiable amount"),
            authorisedAt: EPOCH + 19,
            expiresAt: EPOCH + 23,
            expectedVersion: payments.getObligation(obligationId).version
        });
        uint256 publishedProof = _registerCommitment(payments.HOLDS().temporaryHoldCommitment(hold, ALTERNATIVE));
        requestVm.expectRevert(SparkV15PaymentHolds.InvalidTemporaryHold.selector);
        requestVm.prank(ALTERNATIVE);
        payments.imposeTemporaryHold(hold, publishedProof, publishedAuthority);

        _recordTemporaryHoldDeadlines(termsId, EPOCH + 23, EPOCH + 21);
        (uint64 expiry, uint64 handoff, uint256 datesEvidence) = payments.HOLDS().temporaryHoldDeadlines(termsId);
        require(expiry == EPOCH + 23 && handoff == EPOCH + 21 && datesEvidence != 0, "form dates not recognised");

        uint256 otherProof = _registerCommitment(payments.HOLDS().temporaryHoldCommitment(hold, SUBSTITUTE));
        requestVm.expectRevert(SparkV15PaymentHolds.InvalidTemporaryHold.selector);
        requestVm.prank(SUBSTITUTE);
        payments.imposeTemporaryHold(hold, otherProof, otherAuthority);
        require(!payments.temporarySetterFor(LESSON, caseId, SUBSTITUTE), "unpublished contact set the hold");

        hold.expiresAt = EPOCH + 24;
        uint256 wrongExpiryProof = _registerCommitment(payments.HOLDS().temporaryHoldCommitment(hold, ALTERNATIVE));
        requestVm.expectRevert(SparkV15PaymentHolds.InvalidTemporaryHold.selector);
        requestVm.prank(ALTERNATIVE);
        payments.imposeTemporaryHold(hold, wrongExpiryProof, publishedAuthority);
        require(payments.getObligation(obligationId).version == hold.expectedVersion, "refusal changed obligation");

        hold.expiresAt = expiry;
        _revokeEvidence(datesEvidence);
        requestVm.expectRevert(SparkV15PaymentHolds.InvalidTemporaryHold.selector);
        requestVm.prank(ALTERNATIVE);
        payments.imposeTemporaryHold(hold, publishedProof, publishedAuthority);

        SparkV15PaymentHolds holdRegistry = payments.HOLDS();
        uint256 differentDates =
            _registerCommitment(holdRegistry.temporaryHoldDeadlinesCommitment(termsId, expiry + 1, handoff));
        requestVm.expectRevert(SparkV15PaymentHolds.InvalidTemporaryHold.selector);
        holdRegistry.recordTemporaryHoldDeadlines(termsId, expiry + 1, handoff, differentDates);
        _recordTemporaryHoldDeadlines(termsId, expiry, handoff);
        requestVm.prank(ALTERNATIVE);
        bytes32 holdId = payments.imposeTemporaryHold(hold, publishedProof, publishedAuthority);
        SparkV15TemporaryHolds.Hold memory saved = payments.HOLDS().getTemporaryHold(holdId);
        require(saved.terms.obligationId == obligationId && saved.terms.caseId == caseId, "hold scope changed");
        require(saved.amount == 5 && saved.setter == ALTERNATIVE, "published contact's hold was not recorded");

        (,, uint256 newDatesEvidence) = holdRegistry.temporaryHoldDeadlines(termsId);
        _revokeEvidence(newDatesEvidence);
        requestVm.warp(handoff + 1);
        requestVm.expectRevert(SparkV15Payments.PaymentNotAllowed.selector);
        requestVm.prank(STUDENT);
        payments.pay(approvalId, 5);
        requestVm.warp(expiry);
        requestVm.prank(STUDENT);
        payments.pay(approvalId, 5);
        require(payments.getObligation(obligationId).paid == 5, "scheduled expiry did not clear payment");
    }

    function testTheRecordedTemporarySetterCannotReviewTheSameCaseAfterExpiry() public {
        bytes32 termsId = _publishTerms(true);
        bytes32 obligationId = _establishPayment();
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        bytes32 caseId = _fileStudentConcern(termsId, parties, obligationId);
        bytes32 alternativeAuthority = _authority(SparkV15.ALTERNATIVE_CONTACT_ROLE);
        identityRegistry.assignSubject(
            ALTERNATIVE,
            SparkV15.APP_ID,
            SparkV15.ALTERNATIVE_CONTACT_ROLE,
            alternativeAuthority,
            "test:temporary-contact"
        );
        authorityMatrix.setPermission(
            SparkV15.APP_ID, SparkV15.ALTERNATIVE_CONTACT_ROLE, SparkV15.ACTION_TEMPORARY_HOLD, true
        );

        requestVm.warp(EPOCH + 1);
        SparkV15TemporaryHolds.Terms memory hold = SparkV15TemporaryHolds.Terms({
            obligationId: obligationId,
            caseId: caseId,
            noticeHash: keccak256("verified authority and immediate notice for this refund only"),
            authorisedAt: EPOCH,
            expiresAt: EPOCH + 3,
            expectedVersion: payments.getObligation(obligationId).version
        });
        uint256 holdProof = _registerCommitment(payments.HOLDS().temporaryHoldCommitment(hold, ALTERNATIVE));
        requestVm.prank(ALTERNATIVE);
        payments.imposeTemporaryHold(hold, holdProof, alternativeAuthority);

        requestVm.warp(EPOCH + 4);
        SparkV15ReviewContext.AppointmentInput memory appointment = SparkV15ReviewContext.AppointmentInput({
            purpose: SparkV15ReviewContext.AppointmentPurpose.IndependentReview,
            handler: ALTERNATIVE,
            handlerAuthorityId: _businessAuthority(ALTERNATIVE),
            recusedActor: address(0),
            disclosure: SparkV15ReviewContext.Notice(bytes32(0), 0)
        });
        uint256 proof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR,
            CORE_PARTNER,
            keccak256(abi.encode(appointment, keccak256(abi.encode(parties))))
        );
        requestVm.prank(CORE_PARTNER);
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        cases.appoint(caseId, appointment, proof, _businessAuthority(CORE_PARTNER));
    }

    function testFormalLiftUsesRecusalRecordedAfterTheHoldAndKeepsThePriorApproval() public {
        payments.bindReviewCases(ISparkV15AdoptedDispositions(address(cases)));
        bytes32 termsId = _publishTerms(true);
        bytes32 obligationId = _establishPayment();
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        bytes32 caseId = _fileStudentConcern(termsId, parties, obligationId);
        bytes32 partiesHash = keccak256(abi.encode(parties));
        _appointReviewer(caseId, SUBSTITUTE, partiesHash);
        uint256 approvalId = _recordPaymentApproval(obligationId);
        _grantCaseAction(SparkV15.ACTION_FORMAL_HOLD);
        _grantCaseAction(SparkV15.ACTION_LIFT_HOLD);

        requestVm.warp(EPOCH + 1);
        SparkV15PaymentHolds.HoldTerms memory terms = SparkV15PaymentHolds.HoldTerms({
            obligationId: obligationId,
            caseId: caseId,
            noticeHash: keccak256("notice about the identified refund"),
            reviewAt: EPOCH + 8,
            expectedVersion: payments.getObligation(obligationId).version
        });
        uint256 holdProof = _registerCommitment(payments.HOLDS().formalHoldCommitment(terms, SUBSTITUTE));
        requestVm.prank(SUBSTITUTE);
        bytes32 holdId = payments.imposeFormalHold(terms, holdProof, _businessAuthority(SUBSTITUTE));

        requestVm.warp(EPOCH + 2);
        _replaceRecusedReviewer(caseId, partiesHash);

        uint256 version = payments.getObligation(obligationId).version;
        bytes32 disposition = keccak256("the identified refund may proceed after review");
        uint256 priorReviewerProof =
            _registerCommitment(payments.HOLDS().formalLiftCommitment(holdId, disposition, version, SUBSTITUTE));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(SUBSTITUTE);
        payments.liftFormalHold(holdId, disposition, version, priorReviewerProof, _businessAuthority(SUBSTITUTE));
        require(payments.HOLDS().getStatus(obligationId).active, "the hold changed on refusal");

        uint256 liftProof =
            _registerCommitment(payments.HOLDS().formalLiftCommitment(holdId, disposition, version, ESCALATION));
        requestVm.prank(ESCALATION);
        payments.liftFormalHold(holdId, disposition, version, liftProof, _businessAuthority(ESCALATION));
        SparkV15PaymentHolds.FormalHold memory saved = payments.HOLDS().getFormalHold(holdId);
        require(saved.reviewer == SUBSTITUTE && saved.liftedBy == ESCALATION, "decision record changed");
        require(!payments.HOLDS().getStatus(obligationId).active, "the approved lift did not clear the hold");
        require(payments.getApproval(approvalId).stoppedAt == 0, "the previous approval was stopped");

        requestVm.warp(EPOCH + 21);
        requestVm.prank(STUDENT);
        payments.pay(approvalId, 5);
        require(payments.getObligation(obligationId).paid == 5, "the previous approval did not pay");
    }

    function testNamedAlternateStepsAsideFromOwnOutstandingRefund() public {
        payments.bindReviewCases(ISparkV15AdoptedDispositions(address(cases)));
        bytes32 termsId = _publishTerms(true);
        bytes32 account = payments.FUNDS().creditAccount(ALTERNATIVE);
        bytes32 obligationId = _establishPayment(false, ALTERNATIVE, account);
        bytes32 caseId = _fileStudentConcern(termsId, _parties(STUDENT, ALTERNATIVE), obligationId);
        _grantCaseAction(SparkV15.ACTION_FORMAL_HOLD);
        bytes32 alternateAuthority = _authority(SparkV15.ALTERNATIVE_CONTACT_ROLE);
        authorityMatrix.setPermission(
            SparkV15.APP_ID, SparkV15.ALTERNATIVE_CONTACT_ROLE, SparkV15.ACTION_TEMPORARY_HOLD, true
        );
        identityRegistry.assignSubject(
            ALTERNATIVE, SparkV15.APP_ID, SparkV15.ALTERNATIVE_CONTACT_ROLE, alternateAuthority, "test:case-contact"
        );

        requestVm.warp(EPOCH + 1);
        uint256 version = payments.getObligation(obligationId).version;
        _recordTemporaryHoldDeadlines(termsId, EPOCH + 3, EPOCH + 2);
        bytes32 notice = keccak256("notice records the exact original-account refund");
        SparkV15TemporaryHolds.Terms memory temporary =
            SparkV15TemporaryHolds.Terms(obligationId, caseId, notice, EPOCH, EPOCH + 3, version);
        uint256 temporaryProof = _registerCommitment(payments.HOLDS().temporaryHoldCommitment(temporary, ALTERNATIVE));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(ALTERNATIVE);
        payments.imposeTemporaryHold(temporary, temporaryProof, alternateAuthority);

        SparkV15PaymentHolds.HoldTerms memory formal =
            SparkV15PaymentHolds.HoldTerms(obligationId, caseId, notice, EPOCH + 3, version);
        uint256 ownFormalProof = _registerCommitment(payments.HOLDS().formalHoldCommitment(formal, ALTERNATIVE));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(ALTERNATIVE);
        payments.imposeFormalHold(formal, ownFormalProof, _businessAuthority(ALTERNATIVE));
        require(!payments.HOLDS().getStatus(obligationId).active, "the refund was held on recusal");
        require(payments.getObligation(obligationId).version == version, "the refund version changed on recusal");

        uint256 formalProof = _registerCommitment(payments.HOLDS().formalHoldCommitment(formal, SUBSTITUTE));
        requestVm.prank(SUBSTITUTE);
        bytes32 holdId = payments.imposeFormalHold(formal, formalProof, _businessAuthority(SUBSTITUTE));
        require(payments.HOLDS().getFormalHold(holdId).amount == 5, "the independent hold omitted the refund");
    }

    function testFormalLiftKeepsAnEarlierHoldWhenReviewCasesIsBoundLater() public {
        bytes32 obligationId = _establishPayment();
        _grantCaseAction(SparkV15.ACTION_FORMAL_HOLD);
        _grantCaseAction(SparkV15.ACTION_LIFT_HOLD);
        requestVm.warp(EPOCH + 1);
        SparkV15PaymentHolds.HoldTerms memory terms = SparkV15PaymentHolds.HoldTerms({
            obligationId: obligationId,
            caseId: keccak256("a case recorded when this installation had no intake"),
            noticeHash: keccak256("original verified hold notice"),
            reviewAt: EPOCH + 3,
            expectedVersion: payments.getObligation(obligationId).version
        });
        uint256 holdProof = _registerCommitment(payments.HOLDS().formalHoldCommitment(terms, SUBSTITUTE));
        requestVm.prank(SUBSTITUTE);
        bytes32 holdId = payments.imposeFormalHold(terms, holdProof, _businessAuthority(SUBSTITUTE));
        payments.bindReviewCases(ISparkV15AdoptedDispositions(address(cases)));

        requestVm.warp(EPOCH + 2);
        uint256 version = payments.getObligation(obligationId).version;
        bytes32 finding = keccak256("authorised decision to lift the recorded hold");
        uint256 liftProof =
            _registerCommitment(payments.HOLDS().formalLiftCommitment(holdId, finding, version, SUBSTITUTE));
        requestVm.prank(SUBSTITUTE);
        payments.liftFormalHold(holdId, finding, version, liftProof, _businessAuthority(SUBSTITUTE));
        require(payments.HOLDS().getFormalHold(holdId).liftedAt == EPOCH + 2, "the old hold could not be lifted");
    }

    function testLegacyLiftReadsRetainedSameCaseRecusalBeforeTheIntakeIsRecorded() public {
        bytes32 termsId = _publishTerms(true);
        bytes32 obligationId = _establishPayment();
        bytes32 caseId = cases.caseIdFor(LESSON, CONCERN);
        _grantCaseAction(SparkV15.ACTION_FORMAL_HOLD);
        _grantCaseAction(SparkV15.ACTION_LIFT_HOLD);
        requestVm.warp(EPOCH + 1);
        SparkV15PaymentHolds.HoldTerms memory terms = SparkV15PaymentHolds.HoldTerms(
            obligationId, caseId, keccak256("notice of the assessed refund"), EPOCH + 8,
            payments.getObligation(obligationId).version
        );
        uint256 proof = _registerCommitment(payments.HOLDS().formalHoldCommitment(terms, SUBSTITUTE));
        requestVm.prank(SUBSTITUTE);
        bytes32 holdId = payments.imposeFormalHold(terms, proof, _businessAuthority(SUBSTITUTE));
        payments.bindReviewCases(ISparkV15AdoptedDispositions(address(cases)));

        address[] memory parties = _parties(STUDENT, COORDINATOR);
        SparkV15ReviewContext.OriginalInput memory original = SparkV15ReviewContext.OriginalInput({
            termsId: termsId,
            concernRef: CONCERN,
            obligationId: obligationId,
            paymentCommitment: payments.getObligation(obligationId).commitment,
            decider: LEAD_TUTOR,
            decidedAt: EPOCH,
            outcome: keccak256("retained original payment decision"),
            parties: parties
        });
        requestVm.warp(EPOCH + 2);
        proof = _evidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(original))
        );
        requestVm.prank(VERIFIER_ACTOR);
        cases.retainOriginal(original, proof, _authority(ROLE_VERIFIER));
        require(!cases.isPaymentConcern(caseId, LESSON, obligationId), "an intake was invented");

        bytes32 partiesHash = keccak256(abi.encode(parties));
        _appointReviewer(caseId, SUBSTITUTE, partiesHash);
        requestVm.warp(EPOCH + 3);
        _replaceRecusedReviewer(caseId, partiesHash);

        uint256 version = payments.getObligation(obligationId).version;
        bytes32 disposition = keccak256("completed independent review of the recorded hold");
        proof = _registerCommitment(payments.HOLDS().formalLiftCommitment(holdId, disposition, version, SUBSTITUTE));
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        requestVm.prank(SUBSTITUTE);
        payments.liftFormalHold(holdId, disposition, version, proof, _businessAuthority(SUBSTITUTE));

        proof = _registerCommitment(payments.HOLDS().formalLiftCommitment(holdId, disposition, version, ESCALATION));
        requestVm.prank(ESCALATION);
        payments.liftFormalHold(holdId, disposition, version, proof, _businessAuthority(ESCALATION));
        require(payments.HOLDS().getFormalHold(holdId).liftedBy == ESCALATION, "the retained hold was not released");
    }

    function testHeldReviewTakeoverUsesTheLiveHoldForTheExactCase() public {
        bytes32 termsId = _publishTerms(true, EPOCH + 12);
        bytes32 obligationId = _establishPayment();
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        bytes32 caseId = _fileStudentConcern(termsId, parties, obligationId);
        _grantCaseAction(SparkV15.ACTION_FORMAL_HOLD);
        requestVm.warp(EPOCH + 2);
        SparkV15PaymentHolds.HoldTerms memory hold = SparkV15PaymentHolds.HoldTerms({
            obligationId: obligationId,
            caseId: caseId,
            noticeHash: keccak256("precise held amount, reasons and review date sent"),
            reviewAt: EPOCH + 9,
            expectedVersion: payments.getObligation(obligationId).version
        });
        uint256 holdProof = _registerCommitment(payments.HOLDS().formalHoldCommitment(hold, SUBSTITUTE));
        requestVm.prank(SUBSTITUTE);
        bytes32 holdId = payments.imposeFormalHold(hold, holdProof, _businessAuthority(SUBSTITUTE));

        requestVm.warp(EPOCH + 13);
        SparkV15ReviewContext.EscalationInput memory input = SparkV15ReviewContext.EscalationInput({
            kind: SparkV15ReviewContext.EscalationKind.HeldReview,
            holdId: keccak256("another hold"),
            assignedTo: ALTERNATIVE,
            assignedAuthorityId: _businessAuthority(ALTERNATIVE),
            takenOverAt: EPOCH + 13,
            assignedAt: EPOCH + 13,
            newActionDate: EPOCH + 15,
            progress: keccak256("the formal hold is still pending an independent assessment"),
            notice: SparkV15ReviewContext.Notice(keccak256("takeover and next date sent"), EPOCH + 13)
        });
        requestVm.prank(ESCALATION);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        intake.escalate(caseId, input, 0, _businessAuthority(ESCALATION));

        input.holdId = holdId;
        uint256 proof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_ESCALATE_CASE,
            ESCALATION,
            keccak256(abi.encode(input, keccak256(abi.encode(parties)), bytes32(0)))
        );
        requestVm.prank(ESCALATION);
        intake.escalate(caseId, input, proof, _businessAuthority(ESCALATION));
        require(intake.getEscalation(caseId, 0).input.holdId == holdId, "held review lineage missing");
    }

    function testRequestedReviewUsesEarlierLegalCutoffAndKeepsTheTakeoverAfterLateCompletion() public {
        bytes32 termsId = _publishTerms(true, EPOCH + 12);
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        bytes32 partiesHash = keccak256(abi.encode(parties));
        bytes32 caseId = _fileStudentConcern(termsId, parties, bytes32(0));
        requestVm.prank(STUDENT);
        intake.requestReview(caseId, keccak256("review requested by the affected student"));
        requestVm.warp(EPOCH + 12);

        SparkV15ReviewContext.EscalationInput memory escalation = SparkV15ReviewContext.EscalationInput({
            kind: SparkV15ReviewContext.EscalationKind.RequestedReview,
            holdId: bytes32(0),
            assignedTo: REVIEWER,
            assignedAuthorityId: _businessAuthority(REVIEWER),
            takenOverAt: EPOCH + 12,
            assignedAt: EPOCH + 12,
            newActionDate: EPOCH + 15,
            progress: keccak256("the review is pending and has a new responsible person"),
            notice: SparkV15ReviewContext.Notice(keccak256("status and new date sent to both parties"), EPOCH + 12)
        });
        uint256 premature = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_ESCALATE_CASE,
            ESCALATION,
            keccak256(abi.encode(escalation, partiesHash, bytes32(0)))
        );
        requestVm.prank(ESCALATION);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        intake.escalate(caseId, escalation, premature, _businessAuthority(ESCALATION));

        requestVm.warp(EPOCH + 13);
        escalation.takenOverAt = EPOCH + 13;
        escalation.assignedAt = EPOCH + 13;
        escalation.notice.sentAt = EPOCH + 13;
        uint256 takeoverProof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_ESCALATE_CASE,
            ESCALATION,
            keccak256(abi.encode(escalation, partiesHash, bytes32(0)))
        );
        (, SparkV15ReviewContext.DeadlineProgress beforeAction) = intake.getProgress(caseId);
        require(beforeAction == SparkV15ReviewContext.DeadlineProgress.Overdue, "earlier deadline did not apply");
        requestVm.prank(ESCALATION);
        intake.escalate(caseId, escalation, takeoverProof, _businessAuthority(ESCALATION));
        _appointReviewer(caseId, REVIEWER, partiesHash);

        requestVm.warp(EPOCH + 14);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.Affirmed,
            outcome: keccak256("affirmed attendance"),
            reasons: keccak256("late but substantiated review"),
            approvalRequestId: 0
        });
        uint256 proof =
            _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(review)));
        requestVm.prank(REVIEWER);
        cases.decideReview(caseId, review, proof, _businessAuthority(REVIEWER));

        (, SparkV15ReviewContext.DeadlineProgress progress) = intake.getProgress(caseId);
        require(progress == SparkV15ReviewContext.DeadlineProgress.CompletedLate, "late result was lost");
        SparkV15ReviewContext.Escalation memory saved = intake.getEscalation(caseId, 0);
        require(saved.input.assignedTo == REVIEWER && saved.evidenceId == takeoverProof, "takeover was lost");
        require(intake.getConcern(caseId).reviewCutoff == EPOCH + 12, "takeover extended the deadline");
        require(intake.getPublishedContacts(termsId).terms.reviewDeadline == EPOCH + 30, "agreed deadline overwritten");
    }

    function testTriggeredReviewUsesAnAppointmentMadeAfterTheSameCaseWasReceived() public {
        bytes32 termsId = _publishTerms(true);
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        bytes32 caseId = cases.caseIdFor(LESSON, CONCERN);
        bytes32 outcome = _retainAttendanceOutcome(termsId, caseId, parties);
        _appointReviewer(caseId, SUBSTITUTE, keccak256(abi.encode(parties)));

        _fileStudentConcern(termsId, parties, bytes32(0));
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.Affirmed,
            outcome: outcome,
            reasons: keccak256("justified independent review of the retained decision"),
            approvalRequestId: 0
        });
        uint256 proof =
            _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, SUBSTITUTE, keccak256(abi.encode(review)));
        requestVm.prank(STUDENT);
        intake.requestReview(caseId, keccak256("independent review requested for this complaint"));
        require(intake.getConcern(caseId).intake.receivedAt == EPOCH, "receipt did not share the appointment time");

        requestVm.prank(SUBSTITUTE);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        cases.decideReview(caseId, review, proof, _businessAuthority(SUBSTITUTE));
        require(cases.getReview(caseId).decidedAt == 0, "a pre-receipt appointment decided the complaint");

        _appointReviewer(caseId, SUBSTITUTE, keccak256(abi.encode(parties)));
        requestVm.prank(SUBSTITUTE);
        cases.decideReview(caseId, review, proof, _businessAuthority(SUBSTITUTE));
        require(cases.getReview(caseId).decidedAt == EPOCH, "a later action in the same second did not qualify");
        require(cases.reviewedPaymentRevision(caseId) == bytes32(0), "generic review became a payment revision");
    }

    function testVerifiedEarlierReceiptSupportsAnAppointmentMadeBeforeTheIntakeWasRecorded() public {
        _reviewAfterLateReceipt(EPOCH + 1, true);
    }

    function testLateRecordedSameSecondReceiptLeavesTheAppointmentOrderUncertain() public {
        _reviewAfterLateReceipt(EPOCH + 2, false);
    }

    function _reviewAfterLateReceipt(uint64 receivedAt, bool appointmentApplies) private {
        bytes32 termsId = _publishTerms(true);
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        bytes32 caseId = cases.caseIdFor(LESSON, CONCERN);
        bytes32 outcome = _retainAttendanceOutcome(termsId, caseId, parties);
        requestVm.warp(EPOCH + 2);
        _appointReviewer(caseId, SUBSTITUTE, keccak256(abi.encode(parties)));

        requestVm.warp(EPOCH + 4);
        SparkV15ReviewContext.ConcernInput memory concern = SparkV15ReviewContext.ConcernInput({
            termsId: termsId,
            concernRef: CONCERN,
            obligationId: bytes32(0),
            receiver: COORDINATOR,
            subject: SparkV15ReviewContext.ConcernSubject.StudentAttendance,
            alternativeGround: SparkV15ReviewContext.AlternativeGround.None,
            claim: keccak256("review my attendance"),
            subjectRef: keccak256("student place"),
            parties: parties
        });
        bytes32 receiptRef = keccak256("verified original receipt through the published channel");
        uint256 proof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_RECEIVE_CONCERN,
            STUDENT,
            keccak256(abi.encode(concern, receivedAt, receiptRef))
        );
        requestVm.prank(STUDENT);
        intake.receiveConcernAt(concern, receivedAt, receiptRef, proof);
        requestVm.prank(STUDENT);
        intake.requestReview(caseId, keccak256("independent review requested for the retained case"));

        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.Affirmed,
            outcome: outcome,
            reasons: keccak256("verified records support the original finding"),
            approvalRequestId: 0
        });
        proof = _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, SUBSTITUTE, keccak256(abi.encode(review)));
        if (!appointmentApplies) requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        requestVm.prank(SUBSTITUTE);
        cases.decideReview(caseId, review, proof, _businessAuthority(SUBSTITUTE));
        require(cases.getReview(caseId).decidedAt == (appointmentApplies ? EPOCH + 4 : 0), "wrong review result");
        require(
            cases.getAppointment(caseId, SparkV15ReviewContext.AppointmentPurpose.IndependentReview, 0).appointedAt
                == EPOCH + 2,
            "appointment history changed"
        );
    }

    function testReplacementHandlerReplyUsesAnAppointmentMadeAfterReceipt() public {
        _assertReplacementHandlerReply(false);
    }

    function testIndependentReviewEvidenceDoesNotReplaceReplyAuthority() public {
        _assertReplacementHandlerReply(true);
    }

    function _assertReplacementHandlerReply(bool withReview) private {
        bytes32 termsId = _publishTerms(true);
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        bytes32 caseId = cases.caseIdFor(LESSON, CONCERN);
        bytes32 partiesHash = keccak256(abi.encode(parties));
        SparkV15ReviewContext.AppointmentPurpose purpose = SparkV15ReviewContext.AppointmentPurpose.ConcernHandling;
        bytes32 outcome = _retainAttendanceOutcome(termsId, caseId, parties);
        _appointCaseActor(caseId, SUBSTITUTE, partiesHash, purpose);
        _fileStudentConcern(termsId, parties, bytes32(0));

        SparkV15ReviewContext.AcknowledgmentInput memory acknowledgment = SparkV15ReviewContext.AcknowledgmentInput({
            handler: COORDINATOR,
            replyDeadline: EPOCH + 10,
            escalationContact: ESCALATION,
            notice: SparkV15ReviewContext.Notice(keccak256("receipt acknowledged"), EPOCH)
        });
        uint256 acknowledgmentProof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_ACKNOWLEDGE_CONCERN,
            COORDINATOR,
            keccak256(abi.encode(acknowledgment, STUDENT))
        );
        requestVm.prank(COORDINATOR);
        intake.acknowledge(caseId, acknowledgment, acknowledgmentProof, _businessAuthority(COORDINATOR));

        SparkV15ReviewContext.ReplyInput memory reply = SparkV15ReviewContext.ReplyInput({
            checkedAt: EPOCH,
            factCheck: keccak256("verified attendance"),
            outcome: outcome,
            reasons: keccak256("independent documented reasons"),
            reviewEvidenceId: 0,
            notice: SparkV15ReviewContext.Notice(keccak256("reply sent to both parties"), EPOCH)
        });
        ReviewSnapshotVm snapshots = ReviewSnapshotVm(address(requestVm));
        uint256 beforeReply = snapshots.snapshotState();
        if (withReview) reply.reviewEvidenceId = _decideReplyReview(caseId, partiesHash, reply);
        uint256 proof = _replyEvidence(caseId, partiesHash, reply);
        requestVm.prank(SUBSTITUTE);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        intake.reply(caseId, reply, proof, _businessAuthority(SUBSTITUTE));
        require(snapshots.revertToState(beforeReply));

        _appointCaseActor(caseId, SUBSTITUTE, partiesHash, purpose);
        if (withReview) reply.reviewEvidenceId = _decideReplyReview(caseId, partiesHash, reply);
        proof = _replyEvidence(caseId, partiesHash, reply);
        requestVm.prank(SUBSTITUTE);
        intake.reply(caseId, reply, proof, _businessAuthority(SUBSTITUTE));
        SparkV15ReviewContext.ReplyRecord memory saved = intake.getReply(caseId, 0);
        require(saved.handler == SUBSTITUTE && saved.input.reviewEvidenceId == reply.reviewEvidenceId, "replacement reply not recorded");
    }

    function _decideReplyReview(bytes32 caseId, bytes32 partiesHash, SparkV15ReviewContext.ReplyInput memory reply)
        private
        returns (uint256 proof)
    {
        requestVm.prank(STUDENT);
        intake.requestReview(caseId, keccak256("separate request for independent review"));
        _appointReviewer(caseId, SUBSTITUTE, partiesHash);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput(
            SparkV15ReviewContext.ReviewDisposition.Affirmed, reply.outcome, reply.reasons, 0
        );
        proof = _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, SUBSTITUTE, keccak256(abi.encode(review)));
        requestVm.prank(SUBSTITUTE);
        cases.decideReview(caseId, review, proof, _businessAuthority(SUBSTITUTE));
    }

    function _replyEvidence(bytes32 caseId, bytes32 partiesHash, SparkV15ReviewContext.ReplyInput memory reply)
        private
        returns (uint256)
    {
        return _evidence(
            caseId, SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN, SUBSTITUTE, keccak256(abi.encode(reply, partiesHash))
        );
    }

    function testRecognisedPaymentMatterPreservesTheOriginalAndRequiresIndependentReviewAndAdoption() public {
        bytes32 termsId = _publishTerms(true);
        bytes32 obligationId = _establishPayment();
        SparkV15ReviewContext.OriginalInput memory original = SparkV15ReviewContext.OriginalInput({
            termsId: termsId,
            concernRef: CONCERN,
            obligationId: obligationId,
            paymentCommitment: payments.getObligation(obligationId).commitment,
            decider: REVIEWER,
            decidedAt: EPOCH,
            outcome: keccak256("original assessment retained"),
            parties: _parties(STUDENT, LEAD_TUTOR)
        });
        bytes32 caseId = cases.caseIdFor(LESSON, CONCERN);
        uint256 originalProof = _evidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(original))
        );
        requestVm.prank(VERIFIER_ACTOR);
        require(cases.retainOriginal(original, originalProof, _authority(ROLE_VERIFIER)) == caseId, "original case id");

        address[] memory parties = _parties(STUDENT, COORDINATOR);
        _fileStudentConcern(termsId, parties, obligationId);
        require(cases.isPaymentConcern(caseId, LESSON, obligationId), "exact payment complaint");
        require(!cases.isPaymentConcern(caseId, keccak256("different lesson"), obligationId), "wrong lesson");
        requestVm.prank(STUDENT);
        intake.requestReview(caseId, keccak256("requested independent review"));

        requestVm.warp(EPOCH + 3);
        SparkV15ReviewContext.ReviewInput memory review = SparkV15ReviewContext.ReviewInput({
            disposition: SparkV15ReviewContext.ReviewDisposition.CorrectionRequired,
            outcome: keccak256("corrected institutional outcome"),
            reasons: keccak256("independent reasons"),
            approvalRequestId: 0
        });
        uint256 ownReview =
            _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, REVIEWER, keccak256(abi.encode(review)));
        requestVm.prank(REVIEWER);
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        cases.decideReview(caseId, review, ownReview, _businessAuthority(REVIEWER));

        _appointReviewer(caseId, SUBSTITUTE, keccak256(abi.encode(parties)));
        uint256 reviewProof =
            _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, SUBSTITUTE, keccak256(abi.encode(review)));
        requestVm.prank(SUBSTITUTE);
        cases.decideReview(caseId, review, reviewProof, _businessAuthority(SUBSTITUTE));
        require(cases.getAdoptedDisposition(caseId).adoptedAt == 0, "review incorrectly enacted correction");

        requestVm.warp(EPOCH + 4);
        SparkV15ReviewContext.Notice memory notice =
            SparkV15ReviewContext.Notice(keccak256("all parties notified"), EPOCH + 4);
        uint256 adoptionProof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_ADOPT_CORRECTION,
            COORDINATOR,
            keccak256(
                abi.encode(
                    notice,
                    originalProof,
                    reviewProof,
                    keccak256(abi.encode(original.parties)),
                    keccak256(abi.encode(parties))
                )
            )
        );
        requestVm.prank(COORDINATOR);
        cases.adoptCorrection(caseId, notice, adoptionProof, _businessAuthority(COORDINATOR));
        SparkV15ReviewCases.AdoptedDisposition memory adopted = cases.getAdoptedDisposition(caseId);
        require(adopted.obligationId == obligationId && adopted.originalOutcome == original.outcome, "original scope");
        require(
            adopted.originalPaymentCommitment == original.paymentCommitment && adopted.outcome == review.outcome,
            "reviewed scope"
        );
        require(adopted.reviewedAt == EPOCH + 3 && adopted.adoptedAt == EPOCH + 4, "separate occurrence times");
        require(adopted.adoptionEvidenceId == adoptionProof && adopted.reviewEvidenceId == reviewProof, "source proofs");
        require(cases.getCase(caseId).original.evidenceId == originalProof, "original was discarded");
    }

    function testVerifiedRecusalAndAppointmentGiveTheFindingToTheAuthorisedSubstitute() public {
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        bytes32 caseId = _fileStudentConcern(_publishTerms(true), parties, bytes32(0));
        requestVm.warp(EPOCH + 2);
        SparkV15ReviewContext.AppointmentInput memory appointment = SparkV15ReviewContext.AppointmentInput({
            purpose: SparkV15ReviewContext.AppointmentPurpose.InitialDecision,
            handler: SUBSTITUTE,
            handlerAuthorityId: _businessAuthority(SUBSTITUTE),
            recusedActor: LEAD_TUTOR,
            disclosure: SparkV15ReviewContext.Notice(
                keccak256("lead tutor conflict disclosed to both parties"), EPOCH + 2
            )
        });
        uint256 appointmentProof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR,
            CORE_PARTNER,
            keccak256(abi.encode(appointment, keccak256(abi.encode(parties))))
        );
        requestVm.prank(CORE_PARTNER);
        cases.appoint(caseId, appointment, appointmentProof, _businessAuthority(CORE_PARTNER));

        requestVm.warp(EPOCH + 3);
        SparkV15ReviewContext.InitialInput memory finding = SparkV15ReviewContext.InitialInput({
            issue: SparkV15ReviewContext.DisputedFinding.AbsenceReason,
            outcome: keccak256("absence was justified"),
            reasons: keccak256("verified evidence and reasons"),
            support: keccak256("retained advice to substitute")
        });
        uint256 leadProof =
            _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, LEAD_TUTOR, keccak256(abi.encode(finding)));
        requestVm.prank(LEAD_TUTOR);
        requestVm.expectRevert(SparkV15ReviewContext.ConflictedCaseActor.selector);
        cases.decideInitial(caseId, finding, leadProof, _businessAuthority(LEAD_TUTOR));

        uint256 findingProof =
            _evidence(caseId, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, SUBSTITUTE, keccak256(abi.encode(finding)));
        requestVm.prank(SUBSTITUTE);
        cases.decideInitial(caseId, finding, findingProof, _businessAuthority(SUBSTITUTE));
        SparkV15ReviewContext.InitialFinding memory saved = cases.getCase(caseId).initial;
        require(saved.decider == SUBSTITUTE && saved.decidedAt == EPOCH + 3, "actual decider not retained");
        require(saved.input.reasons == finding.reasons && saved.input.support == finding.support, "finding support");
        require(
            cases.getAppointment(caseId, SparkV15ReviewContext.AppointmentPurpose.InitialDecision, 0).evidenceId
                == appointmentProof,
            "recusal authorization was lost"
        );
    }

    function testReceiverAcknowledgesTheFilerAndRecordsTheHandlersVerifiedReply() public {
        bytes32 termsId = _publishTerms(true);
        address[] memory parties = _parties(STUDENT, COORDINATOR);
        bytes32 caseId = _fileStudentConcern(termsId, parties, bytes32(0));
        requestVm.warp(EPOCH + 1);
        SparkV15ReviewContext.AcknowledgmentInput memory acknowledgment = SparkV15ReviewContext.AcknowledgmentInput({
            handler: COORDINATOR,
            replyDeadline: EPOCH + 10,
            escalationContact: ESCALATION,
            notice: SparkV15ReviewContext.Notice(keccak256("receipt sent to the student"), EPOCH + 1)
        });
        uint256 proof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_ACKNOWLEDGE_CONCERN,
            COORDINATOR,
            keccak256(abi.encode(acknowledgment, STUDENT))
        );

        requestVm.prank(ALTERNATIVE);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        intake.acknowledge(caseId, acknowledgment, proof, _businessAuthority(ALTERNATIVE));
        requestVm.prank(COORDINATOR);
        intake.acknowledge(caseId, acknowledgment, proof, _businessAuthority(COORDINATOR));
        require(intake.getConcern(caseId).acknowledgment.input.handler == COORDINATOR, "handler missing");

        requestVm.warp(EPOCH + 4);
        SparkV15ReviewContext.ReplyInput memory reply = SparkV15ReviewContext.ReplyInput({
            checkedAt: EPOCH + 3,
            factCheck: keccak256("attendance verified"),
            outcome: keccak256("attendance record confirmed"),
            reasons: keccak256("documented reasons sent"),
            reviewEvidenceId: 0,
            notice: SparkV15ReviewContext.Notice(keccak256("reply sent to both parties"), EPOCH + 4)
        });
        uint256 wrongNotice = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN,
            COORDINATOR,
            keccak256(abi.encode(reply, keccak256(abi.encode(STUDENT))))
        );
        requestVm.prank(COORDINATOR);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidEvidence.selector);
        intake.reply(caseId, reply, wrongNotice, _businessAuthority(COORDINATOR));

        uint256 proofOfReply = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN,
            COORDINATOR,
            keccak256(abi.encode(reply, keccak256(abi.encode(parties))))
        );
        requestVm.prank(COORDINATOR);
        intake.reply(caseId, reply, proofOfReply, _businessAuthority(COORDINATOR));
        SparkV15ReviewContext.ReplyRecord memory saved = intake.getReply(caseId, 0);
        require(saved.input.outcome == reply.outcome && saved.evidenceId == proofOfReply, "verified reply missing");
        require(intake.getConcern(caseId).firstReplyAt == EPOCH + 4, "actual reply timing");
    }

    function testContributorCanFileThroughPublishedAlternativeContactWithoutAFormOrAllocation() public {
        bytes32 termsId = _publishTerms(false);
        SparkV15ReviewContext.ConcernInput memory input = SparkV15ReviewContext.ConcernInput({
            termsId: termsId,
            concernRef: CONCERN,
            obligationId: bytes32(0),
            receiver: ALTERNATIVE,
            subject: SparkV15ReviewContext.ConcernSubject.MaterialOmission,
            alternativeGround: SparkV15ReviewContext.AlternativeGround.Contributor,
            claim: keccak256("the reason use is believed omitted"),
            subjectRef: keccak256("materials identified by contributor"),
            parties: _parties(CONTRIBUTOR, COORDINATOR)
        });
        bytes32 caseId = cases.caseIdFor(LESSON, CONCERN);
        uint256 proof =
            _evidence(caseId, SparkV15ReviewActions.ACTION_RECEIVE_CONCERN, CONTRIBUTOR, keccak256(abi.encode(input)));

        requestVm.prank(COORDINATOR);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidEvidence.selector);
        intake.receiveConcern(input, proof);

        requestVm.prank(CONTRIBUTOR);
        require(intake.receiveConcern(input, proof) == caseId, "case identity");
        SparkV15ReviewContext.ConcernRecord memory item = intake.getConcern(caseId);
        require(item.intake.evidenceId == proof && item.intake.raisedBy == CONTRIBUTOR, "standing history");
        require(item.intake.receiver == ALTERNATIVE && item.intake.receivedAt == EPOCH, "published channel");
        require(item.replyCutoff == EPOCH + 10 && item.reviewCutoff == EPOCH + 30, "retained deadlines");
        require(cases.getAdoptedDisposition(caseId).adoptedAt == 0, "filing decided the merits");

        requestVm.prank(CONTRIBUTOR);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidCase.selector);
        intake.receiveConcern(input, proof);
    }

    function testVerifiedPublishedChannelReceiptUsesOriginalTimeForTheReplyDeadline() public {
        bytes32 termsId = _publishTerms(false);
        SparkV15ReviewContext.ConcernInput memory input = SparkV15ReviewContext.ConcernInput({
            termsId: termsId,
            concernRef: CONCERN,
            obligationId: bytes32(0),
            receiver: ALTERNATIVE,
            subject: SparkV15ReviewContext.ConcernSubject.MaterialOmission,
            alternativeGround: SparkV15ReviewContext.AlternativeGround.Contributor,
            claim: keccak256("the reason use is believed omitted"),
            subjectRef: keccak256("materials identified by contributor"),
            parties: _parties(CONTRIBUTOR, COORDINATOR)
        });
        bytes32 caseId = cases.caseIdFor(LESSON, CONCERN);
        uint64 receivedAt = EPOCH + 2;
        bytes32 receiptRef = keccak256("receipt from the published alternative channel");
        requestVm.warp(EPOCH + 14);
        (SparkV15ReviewContext.DeadlineProgress beforeRecording,) = intake.getProgress(caseId);
        require(beforeRecording == SparkV15ReviewContext.DeadlineProgress.NotTriggered, "case not yet recorded");
        uint256 proof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_RECEIVE_CONCERN,
            CONTRIBUTOR,
            keccak256(abi.encode(input, receivedAt, receiptRef))
        );
        requestVm.prank(CONTRIBUTOR);
        requestVm.expectRevert(SparkV15ReviewContext.InvalidEvidence.selector);
        intake.receiveConcernAt(input, receivedAt + 1, receiptRef, proof);
        requestVm.prank(CONTRIBUTOR);
        require(intake.receiveConcernAt(input, receivedAt, receiptRef, proof) == caseId, "same case");
        SparkV15ReviewContext.ConcernRecord memory item = intake.getConcern(caseId);
        require(item.intake.receivedAt == receivedAt && item.intake.evidenceId == proof, "actual receipt");
        require(item.replyCutoff == receivedAt + 10 && item.reviewCutoff == EPOCH + 30, "applicable cutoffs");
        (SparkV15ReviewContext.DeadlineProgress afterRecording,) = intake.getProgress(caseId);
        require(afterRecording == SparkV15ReviewContext.DeadlineProgress.Overdue, "registration did not restart the clock");
        require(cases.getAdoptedDisposition(caseId).adoptedAt == 0, "receipt is not a decision");
    }

    function _publishTerms(bool hasForm) private returns (bytes32 termsId) {
        return _publishTerms(hasForm, 0);
    }

    function _publishTerms(bool hasForm, uint64 legalReviewDeadline) private returns (bytes32 termsId) {
        SparkV15ReviewContext.ReviewTerms memory terms = SparkV15ReviewContext.ReviewTerms({
            lessonId: LESSON,
            publication: keccak256("the provider published both contact routes"),
            governingForm: hasForm ? keccak256("applicable confirmation form") : bytes32(0),
            provider: VERIFIER_ACTOR,
            coordinator: COORDINATOR,
            alternativeContact: ALTERNATIVE,
            leadAcademicTutor: LEAD_TUTOR,
            namedReviewer: hasForm ? REVIEWER : address(0),
            escalationContact: ESCALATION,
            replyDate: 0,
            replyPeriod: 10,
            replyLegalDeadline: 0,
            reviewDeadline: EPOCH + 30,
            reviewLegalDeadline: legalReviewDeadline
        });
        termsId = keccak256(abi.encode(terms));
        uint256 proof = _evidence(
            termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, VERIFIER_ACTOR, keccak256(abi.encode(terms))
        );
        requestVm.prank(VERIFIER_ACTOR);
        require(intake.publishContacts(terms, proof, _authority(ROLE_VERIFIER)) == termsId, "terms identity");
    }

    function _evidence(bytes32 subject, bytes32 action, address actor, bytes32 payload) private returns (uint256) {
        return _registerCommitment(cases.evidenceCommitment(subject, action, actor, payload));
    }

    function _registerCommitment(bytes32 commitment) private returns (uint256) {
        requestVm.prank(SOURCE_ACTOR);
        return evidenceRegistry.registerEvidence(
            AVAEvidenceRegistry.EvidenceRegistrationInput({
                appId: requestAppId,
                workflowKey: REQUEST_WORKFLOW,
                packageId: requestPackageId,
                roleKey: ROLE_SOURCE,
                subjectId: _authority(ROLE_SOURCE),
                commitment: commitment,
                evidenceTypeHash: keccak256("spark.review.facts-and-notifications.v1.5"),
                disclosurePolicyId: requestPolicyId,
                authorityId: _authority(ROLE_SOURCE),
                uri: "test:verified-private-review-facts"
            })
        );
    }

    function _recordTemporaryHoldDeadlines(bytes32 termsId, uint64 expiry, uint64 handoff) private {
        SparkV15PaymentHolds holds = payments.HOLDS();
        uint256 evidenceId = _registerCommitment(holds.temporaryHoldDeadlinesCommitment(termsId, expiry, handoff));
        holds.recordTemporaryHoldDeadlines(termsId, expiry, handoff, evidenceId);
    }

    function _revokeEvidence(uint256 evidenceId) private {
        requestVm.prank(SOURCE_ACTOR);
        evidenceRegistry.recordEvidenceLifecycle(
            evidenceId,
            ROLE_SOURCE,
            _authority(ROLE_SOURCE),
            AVACoreTypes.EvidenceLifecycleKind.Revoke,
            0,
            keccak256("withdrawn supporting record"),
            "test:withdrawn-support"
        );
    }

    function _establishPayment() private returns (bytes32 obligationId) {
        return _establishPayment(false);
    }

    function _establishPayment(bool nativePayment) private returns (bytes32 obligationId) {
        return _establishPayment(nativePayment, STUDENT, keccak256("retained refund account"));
    }

    function _establishPayment(bool nativePayment, address recipient, bytes32 refundAccount)
        private
        returns (bytes32 obligationId)
    {
        MockERC20(address(payments.TOKEN())).mint(address(payments.FUNDS()), 5);
        SparkV15Payments.PaymentTerms memory terms = SparkV15Payments.PaymentTerms({
            lessonId: LESSON,
            paymentPart: keccak256("recognised refund"),
            recipient: recipient,
            originalDebitAccount: refundAccount,
            originalDebitAmount: 9,
            amount: 5,
            agreedStart: 0,
            dueAt: EPOCH + 20,
            executionDeadline: EPOCH + 40,
            legalDeadline: 0,
            postLiftDeadline: 0,
            postLiftPeriod: 0,
            dueAtExact: true,
            executionDeadlineExact: true,
            legalDeadlineExact: false,
            postLiftDeadlineExact: false,
            settlementProposer: LEAD_TUTOR,
            settlementApprover: REVIEWER
        });
        if (nativePayment) {
            terms.paymentPart = keccak256("recognised native payment");
            terms.originalDebitAccount = bytes32(0);
            terms.originalDebitAmount = 0;
            terms.agreedStart = EPOCH;
            terms.legalDeadline = terms.executionDeadline;
            terms.legalDeadlineExact = true;
        }
        bytes32 basis = keccak256("verified original assessment");
        uint256 evidenceId = _registerCommitment(payments.paymentEvidenceCommitment(terms, basis));
        requestVm.prank(VERIFIER_ACTOR);
        return payments.establishPayment(terms, basis, evidenceId, _authority(ROLE_VERIFIER));
    }

    function _recordPaymentApproval(bytes32 obligationId) private returns (uint256 requestId) {
        return _recordPaymentApproval(obligationId, 5);
    }

    function _recordPaymentApproval(bytes32 obligationId, uint128 ceiling) private returns (uint256 requestId) {
        uint64 validThrough = EPOCH + 40;
        SparkV15Payments.ApprovalTerms memory terms =
            SparkV15Payments.ApprovalTerms(obligationId, STUDENT, ceiling, validThrough, 0);
        bytes32 parameters = payments.approvalParameters(terms);
        uint256 state = _createRequestState(
            address(payments), SparkV15.RESPONSE_APPROVE_PAYMENT, parameters, SparkV15.APPROVAL_BURDEN, validThrough
        );
        requestId = _createRequest(
            AVARequestAllocation.RequestInput(
                state,
                address(payments),
                SparkV15.RESPONSE_APPROVE_PAYMENT,
                parameters,
                SparkV15.APPROVAL_BURDEN,
                validThrough
            )
        );
        _approveRequest(requestId);
        requestVm.prank(ALLOCATOR_ACTOR);
        payments.recordApproval(requestId, terms);
    }

    function _appointReviewer(bytes32 caseId, address actor, bytes32 partiesHash) private {
        _appointCaseActor(caseId, actor, partiesHash, SparkV15ReviewContext.AppointmentPurpose.IndependentReview);
    }

    function _replaceRecusedReviewer(bytes32 caseId, bytes32 partiesHash) private {
        SparkV15ReviewContext.AppointmentInput memory appointment = SparkV15ReviewContext.AppointmentInput({
            purpose: SparkV15ReviewContext.AppointmentPurpose.IndependentReview,
            handler: ESCALATION,
            handlerAuthorityId: _businessAuthority(ESCALATION),
            recusedActor: SUBSTITUTE,
            disclosure: SparkV15ReviewContext.Notice(keccak256("recusal disclosed to both parties"), uint64(block.timestamp))
        });
        uint256 proof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR,
            CORE_PARTNER,
            keccak256(abi.encode(appointment, partiesHash))
        );
        requestVm.prank(CORE_PARTNER);
        cases.appoint(caseId, appointment, proof, _businessAuthority(CORE_PARTNER));
    }

    function _appointCaseActor(
        bytes32 caseId,
        address actor,
        bytes32 partiesHash,
        SparkV15ReviewContext.AppointmentPurpose purpose
    ) private {
        SparkV15ReviewContext.AppointmentInput memory appointment = SparkV15ReviewContext.AppointmentInput({
            purpose: purpose,
            handler: actor,
            handlerAuthorityId: _businessAuthority(actor),
            recusedActor: address(0),
            disclosure: SparkV15ReviewContext.Notice(bytes32(0), 0)
        });
        uint256 proof = _evidence(
            caseId,
            SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR,
            CORE_PARTNER,
            keccak256(abi.encode(appointment, partiesHash))
        );
        requestVm.prank(CORE_PARTNER);
        cases.appoint(caseId, appointment, proof, _businessAuthority(CORE_PARTNER));
    }

    function _retainAttendanceOutcome(bytes32 termsId, bytes32 caseId, address[] memory parties)
        private
        returns (bytes32 outcome)
    {
        outcome = keccak256("retained decision before any complaint");
        SparkV15ReviewContext.OriginalInput memory original = SparkV15ReviewContext.OriginalInput({
            termsId: termsId,
            concernRef: CONCERN,
            obligationId: bytes32(0),
            paymentCommitment: bytes32(0),
            decider: LEAD_TUTOR,
            decidedAt: EPOCH,
            outcome: outcome,
            parties: parties
        });
        uint256 proof = _evidence(
            caseId, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, VERIFIER_ACTOR, keccak256(abi.encode(original))
        );
        requestVm.prank(VERIFIER_ACTOR);
        cases.retainOriginal(original, proof, _authority(ROLE_VERIFIER));
    }

    function _fileStudentConcern(bytes32 termsId, address[] memory parties, bytes32 obligationId)
        private
        returns (bytes32 caseId)
    {
        SparkV15ReviewContext.ConcernInput memory concern = SparkV15ReviewContext.ConcernInput({
            termsId: termsId,
            concernRef: CONCERN,
            obligationId: obligationId,
            receiver: COORDINATOR,
            subject: SparkV15ReviewContext.ConcernSubject.StudentAttendance,
            alternativeGround: SparkV15ReviewContext.AlternativeGround.None,
            claim: keccak256("review my attendance"),
            subjectRef: keccak256("student place"),
            parties: parties
        });
        caseId = cases.caseIdFor(LESSON, CONCERN);
        uint256 evidenceId =
            _evidence(caseId, SparkV15ReviewActions.ACTION_RECEIVE_CONCERN, STUDENT, keccak256(abi.encode(concern)));
        requestVm.prank(STUDENT);
        require(intake.receiveConcern(concern, evidenceId) == caseId, "filing registered a different case");
    }

    function _grantCaseAction(bytes32 action) private {
        authorityMatrix.setPermission(SparkV15.APP_ID, ROLE_VERIFIER, action, true);
    }

    function _enrol(address actor) private {
        identityRegistry.assignSubject(
            actor, SparkV15.APP_ID, ROLE_VERIFIER, _businessAuthority(actor), "test:case-business-role"
        );
    }

    function _businessAuthority(address actor) private pure returns (bytes32) {
        return keccak256(abi.encode("v1.5 case fixture", actor));
    }

    function _parties(address one, address two) private pure returns (address[] memory parties) {
        parties = new address[](2);
        parties[0] = one;
        parties[1] = two;
    }
}
