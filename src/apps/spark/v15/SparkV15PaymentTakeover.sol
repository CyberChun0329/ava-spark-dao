// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {SparkV15Booking} from "./SparkV15Booking.sol";
import {SparkV15MaterialProvisions} from "./SparkV15MaterialProvisions.sol";
import {SparkV15Materials} from "./SparkV15Materials.sol";
import {SparkV15PaymentHolds} from "./SparkV15PaymentHolds.sol";
import {SparkV15Payments} from "./SparkV15Payments.sol";
import {SparkV15ConcernIntake, SparkV15ReviewActions, SparkV15ReviewCases, SparkV15ReviewContext} from
    "./SparkV15ReviewCases.sol";
import {SparkV15Settlement} from "./SparkV15Settlement.sol";
import {SparkV15TemporaryHolds} from "./SparkV15TemporaryHolds.sol";

/// @notice Record the published escalation contact's takeover of a payment overdue under its original terms.
contract SparkV15PaymentTakeover is SparkV15ReviewContext {
    /// @dev All zero selects the default cutoff. An earlier prompt cutoff can use a formal lift and, if a
    /// temporary hold remained in force at the lift, the expiry that completed release.
    struct CutoffSelection {
        bool originalExecution;
        bytes32 releasedHoldId;
        uint128 unpaidAtRelease;
        bytes32 expiringTemporaryHoldId;
    }

    struct Input {
        bytes32 caseId;
        bytes32 termsId;
        bytes32 obligationId;
        uint64 takenOverAt;
        address responsible;
        uint64 assignedAt;
        uint64 newActionDate;
        bytes32 progress;
        Notice notice;
        uint128 unpaidAtDeadline;
        uint128 unpaidAtTakeover;
        CutoffSelection cutoffSelection;
        bytes32 settlementBasis;
    }

    struct Basis {
        bytes32 formId;
        bytes32 originalCommitment;
        uint256 obligationVersion;
        uint64 cutoff;
        uint64 releasedAt;
        uint128 outstanding;
        address debtor;
        address beneficiary;
        bytes32 concernPartiesHash;
        bytes32 originalPartiesHash;
        bytes32 materialContactRef;
    }

    struct Record {
        bytes32 caseId;
        bytes32 termsId;
        bytes32 obligationId;
        address responsible;
        uint64 takenOverAt;
        uint64 newActionDate;
        uint64 cutoff;
        uint64 recordedAt;
        uint256 evidenceId;
    }

    event PaymentTakenOver(
        bytes32 indexed obligationId, bytes32 indexed caseId, bytes32 indexed recordId, uint256 evidenceId
    );

    SparkV15Settlement public immutable SETTLEMENT;
    SparkV15ReviewCases public immutable REVIEW_CASES;

    mapping(bytes32 => Record) private takeovers;

    constructor(SparkV15Settlement settlement, SparkV15ReviewCases cases, bytes32 evidenceRole)
        SparkV15ReviewContext(settlement.PAYMENTS(), evidenceRole, address(this))
    {
        SETTLEMENT = settlement;
        REVIEW_CASES = cases;
    }

    /// @dev Source evidence attests the contact on the exact signed form, historical net unpaid at the
    /// selected cutoff, takeover and any selected release, and delivery to the affected parties.
    /// A release at temporary expiry also requires evidence of all overlapping holds and their order.
    /// For material shares the Source verifies the route under the original annex's contact reference.
    function takeoverCommitment(Input calldata input, address actor) external view returns (bytes32) {
        (Basis memory basis,,) = _basis(input);
        return _commitment(input, basis, actor);
    }

    function record(Input calldata input, uint256 evidenceId, bytes32 authorityId) external returns (bytes32 id) {
        (Basis memory basis, uint256 packageId, address escalator) = _basis(input);
        id = keccak256(abi.encode(
            input.obligationId,
            escalator,
            input.takenOverAt,
            input.responsible,
            input.assignedAt,
            input.newActionDate,
            input.progress,
            input.notice
        ));
        if (
            msg.sender != escalator || input.responsible == address(0) || input.progress == bytes32(0)
                || input.unpaidAtDeadline == 0 || input.unpaidAtTakeover == 0 || input.assignedAt < input.takenOverAt
                || input.newActionDate < input.assignedAt || basis.cutoff == 0 || input.takenOverAt <= basis.cutoff
                || takeovers[id].evidenceId != 0
        ) revert InvalidCase();
        _requireNotice(input.notice, input.assignedAt);
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_ESCALATE_CASE, authorityId);
        _requireEvidence(
            evidenceId,
            packageId,
            _subject(input),
            SparkV15ReviewActions.ACTION_ESCALATE_CASE,
            keccak256(abi.encode(input, basis))
        );
        if (EVIDENCE_REGISTRY.getEvidence(evidenceId).registeredAt < input.notice.sentAt) revert InvalidEvidence();

        takeovers[id] = Record({
            caseId: input.caseId,
            termsId: input.termsId,
            obligationId: input.obligationId,
            responsible: input.responsible,
            takenOverAt: input.takenOverAt,
            newActionDate: input.newActionDate,
            cutoff: basis.cutoff,
            recordedAt: uint64(block.timestamp),
            evidenceId: evidenceId
        });
        emit PaymentTakenOver(input.obligationId, input.caseId, id, evidenceId);
    }

    function get(bytes32 id) external view returns (Record memory) {
        return takeovers[id];
    }

    function _commitment(Input calldata input, Basis memory basis, address actor) private view returns (bytes32) {
        return _evidenceCommitment(
            _subject(input), SparkV15ReviewActions.ACTION_ESCALATE_CASE, actor, keccak256(abi.encode(input, basis))
        );
    }

    function _subject(Input calldata input) private pure returns (bytes32) {
        return input.caseId == bytes32(0) ? input.obligationId : input.caseId;
    }

    function _basis(Input calldata input) private view returns (Basis memory basis, uint256 packageId, address escalator) {
        SparkV15ConcernIntake intake = REVIEW_CASES.INTAKE();
        PublishedContacts memory publication = intake.getPublishedContacts(input.termsId);
        SparkV15Payments.Obligation memory payment = PAYMENTS.getObligation(input.obligationId);
        ReviewTerms memory terms = publication.terms;
        packageId = payment.packageId;
        if (
            packageId == 0 || packageId != publication.packageId || terms.lessonId != payment.terms.lessonId
                || terms.governingForm == bytes32(0)
                || publication.publishedAt > input.takenOverAt || input.takenOverAt > block.timestamp
                || !_available(publication.evidenceId, packageId)
        ) revert InvalidCase();

        if (input.caseId != bytes32(0)) {
            ConcernContext memory context = intake.caseContext(input.caseId);
            if (context.termsId != input.termsId || context.obligationId != input.obligationId) revert InvalidCase();
            uint64 matterAt = context.receivedAt;
            if (matterAt == 0 || !_available(context.evidenceId, packageId)) {
                matterAt = REVIEW_CASES.originalRetainedAt(input.caseId);
            }
            if (matterAt == 0 || matterAt > input.takenOverAt) revert InvalidCase();
            basis.concernPartiesHash = context.partiesHash;
            (, basis.originalPartiesHash) = REVIEW_CASES.reviewHistory(input.caseId);
        }
        _requireGoverningForm(terms, payment, input, basis);

        basis.formId = terms.governingForm;
        basis.originalCommitment = payment.commitment;
        basis.obligationVersion = payment.version;
        if (payment.paid < payment.correctAmount) {
            basis.outstanding = uint128(payment.correctAmount - payment.paid);
        } else if (
            payment.correctAmount != payment.terms.amount || payment.beneficiaryVersion != 0
                || input.unpaidAtDeadline > payment.terms.amount || input.unpaidAtTakeover > payment.terms.amount
        ) {
            revert InvalidCase();
        }
        basis.beneficiary = payment.beneficiary;
        (basis.cutoff, basis.releasedAt) = _cutoff(input, payment);
        escalator = terms.escalationContact;
    }

    function _requireGoverningForm(
        ReviewTerms memory terms,
        SparkV15Payments.Obligation memory payment,
        Input calldata input,
        Basis memory basis
    ) private view {
        SparkV15Booking booking = SETTLEMENT.BOOKING();
        SparkV15Booking.Lesson memory lesson = booking.getLesson(terms.lessonId);
        if (
            lesson.packageId != payment.packageId || terms.publication != lesson.terms.documentsRef
                || terms.provider != lesson.terms.provider || terms.coordinator != lesson.terms.coordinator
        ) revert InvalidCase();

        if (payment.terms.agreedStart == 0 && payment.terms.originalDebitAccount == bytes32(0)) {
            _requireMaterialForm(booking, lesson.terms.materialsTermsRef, terms, payment, input, basis);
            return;
        }

        basis.debtor = terms.provider;
        SparkV15Settlement.SeatSettlement memory seat = SETTLEMENT.getSeatSettlement(terms.lessonId, terms.governingForm);
        if (
            seat.formId != terms.governingForm || payment.beneficiary != payment.terms.recipient
                || (seat.refundObligationId != input.obligationId && seat.tutorObligationId != input.obligationId)
        ) revert InvalidCase();

        bytes32 settlementBasis = input.settlementBasis;
        if (settlementBasis == bytes32(0)) {
            SparkV15Settlement.GroupSettlement memory finalSettlement = SETTLEMENT.getGroupSettlement(terms.lessonId);
            if (!finalSettlement.complete || finalSettlement.approvedAt > input.takenOverAt) revert InvalidCase();
        } else {
            SparkV15Settlement.GroupSettlement memory tranche = SETTLEMENT.getSettlementTranche(settlementBasis);
            // The Source checks the seat's original establishment in that approval receipt. An independently
            // established obligation can also contain a caller-supplied basis, so the hash alone is insufficient.
            if (
                tranche.approvedAt == 0 || tranche.approvedAt > input.takenOverAt
                    || PAYMENTS.paymentEvidenceCommitment(payment.terms, settlementBasis) != payment.commitment
            ) revert InvalidCase();
        }
    }

    function _requireMaterialForm(
        SparkV15Booking booking,
        bytes32 lessonAnnex,
        ReviewTerms memory terms,
        SparkV15Payments.Obligation memory payment,
        Input calldata input,
        Basis memory basis
    ) private view {
        address provisionsAddress = PAYMENTS.FUNDS().materialProvisions();
        if (provisionsAddress == address(0) || input.settlementBasis != bytes32(0)) revert InvalidCase();
        SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(provisionsAddress);
        SparkV15MaterialProvisions.Entitlement memory entitlement = provisions.getEntitlement(input.obligationId);
        if (
            entitlement.evidenceId == 0 || entitlement.input.verifiedAt > input.takenOverAt
                || entitlement.input.holder != payment.beneficiary
        ) revert InvalidCase();

        SparkV15Materials materials = provisions.MATERIALS();
        bytes32 scopeId = entitlement.input.scopeId;
        SparkV15Materials.ChargeScope memory scope = materials.getChargeScope(scopeId);
        SparkV15Materials.AgreedTerms memory annex = materials.getAgreedTerms(terms.lessonId);
        SparkV15Booking.Form memory form = booking.getForm(terms.governingForm);
        if (
            scope.lessonId != terms.lessonId || scope.termsRef != annex.commitment || annex.commitment != lessonAnnex
                || form.lessonId != terms.lessonId || form.confirmation.confirmedAt == 0
                || form.confirmation.confirmedAt > input.takenOverAt
                || form.terms.materialsBundleRef != annex.bundleRef || form.terms.materialPayer != annex.payer
                || payment.terms.settlementApprover != annex.payer || payment.terms.dueAt != annex.paymentDue
                || payment.terms.executionDeadline != annex.paymentDeadline
        ) revert InvalidCase();
        (uint128 gross, bool pending) = materials.activeScopeGrossAt(scopeId, terms.governingForm, input.takenOverAt);
        if (
            gross == 0 || pending
                || input.unpaidAtTakeover
                    > provisions.MATERIAL_BACKING().holderPortion(scopeId, scope, payment.beneficiary, input.takenOverAt)
        ) revert InvalidCase();
        basis.debtor = annex.payer;
        basis.materialContactRef = annex.contactRef;
    }

    function _cutoff(Input calldata input, SparkV15Payments.Obligation memory payment)
        private
        view
        returns (uint64 cutoff, uint64 release)
    {
        SparkV15Payments.PaymentTerms memory terms = payment.terms;
        SparkV15PaymentHolds holds = PAYMENTS.HOLDS();
        (SparkV15PaymentHolds.Status memory hold, bool ordinaryBlocked) = holds.takeoverClock(input.obligationId);
        CutoffSelection calldata selection = input.cutoffSelection;
        bytes32 temporaryId = selection.expiringTemporaryHoldId;
        if (selection.originalExecution || selection.releasedHoldId != bytes32(0) || temporaryId != bytes32(0)) {
            // A different observed deadline cannot bypass coverage of the original execution deadline.
            if (
                ordinaryBlocked || hold.firstFullReleaseAt != 0 || input.unpaidAtDeadline > terms.amount
                    || input.unpaidAtTakeover > terms.amount
            ) revert InvalidCase();
            if (selection.originalExecution) {
                if (
                    !terms.executionDeadlineExact || selection.releasedHoldId != bytes32(0)
                        || selection.unpaidAtRelease != 0 || temporaryId != bytes32(0)
                ) revert InvalidCase();
                return (terms.executionDeadline, 0);
            }

            SparkV15PaymentHolds.FormalHold memory releasedHold = holds.getFormalHold(selection.releasedHoldId);
            release = releasedHold.liftedAt;
            if (
                releasedHold.terms.obligationId != input.obligationId || release == 0
                    || selection.unpaidAtRelease == 0 || selection.unpaidAtRelease > terms.amount
            ) revert InvalidCase();
            if (temporaryId == bytes32(0)) {
                if (!releasedHold.completelyReleased) revert InvalidCase();
            } else {
                if (
                    releasedHold.completelyReleased || !terms.executionDeadlineExact
                        || payment.correctAmount != terms.amount || payment.beneficiaryVersion != 0
                ) revert InvalidCase();
                SparkV15TemporaryHolds.Hold memory temporary = holds.getTemporaryHold(temporaryId);
                if (
                    temporary.terms.obligationId != input.obligationId || temporary.imposedAt > release
                        || temporary.terms.expiresAt <= release || temporary.replacedBy != bytes32(0)
                ) revert InvalidCase();
                release = temporary.terms.expiresAt;
            }
            cutoff = _ordinaryPromptCutoff(terms, release);
            if (
                release > input.takenOverAt || cutoff == 0
                    || (temporaryId != bytes32(0) && terms.legalDeadline != 0 && terms.legalDeadline < cutoff)
            ) revert InvalidCase();
            return (cutoff, release);
        }
        if (selection.unpaidAtRelease != 0) revert InvalidCase();

        if (hold.firstFullReleaseAt != 0) {
            if (hold.firstFullReleaseAt <= input.takenOverAt && hold.postLiftCutoff != 0) {
                cutoff = hold.postLiftCutoff;
                release = hold.firstFullReleaseAt;
            }
        } else if (!ordinaryBlocked) {
            cutoff = terms.executionDeadline;
            if (hold.lastFullReleaseAt <= input.takenOverAt) {
                uint64 prompt = _ordinaryPromptCutoff(terms, hold.lastFullReleaseAt);
                if (prompt != 0) {
                    cutoff = prompt;
                    release = hold.lastFullReleaseAt;
                }
            }
        }
        if (terms.legalDeadline != 0 && (cutoff == 0 || terms.legalDeadline < cutoff)) {
            cutoff = terms.legalDeadline;
            release = 0;
        }
    }

    function _ordinaryPromptCutoff(SparkV15Payments.PaymentTerms memory terms, uint64 releasedAt)
        private
        pure
        returns (uint64)
    {
        if (releasedAt <= terms.dueAt) return 0;
        uint64 prompt = terms.postLiftPeriod == 0 ? terms.postLiftDeadline : releasedAt + terms.postLiftPeriod;
        return prompt < terms.executionDeadline ? prompt : 0;
    }
}
