// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACapabilityKeys} from "@ava-protocol/contracts/src/core/AVACapabilityKeys.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {SparkV15Booking, SparkV15BookingOpening} from "./SparkV15Booking.sol";
import {SparkV15Payments} from "./SparkV15Payments.sol";
import {SparkV15SettlementCompilation} from "./SparkV15SettlementCompilation.sol";
import {SparkV15SettlementAlternatives} from "./SparkV15SettlementAlternatives.sol";
import {SparkV15SettlementOccurrences} from "./SparkV15SettlementOccurrences.sol";

interface ISparkV15SettlementRemedies {
    function faultFee(bytes32 formId) external view returns (bool applicable, uint128 finalFee);
    function allowsTutorWage(bytes32 lessonId, address tutor) external view returns (bool);
    function mayPayRedressPart(bytes32 obligationId) external view returns (bool);
    function mayPaySettledTutorDeductions(bytes32 lessonId, address tutor) external view returns (bool);
    function previewTutorDeductions(bytes32 lessonId, address tutor, uint128 gross) external view returns (uint128 net);
    function recordTutorDeductions(bytes32 lessonId, address tutor, uint128 gross) external returns (uint128 net);
}

/// @notice Assess an effective roster and retain the basis for each independent tuition and wage obligation.
contract SparkV15Settlement {
    enum Route {
        OrdinaryGroup,
        VerifiedGroup,
        OrdinaryOneToOne,
        VerifiedOneToOne,
        OneToOneAbsence,
        OneToOneAgreedAbsence,
        ProviderStartedEarly
    }

    enum SeatDisposition {
        Unverified,
        OrdinaryFee,
        VerifiedAbsence,
        DeferredByHold,
        PreviouslySettled,
        TutorFaultFee,
        ProviderStartedEarly,
        ProviderRedressFee
    }

    struct PaymentSchedule {
        uint64 dueAt;
        uint64 executionDeadline;
        uint64 postLiftDeadline;
        uint64 postLiftPeriod;
    }

    struct TutorSeatTerms {
        bytes32 placeId;
        uint128 ordinaryPay;
        uint128 absencePay;
    }

    struct TutorPayTerms {
        bytes32 agreementRef;
        address recipient;
        PaymentSchedule schedule;
        TutorSeatTerms[] seats;
    }

    struct RefundTerms {
        bytes32 serviceDocumentRef;
        PaymentSchedule schedule;
    }

    struct SeatFinding {
        bytes32 formId;
        SeatDisposition disposition;
        bytes32 serviceAvailabilityRef;
        bytes32 feeHoldCaseId;
        bool studentFaultFound;
        // For a ProviderStartedEarly group, these two fields carry the verified amounts under the provider terms.
        // Their existing ABI names also cover the agreed-absence route.
        uint128 agreedAbsenceFee;
        uint128 agreedAbsenceTutorPay;
    }

    struct GroupAssessment {
        TutorPayTerms tutor;
        RefundTerms refund;
        // Independently verified on approval. See approveOrdinaryGroup for the scope of the finding.
        bytes32 clearanceRef;
        SeatFinding[] seats;
        Route route;
        // For one-to-one ProviderStartedEarly, see OCCURRENCES.encodeProviderStartedEarlyAmounts.
        bytes32 verificationRef;
        bytes32 clockBoundaryRef;
        uint256 clockEvidenceId;
        uint128[] agreedNetWages;
        bytes32 effectiveChangeId;
    }

    struct GroupPreview {
        bytes32 basis;
        uint128 totalTutorPay;
        uint256 attendanceConfirmations;
        SparkV15Payments.PaymentTerms[] payments;
        uint128 netTutorPay;
    }

    struct Proposal {
        bytes32 commitment;
        address proposer;
        bytes32 authorityId;
        uint64 proposedAt;
    }

    struct LocalApproval {
        Proposal proposal;
        bytes32 completionRoot;
        bool adoptAttendance;
    }

    struct SeatSettlement {
        bytes32 formId;
        bytes32 placeId;
        bytes32 debitAccount;
        address debitOwner;
        uint128 normalFee;
        uint128 debited;
        uint128 feeDue;
        uint128 refundDue;
        uint128 tutorPay;
        SeatDisposition disposition;
        uint256 noticeEvidenceId;
        uint256 attendanceEvidenceId;
        uint256 serviceFeedbackEvidenceId;
        bytes32 serviceAvailabilityRef;
        bytes32 refundObligationId;
        bytes32 tutorObligationId;
        uint256 refundAlreadyReceived;
        bytes32 holdWitness;
        uint128 tutorNetPay;
        uint256 replacementNoticeEvidenceId;
    }

    struct GroupSettlement {
        bytes32 basis;
        address approver;
        bytes32 approvalAuthorityId;
        uint64 approvedAt;
        uint256 evidenceId;
        uint128 totalTutorPay;
        uint256 attendanceConfirmations;
        Route route;
        bool complete;
        uint128 netTutorPay;
    }

    struct CompiledGroup {
        GroupPreview preview;
        SeatSettlement[] seats;
        uint256 packageId;
        bytes32 approvalAuthorityId;
        bool partialSettlement;
        bool originalTutorFault;
        address tutor;
        uint256 legalDeadlineEvidenceId;
        SparkV15SettlementAlternatives.AbsenceReason absence;
    }

    struct WageScope {
        bytes32 lessonId;
        bytes32 formId;
        address tutor;
        bool independent;
        SparkV15SettlementAlternatives.AbsenceReason absence;
        bool localCompletionAdopted;
        uint256 legalDeadlineEvidenceId;
    }

    bytes32 public constant ACTION_PROPOSE_GROUP_SETTLEMENT = keccak256("spark.action.propose-group-settlement.v1.5");
    bytes32 public constant ACTION_APPROVE_GROUP_SETTLEMENT = keccak256("spark.action.approve-group-settlement.v1.5");

    error InvalidSettlementInstallation();
    error InvalidGroupProposal();
    error InvalidSettlementEvidence();
    error InvalidAgreedPaymentTerms();
    error OrdinaryGroupConditionsNotMet();
    error InterestedSettlementActor();
    error ApplicableArrangementChanged();
    error InvalidApprovalCaller();

    event GroupSettlementProposed(
        bytes32 indexed lessonId, bytes32 indexed commitment, address indexed proposer, bytes32 authorityId
    );
    event GroupSettlementApproved(
        bytes32 indexed lessonId,
        bytes32 indexed basis,
        address indexed approver,
        uint256 evidenceId,
        uint128 totalTutorPay
    );
    event OrdinarySettlementConsented(
        bytes32 indexed lessonId, bytes32 indexed basis, address indexed source, bytes32 sourceAuthorityId
    );
    event OrdinaryWageEvidenceAdopted(
        bytes32 indexed obligationId,
        bytes32 indexed commitment,
        address indexed source,
        bytes32 sourceAuthorityId,
        uint256 disclosurePolicyId,
        uint64 validThrough
    );
    event OrdinaryWageEvidenceInvalidated(
        bytes32 indexed obligationId,
        AVACoreTypes.EvidenceLifecycleKind kind,
        bytes32 reasonHash,
        bytes32 authorityId,
        address actor
    );
    event OrdinaryOneToOneRecordsAdopted(
        bytes32 indexed lessonId,
        bytes32 indexed formId,
        bytes32 indexed basis,
        bytes32 studentReportRef,
        bytes32 coordinatorReportRef,
        bytes32 proposalCommitment,
        bytes32 coordinatorAuthorityId
    );
    event OrdinaryAttendanceAdopted(
        bytes32 indexed lessonId, bytes32 indexed formId, bytes32 indexed basis, bytes32 reportRef
    );
    event SettlementSeatDeferred(
        bytes32 indexed lessonId, bytes32 indexed formId, bytes32 indexed basis, bytes32 holdWitness
    );

    SparkV15Booking public immutable BOOKING;
    SparkV15Payments public immutable PAYMENTS;
    SparkV15SettlementAlternatives public ALTERNATIVES;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;
    SparkV15BookingOpening private immutable OPENING;
    SparkV15SettlementCompilation private immutable COMPILATION;
    ISparkV15SettlementRemedies public remedyPolicy;

    mapping(bytes32 => Proposal) public proposals;
    mapping(bytes32 => bytes32) private finalSettlementBasis;
    mapping(bytes32 => GroupSettlement) private settlementTranches;
    mapping(bytes32 => mapping(bytes32 => SeatSettlement)) private seatSettlements;
    mapping(bytes32 => WageScope) private wageScopes;
    mapping(bytes32 => mapping(address => bool)) public isSettlementActor;
    mapping(bytes32 => AVACoreTypes.EvidenceStatus) public adoptedWageEvidenceStatus;

    constructor(SparkV15Booking booking, SparkV15Payments payments) {
        if (
            address(booking).code.length == 0 || address(payments).code.length == 0
                || address(booking.REQUEST_ALLOCATION()) != address(payments.REQUEST_ALLOCATION())
                || address(booking.FUNDS()) != address(payments.FUNDS()) || booking.WORKFLOW() != payments.WORKFLOW()
        ) revert InvalidSettlementInstallation();
        SparkV15BookingOpening opening = booking.OPENING();
        if (address(opening) == address(0)) revert InvalidSettlementInstallation();
        BOOKING = booking;
        PAYMENTS = payments;
        EVIDENCE_REGISTRY = payments.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        OPENING = opening;
        COMPILATION = new SparkV15SettlementCompilation(booking, payments);
    }

    function bindAlternatives(SparkV15SettlementAlternatives alternatives) external {
        _requireAppAdmin();
        if (
            address(ALTERNATIVES) != address(0) || address(alternatives).code.length == 0
                || address(alternatives.SETTLEMENT()) != address(this) || alternatives.BOOKING() != BOOKING
                || alternatives.PAYMENTS() != PAYMENTS
        ) revert InvalidSettlementInstallation();
        ALTERNATIVES = alternatives;
    }

    function setRemedyPolicy(ISparkV15SettlementRemedies policy) external {
        _requireAppAdmin();
        if (address(remedyPolicy) != address(0) || address(policy).code.length == 0) {
            revert InvalidSettlementInstallation();
        }
        remedyPolicy = policy;
    }

    function _requireAppAdmin() private view {
        EVIDENCE_REGISTRY.IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
    }

    function refundPaymentPart(bytes32 placeId) public pure returns (bytes32) {
        return keccak256(abi.encode("spark.v1.5.lesson-refund", placeId));
    }

    function tutorPaymentPart(address tutor, bytes32 placeId) public pure returns (bytes32) {
        return keccak256(abi.encode("spark.v1.5.tutor-pay", tutor, placeId));
    }

    function tutorPayTermsCommitment(bytes32 lessonId, TutorPayTerms calldata terms) public view returns (bytes32) {
        return keccak256(
            abi.encode(keccak256("spark.v1.5.tutor-pay-terms"), block.chainid, address(BOOKING), lessonId, terms)
        );
    }

    function refundTermsCommitment(bytes32 lessonId, RefundTerms calldata terms) public view returns (bytes32) {
        return
            keccak256(
                abi.encode(keccak256("spark.v1.5.refund-terms"), block.chainid, address(BOOKING), lessonId, terms)
            );
    }

    function proposalCommitment(bytes32 lessonId, GroupAssessment calldata assessment) public view returns (bytes32) {
        return
            keccak256(abi.encode(ACTION_PROPOSE_GROUP_SETTLEMENT, block.chainid, address(this), lessonId, assessment));
    }

    /// @notice Record the coordinator's signed proposal. A later proposal can replace it before approval.
    function proposeOrdinaryGroup(bytes32 lessonId, bytes32 commitment) external {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        if (
            commitment == bytes32(0) || lesson.terms.coordinator != msg.sender
                || block.timestamp < BOOKING.getEffectiveArrangement(lessonId, uint64(block.timestamp)).startsAt
                || finalSettlementBasis[lessonId] != bytes32(0)
        ) revert InvalidGroupProposal();
        bytes32 authorityId = EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                msg.sender, SparkV15.APP_ID, BOOKING.COORDINATOR_ROLE(), ACTION_PROPOSE_GROUP_SETTLEMENT
            );
        proposals[lessonId] = Proposal(commitment, msg.sender, authorityId, uint64(block.timestamp));
        emit GroupSettlementProposed(lessonId, commitment, msg.sender, authorityId);
    }

    /// @notice Derive the approval evidence commitment and the exact payment terms in evidence registration order.
    function previewOrdinaryGroup(bytes32 lessonId, GroupAssessment calldata assessment, address approver)
        external
        view
        returns (GroupPreview memory)
    {
        LocalApproval memory local;
        local.proposal = proposals[lessonId];
        return _compileGroup(lessonId, assessment, approver, local).preview;
    }

    /// @notice Calculate the matching Source and wage evidence basis without adopting any records.
    function previewOrdinaryOneToOneWithLocalRecords(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        address approver,
        SparkV15SettlementOccurrences.LocalOneToOneRecords calldata records
    ) external view returns (GroupPreview memory) {
        LocalApproval memory local = _localApproval(lessonId, assessment, records);
        return _compileGroup(lessonId, assessment, approver, local).preview;
    }

    /// @notice Preview ordinary settlement with a separately signed positive attendance report.
    function previewOrdinaryOneToOneWithLocalAttendance(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        address approver,
        SparkV15SettlementOccurrences.LocalOneToOneRecords calldata records,
        SparkV15SettlementOccurrences.SignedAttendance calldata signedAttendance
    ) external view returns (GroupPreview memory) {
        LocalApproval memory local = _localApproval(lessonId, assessment, records);
        _includeLocalAttendance(lessonId, records.formId, signedAttendance, local);
        return _compileGroup(lessonId, assessment, approver, local).preview;
    }

    /// @notice Approve the proposal and reserve each independently established obligation in the shared funds.
    /// @dev The independent Core source and approver attest that service was genuinely available at each place and
    /// that the identified actors have no disqualifying interest. The lesson-wide clearance covers the assessment's
    /// scope, treatment of each retained form and any other relevant exception. Case-scoped fee holds and operative
    /// tutor deductions also come from their native records. Each payment uses a separately registered commitment.
    function approveOrdinaryGroup(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        uint256 evidenceId,
        uint256[] calldata paymentEvidenceIds
    ) external {
        SparkV15BookingOpening.OrdinarySettlementConsent memory consent;
        LocalApproval memory local;
        this.approveFromEntry(lessonId, assessment, evidenceId, paymentEvidenceIds, consent, msg.sender, false, local, "");
    }

    /// @notice Approve an ordinary paid one-to-one settlement using a Source consent first adopted here.
    /// @dev The wage requires its own registered evidence. The consent supplies no Core evidence ID.
    function approveOrdinaryOneToOneWithConsent(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        SparkV15BookingOpening.OrdinarySettlementConsent calldata consent,
        uint256[] calldata paymentEvidenceIds
    ) external {
        LocalApproval memory local;
        this.approveFromEntry(lessonId, assessment, 0, paymentEvidenceIds, consent, msg.sender, true, local, "");
    }

    /// @notice Adopt signed completion statements and a proposed assessment in the independent approval transaction.
    /// @dev These records have no earlier App availability. An existing proposal or confirmation uses the legacy path.
    function approveOrdinaryOneToOneWithLocalRecords(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        SparkV15BookingOpening.OrdinarySettlementConsent calldata consent,
        uint256[] calldata paymentEvidenceIds,
        SparkV15SettlementOccurrences.LocalOneToOneRecords calldata records
    ) external {
        LocalApproval memory local = _localApproval(lessonId, assessment, records);
        _approveLocalRecords(lessonId, assessment, consent, paymentEvidenceIds, records, local);
    }

    /// @notice Adopt the student's separate attendance report with the normal independent approval.
    function approveOrdinaryOneToOneWithLocalAttendance(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        SparkV15BookingOpening.OrdinarySettlementConsent calldata consent,
        uint256[] calldata paymentEvidenceIds,
        SparkV15SettlementOccurrences.LocalOneToOneRecords calldata records,
        SparkV15SettlementOccurrences.SignedAttendance calldata signedAttendance
    ) external {
        LocalApproval memory local = _localApproval(lessonId, assessment, records);
        _includeLocalAttendance(lessonId, records.formId, signedAttendance, local);
        _approveLocalRecords(lessonId, assessment, consent, paymentEvidenceIds, records, local);
        _recordAdoptedAttendance(lessonId, records.formId, signedAttendance.reportRef);
    }

    /// @notice Adopt separate signed completion, attendance, settlement support and wage evidence in one approval.
    /// @dev A retained wage, a legacy support record or a nonordinary result uses the existing entry points.
    function approveOrdinaryOneToOneWithAdoptedWage(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        SparkV15BookingOpening.OrdinarySettlementConsent calldata consent,
        SparkV15BookingOpening.OrdinaryWageEvidence calldata wageEvidence,
        SparkV15SettlementOccurrences.LocalOneToOneRecords calldata records,
        SparkV15SettlementOccurrences.SignedAttendance calldata signedAttendance
    ) external {
        LocalApproval memory local = _localApproval(lessonId, assessment, records);
        _includeLocalAttendance(lessonId, records.formId, signedAttendance, local);
        this.approveFromEntry(
            lessonId, assessment, 0, new uint256[](0), consent, msg.sender, true, local, abi.encode(wageEvidence)
        );
        _recordAdoptedCompletions(lessonId, records, local);
        _recordAdoptedAttendance(lessonId, records.formId, signedAttendance.reportRef);
    }

    function _adoptWageEvidence(CompiledGroup memory compiled, SparkV15BookingOpening.OrdinaryWageEvidence memory proof)
        private
    {
        SparkV15Payments.PaymentTerms memory wage = compiled.preview.payments[0];
        bytes32 commitment = PAYMENTS.paymentEvidenceCommitment(wage, compiled.preview.basis);
        address source = OPENING.requireOrdinaryWageEvidence(compiled.packageId, commitment, proof);
        if (source == wage.settlementApprover || source == wage.settlementProposer) revert InterestedSettlementActor();
        COMPILATION.requireDisinterestedWageSource(wage.lessonId, compiled.seats[0].formId, wage.recipient, source);
        bytes32 obligationId = keccak256(abi.encode(wage.lessonId, wage.paymentPart));
        adoptedWageEvidenceStatus[obligationId] = AVACoreTypes.EvidenceStatus.Active;
        emit OrdinaryWageEvidenceAdopted(
            obligationId, commitment, source, proof.sourceAuthorityId, proof.disclosurePolicyId, proof.validThrough
        );
    }

    function _approveLocalRecords(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        SparkV15BookingOpening.OrdinarySettlementConsent calldata consent,
        uint256[] calldata paymentEvidenceIds,
        SparkV15SettlementOccurrences.LocalOneToOneRecords calldata records,
        LocalApproval memory local
    ) private {
        this.approveFromEntry(lessonId, assessment, 0, paymentEvidenceIds, consent, msg.sender, true, local, "");
        _recordAdoptedCompletions(lessonId, records, local);
    }

    function _recordAdoptedCompletions(
        bytes32 lessonId,
        SparkV15SettlementOccurrences.LocalOneToOneRecords calldata records,
        LocalApproval memory local
    ) private {
        emit OrdinaryOneToOneRecordsAdopted(
            lessonId,
            records.formId,
            finalSettlementBasis[lessonId],
            records.studentReportRef,
            records.coordinatorReportRef,
            local.proposal.commitment,
            local.proposal.authorityId
        );
    }

    function _recordAdoptedAttendance(bytes32 lessonId, bytes32 formId, bytes32 reportRef) private {
        BOOKING.recordAttendance(formId, true, reportRef, 0);
        emit OrdinaryAttendanceAdopted(lessonId, formId, finalSettlementBasis[lessonId], reportRef);
    }

    function _localApproval(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        SparkV15SettlementOccurrences.LocalOneToOneRecords calldata records
    ) private view returns (LocalApproval memory local) {
        _requireOrdinaryOneToOneRoute(assessment);
        if (
            proposals[lessonId].proposer != address(0) || assessment.seats.length != 1
                || assessment.seats[0].formId != records.formId
        ) revert InvalidGroupProposal();
        COMPILATION.requireNoExistingRedress(records.formId);
        local.proposal.commitment = proposalCommitment(lessonId, assessment);
        (local.completionRoot, local.proposal.proposer, local.proposal.authorityId) =
            ALTERNATIVES.OCCURRENCES().requireLocalOneToOneRecords(lessonId, local.proposal.commitment, records);
    }

    function _includeLocalAttendance(
        bytes32 lessonId,
        bytes32 formId,
        SparkV15SettlementOccurrences.SignedAttendance calldata signedAttendance,
        LocalApproval memory local
    ) private view {
        bytes32 attendanceMessage = ALTERNATIVES.OCCURRENCES().requireLocalAttendance(lessonId, formId, signedAttendance);
        local.completionRoot = keccak256(abi.encode(local.completionRoot, attendanceMessage));
        local.adoptAttendance = true;
    }

    /// @dev Share one approval body across all entry points under the deployment bytecode limit.
    function approveFromEntry(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        uint256 evidenceId,
        uint256[] calldata paymentEvidenceIds,
        SparkV15BookingOpening.OrdinarySettlementConsent calldata consent,
        address approver,
        bool withConsent,
        LocalApproval calldata local,
        bytes calldata wageProof
    ) external {
        if (msg.sender != address(this)) revert InvalidApprovalCaller();
        if (withConsent) _requireOrdinaryOneToOneRoute(assessment);
        LocalApproval memory effective = local;
        if (effective.completionRoot == bytes32(0)) effective.proposal = proposals[lessonId];
        Proposal memory proposal = effective.proposal;
        CompiledGroup memory compiled = _compileGroup(lessonId, assessment, approver, effective);
        GroupPreview memory preview = compiled.preview;
        bool adoptWage = wageProof.length != 0;
        if (!adoptWage && paymentEvidenceIds.length != preview.payments.length) revert InvalidSettlementEvidence();
        if (withConsent) {
            if (effective.completionRoot == bytes32(0)) COMPILATION.requireNoExistingRedress(compiled.seats[0].formId);
            _validateSettlementConsent(lessonId, compiled, approver, proposal.proposer, consent);
            if (adoptWage) {
                _adoptWageEvidence(compiled, abi.decode(wageProof, (SparkV15BookingOpening.OrdinaryWageEvidence)));
            }
        } else {
            OPENING.requireRegisteredSettlementEvidence(
                evidenceId, compiled.packageId, preview.basis, proposal.proposedAt, proposal.proposer, approver
            );
            if (assessment.route == Route.ProviderStartedEarly) {
                OPENING.requireIndependentProviderStartSource(
                    evidenceId, lessonId, compiled.seats[0].formId, assessment.tutor.recipient
                );
            }
        }
        _approveCompiled(
            lessonId,
            assessment,
            evidenceId,
            paymentEvidenceIds,
            compiled,
            approver,
            local.completionRoot != bytes32(0),
            adoptWage
        );
    }

    function _requireOrdinaryOneToOneRoute(GroupAssessment calldata assessment) private pure {
        if (
            assessment.route != Route.OrdinaryOneToOne || assessment.effectiveChangeId != bytes32(0)
                || assessment.verificationRef != bytes32(0) || assessment.clockBoundaryRef != bytes32(0)
                || assessment.clockEvidenceId != 0
        ) revert OrdinaryGroupConditionsNotMet();
    }

    function _validateSettlementConsent(
        bytes32 lessonId,
        CompiledGroup memory compiled,
        address approver,
        address proposer,
        SparkV15BookingOpening.OrdinarySettlementConsent calldata consent
    ) private {
        SeatSettlement memory seat = compiled.seats[0];
        if (
            compiled.partialSettlement || compiled.originalTutorFault || compiled.legalDeadlineEvidenceId != 0
                || seat.disposition != SeatDisposition.OrdinaryFee || seat.debited == 0 || seat.refundDue != 0
                || compiled.preview.netTutorPay != compiled.preview.totalTutorPay
                || compiled.preview.payments.length != 1
                || (seat.serviceFeedbackEvidenceId != 0
                    && BOOKING.getServiceFeedback(seat.formId).status != SparkV15Booking.ServiceStatus.FullyDelivered)
        ) revert OrdinaryGroupConditionsNotMet();
        bytes32 basis = compiled.preview.basis;
        address source =
            OPENING.requireOrdinarySettlementConsent(compiled.packageId, lessonId, basis, approver, proposer, consent);
        emit OrdinarySettlementConsented(lessonId, basis, source, consent.sourceAuthorityId);
    }

    function _approveCompiled(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        uint256 evidenceId,
        uint256[] calldata paymentEvidenceIds,
        CompiledGroup memory compiled,
        address approver,
        bool localCompletionAdopted,
        bool adoptedWage
    ) private {
        GroupPreview memory preview = compiled.preview;
        address tutor = compiled.tutor;
        if (
            preview.totalTutorPay != 0 && !compiled.partialSettlement && !compiled.originalTutorFault
                && address(remedyPolicy) != address(0)
                && compiled.absence == SparkV15SettlementAlternatives.AbsenceReason.Unverified
                && remedyPolicy.recordTutorDeductions(lessonId, tutor, preview.totalTutorPay) != preview.netTutorPay
        ) revert InvalidAgreedPaymentTerms();
        GroupSettlement memory settlement = GroupSettlement({
            basis: preview.basis,
            approver: approver,
            approvalAuthorityId: compiled.approvalAuthorityId,
            approvedAt: uint64(block.timestamp),
            evidenceId: evidenceId,
            totalTutorPay: preview.totalTutorPay,
            attendanceConfirmations: preview.attendanceConfirmations,
            route: assessment.route,
            complete: !compiled.partialSettlement,
            netTutorPay: preview.netTutorPay
        });
        settlementTranches[preview.basis] = settlement;
        isSettlementActor[lessonId][approver] = true;
        if (settlement.complete) finalSettlementBasis[lessonId] = preview.basis;
        uint256 nextPayment;
        for (uint256 i; i < compiled.seats.length; ++i) {
            SeatSettlement memory seat = compiled.seats[i];
            if (assessment.seats[i].disposition == SeatDisposition.PreviouslySettled) continue;
            if (seat.disposition == SeatDisposition.DeferredByHold) {
                emit SettlementSeatDeferred(lessonId, seat.formId, preview.basis, seat.holdWitness);
                continue;
            }
            if (
                seat.refundDue != 0 && seat.refundObligationId == bytes32(0)
                    && (seat.disposition == SeatDisposition.VerifiedAbsence
                        || seat.disposition == SeatDisposition.ProviderStartedEarly)
            ) {
                seat.refundObligationId = PAYMENTS.establishSettledPayment(
                    preview.payments[nextPayment], preview.basis, paymentEvidenceIds[nextPayment], compiled.packageId
                );
                ++nextPayment;
            }
            if (seat.tutorNetPay != 0 && seat.tutorObligationId == bytes32(0)) {
                if (adoptedWage) {
                    seat.tutorObligationId =
                        PAYMENTS.establishAdoptedWage(preview.payments[nextPayment], preview.basis, compiled.packageId);
                } else {
                    seat.tutorObligationId = PAYMENTS.establishSettledPayment(
                        preview.payments[nextPayment], preview.basis, paymentEvidenceIds[nextPayment], compiled.packageId
                    );
                }
                ++nextPayment;
            }
            if (seat.tutorObligationId != bytes32(0)) {
                wageScopes[seat.tutorObligationId] = WageScope(
                    lessonId,
                    seat.formId,
                    tutor,
                    compiled.partialSettlement,
                    compiled.absence,
                    localCompletionAdopted,
                    compiled.legalDeadlineEvidenceId
                );
            }
            if (adoptedWage && seat.refundAlreadyReceived == 0) {
                // This final ordinary seat has no refund history and uses an immutable confirmed form. Keep the assessed
                // proof references and original debit owner. The unused Unverified value marks this representation.
                SeatSettlement storage stored = seatSettlements[lessonId][seat.formId];
                stored.formId = seat.formId;
                stored.debitOwner = seat.debitOwner;
                stored.noticeEvidenceId = seat.noticeEvidenceId;
                stored.serviceFeedbackEvidenceId = seat.serviceFeedbackEvidenceId;
                stored.serviceAvailabilityRef = seat.serviceAvailabilityRef;
                stored.tutorObligationId = seat.tutorObligationId;
            } else {
                seatSettlements[lessonId][seat.formId] = seat;
            }
        }
        emit GroupSettlementApproved(lessonId, preview.basis, approver, evidenceId, preview.totalTutorPay);
    }

    function getGroupSettlement(bytes32 lessonId) external view returns (GroupSettlement memory) {
        return settlementTranches[finalSettlementBasis[lessonId]];
    }

    function getSeatSettlement(bytes32 lessonId, bytes32 formId) external view returns (SeatSettlement memory) {
        SeatSettlement memory seat = seatSettlements[lessonId][formId];
        if (seat.formId != bytes32(0) && seat.disposition == SeatDisposition.Unverified) {
            (seat.placeId, seat.debitAccount, seat.normalFee, seat.debited) = COMPILATION.confirmedSeatTerms(formId);
            seat.feeDue = seat.debited;
            seat.tutorPay = settlementTranches[finalSettlementBasis[lessonId]].totalTutorPay;
            seat.tutorNetPay = seat.tutorPay;
            seat.disposition = SeatDisposition.OrdinaryFee;
        }
        return seat;
    }

    function hasSeatSettlement(bytes32 lessonId, bytes32 formId) external view returns (bool) {
        return seatSettlements[lessonId][formId].formId != bytes32(0);
    }

    /// @notice Read the settled seat conditions used to qualify a first ordinary wage approval.
    function isOrdinaryWageSeat(bytes32 lessonId, bytes32 formId, bytes32 obligationId) external view returns (bool) {
        SeatSettlement storage seat = seatSettlements[lessonId][formId];
        if (seat.formId == bytes32(0) || seat.tutorObligationId != obligationId) return false;
        return seat.disposition == SeatDisposition.Unverified
            || (seat.disposition == SeatDisposition.OrdinaryFee && seat.debited != 0 && seat.refundDue == 0);
    }

    /// @notice Both local completions became effective with the wage-bearing ordinary settlement for this seat.
    function hasAdoptedOneToOneCompletion(bytes32 lessonId, bytes32 formId) external view returns (bool) {
        return wageScopes[seatSettlements[lessonId][formId].tutorObligationId].localCompletionAdopted;
    }

    function getSettlementTranche(bytes32 basis) external view returns (GroupSettlement memory) {
        return settlementTranches[basis];
    }

    /// @notice Read an established payment by its original exact terms and currently usable proof.
    function retainedPayment(SparkV15Payments.PaymentTerms calldata expected, uint256 packageId)
        external
        view
        returns (bytes32 id, uint256 alreadyReceived)
    {
        id = keccak256(abi.encode(expected.lessonId, expected.paymentPart));
        SparkV15Payments.Obligation memory obligation = PAYMENTS.getObligation(id);
        if (obligation.packageId == 0) return (bytes32(0), 0);
        if (obligation.packageId != packageId) revert SparkV15SettlementAlternatives.InvalidEvidence();
        SparkV15Payments.PaymentTerms memory current = expected;
        current.settlementProposer = obligation.terms.settlementProposer;
        current.settlementApprover = obligation.terms.settlementApprover;
        if (keccak256(abi.encode(current)) != keccak256(abi.encode(obligation.terms))) {
            revert SparkV15SettlementAlternatives.InvalidEvidence();
        }
        if (obligation.evidenceId != 0) {
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(obligation.evidenceId, packageId);
        } else {
            if (adoptedWageEvidenceStatus[id] != AVACoreTypes.EvidenceStatus.Active) {
                revert SparkV15SettlementAlternatives.InvalidEvidence();
            }
            // First adoption required the default evidence policy. Recheck its package identity on use.
            EVIDENCE_REGISTRY.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_POLICY);
        }
        return (id, obligation.paid);
    }

    /// @notice Invalidate first-use wage evidence using the existing evidence lifecycle authority.
    /// @dev No change to established obligations, payment approvals, holds or actual receipts.
    function recordOrdinaryWageEvidenceLifecycle(
        bytes32 obligationId,
        bytes32 role,
        bytes32 authorityId,
        AVACoreTypes.EvidenceLifecycleKind kind,
        bytes32 reasonHash
    ) external {
        if (
            adoptedWageEvidenceStatus[obligationId] != AVACoreTypes.EvidenceStatus.Active || reasonHash == bytes32(0)
                || (kind != AVACoreTypes.EvidenceLifecycleKind.Revoke && kind != AVACoreTypes.EvidenceLifecycleKind.Expire)
        ) revert InvalidSettlementEvidence();
        EVIDENCE_REGISTRY.AUTHORITY_MATRIX().requireAuthorisedSubject(
            msg.sender, SparkV15.APP_ID, role, AVACoreTypes.ACTION_RECORD_EVIDENCE_LIFECYCLE, authorityId
        );
        uint256 packageId = PAYMENTS.getObligation(obligationId).packageId;
        EVIDENCE_REGISTRY.RULE_PACKAGE_REGISTRY().getModule(packageId, AVACapabilityKeys.EVIDENCE_LIFECYCLE);
        adoptedWageEvidenceStatus[obligationId] = kind == AVACoreTypes.EvidenceLifecycleKind.Revoke
            ? AVACoreTypes.EvidenceStatus.Revoked : AVACoreTypes.EvidenceStatus.Expired;
        emit OrdinaryWageEvidenceInvalidated(obligationId, kind, reasonHash, authorityId, msg.sender);
    }

    function mayPaySettlementPart(bytes32 obligationId) external view returns (bool) {
        ISparkV15SettlementRemedies policy = remedyPolicy;
        if (address(policy) != address(0) && !policy.mayPayRedressPart(obligationId)) return false;
        WageScope storage scope = wageScopes[obligationId];
        if (scope.lessonId == bytes32(0)) return true;
        if (
            scope.legalDeadlineEvidenceId != 0
                && !EVIDENCE_REGISTRY.isEvidenceAvailableForPackage(
                    scope.legalDeadlineEvidenceId, BOOKING.getLesson(scope.lessonId).packageId
                )
        ) return false;
        if (address(policy) != address(0)) {
            if (!policy.allowsTutorWage(scope.lessonId, scope.tutor)) return false;
            if (
                scope.absence == SparkV15SettlementAlternatives.AbsenceReason.Unverified
                    && !policy.mayPaySettledTutorDeductions(scope.lessonId, scope.tutor)
            ) {
                return false;
            }
        }
        return ALTERNATIVES.feeConditionsPermitWage(scope.lessonId, scope.formId, scope.independent, scope.absence);
    }

    function _compileGroup(
        bytes32 lessonId,
        GroupAssessment calldata assessment,
        address approver,
        LocalApproval memory local
    ) private view returns (CompiledGroup memory compiled) {
        if (finalSettlementBasis[lessonId] != bytes32(0)) revert InvalidGroupProposal();
        return COMPILATION.compileGroup(lessonId, assessment, approver, local);
    }
}
