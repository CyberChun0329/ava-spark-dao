// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {IERC20} from "../legacy/interfaces/IERC20.sol";
import {ISparkV15BookingChanges, SparkV15Booking, SparkV15BookingOpening} from "./SparkV15Booking.sol";
import {SparkV15BookingChanges} from "./SparkV15BookingChanges.sol";
import {SparkV15Payments} from "./SparkV15Payments.sol";
import {SparkV15ReviewCases, SparkV15ReviewContext} from "./SparkV15ReviewCases.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";

interface ISparkV15TutorCompletions {
    function getTutorCompletedLessons(address tutor) external view returns (bytes32[] memory);
}

/// @notice The per-place redress and tutor-pay consequences of recognised v1.5 lesson findings.
contract SparkV15LessonRemedies {
    enum FaultKind {
        Unrecorded,
        MissedAgreedTeaching,
        SeriousTeachingIncident,
        ProviderArrangementError,
        ProviderNoticeError,
        ProviderAdministrationError,
        NoFault
    }

    enum TeachingReceived {
        Unverified,
        NoneDelivered,
        PartiallyDelivered,
        FullyDelivered
    }

    enum Participation {
        Unverified,
        DidNotAttendOrPrepare,
        AttendedAsAgreed,
        ReadyAsAgreed
    }

    struct AffectedPlace {
        bytes32 formId;
        TeachingReceived teaching;
        Participation participation;
        uint128 lostServiceFee;
        bool missedAgreedTeaching;
        bytes32 evidenceRef;
    }

    struct FaultFinding {
        FaultKind kind;
        bool entireClass;
        address responsibleTutor;
        bytes32 tutorAgreementRef;
        uint64 originalOccurredAt;
        bytes32 groundRef;
        bytes32 tutorInquiryRef;
        bytes32 tutorResponseOpportunityRef;
        bytes32 affectedStudentsInquiryRef;
        AffectedPlace[] affected;
    }

    struct FaultRecord {
        bytes32 lessonId;
        address tutor;
        FaultKind kind;
        bytes32 outcome;
        uint128 originalNormalTutorPay;
        uint128 originalDeduction;
        uint128 originalTutorPay;
        uint64 originalLessonAt;
        uint64 decidedAt;
        uint64 recordedAt;
        uint256 caseEvidenceId;
        uint256 adoptionEvidenceId;
        address decidedBy;
    }

    struct EarlierCompletion {
        bytes32 lessonId;
        uint128 otherwisePayable;
        bytes32 classificationRef;
    }

    struct DeductionShare {
        bytes32 originalLessonId;
        uint128 applied;
        bytes32 shortfallTerms;
    }

    struct TutorPayHistoryInput {
        bytes32 lessonId;
        address tutor;
        bool completed;
        uint128 payableBefore;
        bytes32 historyScopeRef;
        EarlierCompletion[] earlier;
        DeductionShare[] shares;
    }

    struct TutorPayCheck {
        address tutor;
        uint64 occurrenceAt;
        bool completed;
        uint128 payableBefore;
        uint128 payableAfter;
        bytes32 inventory;
        uint256 faultVersion;
        uint256 evidenceId;
        address verifier;
        bytes32 authorityId;
    }

    struct TutorDeduction {
        bytes32 originalLessonId;
        bytes32 nextLessonId;
        uint128 payableBefore;
        uint128 fixedAmount;
        uint128 applied;
        uint128 unapplied;
        bytes32 shortfallTerms;
        uint64 assessedAt;
        uint256 historyEvidenceId;
    }

    bytes32 public constant ACTION_RECORD_UNDISPUTED_PROVIDER_FAULT =
        keccak256("spark.action.record-undisputed-provider-fault.v1.5");
    bytes32 public constant ACTION_VERIFY_TUTOR_PAY_HISTORY = keccak256("spark.action.verify-tutor-pay-history.v1.5");

    error InvalidInstallation();
    error InvalidFault();
    error InvalidEvidence();
    error InvalidTutorPayHistory();
    error UnrepresentableAmount();

    event LessonFaultRecorded(
        bytes32 indexed caseId, uint256 indexed revision, bytes32 indexed lessonId, FaultKind kind, bytes32 outcome
    );
    event TutorPayHistoryVerified(
        bytes32 indexed lessonId, address indexed tutor, uint256 evidenceId, uint128 payableAfter
    );
    event NextTutorDeducted(
        bytes32 indexed originalLessonId,
        bytes32 indexed nextLessonId,
        address indexed tutor,
        uint128 applied,
        uint128 unapplied
    );

    SparkV15Booking public immutable BOOKING;
    SparkV15Payments public immutable PAYMENTS;
    SparkV15ReviewCases public immutable CASES;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;
    bytes32 private immutable EVIDENCE_ROLE;
    SparkV15CustomerRedress public customerRedress;

    mapping(bytes32 => uint256) public latestFaultRevision;
    mapping(bytes32 => mapping(uint256 => FaultRecord)) private faults;
    mapping(bytes32 => mapping(uint256 => bytes32[])) private faultForms;
    mapping(bytes32 => mapping(uint256 => mapping(bytes32 => AffectedPlace))) private placeFacts;
    mapping(bytes32 => mapping(address => uint256)) private activeOriginalTutorFaults;
    mapping(bytes32 => bytes32) public placeFaultCase;
    mapping(bytes32 => bytes32[]) private lessonCases;
    mapping(address => bytes32[]) private tutorOriginalLessons;
    mapping(address => mapping(bytes32 => bool)) private knownOriginalLessons;
    mapping(address => uint256) private tutorFaultVersion;
    mapping(bytes32 => TutorPayCheck[]) private tutorPayChecks;
    mapping(bytes32 => mapping(uint256 => TutorDeduction[])) private proposedDeductions;
    mapping(address => mapping(bytes32 => TutorDeduction)) private tutorDeductions;
    mapping(bytes32 => uint256) private appliedTutorCheck;

    constructor(SparkV15Booking booking, SparkV15Payments payments, SparkV15ReviewCases cases, bytes32 evidenceRole) {
        if (
            address(booking).code.length == 0 || address(payments).code.length == 0 || address(cases).code.length == 0
                || evidenceRole == bytes32(0)
                || address(booking.REQUEST_ALLOCATION()) != address(payments.REQUEST_ALLOCATION())
                || address(booking.FUNDS()) != address(payments.FUNDS()) || booking.WORKFLOW() != payments.WORKFLOW()
        ) revert InvalidInstallation();
        BOOKING = booking;
        PAYMENTS = payments;
        CASES = cases;
        EVIDENCE_REGISTRY = payments.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        EVIDENCE_ROLE = evidenceRole;
    }

    function bindCustomerRedress(SparkV15CustomerRedress source) external {
        PAYMENTS.REQUEST_ALLOCATION().IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
        if (address(customerRedress) != address(0) || address(source.REMEDIES()) != address(this)) {
            revert InvalidInstallation();
        }
        customerRedress = source;
    }

    function mayPayRedressPart(bytes32 obligationId) external view returns (bool) {
        return address(customerRedress) == address(0) || customerRedress.mayPayRedressPart(obligationId);
    }

    function getLessonCases(bytes32 lessonId) external view returns (bytes32[] memory) {
        return lessonCases[lessonId];
    }

    function isOperative(bytes32 caseId, uint256 revision) public view returns (bool) {
        if (caseId == bytes32(0) || revision == 0 || latestFaultRevision[caseId] != revision) return false;
        SparkV15ReviewCases.AdoptedDisposition memory adopted = CASES.getAdoptedDisposition(caseId);
        return adopted.adoptedAt == 0 || adopted.outcome == faults[caseId][revision].outcome;
    }

    function faultOutcome(bytes32 caseId, FaultFinding calldata finding) public view returns (bytes32) {
        return
            keccak256(abi.encode(keccak256("spark.v1.5.lesson-fault"), block.chainid, address(this), caseId, finding));
    }

    /// @notice Interpret the typed finding from the existing case history and retain its economic consequence.
    function recordFault(bytes32 caseId, FaultFinding calldata finding) external {
        SparkV15ReviewContext.ConcernContext memory context = CASES.INTAKE().caseContext(caseId);
        SparkV15ReviewContext.PublishedContacts memory publication =
            CASES.INTAKE().getPublishedContacts(context.termsId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(context.lessonId);
        uint256 previous = latestFaultRevision[caseId];
        FaultRecord memory record;
        record.lessonId = context.lessonId;
        record.kind = finding.kind;
        record.outcome = faultOutcome(caseId, finding);
        record.recordedAt = uint64(block.timestamp);

        if (
            lesson.packageId == 0 || publication.packageId != lesson.packageId
                || publication.terms.provider != lesson.terms.provider
                || publication.terms.coordinator != lesson.terms.coordinator || finding.kind == FaultKind.Unrecorded
                || finding.groundRef == bytes32(0) || finding.affected.length == 0
                || (finding.kind == FaultKind.NoFault && previous == 0)
        ) revert InvalidFault();

        _readDecision(caseId, lesson.packageId, previous, record);
        _commitFault(caseId, lesson, publication.terms.governingForm, finding, record);
    }

    function providerFaultCommitment(
        bytes32 governingForm,
        bytes32 matter,
        FaultFinding calldata finding,
        bytes32 verifiedNoDispute,
        address coordinator
    ) public view returns (bytes32) {
        return keccak256(
            abi.encode(
                ACTION_RECORD_UNDISPUTED_PROVIDER_FAULT,
                block.chainid,
                address(this),
                governingForm,
                matter,
                finding,
                verifiedNoDispute,
                coordinator
            )
        );
    }

    /// @notice The coordinator records independently verified provider fault for an undisputed matter.
    function recordUndisputedProviderFault(
        bytes32 governingForm,
        bytes32 matter,
        FaultFinding calldata finding,
        bytes32 verifiedNoDispute,
        uint256 evidenceId
    ) external returns (bytes32 caseId) {
        SparkV15Booking.Form memory form = BOOKING.getForm(governingForm);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        caseId = CASES.caseIdFor(form.lessonId, matter);
        if (
            msg.sender != lesson.terms.coordinator || lesson.packageId == 0 || matter == bytes32(0)
                || verifiedNoDispute == bytes32(0) || latestFaultRevision[caseId] != 0
                || finding.kind < FaultKind.ProviderArrangementError
                || finding.kind > FaultKind.ProviderAdministrationError || finding.groundRef == bytes32(0)
                || finding.affected.length == 0 || CASES.INTAKE().caseContext(caseId).evidenceId != 0
                || CASES.getCase(caseId).initial.evidenceId != 0
        ) revert InvalidFault();
        EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                msg.sender, SparkV15.APP_ID, BOOKING.COORDINATOR_ROLE(), ACTION_RECORD_UNDISPUTED_PROVIDER_FAULT
            );
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, lesson.packageId);
        AVAEvidenceRegistry.EvidenceReference memory proof = EVIDENCE_REGISTRY.getEvidenceReference(evidenceId);
        if (
            proof.commitment != providerFaultCommitment(governingForm, matter, finding, verifiedNoDispute, msg.sender)
                || EVIDENCE_REGISTRY.IDENTITY_REGISTRY().getSubjectContext(proof.authorityId).roleKey != EVIDENCE_ROLE
        ) revert InvalidEvidence();
        FaultRecord memory record;
        record.lessonId = form.lessonId;
        record.kind = finding.kind;
        record.outcome = faultOutcome(caseId, finding);
        record.decidedAt = uint64(block.timestamp);
        record.recordedAt = record.decidedAt;
        record.caseEvidenceId = evidenceId;
        record.decidedBy = msg.sender;
        _commitFault(caseId, lesson, governingForm, finding, record);
    }

    function _commitFault(
        bytes32 caseId,
        SparkV15Booking.Lesson memory lesson,
        bytes32 governingForm,
        FaultFinding calldata finding,
        FaultRecord memory record
    ) private {
        uint256 previous = latestFaultRevision[caseId];
        uint256 revision = previous + 1;
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(record.lessonId);
        ISparkV15BookingChanges.Arrangement memory arrangement = BOOKING.getEffectiveArrangement(
            record.lessonId, teaching.startedAt == 0 ? record.decidedAt : teaching.startedAt
        );
        record.tutor = arrangement.tutor;
        record.originalNormalTutorPay = arrangement.tutorFee;
        record.originalLessonAt = teaching.endedAt == 0 ? arrangement.startsAt : teaching.endedAt;
        if (teaching.endedAt != 0) {
            BOOKING.OPENING().requireTeachingEndEvidence(record.lessonId, teaching.endEvidenceId, lesson.packageId);
        }
        if (record.originalLessonAt > record.decidedAt) revert InvalidFault();
        if (_isTutorFault(finding.kind)) {
            if (
                finding.responsibleTutor != arrangement.tutor
                    || finding.tutorAgreementRef != arrangement.tutorAgreementRef
                    || finding.originalOccurredAt != record.originalLessonAt || finding.tutorInquiryRef == bytes32(0)
                    || finding.tutorResponseOpportunityRef == bytes32(0)
                    || finding.affectedStudentsInquiryRef == bytes32(0)
                    || (arrangement.changeId == bytes32(0)
                        && (BOOKING.teachingAgreementSignedAt(record.lessonId, arrangement.tutor) == 0
                            || BOOKING.teachingAgreementSignedAt(record.lessonId, lesson.terms.provider) == 0))
            ) revert InvalidFault();
            record.originalDeduction = record.originalNormalTutorPay;
            ++activeOriginalTutorFaults[record.lessonId][record.tutor];
            if (!knownOriginalLessons[record.tutor][record.lessonId]) {
                knownOriginalLessons[record.tutor][record.lessonId] = true;
                tutorOriginalLessons[record.tutor].push(record.lessonId);
            }
            ++tutorFaultVersion[record.tutor];
        }
        FaultRecord storage prior = faults[caseId][previous];
        if (_isTutorFault(prior.kind)) {
            --activeOriginalTutorFaults[record.lessonId][prior.tutor];
            if (!_isTutorFault(finding.kind) || prior.tutor != record.tutor) ++tutorFaultVersion[prior.tutor];
        }
        _recordAffectedPlaces(caseId, revision, lesson, governingForm, record.decidedAt, finding);

        faults[caseId][revision] = record;
        latestFaultRevision[caseId] = revision;
        if (previous == 0) lessonCases[record.lessonId].push(caseId);
        emit LessonFaultRecorded(caseId, revision, record.lessonId, finding.kind, record.outcome);
    }

    function getFault(bytes32 caseId, uint256 revision) external view returns (FaultRecord memory) {
        return faults[caseId][revision];
    }

    function getFaultForms(bytes32 caseId, uint256 revision) external view returns (bytes32[] memory) {
        return faultForms[caseId][revision];
    }

    function getPlaceFinding(bytes32 caseId, uint256 revision, bytes32 formId)
        external
        view
        returns (AffectedPlace memory)
    {
        return placeFacts[caseId][revision][formId];
    }

    /// @notice Read current original-lesson tutor pay eligibility. Existing receipts are unaffected by a later finding.
    function allowsTutorWage(bytes32 lessonId, address tutor) external view returns (bool) {
        return activeOriginalTutorFaults[lessonId][tutor] == 0;
    }

    function tutorPayHistoryCommitment(TutorPayHistoryInput calldata history, address verifier)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                ACTION_VERIFY_TUTOR_PAY_HISTORY,
                block.chainid,
                address(this),
                history,
                tutorFaultVersion[history.tutor],
                verifier
            )
        );
    }

    /// @notice Verify the effective tutor and the complete payable classification of earlier actual completions.
    function verifyTutorPayHistory(TutorPayHistoryInput calldata history, uint256 evidenceId, bytes32 authorityId)
        external
    {
        bytes32 role =
            EVIDENCE_REGISTRY.IDENTITY_REGISTRY().requireActiveSubjectContext(authorityId, SparkV15.APP_ID).roleKey;
        EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(msg.sender, SparkV15.APP_ID, role, ACTION_VERIFY_TUTOR_PAY_HISTORY, authorityId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(history.lessonId);
        (uint64 occurrenceAt, bool completed, address actualTutor) = _tutorOccurrence(history.lessonId);
        if (
            lesson.packageId == 0 || actualTutor != history.tutor || history.completed != completed
                || history.historyScopeRef == bytes32(0) || history.payableBefore == 0 || occurrenceAt > block.timestamp
                || activeOriginalTutorFaults[history.lessonId][history.tutor] != 0
        ) revert InvalidTutorPayHistory();
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, lesson.packageId);
        AVAEvidenceRegistry.EvidenceReference memory proof = EVIDENCE_REGISTRY.getEvidenceReference(evidenceId);
        if (
            proof.commitment != tutorPayHistoryCommitment(history, msg.sender)
                || EVIDENCE_REGISTRY.IDENTITY_REGISTRY().getSubjectContext(proof.authorityId).roleKey != EVIDENCE_ROLE
        ) revert InvalidEvidence();
        uint64 earliest = _earliestOriginal(history.lessonId, history.tutor, occurrenceAt);
        if (earliest == 0) revert InvalidTutorPayHistory();
        (bytes32 inventory, uint256 known) =
            _completionInventory(history.lessonId, history.tutor, earliest, occurrenceAt);
        if (known != history.earlier.length) revert InvalidTutorPayHistory();
        uint64 last = earliest;
        for (uint256 i; i < known; ++i) {
            EarlierCompletion calldata earlier = history.earlier[i];
            (uint64 completedAt, bool verifiedCompleted, address earlierTutor) = _tutorOccurrence(earlier.lessonId);
            if (
                !verifiedCompleted || earlierTutor != history.tutor || completedAt <= last
                    || completedAt >= occurrenceAt || earlier.classificationRef == bytes32(0)
            ) revert InvalidTutorPayHistory();
            last = completedAt;
        }
        uint256 revision = tutorPayChecks[history.lessonId].length + 1;
        uint128 net = _verifyDeductionShares(history, occurrenceAt, evidenceId, revision);
        tutorPayChecks[history.lessonId].push(
            TutorPayCheck({
                tutor: history.tutor,
                occurrenceAt: occurrenceAt,
                completed: completed,
                payableBefore: history.payableBefore,
                payableAfter: net,
                inventory: inventory,
                faultVersion: tutorFaultVersion[history.tutor],
                evidenceId: evidenceId,
                verifier: msg.sender,
                authorityId: authorityId
            })
        );
        emit TutorPayHistoryVerified(history.lessonId, history.tutor, evidenceId, net);
    }

    function previewTutorDeductions(bytes32 lessonId, address tutor, uint128 payableBefore)
        public
        view
        returns (uint128)
    {
        (uint128 net,) = _tutorDeductions(lessonId, tutor, payableBefore);
        return net;
    }

    /// @notice Apply each verified deduction once when settling the later lesson.
    function recordTutorDeductions(bytes32 lessonId, address tutor, uint128 payableBefore)
        external
        returns (uint128 net)
    {
        PAYMENTS.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                msg.sender, SparkV15.APP_ID, PAYMENTS.settlementRole(), PAYMENTS.ACTION_RECORD_SETTLEMENT_OBLIGATION()
            );
        uint256 revision;
        (net, revision) = _tutorDeductions(lessonId, tutor, payableBefore);
        if (revision == 0) return net;
        uint256 applied = appliedTutorCheck[lessonId];
        if (applied == revision) return net;
        if (applied != 0) revert InvalidTutorPayHistory();
        appliedTutorCheck[lessonId] = revision;
        TutorDeduction[] storage rows = proposedDeductions[lessonId][revision];
        for (uint256 i; i < rows.length; ++i) {
            TutorDeduction memory row = rows[i];
            if (tutorDeductions[tutor][row.originalLessonId].nextLessonId != bytes32(0)) {
                revert InvalidTutorPayHistory();
            }
            row.assessedAt = uint64(block.timestamp);
            tutorDeductions[tutor][row.originalLessonId] = row;
            emit NextTutorDeducted(row.originalLessonId, lessonId, tutor, row.applied, row.unapplied);
        }
    }

    // A zero revision leaves the deduction ledger untouched.
    function _tutorDeductions(bytes32 lessonId, address tutor, uint128 payableBefore)
        private
        view
        returns (uint128 net, uint256 revision)
    {
        if (activeOriginalTutorFaults[lessonId][tutor] != 0) return (0, 0);
        bool needsCheck;
        (revision, needsCheck) = _currentTutorCheck(lessonId, tutor);
        if (!needsCheck || payableBefore == 0) return (payableBefore, 0);
        if (revision == 0) revert InvalidTutorPayHistory();
        TutorPayCheck storage check = tutorPayChecks[lessonId][revision - 1];
        if (check.payableBefore != payableBefore) revert InvalidTutorPayHistory();
        return (check.payableAfter, revision);
    }

    function mayPaySettledTutorDeductions(bytes32 lessonId, address tutor) external view returns (bool) {
        (uint256 revision, bool needsCheck) = _currentTutorCheck(lessonId, tutor);
        return !needsCheck || (revision != 0 && appliedTutorCheck[lessonId] == revision);
    }

    function getTutorDeduction(address tutor, bytes32 originalLessonId) external view returns (TutorDeduction memory) {
        return tutorDeductions[tutor][originalLessonId];
    }

    function faultFee(bytes32 formId) external view returns (bool applicable, uint128 finalFee) {
        bytes32 caseId = placeFaultCase[formId];
        uint256 revision = latestFaultRevision[caseId];
        FaultKind kind = faults[caseId][revision].kind;
        AffectedPlace storage finding = placeFacts[caseId][revision][formId];
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        if (!_isTutorFault(kind) || !_eligible(form, finding)) return (false, 0);
        if (finding.teaching == TeachingReceived.NoneDelivered) return (true, 0);
        if (form.terms.normalFee % 2 != 0) revert UnrepresentableAmount();
        uint128 benefit = form.terms.normalFee / 2;
        return (true, form.terms.payableFee > benefit ? form.terms.payableFee - benefit : 0);
    }

    function _tutorOccurrence(bytes32 lessonId)
        private
        view
        returns (uint64 occurrenceAt, bool completed, address tutor)
    {
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        ISparkV15BookingChanges.Arrangement memory arrangement = BOOKING.getEffectiveArrangement(
            lessonId, teaching.startedAt == 0 ? uint64(block.timestamp) : teaching.startedAt
        );
        tutor = arrangement.tutor;
        occurrenceAt = teaching.endedAt == 0 ? arrangement.startsAt : teaching.endedAt;
        completed = teaching.endedAt != 0 && BOOKING.getTutorDelivery(lessonId).completed;
    }

    function _currentTutorCheck(bytes32 lessonId, address tutor)
        private
        view
        returns (uint256 revision, bool needsCheck)
    {
        if (tutorOriginalLessons[tutor].length == 0) return (0, false);
        (uint64 occurrenceAt, bool completed, address actualTutor) = _tutorOccurrence(lessonId);
        if (actualTutor != tutor) return (0, false);
        uint64 earliest = _earliestOriginal(lessonId, tutor, occurrenceAt);
        if (earliest == 0) return (0, false);
        TutorPayCheck[] storage checks = tutorPayChecks[lessonId];
        if (checks.length == 0) return (0, true);
        TutorPayCheck storage check = checks[checks.length - 1];
        if (
            check.tutor != tutor || check.occurrenceAt != occurrenceAt || check.completed != completed
                || check.faultVersion != tutorFaultVersion[tutor]
                || !EVIDENCE_REGISTRY.isEvidenceAvailableForPackage(
                    check.evidenceId, BOOKING.getLesson(lessonId).packageId
                )
        ) {
            return (0, true);
        }
        (bytes32 inventory,) = _completionInventory(lessonId, tutor, earliest, occurrenceAt);
        return inventory == check.inventory ? (checks.length, true) : (0, true);
    }

    function _earliestOriginal(bytes32 lessonId, address tutor, uint64 occurrenceAt)
        private
        view
        returns (uint64 earliest)
    {
        bytes32[] storage originals = tutorOriginalLessons[tutor];
        for (uint256 i; i < originals.length; ++i) {
            bytes32 originalLessonId = originals[i];
            if (originalLessonId == lessonId || activeOriginalTutorFaults[originalLessonId][tutor] == 0) continue;
            FaultRecord storage fault = _originalTutorFault(originalLessonId, tutor);
            if (fault.originalLessonAt == occurrenceAt) revert InvalidTutorPayHistory();
            if (fault.originalLessonAt < occurrenceAt && (earliest == 0 || fault.originalLessonAt < earliest)) {
                earliest = fault.originalLessonAt;
            }
        }
    }

    function _originalTutorFault(bytes32 lessonId, address tutor) private view returns (FaultRecord storage original) {
        bytes32[] storage cases = lessonCases[lessonId];
        bytes32 selected;
        for (uint256 i; i < cases.length; ++i) {
            uint256 revision = latestFaultRevision[cases[i]];
            FaultRecord storage item = faults[cases[i]][revision];
            if (!_isTutorFault(item.kind) || item.tutor != tutor) continue;
            if (!isOperative(cases[i], revision)) revert InvalidTutorPayHistory();
            if (selected == bytes32(0)) {
                selected = cases[i];
            } else {
                FaultRecord storage prior = faults[selected][latestFaultRevision[selected]];
                if (
                    item.originalLessonAt != prior.originalLessonAt
                        || item.originalNormalTutorPay != prior.originalNormalTutorPay
                ) {
                    revert InvalidTutorPayHistory();
                }
            }
        }
        if (selected == bytes32(0)) revert InvalidTutorPayHistory();
        return faults[selected][latestFaultRevision[selected]];
    }

    function _completionInventory(bytes32 candidate, address tutor, uint64 afterOriginal, uint64 beforeCandidate)
        private
        view
        returns (bytes32 inventory, uint256 count)
    {
        bytes32[] memory known = ISparkV15TutorCompletions(address(BOOKING)).getTutorCompletedLessons(tutor);
        for (uint256 i; i < known.length; ++i) {
            bytes32 lessonId = known[i];
            if (lessonId == candidate) continue;
            SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
            if (teaching.endedAt <= afterOriginal || teaching.endedAt > beforeCandidate) continue;
            if (teaching.endedAt == beforeCandidate) revert InvalidTutorPayHistory();
            SparkV15Booking.TutorDelivery memory delivery = BOOKING.getTutorDelivery(lessonId);
            inventory = keccak256(
                abi.encode(inventory, lessonId, teaching.endedAt, teaching.endEvidenceId, delivery.evidenceId)
            );
            ++count;
        }
    }

    function _verifyDeductionShares(
        TutorPayHistoryInput calldata input,
        uint64 occurrenceAt,
        uint256 evidenceId,
        uint256 revision
    ) private returns (uint128) {
        if (!input.completed) {
            if (input.shares.length != 0) revert InvalidTutorPayHistory();
            return input.payableBefore;
        }
        bytes32[] storage originals = tutorOriginalLessons[input.tutor];
        uint256 found;
        uint256 totalFixed;
        uint256 totalApplied;
        for (uint256 i; i < originals.length; ++i) {
            bytes32 originalLessonId = originals[i];
            if (originalLessonId == input.lessonId || activeOriginalTutorFaults[originalLessonId][input.tutor] == 0) {
                continue;
            }
            FaultRecord storage fault = _originalTutorFault(originalLessonId, input.tutor);
            if (fault.originalLessonAt >= occurrenceAt || _earlierPayable(input.earlier, fault.originalLessonAt)) {
                continue;
            }
            if (fault.originalNormalTutorPay % 2 != 0) revert UnrepresentableAmount();
            uint128 fixedAmount = fault.originalNormalTutorPay / 2;
            DeductionShare calldata share = _shareFor(input.shares, originalLessonId);
            uint128 applied = share.applied;
            if (applied > fixedAmount || (applied < fixedAmount && share.shortfallTerms == bytes32(0))) {
                revert InvalidTutorPayHistory();
            }
            proposedDeductions[input.lessonId][revision].push(
                TutorDeduction({
                    originalLessonId: originalLessonId,
                    nextLessonId: input.lessonId,
                    payableBefore: input.payableBefore,
                    fixedAmount: fixedAmount,
                    applied: applied,
                    unapplied: fixedAmount - applied,
                    shortfallTerms: share.shortfallTerms,
                    assessedAt: 0,
                    historyEvidenceId: evidenceId
                })
            );
            totalFixed += fixedAmount;
            totalApplied += applied;
            ++found;
        }
        uint256 due = totalFixed < input.payableBefore ? totalFixed : input.payableBefore;
        if (found != input.shares.length || totalApplied != due) revert InvalidTutorPayHistory();
        return input.payableBefore - uint128(totalApplied);
    }

    function _earlierPayable(EarlierCompletion[] calldata earlier, uint64 afterOriginal) private view returns (bool) {
        for (uint256 i; i < earlier.length; ++i) {
            uint64 completedAt = BOOKING.getTeaching(earlier[i].lessonId).endedAt;
            if (completedAt == afterOriginal) revert InvalidTutorPayHistory();
            if (earlier[i].otherwisePayable != 0 && completedAt > afterOriginal) return true;
        }
        return false;
    }

    function _shareFor(DeductionShare[] calldata shares, bytes32 originalLessonId)
        private
        pure
        returns (DeductionShare calldata)
    {
        for (uint256 i; i < shares.length; ++i) {
            if (shares[i].originalLessonId == originalLessonId) return shares[i];
        }
        revert InvalidTutorPayHistory();
    }

    function _readDecision(bytes32 caseId, uint256 packageId, uint256 previous, FaultRecord memory record)
        private
        view
    {
        SparkV15ReviewContext.CaseRecord memory decision = CASES.getCase(caseId);
        SparkV15ReviewCases.AdoptedDisposition memory adopted = CASES.getAdoptedDisposition(caseId);
        if (adopted.adoptedAt != 0) {
            if (
                adopted.outcome != record.outcome || adopted.lessonId != record.lessonId
                    || (previous != 0 && adopted.originalOutcome != faults[caseId][previous].outcome)
            ) revert InvalidFault();
            record.caseEvidenceId = adopted.reviewEvidenceId;
            record.adoptionEvidenceId = adopted.adoptionEvidenceId;
            record.decidedAt = adopted.reviewedAt;
            record.decidedBy = decision.review.reviewer;
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(adopted.adoptionEvidenceId, packageId);
        } else {
            if (
                previous != 0 || decision.review.decidedAt != 0
                    || decision.initial.input.issue != SparkV15ReviewContext.DisputedFinding.Fault
                    || decision.initial.input.outcome != record.outcome || decision.original.outcome != record.outcome
                    || decision.initial.decider != decision.original.decider
                    || decision.initial.decidedAt != decision.original.decidedAt
            ) revert InvalidFault();
            record.caseEvidenceId = decision.initial.evidenceId;
            record.decidedAt = decision.initial.decidedAt;
            record.decidedBy = decision.initial.decider;
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(decision.original.evidenceId, packageId);
        }
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(record.caseEvidenceId, packageId);
    }

    function _recordAffectedPlaces(
        bytes32 caseId,
        uint256 revision,
        SparkV15Booking.Lesson memory lesson,
        bytes32 governingForm,
        uint64 decidedAt,
        FaultFinding calldata finding
    ) private {
        bytes32[] memory roster = lesson.terms.rosterLockAt == 0
            ? BOOKING.getPlannedForms(lesson.terms.lessonId)
            : BOOKING.getLockedForms(lesson.terms.lessonId);
        if (finding.entireClass) {
            uint256 effectivePlaces;
            for (uint256 i; i < roster.length; ++i) {
                if (
                    BOOKING.getForm(roster[i]).confirmation.confirmedAt != 0
                        && !BOOKING.isCancelledAt(roster[i], decidedAt)
                ) {
                    ++effectivePlaces;
                }
            }
            if (finding.affected.length != effectivePlaces) revert InvalidFault();
        }
        if (revision > 1) {
            bytes32[] storage previous = faultForms[caseId][revision - 1];
            for (uint256 i; i < previous.length; ++i) {
                delete placeFaultCase[previous[i]];
            }
        }
        bool coversGoverningForm;
        for (uint256 i; i < finding.affected.length; ++i) {
            AffectedPlace calldata item = finding.affected[i];
            SparkV15Booking.Form memory form = BOOKING.getForm(item.formId);
            if (
                form.lessonId != lesson.terms.lessonId || form.confirmation.confirmedAt == 0
                    || !_inRoster(roster, item.formId) || placeFaultCase[item.formId] != bytes32(0)
                    || item.evidenceRef == bytes32(0) || item.teaching == TeachingReceived.Unverified
                    || placeFacts[caseId][revision][item.formId].evidenceRef != bytes32(0)
                    || item.lostServiceFee > form.terms.payableFee || BOOKING.isCancelledAt(item.formId, decidedAt)
            ) revert InvalidFault();
            if (item.formId == governingForm) coversGoverningForm = true;
            faultForms[caseId][revision].push(item.formId);
            placeFacts[caseId][revision][item.formId] = item;
            placeFaultCase[item.formId] = caseId;
            if (finding.kind == FaultKind.NoFault) delete placeFaultCase[item.formId];
        }
        if (!coversGoverningForm) revert InvalidFault();
    }

    function _inRoster(bytes32[] memory roster, bytes32 formId) private pure returns (bool) {
        for (uint256 i; i < roster.length; ++i) {
            if (roster[i] == formId) return true;
        }
        return false;
    }

    function _isTutorFault(FaultKind kind) private pure returns (bool) {
        return kind == FaultKind.MissedAgreedTeaching || kind == FaultKind.SeriousTeachingIncident;
    }

    function _eligible(SparkV15Booking.Form memory form, AffectedPlace storage finding) private view returns (bool) {
        return form.confirmation.debitedUnits == form.terms.payableFee
            && (finding.participation == Participation.AttendedAsAgreed
                || finding.participation == Participation.ReadyAsAgreed);
    }
}

/// @notice The customer's choices, usable course credit and refund claims against the original debit.
contract SparkV15CustomerRedress {
    struct RedressTerms {
        uint64 acceptThrough;
        uint64 deliverThrough;
        uint64 refundDuePeriod;
        uint64 refundExecutionPeriod;
        uint64 earlierLegalExecutionPeriod;
        uint64 postLiftPeriod;
        bytes32 coveredService;
        bytes32 agreementRef;
    }

    struct RedressRecord {
        bytes32 caseId;
        uint256 faultRevision;
        address acceptedBy;
        uint64 acceptedAt;
        uint64 creditIssuedAt;
        uint64 directRefundAt;
        uint64 unableAt;
        uint64 closedAt;
        address refundRequestedBy;
        bytes32 remedialLinkId;
        uint64 remedialDeliveryAt;
        uint256 refundSwitchEvidence;
        uint128 unusedCreditRemoved;
    }

    enum RefundBasis {
        OriginalRelief,
        DirectRequest,
        NoRemedyAgreed,
        FailedRemedy
    }

    struct RefundAssessment {
        RefundBasis cause;
        bytes32 caseId;
        uint256 faultRevision;
        uint64 triggerAt;
        uint64 assessedAt;
        uint128 finalFee;
        uint128 grossCreditRestoration;
        uint128 principal;
        bytes32 basis;
        address verifier;
        uint256 evidenceId;
        bytes32 obligationId;
    }

    bytes32 public constant ACTION_ASSESS_REFUND = keccak256("spark.action.assess-fault-refund.v1.5");

    error InvalidEvidence();
    error InvalidCustomerChoice();
    error InvalidRefund();
    error UnrepresentableAmount();

    event RedressTermsPublished(bytes32 indexed formId, uint256 indexed evidenceId);
    event StandardCompensationAccepted(bytes32 indexed formId, address indexed customerActor, uint64 acceptedAt);
    event RemedialTeachingAccepted(bytes32 indexed formId, bytes32 indexed linkId, address indexed customerActor);
    event RemedialTeachingDelivered(bytes32 indexed formId, bytes32 indexed linkId, uint64 deliveredAt);
    event CompensationCreditIssued(bytes32 indexed formId, bytes32 indexed account, uint128 amount, uint64 availableAt);
    event DirectRefundRequested(bytes32 indexed formId, address indexed customerActor, uint64 receivedAt);
    event RefundAssessed(bytes32 indexed formId, uint256 indexed index, uint128 principal, uint64 triggerAt);
    event RefundPaymentEstablished(bytes32 indexed formId, uint256 indexed index, bytes32 indexed obligationId);
    event FullRefundClosed(bytes32 indexed formId, uint64 closedAt);
    SparkV15LessonRemedies public immutable REMEDIES;
    SparkV15Booking public immutable BOOKING;
    SparkV15Payments public immutable PAYMENTS;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;
    bytes32 private immutable EVIDENCE_ROLE;
    SparkV15RemedyBookings public remedyBookings;

    mapping(bytes32 => RedressTerms) private redressTerms;
    mapping(bytes32 => RedressRecord) private redress;
    mapping(bytes32 => uint256) public redressTermsEvidence;
    mapping(bytes32 => RefundAssessment[]) private refunds;
    mapping(bytes32 => mapping(bytes32 => bool)) private refundScenarios;
    mapping(bytes32 => bytes32) private refundForms;
    mapping(bytes32 => uint256) private refundIndices;

    constructor(SparkV15LessonRemedies remedies, bytes32 evidenceRole) {
        if (address(remedies).code.length == 0 || evidenceRole == bytes32(0)) revert InvalidEvidence();
        REMEDIES = remedies;
        BOOKING = remedies.BOOKING();
        PAYMENTS = remedies.PAYMENTS();
        EVIDENCE_REGISTRY = PAYMENTS.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        EVIDENCE_ROLE = evidenceRole;
    }

    function bindRemedyBookings(SparkV15RemedyBookings source) external {
        PAYMENTS.REQUEST_ALLOCATION().IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
        if (address(remedyBookings) != address(0) || address(source.REDRESS()) != address(this)) {
            revert InvalidCustomerChoice();
        }
        remedyBookings = source;
    }

    function redressTermsCommitment(bytes32 formId, RedressTerms calldata terms) public view returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.redress-terms"), block.chainid, address(this), formId, terms));
    }

    /// @notice Retain the redress terms evidenced as part of the governing course form.
    function publishRedressTerms(bytes32 formId, RedressTerms calldata terms, uint256 evidenceId) external {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        if (
            msg.sender != lesson.terms.provider || lesson.packageId == 0 || redressTermsEvidence[formId] != 0
                || terms.agreementRef != lesson.terms.documentsRef || terms.coveredService == bytes32(0)
                || terms.acceptThrough < lesson.terms.startsAt || terms.deliverThrough < terms.acceptThrough
                || terms.refundDuePeriod > terms.refundExecutionPeriod || terms.refundExecutionPeriod == 0
        ) revert InvalidCustomerChoice();
        _requireEvidence(evidenceId, lesson.packageId, redressTermsCommitment(formId, terms));
        redressTerms[formId] = terms;
        redressTermsEvidence[formId] = evidenceId;
        emit RedressTermsPublished(formId, evidenceId);
    }

    function getRedressTerms(bytes32 formId) external view returns (RedressTerms memory) {
        return redressTerms[formId];
    }

    function getRedress(bytes32 formId) external view returns (RedressRecord memory) {
        return redress[formId];
    }

    function deliveryDeadline(bytes32 formId) public view returns (uint64) {
        if (address(remedyBookings) != address(0)) {
            uint64 extended = remedyBookings.extendedDeadline(formId);
            if (extended != 0) return extended;
        }
        return redressTerms[formId].deliverThrough;
    }

    function remedyOutstanding(bytes32 formId) external view returns (bool) {
        RedressRecord storage item = redress[formId];
        return item.acceptedAt != 0 && item.unableAt == 0 && item.directRefundAt == 0 && item.closedAt == 0
            && !_remedyDelivered(formId, item);
    }

    /// @notice The contracting customer or their authorised representative independently accepts compensation.
    function acceptStandardCompensation(bytes32 formId) external {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        _requireCustomer(formId, form);
        bytes32 caseId = REMEDIES.placeFaultCase(formId);
        uint256 revision = REMEDIES.latestFaultRevision(caseId);
        SparkV15LessonRemedies.AffectedPlace memory place = REMEDIES.getPlaceFinding(caseId, revision, formId);
        SparkV15LessonRemedies.FaultKind kind = REMEDIES.getFault(caseId, revision).kind;
        RedressRecord storage item = redress[formId];
        if (
            !REMEDIES.isOperative(caseId, revision) || item.acceptedAt != 0 || item.directRefundAt != 0
                || redressTermsEvidence[formId] == 0 || block.timestamp > redressTerms[formId].acceptThrough
                || (_isTutorFault(kind) ? !_eligible(form, place) : !place.missedAgreedTeaching)
        ) revert InvalidCustomerChoice();
        item.caseId = caseId;
        item.faultRevision = revision;
        item.acceptedBy = msg.sender;
        item.acceptedAt = uint64(block.timestamp);
        emit StandardCompensationAccepted(formId, msg.sender, item.acceptedAt);
    }

    function recordAgreedRemedialTeaching(bytes32 formId, bytes32 linkId, address customerActor) external {
        if (msg.sender != address(remedyBookings)) revert InvalidCustomerChoice();
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        bytes32 caseId = REMEDIES.placeFaultCase(formId);
        uint256 revision = REMEDIES.latestFaultRevision(caseId);
        RedressRecord storage item = redress[formId];
        if (
            !_redressApplies(form, caseId, revision, formId) || item.acceptedAt != 0 || item.directRefundAt != 0
                || redressTermsEvidence[formId] == 0 || block.timestamp > redressTerms[formId].acceptThrough
        ) revert InvalidCustomerChoice();
        item.caseId = caseId;
        item.faultRevision = revision;
        item.acceptedBy = customerActor;
        item.acceptedAt = uint64(block.timestamp);
        item.remedialLinkId = linkId;
        emit RemedialTeachingAccepted(formId, linkId, customerActor);
    }

    function recordRemedialDelivery(bytes32 formId, uint64 deliveredAt) external {
        if (msg.sender != address(remedyBookings)) revert InvalidCustomerChoice();
        RedressRecord storage item = redress[formId];
        if (
            item.remedialLinkId == bytes32(0) || item.remedialDeliveryAt != 0 || item.unableAt != 0
                || item.directRefundAt != 0 || item.closedAt != 0
                || !REMEDIES.isOperative(item.caseId, item.faultRevision)
        ) revert InvalidCustomerChoice();
        if (deliveredAt < item.acceptedAt || deliveredAt > deliveryDeadline(formId)) revert InvalidCustomerChoice();
        item.remedialDeliveryAt = deliveredAt;
        emit RemedialTeachingDelivered(formId, item.remedialLinkId, deliveredAt);
    }

    /// @notice Complete the separately owed course credit only after it posts to the customer's usable balance.
    function issueCourseCredit(bytes32 formId) external {
        RedressRecord storage item = redress[formId];
        if (
            item.acceptedAt == 0 || item.remedialLinkId != bytes32(0) || item.creditIssuedAt != 0 || item.unableAt != 0
                || item.directRefundAt != 0 || item.closedAt != 0 || item.caseId != REMEDIES.placeFaultCase(formId)
                || !REMEDIES.isOperative(item.caseId, item.faultRevision) || block.timestamp > deliveryDeadline(formId)
        ) revert InvalidCustomerChoice();
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        item.creditIssuedAt = uint64(block.timestamp);
        PAYMENTS.FUNDS()
            .grantCompensationCredit(form.lessonId, form.terms.placeId, form.terms.customer, form.terms.normalFee);
        emit CompensationCreditIssued(
            formId, PAYMENTS.FUNDS().creditAccount(form.terms.customer), form.terms.normalFee, item.creditIssuedAt
        );
    }

    function requestDirectRefund(bytes32 formId) external {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        _requireCustomer(formId, form);
        _requestDirectRefund(formId, form, msg.sender, 0);
    }

    function recordRefundSwitch(bytes32 formId, address customerActor, uint256 evidenceId) external {
        if (msg.sender != address(remedyBookings)) revert InvalidCustomerChoice();
        _requestDirectRefund(formId, BOOKING.getForm(formId), customerActor, evidenceId);
    }

    function _requestDirectRefund(
        bytes32 formId,
        SparkV15Booking.Form memory form,
        address customerActor,
        uint256 switchEvidence
    ) private {
        RedressRecord storage item = redress[formId];
        bytes32 caseId = REMEDIES.placeFaultCase(formId);
        uint256 revision = REMEDIES.latestFaultRevision(caseId);
        if (
            !_redressApplies(form, caseId, revision, formId) || redressTermsEvidence[formId] == 0
                || item.directRefundAt != 0 || (item.acceptedAt != 0 && switchEvidence == 0) || item.closedAt != 0
        ) revert InvalidCustomerChoice();
        item.caseId = caseId;
        item.faultRevision = revision;
        item.directRefundAt = uint64(block.timestamp);
        item.refundRequestedBy = customerActor;
        item.refundSwitchEvidence = switchEvidence;
        emit DirectRefundRequested(formId, customerActor, item.directRefundAt);
    }

    function confirmUnableToDeliver(bytes32 formId) external {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        RedressRecord storage item = redress[formId];
        if (
            msg.sender != BOOKING.getLesson(form.lessonId).terms.provider || item.acceptedAt == 0 || item.unableAt != 0
                || item.closedAt != 0 || item.directRefundAt != 0 || _remedyDelivered(formId, item)
        ) revert InvalidCustomerChoice();
        item.unableAt = uint64(block.timestamp);
    }

    /// @notice Preview the refund trigger, the additional principal and its payment terms.
    function previewRefund(bytes32 formId, RefundBasis cause, address verifier)
        external
        view
        returns (RefundAssessment memory item, SparkV15Payments.PaymentTerms memory terms)
    {
        (item, terms,) = _previewRefund(formId, cause, verifier);
    }

    function _previewRefund(bytes32 formId, RefundBasis cause, address verifier)
        private
        view
        returns (RefundAssessment memory item, SparkV15Payments.PaymentTerms memory terms, uint256 packageId)
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        bytes32 caseId = REMEDIES.placeFaultCase(formId);
        uint256 revision = REMEDIES.latestFaultRevision(caseId);
        if (!_redressApplies(form, caseId, revision, formId) || redressTermsEvidence[formId] == 0) {
            revert InvalidRefund();
        }
        item.caseId = caseId;
        item.faultRevision = revision;
        item.cause = cause;
        item.verifier = verifier;
        (item.triggerAt, item.finalFee) = _refundAmounts(formId, form, caseId, revision, cause);
        item.grossCreditRestoration =
            form.confirmation.debitedUnits > item.finalFee ? form.confirmation.debitedUnits - item.finalFee : 0;
        (uint256 priorPrincipal, uint256 priorNetReceived) = _refundTotals(formId, form);
        if (item.grossCreditRestoration > priorPrincipal) {
            item.principal = item.grossCreditRestoration - uint128(priorPrincipal);
        }
        bytes32 scenario = _refundScenario(item);
        if (refundScenarios[formId][scenario]) revert InvalidRefund();
        item.basis = keccak256(
            abi.encode(
                ACTION_ASSESS_REFUND,
                block.chainid,
                address(this),
                formId,
                scenario,
                redressTermsEvidence[formId],
                form.confirmation,
                item.finalFee,
                item.grossCreditRestoration,
                item.principal,
                priorPrincipal,
                priorNetReceived,
                verifier
            )
        );
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        terms = _refundPaymentTerms(formId, form, item, lesson.terms.coordinator);
        packageId = lesson.packageId;
    }

    /// @notice A refund assessment can be retained even when payment backing is unavailable.
    /// @dev The evidence affirms the source facts and any earlier external choices or entitlements, including a
    /// deadline that passed without any remedy being agreed. Contract history checks known native choices as well.
    function assessRefund(bytes32 formId, RefundBasis cause, uint256 evidenceId, bytes32 authorityId)
        external
        returns (uint256 index)
    {
        _requireAuthority(ACTION_ASSESS_REFUND, authorityId);
        (RefundAssessment memory item,, uint256 packageId) = _previewRefund(formId, cause, msg.sender);
        _requireEvidence(evidenceId, packageId, item.basis);
        item.evidenceId = evidenceId;
        item.assessedAt = uint64(block.timestamp);
        refundScenarios[formId][_refundScenario(item)] = true;
        index = refunds[formId].length;
        refunds[formId].push(item);
        emit RefundAssessed(formId, index, item.principal, item.triggerAt);
    }

    function establishRefundPayment(bytes32 formId, uint256 index, uint256 paymentEvidenceId)
        external
        returns (bytes32 obligationId)
    {
        RefundAssessment storage item = refunds[formId][index];
        if (
            item.principal == 0 || item.obligationId != bytes32(0) || REMEDIES.placeFaultCase(formId) != item.caseId
                || !REMEDIES.isOperative(item.caseId, item.faultRevision)
        ) revert InvalidRefund();
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(item.evidenceId, lesson.packageId);
        SparkV15Payments.PaymentTerms memory terms = _refundPaymentTerms(formId, form, item, lesson.terms.coordinator);
        obligationId = PAYMENTS.establishSettledPayment(terms, item.basis, paymentEvidenceId, lesson.packageId);
        item.obligationId = obligationId;
        refundForms[obligationId] = formId;
        refundIndices[obligationId] = index;
        emit RefundPaymentEstablished(formId, index, obligationId);
    }

    function mayPayRedressPart(bytes32 obligationId) external view returns (bool) {
        bytes32 formId = refundForms[obligationId];
        if (formId == bytes32(0)) return true;
        RefundAssessment storage item = refunds[formId][refundIndices[obligationId]];
        return REMEDIES.placeFaultCase(formId) == item.caseId && REMEDIES.isOperative(item.caseId, item.faultRevision);
    }

    function getRefund(bytes32 formId, uint256 index) external view returns (RefundAssessment memory) {
        return refunds[formId][index];
    }

    function refundStatus(bytes32 formId)
        external
        view
        returns (uint256 assessments, uint256 principal, uint256 received)
    {
        (principal, received) = _refundTotals(formId, BOOKING.getForm(formId));
        return (refunds[formId].length, principal, received);
    }

    /// @notice Close the outstanding remedy only after the original account actually received a full refund.
    function recordFullRefundClosure(bytes32 formId, uint256 index, uint128 creditRemoval) external {
        if (msg.sender != address(remedyBookings)) revert InvalidRefund();
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        RefundAssessment storage assessment = refunds[formId][index];
        RedressRecord storage item = redress[formId];
        if (
            item.closedAt != 0 || assessment.cause == RefundBasis.OriginalRelief || assessment.finalFee != 0
                || REMEDIES.placeFaultCase(formId) != assessment.caseId
                || !REMEDIES.isOperative(assessment.caseId, assessment.faultRevision)
        ) revert InvalidRefund();
        (, uint256 received) = _refundTotals(formId, form);
        if (received != form.confirmation.debitedUnits) revert InvalidRefund();
        item.closedAt = uint64(block.timestamp);
        if (creditRemoval != 0) {
            PAYMENTS.FUNDS().revokeUnspentCompensation(form.lessonId, form.terms.placeId, creditRemoval);
            item.unusedCreditRemoved = creditRemoval;
        }
        emit FullRefundClosed(formId, item.closedAt);
    }

    function lessonRedressDelivered(bytes32 lessonId) public view returns (bool hasKnownFault, bool delivered) {
        bytes32[] memory cases = REMEDIES.getLessonCases(lessonId);
        for (uint256 i; i < cases.length; ++i) {
            uint256 revision = REMEDIES.latestFaultRevision(cases[i]);
            SparkV15LessonRemedies.FaultKind kind = REMEDIES.getFault(cases[i], revision).kind;
            if (kind == SparkV15LessonRemedies.FaultKind.NoFault) continue;
            hasKnownFault = true;
            if (!REMEDIES.isOperative(cases[i], revision)) return (true, false);
            bytes32[] memory forms = REMEDIES.getFaultForms(cases[i], revision);
            for (uint256 j; j < forms.length; ++j) {
                if (!_customerRedressDelivered(cases[i], revision, forms[j])) return (true, false);
            }
        }
        return (hasKnownFault, hasKnownFault);
    }

    function _refundAmounts(
        bytes32 formId,
        SparkV15Booking.Form memory form,
        bytes32 caseId,
        uint256 revision,
        RefundBasis cause
    ) private view returns (uint64 trigger, uint128 fee) {
        SparkV15LessonRemedies.AffectedPlace memory facts = REMEDIES.getPlaceFinding(caseId, revision, formId);
        SparkV15LessonRemedies.FaultRecord memory fault = REMEDIES.getFault(caseId, revision);
        RedressRecord storage choice = redress[formId];
        RedressTerms storage terms = redressTerms[formId];
        if (choice.closedAt != 0) revert InvalidRefund();
        if (cause == RefundBasis.OriginalRelief) {
            if (
                !_isTutorFault(fault.kind)
                    && (!facts.missedAgreedTeaching
                        || (facts.teaching != SparkV15LessonRemedies.TeachingReceived.NoneDelivered
                            && (choice.acceptedAt == 0 || choice.remedialLinkId != bytes32(0))))
            ) revert InvalidRefund();
            trigger = fault.recordedAt;
            if (!_isTutorFault(fault.kind) && choice.acceptedAt > trigger) trigger = choice.acceptedAt;
            if (facts.teaching != SparkV15LessonRemedies.TeachingReceived.NoneDelivered) {
                if (form.terms.normalFee % 2 != 0) revert UnrepresentableAmount();
                uint128 half = form.terms.normalFee / 2;
                fee = form.terms.payableFee > half ? form.terms.payableFee - half : 0;
            }
        } else if (cause == RefundBasis.FailedRemedy) {
            uint64 through = deliveryDeadline(formId);
            if (
                choice.acceptedAt == 0 || (choice.unableAt == 0 && block.timestamp <= through)
                    || _remedyDelivered(formId, choice)
            ) revert InvalidRefund();
            trigger = choice.unableAt != 0 && choice.unableAt < through ? choice.unableAt : through;
        } else {
            if (cause == RefundBasis.DirectRequest) {
                if (choice.directRefundAt == 0) revert InvalidRefund();
                trigger = choice.directRefundAt;
            } else {
                if (choice.acceptedAt != 0 || choice.directRefundAt != 0 || block.timestamp <= terms.acceptThrough) {
                    revert InvalidRefund();
                }
                trigger = terms.acceptThrough;
            }
            if (facts.teaching != SparkV15LessonRemedies.TeachingReceived.NoneDelivered) {
                fee = form.terms.payableFee - facts.lostServiceFee;
            }
        }
        RefundAssessment[] storage prior = refunds[formId];
        for (uint256 i; i < prior.length; ++i) {
            RefundAssessment storage previous = prior[i];
            if (previous.caseId == caseId && previous.faultRevision == revision && previous.finalFee < fee) {
                fee = previous.finalFee;
            }
        }
    }

    function _refundScenario(RefundAssessment memory item) private pure returns (bytes32) {
        return keccak256(abi.encode(item.caseId, item.faultRevision, item.cause, item.triggerAt));
    }

    function _refundPaymentTerms(
        bytes32 formId,
        SparkV15Booking.Form memory form,
        RefundAssessment memory item,
        address coordinator
    ) private view returns (SparkV15Payments.PaymentTerms memory terms) {
        RedressTerms storage agreement = redressTerms[formId];
        terms.lessonId = form.lessonId;
        terms.paymentPart = keccak256(abi.encode("spark.v1.5.fault-refund", form.terms.placeId, _refundScenario(item)));
        terms.recipient = _debitOwner(form);
        terms.originalDebitAccount = form.terms.creditAccount;
        terms.originalDebitAmount = form.confirmation.debitedUnits;
        terms.amount = item.principal;
        terms.dueAt = item.triggerAt + agreement.refundDuePeriod;
        terms.executionDeadline = item.triggerAt + agreement.refundExecutionPeriod;
        if (agreement.earlierLegalExecutionPeriod != 0) {
            terms.legalDeadline = item.triggerAt + agreement.earlierLegalExecutionPeriod;
            terms.legalDeadlineExact = true;
            if (terms.legalDeadline < terms.dueAt) terms.dueAt = terms.legalDeadline;
        }
        terms.postLiftPeriod = agreement.postLiftPeriod;
        terms.dueAtExact = true;
        terms.executionDeadlineExact = true;
        terms.settlementProposer = coordinator;
        terms.settlementApprover = item.verifier;
    }

    function _debitOwner(SparkV15Booking.Form memory form) private view returns (address) {
        return PAYMENTS.FUNDS().creditAccount(form.terms.payer) == form.terms.creditAccount
            ? form.terms.payer
            : form.terms.customer;
    }

    /// @dev Stale assessments' outstanding portions do not become new liabilities. Their prior actual receipts
    /// still count against the original debit and remain visible through the normal payment history.
    function _refundTotals(bytes32 formId, SparkV15Booking.Form memory form)
        private
        view
        returns (uint256 principal, uint256 received)
    {
        bytes32 ordinaryPart = keccak256(abi.encode("spark.v1.5.lesson-refund", form.terms.placeId));
        SparkV15Payments.Obligation memory ordinary =
            PAYMENTS.getObligation(keccak256(abi.encode(form.lessonId, ordinaryPart)));
        if (ordinary.packageId != 0) {
            if (
                ordinary.terms.originalDebitAmount != form.confirmation.debitedUnits
                    || ordinary.terms.originalDebitAccount != form.terms.creditAccount
                    || ordinary.terms.recipient != _debitOwner(form)
                    || ordinary.packageId != BOOKING.getLesson(form.lessonId).packageId
            ) revert InvalidRefund();
            received = ordinary.paid;
            principal = ordinary.correctAmount > received ? ordinary.correctAmount : received;
        }
        RefundAssessment[] storage prior = refunds[formId];
        for (uint256 i; i < prior.length; ++i) {
            RefundAssessment storage item = prior[i];
            bool current = REMEDIES.placeFaultCase(formId) == item.caseId
                && REMEDIES.latestFaultRevision(item.caseId) == item.faultRevision;
            uint256 paid;
            uint128 amount = item.principal;
            if (item.obligationId != bytes32(0)) {
                SparkV15Payments.Obligation memory payment = PAYMENTS.getObligation(item.obligationId);
                paid = payment.paid;
                amount = payment.correctAmount;
            }
            received += paid;
            principal += current && amount > paid ? amount : paid;
        }
    }

    function _redressApplies(SparkV15Booking.Form memory form, bytes32 caseId, uint256 revision, bytes32 formId)
        private
        view
        returns (bool)
    {
        return REMEDIES.isOperative(caseId, revision)
            && (!_isTutorFault(REMEDIES.getFault(caseId, revision).kind)
                || _eligible(form, REMEDIES.getPlaceFinding(caseId, revision, formId)));
    }

    function _remedyDelivered(bytes32 formId, RedressRecord storage item) private view returns (bool) {
        if (item.remedialLinkId != bytes32(0)) return item.remedialDeliveryAt != 0;
        return address(remedyBookings) != address(0) && remedyBookings.standardRemedyDelivered(formId);
    }

    function _customerRedressDelivered(bytes32 caseId, uint256 revision, bytes32 formId) private view returns (bool) {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        if (!_redressApplies(form, caseId, revision, formId)) return true;
        (uint256 principal, uint256 received) = _refundTotals(formId, form);
        if (principal > received) return false;
        RedressRecord storage item = redress[formId];
        if (item.closedAt != 0 && received >= form.confirmation.debitedUnits) return true;
        if (item.acceptedAt != 0 && item.directRefundAt == 0) {
            return _remedyDelivered(formId, item) && remedyBookings.originalReliefSatisfied(formId, received);
        }
        RefundAssessment[] storage prior = refunds[formId];
        for (uint256 i; i < prior.length; ++i) {
            if (
                prior[i].caseId == caseId && prior[i].faultRevision == revision
                    && prior[i].cause != RefundBasis.OriginalRelief && prior[i].grossCreditRestoration <= received
            ) return true;
        }
        return false;
    }

    function _isTutorFault(SparkV15LessonRemedies.FaultKind kind) private pure returns (bool) {
        return kind == SparkV15LessonRemedies.FaultKind.MissedAgreedTeaching
            || kind == SparkV15LessonRemedies.FaultKind.SeriousTeachingIncident;
    }

    function _eligible(SparkV15Booking.Form memory form, SparkV15LessonRemedies.AffectedPlace memory finding)
        private
        pure
        returns (bool)
    {
        return form.confirmation.debitedUnits == form.terms.payableFee
            && (finding.participation == SparkV15LessonRemedies.Participation.AttendedAsAgreed
                || finding.participation == SparkV15LessonRemedies.Participation.ReadyAsAgreed);
    }

    function _requireCustomer(bytes32 formId, SparkV15Booking.Form memory form) private view {
        if (
            msg.sender != form.terms.customer
                && !(msg.sender == form.terms.customerRepresentative && BOOKING.representativeAuthorised(formId))
        ) revert InvalidCustomerChoice();
    }

    function _requireAuthority(bytes32 action, bytes32 authorityId) private view {
        bytes32 role =
            EVIDENCE_REGISTRY.IDENTITY_REGISTRY().requireActiveSubjectContext(authorityId, SparkV15.APP_ID).roleKey;
        EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(msg.sender, SparkV15.APP_ID, role, action, authorityId);
    }

    function _requireEvidence(uint256 evidenceId, uint256 packageId, bytes32 commitment) private view {
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        AVAEvidenceRegistry.EvidenceReference memory proof = EVIDENCE_REGISTRY.getEvidenceReference(evidenceId);
        if (
            proof.commitment != commitment
                || EVIDENCE_REGISTRY.IDENTITY_REGISTRY().getSubjectContext(proof.authorityId).roleKey != EVIDENCE_ROLE
        ) revert InvalidEvidence();
    }

    function faultRedressDelivered(bytes32 caseId, uint256 revision) external view returns (bool) {
        if (!REMEDIES.isOperative(caseId, revision)) return false;
        bytes32[] memory forms = REMEDIES.getFaultForms(caseId, revision);
        for (uint256 i; i < forms.length; ++i) {
            if (!_customerRedressDelivered(caseId, revision, forms[i])) return false;
        }
        return forms.length != 0;
    }
}

/// @notice Verified tutor losses and actual recoveries, separate from tutor pay and customer balances.
contract SparkV15TutorDebt {
    struct LossFinding {
        bytes32 lossId;
        bytes32 lossEvidenceRef;
        bytes32 teachingAgreementRef;
        uint64 breachedAt;
        uint64 incurredAt;
        uint128 actualLoss;
        uint128 responsibility;
    }

    struct Debt {
        bytes32 caseId;
        uint256 faultRevision;
        LossFinding loss;
        address debtor;
        address creditor;
        address verifier;
        bytes32 authorityId;
        uint256 evidenceId;
        uint64 recordedAt;
        uint64 deliveryVerifiedAt;
        uint256 deliveryEvidenceId;
        uint64 lastRecoveryAt;
        uint128 remaining;
    }

    struct DebtReceipt {
        bytes32 debtId;
        address debtor;
        address creditor;
        uint128 actualReceipt;
        uint64 receivedAt;
    }

    bytes32 public constant ACTION_CONFIRM_TUTOR_LOSS = keccak256("spark.action.confirm-tutor-loss.v1.5");
    bytes32 public constant ACTION_VERIFY_CUSTOMER_DELIVERY = keccak256("spark.action.verify-customer-redress.v1.5");

    error InvalidDebt();
    error InvalidEvidence();
    error TransferMismatch();

    event TutorLossConfirmed(bytes32 indexed debtId, bytes32 indexed caseId, address indexed debtor, uint128 amount);
    event CustomerRedressVerified(bytes32 indexed debtId, uint256 indexed evidenceId, uint64 verifiedAt);
    event TutorDebtRecovered(bytes32 indexed debtId, uint256 indexed receiptId, uint128 amount);

    SparkV15LessonRemedies public immutable REMEDIES;
    SparkV15CustomerRedress public immutable REDRESS;
    SparkV15Booking public immutable BOOKING;
    SparkV15Payments public immutable PAYMENTS;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;
    bytes32 private immutable EVIDENCE_ROLE;

    mapping(bytes32 => Debt) private debts;
    mapping(uint256 => DebtReceipt) private debtReceipts;
    uint256 private nextDebtReceipt = 1;
    bool private collectingDebt;

    constructor(SparkV15LessonRemedies remedies, SparkV15CustomerRedress redress, bytes32 evidenceRole) {
        if (address(redress.REMEDIES()) != address(remedies) || evidenceRole == bytes32(0)) revert InvalidDebt();
        REMEDIES = remedies;
        REDRESS = redress;
        BOOKING = remedies.BOOKING();
        PAYMENTS = remedies.PAYMENTS();
        EVIDENCE_REGISTRY = PAYMENTS.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        EVIDENCE_ROLE = evidenceRole;
    }

    function lossCommitment(bytes32 caseId, LossFinding calldata loss, address verifier) public view returns (bytes32) {
        return keccak256(
            abi.encode(
                ACTION_CONFIRM_TUTOR_LOSS,
                block.chainid,
                address(this),
                caseId,
                REMEDIES.latestFaultRevision(caseId),
                loss,
                verifier
            )
        );
    }

    /// @notice This verifies an actual loss and its attributable share under the effective teaching agreement.
    function confirmTutorLoss(bytes32 caseId, LossFinding calldata loss, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 debtId)
    {
        _requireAuthority(ACTION_CONFIRM_TUTOR_LOSS, authorityId);
        uint256 revision = REMEDIES.latestFaultRevision(caseId);
        SparkV15LessonRemedies.FaultRecord memory fault = REMEDIES.getFault(caseId, revision);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(fault.lessonId);
        ISparkV15BookingChanges.Arrangement memory arrangement =
            BOOKING.getEffectiveArrangement(fault.lessonId, loss.breachedAt);
        debtId = keccak256(abi.encode(lesson.terms.provider, loss.lossId));
        if (
            !_isTutorFault(fault.kind) || arrangement.tutor != fault.tutor
                || loss.teachingAgreementRef != arrangement.tutorAgreementRef || loss.breachedAt < arrangement.startsAt
                || loss.breachedAt > loss.incurredAt || loss.incurredAt > block.timestamp || loss.actualLoss == 0
                || loss.responsibility > loss.actualLoss || loss.lossId == bytes32(0)
                || loss.lossEvidenceRef == bytes32(0) || debts[debtId].recordedAt != 0
                || fault.tutor == lesson.terms.provider
        ) revert InvalidDebt();
        _requireEvidence(evidenceId, lesson.packageId, lossCommitment(caseId, loss, msg.sender));
        Debt storage debt = debts[debtId];
        debt.caseId = caseId;
        debt.faultRevision = revision;
        debt.loss = loss;
        debt.debtor = fault.tutor;
        debt.creditor = lesson.terms.provider;
        debt.verifier = msg.sender;
        debt.authorityId = authorityId;
        debt.evidenceId = evidenceId;
        debt.recordedAt = uint64(block.timestamp);
        debt.remaining = loss.responsibility;
        emit TutorLossConfirmed(debtId, caseId, debt.debtor, loss.responsibility);
    }

    function getDebt(bytes32 debtId) external view returns (Debt memory) {
        return debts[debtId];
    }

    function getDebtReceipt(uint256 receiptId) external view returns (DebtReceipt memory) {
        return debtReceipts[receiptId];
    }

    function recoveryReadinessCommitment(bytes32 debtId, address verifier) public view returns (bytes32) {
        Debt storage debt = debts[debtId];
        return keccak256(
            abi.encode(
                ACTION_VERIFY_CUSTOMER_DELIVERY,
                block.chainid,
                address(this),
                debtId,
                debt.caseId,
                debt.faultRevision,
                debt.evidenceId,
                verifier
            )
        );
    }

    /// @dev The evidence verifies coverage of all redress from this breach, including any separate commitments
    /// outside the application's native record. The native receipts must also independently pass the current check.
    function verifyRecoveryReadiness(bytes32 debtId, uint256 evidenceId, bytes32 authorityId) external {
        _requireAuthority(ACTION_VERIFY_CUSTOMER_DELIVERY, authorityId);
        Debt storage debt = debts[debtId];
        if (
            debt.recordedAt == 0 || debt.deliveryVerifiedAt != 0
                || !REDRESS.faultRedressDelivered(debt.caseId, debt.faultRevision)
        ) revert InvalidDebt();
        uint256 packageId = BOOKING.getLesson(REMEDIES.getFault(debt.caseId, debt.faultRevision).lessonId).packageId;
        _requireEvidence(evidenceId, packageId, recoveryReadinessCommitment(debtId, msg.sender));
        debt.deliveryVerifiedAt = uint64(block.timestamp);
        debt.deliveryEvidenceId = evidenceId;
        emit CustomerRedressVerified(debtId, evidenceId, debt.deliveryVerifiedAt);
    }

    /// @notice The tutor separately pays the provider against a confirmed loss after customer redress.
    function collectDebt(bytes32 debtId, uint128 amount) external returns (uint256 receiptId) {
        Debt storage debt = debts[debtId];
        if (
            collectingDebt || msg.sender != debt.debtor || amount == 0 || amount > debt.remaining
                || debt.deliveryVerifiedAt == 0 || debt.deliveryVerifiedAt >= block.timestamp
                || debt.lastRecoveryAt >= block.timestamp
                || !REDRESS.faultRedressDelivered(debt.caseId, debt.faultRevision)
        ) revert InvalidDebt();
        collectingDebt = true;
        debt.remaining -= amount;
        debt.lastRecoveryAt = uint64(block.timestamp);
        IERC20 token = PAYMENTS.TOKEN();
        uint256 beforeCreditor = token.balanceOf(debt.creditor);
        uint256 beforeDebtor = token.balanceOf(debt.debtor);
        if (
            !token.transferFrom(debt.debtor, debt.creditor, amount)
                || token.balanceOf(debt.creditor) != beforeCreditor + amount
                || token.balanceOf(debt.debtor) + amount != beforeDebtor
        ) revert TransferMismatch();
        collectingDebt = false;
        receiptId = nextDebtReceipt++;
        debtReceipts[receiptId] = DebtReceipt(debtId, debt.debtor, debt.creditor, amount, debt.lastRecoveryAt);
        emit TutorDebtRecovered(debtId, receiptId, amount);
    }

    function _requireAuthority(bytes32 action, bytes32 authorityId) private view {
        bytes32 role =
            EVIDENCE_REGISTRY.IDENTITY_REGISTRY().requireActiveSubjectContext(authorityId, SparkV15.APP_ID).roleKey;
        EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(msg.sender, SparkV15.APP_ID, role, action, authorityId);
    }

    function _requireEvidence(uint256 evidenceId, uint256 packageId, bytes32 commitment) private view {
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        AVAEvidenceRegistry.EvidenceReference memory proof = EVIDENCE_REGISTRY.getEvidenceReference(evidenceId);
        if (
            proof.commitment != commitment
                || EVIDENCE_REGISTRY.IDENTITY_REGISTRY().getSubjectContext(proof.authorityId).roleKey != EVIDENCE_ROLE
        ) revert InvalidEvidence();
    }

    function _isTutorFault(SparkV15LessonRemedies.FaultKind kind) private pure returns (bool) {
        return kind == SparkV15LessonRemedies.FaultKind.MissedAgreedTeaching
            || kind == SparkV15LessonRemedies.FaultKind.SeriousTeachingIncident;
    }
}

/// @notice Books the original fee's fixed benefit through Booking's actual confirmation and debit.
contract SparkV15RemedyBookings {
    struct Discount {
        bytes32 originalFormId;
        uint128 fixedAmount;
        uint64 availableAt;
        bytes32 usedFormId;
        uint64 usedAt;
        uint128 applied;
        uint128 unapplied;
    }

    struct DiscountSelection {
        bytes32 formId;
        address selectedBy;
        uint128 feeOtherwiseDue;
        bytes32 remainderTerms;
        uint64 selectedAt;
        uint256 evidenceId;
    }

    struct DeadlineExtension {
        bytes32 formId;
        uint64 priorDeadline;
        uint64 newDeadline;
        uint64 proposedAt;
        uint64 customerAcceptedAt;
        uint64 payerAcceptedAt;
        uint64 studentAcceptedAt;
        uint64 agreedAt;
        uint256 evidenceId;
        address payer;
        address student;
    }

    struct RefundClosureDecision {
        bytes32 termsAndLawRef;
        bytes32 remedyTreatmentRef;
        bytes32 discountTreatmentRef;
        bytes32 creditTreatmentRef;
        uint128 unusedCredit;
        uint128 creditRemoval;
    }

    struct RefundClosure {
        uint256 assessmentIndex;
        RefundClosureDecision decision;
        uint256 evidenceId;
        uint64 closedAt;
    }

    error InvalidCustomerChoice();
    error InvalidEvidence();
    error UnrepresentableAmount();

    SparkV15CustomerRedress public immutable REDRESS;
    SparkV15LessonRemedies public immutable REMEDIES;
    SparkV15Booking public immutable BOOKING;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;
    bytes32 private immutable EVIDENCE_ROLE;

    event LaterDiscountMadeUsable(bytes32 indexed formId, bytes32 indexed discountId, uint64 availableAt);
    event LaterDiscountSelected(bytes32 indexed discountId, bytes32 indexed selectedFormId, address indexed selectedBy);
    event LaterDiscountBooked(
        bytes32 indexed discountId, bytes32 indexed selectedFormId, uint128 applied, uint128 unapplied
    );
    event RemedyExtensionProposed(bytes32 indexed formId, bytes32 indexed extensionId, uint64 newDeadline);
    event RemedyExtensionAgreed(bytes32 indexed formId, bytes32 indexed extensionId, uint64 newDeadline);

    mapping(bytes32 => bytes32) public discountFor;
    mapping(bytes32 => Discount) private discounts;
    mapping(bytes32 => DiscountSelection[]) private discountSelections;
    mapping(bytes32 => DeadlineExtension) private extensions;
    mapping(bytes32 => uint64) public extendedDeadline;
    mapping(bytes32 => RefundClosure) private refundClosures;

    constructor(SparkV15CustomerRedress redress, bytes32 evidenceRole) {
        if (address(redress).code.length == 0 || evidenceRole == bytes32(0)) revert InvalidEvidence();
        REDRESS = redress;
        REMEDIES = redress.REMEDIES();
        BOOKING = redress.BOOKING();
        EVIDENCE_REGISTRY = BOOKING.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        EVIDENCE_ROLE = evidenceRole;
    }

    function discountAvailableAt(bytes32 originalFormId) external view returns (uint64) {
        return discounts[discountFor[originalFormId]].availableAt;
    }

    function standardRemedyDelivered(bytes32 formId) external view returns (bool) {
        SparkV15CustomerRedress.RedressRecord memory item = REDRESS.getRedress(formId);
        if (item.creditIssuedAt == 0) return false;
        if (
            REMEDIES.getPlaceFinding(item.caseId, item.faultRevision, formId).teaching
                    == SparkV15LessonRemedies.TeachingReceived.NoneDelivered
                && discounts[discountFor[formId]].availableAt == 0
        ) return false;
        (uint256 assessments,, uint256 received) = REDRESS.refundStatus(formId);
        for (uint256 i; i < assessments; ++i) {
            SparkV15CustomerRedress.RefundAssessment memory refund = REDRESS.getRefund(formId, i);
            if (
                refund.caseId == item.caseId && refund.faultRevision == item.faultRevision
                    && refund.cause == SparkV15CustomerRedress.RefundBasis.OriginalRelief
            ) return received >= refund.grossCreditRestoration;
        }
        return false;
    }

    function originalReliefSatisfied(bytes32 formId, uint256 received) external view returns (bool) {
        (bool applicable, uint128 fee) = REMEDIES.faultFee(formId);
        return !applicable || uint256(fee) + received >= BOOKING.getForm(formId).confirmation.debitedUnits;
    }

    function remedialTeachingForm(bytes32 originalFormId, bytes32 linkId) public view returns (bytes32) {
        SparkV15BookingChanges changes = SparkV15BookingChanges(address(BOOKING.bookingChanges()));
        if (address(changes) == address(0)) return bytes32(0);
        SparkV15BookingChanges.SeparateLink memory link = changes.getSeparateBooking(linkId);
        if (link.originalFormId != originalFormId || link.payerAcceptedAt == 0 || link.linkedAt == 0) {
            return bytes32(0);
        }
        SparkV15Booking.Form memory original = BOOKING.getForm(originalFormId);
        SparkV15Booking.Form memory next = BOOKING.getForm(link.nextFormId);
        if (
            next.terms.customer != original.terms.customer || next.terms.student != original.terms.student
                || next.confirmation.confirmedAt == 0 || BOOKING.isCancelledAt(link.nextFormId, uint64(block.timestamp))
                || BOOKING.getEffectiveArrangement(next.lessonId, link.agreedAt).startsAt <= link.agreedAt
        ) return bytes32(0);
        uint256 packageId = BOOKING.getLesson(original.lessonId).packageId;
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(link.studentNotice.evidenceId, packageId);
        return link.nextFormId;
    }

    function remedialTeachingDeliveredAt(bytes32 originalFormId, bytes32 linkId) public view returns (uint64) {
        bytes32 nextFormId = remedialTeachingForm(originalFormId, linkId);
        if (nextFormId == bytes32(0)) return 0;
        SparkV15Booking.Form memory form = BOOKING.getForm(nextFormId);
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(form.lessonId);
        SparkV15Booking.TutorDelivery memory delivery = BOOKING.getTutorDelivery(form.lessonId);
        SparkV15Booking.ServiceFeedback memory service = BOOKING.getServiceFeedback(nextFormId);
        if (
            teaching.endedAt == 0 || !delivery.completed || service.status != SparkV15Booking.ServiceStatus.FullyDelivered
        ) return 0;
        SparkV15BookingOpening opening = BOOKING.OPENING();
        if (
            teaching.startPermission != SparkV15Booking.StartPermission.Permitted
                && (
                    teaching.startPermission != SparkV15Booking.StartPermission.Unverified
                        || address(opening) == address(0)
                        || !opening.TEACHING_END().hasUsableLateOpeningNotices(form.lessonId)
                )
        ) return 0;
        uint256 packageId = BOOKING.getLesson(form.lessonId).packageId;
        opening.requireTeachingStartEvidence(form.lessonId, teaching.startEvidenceId, packageId);
        opening.requireTeachingEndEvidence(form.lessonId, teaching.endEvidenceId, packageId);
        opening.SERVICE_REPORTS().requireUsableTutorDeliveryEvidence(form.lessonId, delivery.evidenceId, packageId);
        opening.SERVICE_REPORTS().requireUsableFeedbackEvidence(nextFormId, service.evidenceId, packageId);
        return teaching.endedAt;
    }

    /// @notice The customer accepts a dated remedy with the designated payer's confirmation and an actual student notice.
    function acceptRemedialTeaching(bytes32 formId, bytes32 linkId) external {
        _requireCustomer(formId, BOOKING.getForm(formId));
        if (remedialTeachingForm(formId, linkId) == bytes32(0)) revert InvalidCustomerChoice();
        REDRESS.recordAgreedRemedialTeaching(formId, linkId, msg.sender);
    }

    function recordRemedialDelivery(bytes32 formId) external {
        uint64 deliveredAt = remedialTeachingDeliveredAt(formId, REDRESS.getRedress(formId).remedialLinkId);
        REDRESS.recordRemedialDelivery(formId, deliveredAt);
    }

    function refundSwitchCommitment(bytes32 formId, bytes32 grounds, address customerActor)
        public
        view
        returns (bytes32)
    {
        SparkV15CustomerRedress.RedressRecord memory item = REDRESS.getRedress(formId);
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.switch-remedy-to-refund"),
                block.chainid,
                address(this),
                formId,
                item.caseId,
                item.faultRevision,
                item.acceptedAt,
                item.remedialLinkId,
                grounds,
                customerActor
            )
        );
    }

    /// @notice A customer changes an outstanding accepted remedy under the applicable terms or law.
    function switchToRefund(bytes32 formId, bytes32 grounds, uint256 evidenceId) external {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        _requireCustomer(formId, form);
        if (grounds == bytes32(0) || !REDRESS.remedyOutstanding(formId)) revert InvalidCustomerChoice();
        _requireEvidence(
            evidenceId, BOOKING.getLesson(form.lessonId).packageId, refundSwitchCommitment(formId, grounds, msg.sender)
        );
        REDRESS.recordRefundSwitch(formId, msg.sender, evidenceId);
    }

    function extensionCommitment(bytes32 formId, uint64 priorDeadline, uint64 newDeadline, bytes32 source)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.remedy-deadline"),
                block.chainid,
                address(this),
                formId,
                priorDeadline,
                newDeadline,
                source
            )
        );
    }

    function proposeExtension(bytes32 formId, uint64 newDeadline, bytes32 source, uint256 evidenceId)
        external
        returns (bytes32 extensionId)
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        uint64 priorDeadline = REDRESS.deliveryDeadline(formId);
        if (
            msg.sender != lesson.terms.provider || block.timestamp >= priorDeadline || newDeadline <= priorDeadline
                || source == bytes32(0) || !REDRESS.remedyOutstanding(formId)
        ) revert InvalidCustomerChoice();
        extensionId = extensionCommitment(formId, priorDeadline, newDeadline, source);
        DeadlineExtension storage extension = extensions[extensionId];
        if (extension.proposedAt != 0) revert InvalidCustomerChoice();
        _requireEvidence(evidenceId, lesson.packageId, extensionId);
        extension.formId = formId;
        extension.priorDeadline = priorDeadline;
        extension.newDeadline = newDeadline;
        extension.proposedAt = uint64(block.timestamp);
        extension.evidenceId = evidenceId;
        bytes32 remedialLinkId = REDRESS.getRedress(formId).remedialLinkId;
        if (remedialLinkId != bytes32(0)) {
            bytes32 remedialFormId = remedialTeachingForm(formId, remedialLinkId);
            if (remedialFormId == bytes32(0)) revert InvalidCustomerChoice();
            SparkV15Booking.Form memory remedial = BOOKING.getForm(remedialFormId);
            extension.payer = remedial.terms.payer;
            extension.student = remedial.terms.student;
        }
        emit RemedyExtensionProposed(formId, extensionId, newDeadline);
    }

    function acceptExtension(bytes32 extensionId) external {
        DeadlineExtension storage extension = extensions[extensionId];
        bytes32 formId = extension.formId;
        if (
            extension.proposedAt == 0 || extension.agreedAt != 0 || block.timestamp >= extension.priorDeadline
                || REDRESS.deliveryDeadline(formId) != extension.priorDeadline || !REDRESS.remedyOutstanding(formId)
        ) revert InvalidCustomerChoice();
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        bool customer = msg.sender == form.terms.customer
            || (msg.sender == form.terms.customerRepresentative && BOOKING.representativeAuthorised(formId));
        if (!customer && msg.sender != extension.payer && msg.sender != extension.student) {
            revert InvalidCustomerChoice();
        }
        uint64 at = uint64(block.timestamp);
        if (customer && extension.customerAcceptedAt == 0) extension.customerAcceptedAt = at;
        if (msg.sender == extension.payer && extension.payerAcceptedAt == 0) extension.payerAcceptedAt = at;
        if (msg.sender == extension.student && extension.studentAcceptedAt == 0) extension.studentAcceptedAt = at;
        if (
            extension.customerAcceptedAt != 0 && (extension.payer == address(0) || extension.payerAcceptedAt != 0)
                && (extension.student == address(0) || extension.studentAcceptedAt != 0)
        ) {
            extension.agreedAt = at;
            extendedDeadline[formId] = extension.newDeadline;
            emit RemedyExtensionAgreed(formId, extensionId, extension.newDeadline);
        }
    }

    function getExtension(bytes32 extensionId) external view returns (DeadlineExtension memory) {
        return extensions[extensionId];
    }

    function refundClosureCommitment(bytes32 formId, uint256 assessmentIndex, RefundClosureDecision calldata decision)
        public
        view
        returns (bytes32)
    {
        SparkV15CustomerRedress.RefundAssessment memory assessment = REDRESS.getRefund(formId, assessmentIndex);
        SparkV15CustomerRedress.RedressRecord memory choice = REDRESS.getRedress(formId);
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.full-refund-closure"),
                block.chainid,
                address(this),
                formId,
                assessmentIndex,
                assessment.basis,
                choice.acceptedAt,
                choice.creditIssuedAt,
                discounts[discountFor[formId]],
                decision
            )
        );
    }

    /// @notice The provider closes against verified terms and the exact unused credit from the original place's grant.
    function closeFullRefund(
        bytes32 formId,
        uint256 assessmentIndex,
        RefundClosureDecision calldata decision,
        uint256 evidenceId
    ) external {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        SparkV15CustomerRedress.RedressRecord memory choice = REDRESS.getRedress(formId);
        uint128 unused = REDRESS.PAYMENTS().FUNDS().compensationCreditRemaining(form.lessonId, form.terms.placeId);
        if (
            msg.sender != lesson.terms.provider || decision.termsAndLawRef == bytes32(0)
                || (choice.acceptedAt != 0 && decision.remedyTreatmentRef == bytes32(0))
                || (discountFor[formId] != bytes32(0) && decision.discountTreatmentRef == bytes32(0))
                || (choice.creditIssuedAt != 0 && decision.creditTreatmentRef == bytes32(0))
                || decision.unusedCredit != unused || decision.creditRemoval > unused
        ) revert InvalidCustomerChoice();
        _requireEvidence(evidenceId, lesson.packageId, refundClosureCommitment(formId, assessmentIndex, decision));
        REDRESS.recordFullRefundClosure(formId, assessmentIndex, decision.creditRemoval);
        refundClosures[formId] = RefundClosure(assessmentIndex, decision, evidenceId, uint64(block.timestamp));
    }

    function getRefundClosure(bytes32 formId) external view returns (RefundClosure memory) {
        return refundClosures[formId];
    }

    /// @notice Activate a fixed benefit against a later normal booking through the installed booking consumer.
    function makeDiscountUsable(bytes32 originalFormId) external returns (bytes32 discountId) {
        SparkV15Booking.Form memory form = BOOKING.getForm(originalFormId);
        SparkV15CustomerRedress.RedressRecord memory choice = REDRESS.getRedress(originalFormId);
        SparkV15BookingChanges changes = SparkV15BookingChanges(address(BOOKING.bookingChanges()));
        if (
            msg.sender != BOOKING.getLesson(form.lessonId).terms.provider || address(changes) == address(0)
                || address(changes.bookingRemedyConsumer()) != address(this)
                || !_standardChoiceCurrent(originalFormId, choice) || discountFor[originalFormId] != bytes32(0)
                || block.timestamp > REDRESS.deliveryDeadline(originalFormId)
                || REMEDIES.getPlaceFinding(choice.caseId, choice.faultRevision, originalFormId).teaching
                    != SparkV15LessonRemedies.TeachingReceived.NoneDelivered
        ) revert InvalidCustomerChoice();
        if (form.terms.normalFee % 2 != 0) revert UnrepresentableAmount();
        discountId = keccak256(abi.encode(keccak256("spark.v1.5.later-lesson-discount"), address(this), originalFormId));
        discountFor[originalFormId] = discountId;
        Discount storage item = discounts[discountId];
        item.originalFormId = originalFormId;
        item.fixedAmount = form.terms.normalFee / 2;
        item.availableAt = uint64(block.timestamp);
        emit LaterDiscountMadeUsable(originalFormId, discountId, item.availableAt);
    }

    function getDiscount(bytes32 discountId) external view returns (Discount memory) {
        return discounts[discountId];
    }

    function getDiscountSelection(bytes32 discountId, uint256 index) external view returns (DiscountSelection memory) {
        return discountSelections[discountId][index];
    }

    function discountSelectionCommitment(
        bytes32 discountId,
        bytes32 selectedFormId,
        uint128 feeOtherwiseDue,
        bytes32 remainderTerms,
        address customerActor
    ) public view returns (bytes32) {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.discount-selection"),
                block.chainid,
                address(this),
                discountId,
                selectedFormId,
                feeOtherwiseDue,
                remainderTerms,
                customerActor
            )
        );
    }

    /// @dev The independent evidence identifies the selected course's price before this benefit and the agreed treatment
    /// of any amount it cannot cover. A still-unused offer can be selected for a different course.
    function selectDiscountCourse(
        bytes32 discountId,
        bytes32 selectedFormId,
        uint128 feeOtherwiseDue,
        bytes32 remainderTerms,
        uint256 evidenceId
    ) external {
        Discount storage offer = discounts[discountId];
        SparkV15Booking.Form memory original = BOOKING.getForm(offer.originalFormId);
        SparkV15Booking.Form memory selected = BOOKING.getForm(selectedFormId);
        _requireCustomer(offer.originalFormId, original);
        uint128 applied = feeOtherwiseDue < offer.fixedAmount ? feeOtherwiseDue : offer.fixedAmount;
        if (
            offer.availableAt == 0 || offer.usedAt != 0
                || !_standardChoiceCurrent(offer.originalFormId, REDRESS.getRedress(offer.originalFormId))
                || selected.confirmation.confirmedAt != 0 || selected.terms.remedyDiscountId != discountId
                || !_matchesSelectedCourse(original, selected, REDRESS.getRedress(offer.originalFormId))
                || feeOtherwiseDue > selected.terms.normalFee || applied == 0
                || selected.terms.payableFee != feeOtherwiseDue - applied
                || (applied < offer.fixedAmount && remainderTerms == bytes32(0))
        ) revert InvalidCustomerChoice();
        _requireEvidence(
            evidenceId,
            BOOKING.getLesson(selected.lessonId).packageId,
            discountSelectionCommitment(discountId, selectedFormId, feeOtherwiseDue, remainderTerms, msg.sender)
        );
        discountSelections[discountId].push(
            DiscountSelection(
                selectedFormId, msg.sender, feeOtherwiseDue, remainderTerms, uint64(block.timestamp), evidenceId
            )
        );
        emit LaterDiscountSelected(discountId, selectedFormId, msg.sender);
    }

    /// @dev The booking companion calls this for the signed entitlement during the exact atomic confirmation/debit.
    function consumeBookingDiscount(bytes32 formId) external {
        if (msg.sender != address(BOOKING.bookingChanges())) revert InvalidCustomerChoice();
        SparkV15Booking.Form memory selected = BOOKING.getForm(formId);
        bytes32 discountId = selected.terms.remedyDiscountId;
        Discount storage offer = discounts[discountId];
        DiscountSelection[] storage choices = discountSelections[discountId];
        SparkV15CustomerRedress.RedressRecord memory choice = REDRESS.getRedress(offer.originalFormId);
        if (
            offer.usedAt != 0 || choices.length == 0 || selected.confirmation.confirmedAt != block.timestamp
                || !_standardChoiceCurrent(offer.originalFormId, choice)
                || !_matchesSelectedCourse(BOOKING.getForm(offer.originalFormId), selected, choice)
        ) revert InvalidCustomerChoice();
        DiscountSelection storage selection = choices[choices.length - 1];
        if (selection.formId != formId || selected.confirmation.debitedUnits != selected.terms.payableFee) {
            revert InvalidCustomerChoice();
        }
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(
            selection.evidenceId, BOOKING.getLesson(selected.lessonId).packageId
        );
        offer.usedFormId = formId;
        offer.usedAt = uint64(block.timestamp);
        offer.applied = selection.feeOtherwiseDue - selected.terms.payableFee;
        offer.unapplied = offer.fixedAmount - offer.applied;
        emit LaterDiscountBooked(discountId, formId, offer.applied, offer.unapplied);
    }

    function _matchesSelectedCourse(
        SparkV15Booking.Form memory original,
        SparkV15Booking.Form memory selected,
        SparkV15CustomerRedress.RedressRecord memory choice
    ) private view returns (bool) {
        if (
            selected.lessonId == original.lessonId || selected.terms.customer != original.terms.customer
                || selected.version == 0
        ) return false;
        uint64 selectedStart = BOOKING.getEffectiveArrangement(selected.lessonId, uint64(block.timestamp)).startsAt;
        return selectedStart > REMEDIES.getFault(choice.caseId, choice.faultRevision).originalLessonAt;
    }

    function _standardChoiceCurrent(bytes32 formId, SparkV15CustomerRedress.RedressRecord memory choice)
        private
        view
        returns (bool)
    {
        return choice.acceptedAt != 0 && choice.remedialLinkId == bytes32(0) && choice.directRefundAt == 0
            && choice.unableAt == 0 && choice.closedAt == 0 && REMEDIES.placeFaultCase(formId) == choice.caseId
            && REMEDIES.isOperative(choice.caseId, choice.faultRevision);
    }

    function _requireCustomer(bytes32 formId, SparkV15Booking.Form memory form) private view {
        if (
            msg.sender != form.terms.customer
                && !(msg.sender == form.terms.customerRepresentative && BOOKING.representativeAuthorised(formId))
        ) revert InvalidCustomerChoice();
    }

    function _requireEvidence(uint256 evidenceId, uint256 packageId, bytes32 commitment) private view {
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        AVAEvidenceRegistry.EvidenceReference memory proof = EVIDENCE_REGISTRY.getEvidenceReference(evidenceId);
        if (
            proof.commitment != commitment
                || EVIDENCE_REGISTRY.IDENTITY_REGISTRY().getSubjectContext(proof.authorityId).roleKey != EVIDENCE_ROLE
        ) revert InvalidEvidence();
    }
}
