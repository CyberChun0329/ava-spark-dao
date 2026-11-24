// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVAIdentityRegistry} from "@ava-protocol/contracts/src/core/AVAIdentityRegistry.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {SparkV15Payments} from "./SparkV15Payments.sol";
import {SparkV15PaymentApprovalChecks} from "./SparkV15PaymentApprovalChecks.sol";

interface ISparkV15CaseMaterialProvisions {
    function caseChargeInterest(
        bytes32 caseId,
        bytes32 lessonId,
        bytes32 scopeId,
        bytes32 obligationId,
        bytes32 omissionForm,
        address actor
    ) external view returns (bool recognised, bool interested);
}

library SparkV15ReviewActions {
    bytes32 internal constant ACTION_PUBLISH_CONTACTS = keccak256("spark.action.publish-review-contacts.v1.5");
    bytes32 internal constant ACTION_RECEIVE_CONCERN = keccak256("spark.action.receive-concern.v1.5");
    bytes32 internal constant ACTION_ACKNOWLEDGE_CONCERN = keccak256("spark.action.acknowledge-concern.v1.5");
    bytes32 internal constant ACTION_REPLY_TO_CONCERN = keccak256("spark.action.reply-to-concern.v1.5");
    bytes32 internal constant ACTION_REQUIRE_CASE_APPOINTMENT = keccak256("spark.action.require-case-appointment.v1.5");
    bytes32 internal constant ACTION_APPOINT_CASE_ACTOR = keccak256("spark.action.appoint-case-actor.v1.5");
    bytes32 internal constant ACTION_DECIDE_INITIAL = keccak256("spark.action.decide-initial-finding.v1.5");
    bytes32 internal constant ACTION_RETAIN_ORIGINAL = keccak256("spark.action.retain-original-outcome.v1.5");
    bytes32 internal constant ACTION_DECIDE_REVIEW = keccak256("spark.action.decide-independent-review.v1.5");
    bytes32 internal constant ACTION_ADOPT_CORRECTION = keccak256("spark.action.adopt-review-correction.v1.5");
    bytes32 internal constant ACTION_ESCALATE_CASE = keccak256("spark.action.escalate-review-case.v1.5");
}

abstract contract SparkV15ReviewContext {
    enum ConcernSubject {
        CustomerFee,
        CustomerRefund,
        CustomerCompensation,
        StudentAttendance,
        StudentService,
        StudentRemedy,
        StudentPayment,
        Tutor,
        RevenueShare,
        MaterialOmission
    }

    enum AlternativeGround {
        None,
        CoordinatorUnreachable,
        CoordinatorInterested,
        AboutCoordinator,
        Contributor
    }

    struct ReviewTerms {
        bytes32 lessonId;
        bytes32 publication;
        bytes32 governingForm;
        address provider;
        address coordinator;
        address alternativeContact;
        address leadAcademicTutor;
        address namedReviewer;
        address escalationContact;
        uint64 replyDate;
        uint64 replyPeriod;
        uint64 replyLegalDeadline;
        uint64 reviewDeadline;
        uint64 reviewLegalDeadline;
    }

    struct PublishedContacts {
        ReviewTerms terms;
        uint256 packageId;
        uint256 evidenceId;
        bytes32 publisherAuthority;
        uint64 publishedAt;
    }

    struct ConcernInput {
        bytes32 termsId;
        bytes32 concernRef;
        bytes32 obligationId;
        address receiver;
        ConcernSubject subject;
        AlternativeGround alternativeGround;
        bytes32 claim;
        bytes32 subjectRef;
        address[] parties;
    }

    struct Intake {
        address raisedBy;
        address receiver;
        ConcernSubject subject;
        AlternativeGround alternativeGround;
        uint64 receivedAt;
        bytes32 claim;
        bytes32 subjectRef;
        bytes32 partiesHash;
        uint256 evidenceId;
    }

    struct Notice {
        bytes32 referenceHash;
        uint64 sentAt;
    }

    struct AcknowledgmentInput {
        address handler;
        uint64 replyDeadline;
        address escalationContact;
        Notice notice;
    }

    struct Acknowledgment {
        AcknowledgmentInput input;
        bytes32 authorityId;
        uint256 evidenceId;
        uint64 recordedAt;
    }

    struct ReplyInput {
        uint64 checkedAt;
        bytes32 factCheck;
        bytes32 outcome;
        bytes32 reasons;
        uint256 reviewEvidenceId;
        Notice notice;
    }

    struct ReplyRecord {
        ReplyInput input;
        address handler;
        bytes32 authorityId;
        uint256 evidenceId;
        uint64 recordedAt;
    }

    enum AppointmentPurpose {
        ConcernHandling,
        InitialDecision,
        IndependentReview
    }

    struct AppointmentInput {
        AppointmentPurpose purpose;
        address handler;
        bytes32 handlerAuthorityId;
        address recusedActor;
        Notice disclosure;
    }

    struct Appointment {
        AppointmentInput input;
        address appointedBy;
        bytes32 authorityId;
        uint256 evidenceId;
        uint64 appointedAt;
    }

    enum DisputedFinding {
        AbsenceReason,
        Fault,
        OtherDisputedFact
    }

    struct InitialInput {
        DisputedFinding issue;
        bytes32 outcome;
        bytes32 reasons;
        bytes32 support;
    }

    struct InitialFinding {
        InitialInput input;
        address decider;
        bytes32 authorityId;
        uint256 evidenceId;
        uint64 decidedAt;
    }

    struct OriginalInput {
        bytes32 termsId;
        bytes32 concernRef;
        bytes32 obligationId;
        bytes32 paymentCommitment;
        address decider;
        uint64 decidedAt;
        bytes32 outcome;
        address[] parties;
    }

    struct OriginalOutcome {
        address decider;
        uint64 decidedAt;
        bytes32 outcome;
        bytes32 paymentCommitment;
        bytes32 partiesHash;
        address retainedBy;
        bytes32 authorityId;
        uint256 evidenceId;
        uint64 retainedAt;
    }

    enum ReviewDisposition {
        None,
        Affirmed,
        CorrectionRequired,
        Withdrawn,
        EvidenceUnavailable
    }

    struct ReviewInput {
        ReviewDisposition disposition;
        bytes32 outcome;
        bytes32 reasons;
        uint256 approvalRequestId;
    }

    struct ReviewFinding {
        ReviewInput input;
        address reviewer;
        bytes32 authorityId;
        uint256 evidenceId;
        uint64 decidedAt;
    }

    enum EscalationKind {
        Reply,
        RequestedReview,
        HeldReview
    }

    enum DeadlineProgress {
        NotTriggered,
        Pending,
        Overdue,
        CompletedOnTime,
        CompletedLate,
        CompletedAtUnverifiedCutoff
    }

    struct EscalationInput {
        EscalationKind kind;
        bytes32 holdId;
        address assignedTo;
        bytes32 assignedAuthorityId;
        uint64 takenOverAt;
        uint64 assignedAt;
        uint64 newActionDate;
        bytes32 progress;
        Notice notice;
    }

    struct Escalation {
        EscalationInput input;
        address takenOverBy;
        bytes32 authorityId;
        uint256 evidenceId;
        uint64 recordedAt;
    }

    struct ConcernRecord {
        bytes32 termsId;
        bytes32 lessonId;
        bytes32 concernRef;
        bytes32 obligationId;
        uint64 replyCutoff;
        uint64 reviewCutoff;
        Intake intake;
        Acknowledgment acknowledgment;
        uint64 firstReplyAt;
        uint64 reviewRequestedAt;
        uint64 appointmentRequiredAt;
    }

    struct ConcernContext {
        bytes32 termsId;
        bytes32 lessonId;
        bytes32 obligationId;
        bytes32 partiesHash;
        address raisedBy;
        address handler;
        uint64 receivedAt;
        uint64 appointmentRequiredAt;
        uint256 evidenceId;
    }

    struct CaseRecord {
        InitialFinding initial;
        OriginalOutcome original;
        ReviewFinding review;
        Notice adoptionNotice;
        bytes32 adoptionAuthorityId;
    }

    error InvalidTerms();
    error InvalidCase();
    error InvalidEvidence();
    error ConflictedCaseActor();

    SparkV15Payments internal immutable PAYMENTS;
    AVAEvidenceRegistry internal immutable EVIDENCE_REGISTRY;
    bytes32 internal immutable WORKFLOW;
    bytes32 private immutable EVIDENCE_ROLE;
    address private immutable REVIEW_DOMAIN;

    constructor(SparkV15Payments payments, bytes32 evidenceRole, address reviewDomain) {
        if (address(payments).code.length == 0 || evidenceRole == bytes32(0)) revert InvalidTerms();
        PAYMENTS = payments;
        EVIDENCE_REGISTRY = payments.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        WORKFLOW = payments.WORKFLOW();
        EVIDENCE_ROLE = evidenceRole;
        REVIEW_DOMAIN = reviewDomain;
    }

    function _caseIdFor(bytes32 lessonId, bytes32 concernRef) internal pure returns (bytes32) {
        return keccak256(abi.encode(lessonId, concernRef));
    }

    function _evidenceCommitment(bytes32 subject, bytes32 action, address actor, bytes32 payload)
        internal
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.review.evidence"), block.chainid, REVIEW_DOMAIN, subject, action, actor, payload
            )
        );
    }

    function _available(uint256 evidenceId, uint256 packageId) internal view returns (bool) {
        return evidenceId != 0 && EVIDENCE_REGISTRY.isEvidenceAvailableForPackage(evidenceId, packageId);
    }

    function _requireAuthority(address actor, bytes32 action, bytes32 authorityId) internal view {
        AVAIdentityRegistry.SubjectContext memory authority =
            EVIDENCE_REGISTRY.IDENTITY_REGISTRY().requireActiveSubjectContext(authorityId, SparkV15.APP_ID);
        EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(actor, SparkV15.APP_ID, authority.roleKey, action, authorityId);
    }

    function _requireNotice(Notice calldata notice, uint64 earliest) internal view {
        if (notice.referenceHash == bytes32(0) || notice.sentAt < earliest || notice.sentAt > block.timestamp) {
            revert InvalidCase();
        }
    }

    function _requireEvidence(uint256 evidenceId, uint256 packageId, bytes32 subject, bytes32 action, bytes32 payload)
        internal
        view
    {
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        AVAEvidenceRegistry.EvidenceReference memory evidence = EVIDENCE_REGISTRY.getEvidenceReference(evidenceId);
        AVAIdentityRegistry.SubjectContext memory source =
            EVIDENCE_REGISTRY.IDENTITY_REGISTRY().getSubjectContext(evidence.authorityId);
        if (
            source.roleKey != EVIDENCE_ROLE || source.appId != SparkV15.APP_ID
                || evidence.commitment != _evidenceCommitment(subject, action, msg.sender, payload)
        ) revert InvalidEvidence();
    }

    function _earlier(uint64 agreed, uint64 legal) internal pure returns (uint64) {
        return legal != 0 && legal < agreed ? legal : agreed;
    }
}

/// @notice Published contact routes, participant complaints and their handling history.
contract SparkV15ConcernIntake is SparkV15ReviewContext {
    event ContactsPublished(bytes32 indexed termsId, bytes32 indexed lessonId, uint256 indexed evidenceId);
    event ConcernReceived(bytes32 indexed caseId, bytes32 indexed obligationId, uint256 indexed evidenceId);
    event ConcernAcknowledged(bytes32 indexed caseId, address indexed handler, uint256 indexed evidenceId);
    event ConcernReplyRecorded(bytes32 indexed caseId, uint256 indexed index, uint256 indexed evidenceId);
    event DecisionNeedRecorded(bytes32 indexed caseId, address indexed actor, uint256 indexed evidenceId);
    event ReviewRequested(bytes32 indexed caseId, address indexed party, bytes32 grounds);
    event CaseEscalated(bytes32 indexed caseId, uint256 indexed index, uint256 indexed evidenceId);

    SparkV15ReviewCases public immutable REVIEW_CASES;

    mapping(bytes32 => PublishedContacts) private publications;
    mapping(bytes32 => ConcernRecord) private concerns;
    mapping(bytes32 => mapping(address => bool)) private concernParties;
    mapping(bytes32 => ReplyRecord[]) private replies;
    mapping(bytes32 => mapping(bytes32 => bool)) private recordedReplies;
    mapping(uint256 => bool) private decisionNeedRecorded;
    mapping(bytes32 => Escalation[]) private escalations;
    mapping(bytes32 => mapping(bytes32 => bool)) private recordedEscalations;

    constructor(SparkV15Payments payments, bytes32 evidenceRole, SparkV15ReviewCases reviewCases)
        SparkV15ReviewContext(payments, evidenceRole, address(reviewCases))
    {
        REVIEW_CASES = reviewCases;
    }

    function caseContext(bytes32 caseId) external view returns (ConcernContext memory) {
        ConcernRecord storage item = concerns[caseId];
        return ConcernContext({
            termsId: item.termsId,
            lessonId: item.lessonId,
            obligationId: item.obligationId,
            partiesHash: item.intake.partiesHash,
            raisedBy: item.intake.raisedBy,
            handler: item.acknowledgment.input.handler,
            receivedAt: item.intake.receivedAt,
            appointmentRequiredAt: item.appointmentRequiredAt,
            evidenceId: item.intake.evidenceId
        });
    }

    function requireMaterialCaseDisinterest(bytes32 caseId, address actor) external view {
        ConcernRecord storage item = concerns[caseId];
        Intake storage filed = item.intake;
        if (
            filed.evidenceId != 0
                && (filed.subject != ConcernSubject.RevenueShare && filed.subject != ConcernSubject.MaterialOmission)
        ) return;

        address provisions = PAYMENTS.FUNDS().materialProvisions();
        if (provisions == address(0)) return;
        PublishedContacts storage publication = publications[item.termsId];
        bytes32 omissionForm =
            filed.subject == ConcernSubject.MaterialOmission ? publication.terms.governingForm : bytes32(0);
        (bool recognised, bool interested) = ISparkV15CaseMaterialProvisions(provisions)
            .caseChargeInterest(caseId, item.lessonId, filed.subjectRef, item.obligationId, omissionForm, actor);
        if (!recognised) return;
        if (filed.evidenceId != 0 && !_available(filed.evidenceId, publication.packageId)) revert InvalidEvidence();
        if (interested) revert ConflictedCaseActor();
    }

    function retainReviewMatter(bytes32 termsId, bytes32 concernRef, bytes32 obligationId) external {
        if (msg.sender != address(REVIEW_CASES)) revert InvalidCase();
        ReviewTerms storage terms = publications[termsId].terms;
        bytes32 caseId = _caseIdFor(terms.lessonId, concernRef);
        _retainCase(concerns[caseId], termsId, concernRef, obligationId, terms);
    }

    function publishContacts(ReviewTerms calldata terms, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 termsId)
    {
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, authorityId);
        termsId = keccak256(abi.encode(terms));
        if (
            terms.lessonId == bytes32(0) || terms.publication == bytes32(0) || terms.provider != msg.sender
                || terms.coordinator == address(0) || terms.alternativeContact == address(0)
                || terms.alternativeContact == terms.coordinator || terms.leadAcademicTutor == address(0)
                || terms.escalationContact == address(0) || (terms.replyDate == 0) == (terms.replyPeriod == 0)
                || terms.reviewDeadline == 0 || (terms.namedReviewer != address(0) && terms.governingForm == bytes32(0))
                || publications[termsId].packageId != 0
        ) revert InvalidTerms();

        uint256 packageId = EVIDENCE_REGISTRY.RULE_PACKAGE_REGISTRY().getActivePackageId(SparkV15.APP_ID, WORKFLOW);
        _requireEvidence(evidenceId, packageId, termsId, SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, termsId);
        publications[termsId] = PublishedContacts(terms, packageId, evidenceId, authorityId, uint64(block.timestamp));
        emit ContactsPublished(termsId, terms.lessonId, evidenceId);
    }

    function receiveConcern(ConcernInput calldata input, uint256 evidenceId) external returns (bytes32 caseId) {
        return _receiveConcern(input, evidenceId, uint64(block.timestamp), keccak256(abi.encode(input)));
    }

    /// @notice Records verified receipt through the published channel at an earlier business time.
    function receiveConcernAt(ConcernInput calldata input, uint64 receivedAt, bytes32 receiptRef, uint256 evidenceId)
        external
        returns (bytes32 caseId)
    {
        if (receiptRef == bytes32(0) || receivedAt >= block.timestamp) revert InvalidCase();
        return _receiveConcern(input, evidenceId, receivedAt, keccak256(abi.encode(input, receivedAt, receiptRef)));
    }

    function _receiveConcern(ConcernInput calldata input, uint256 evidenceId, uint64 receivedAt, bytes32 payload)
        private
        returns (bytes32 caseId)
    {
        PublishedContacts storage publication = publications[input.termsId];
        ReviewTerms storage terms = publication.terms;
        caseId = _caseIdFor(terms.lessonId, input.concernRef);
        ConcernRecord storage item = concerns[caseId];
        if (
            publication.packageId == 0 || receivedAt < publication.publishedAt
                || input.concernRef == bytes32(0) || item.intake.evidenceId != 0
                || input.claim == bytes32(0) || input.parties.length == 0
                || ((input.subject <= ConcernSubject.StudentPayment || input.subject == ConcernSubject.MaterialOmission)
                    && input.subjectRef == bytes32(0))
                || (input.receiver == terms.coordinator && input.alternativeGround != AlternativeGround.None)
                || (input.receiver != terms.coordinator
                    && (input.receiver != terms.alternativeContact
                        || input.alternativeGround == AlternativeGround.None))
        ) revert InvalidCase();
        _requireEvidence(
            evidenceId,
            publication.packageId,
            caseId,
            SparkV15ReviewActions.ACTION_RECEIVE_CONCERN,
            payload
        );
        REVIEW_CASES.requirePaymentScope(terms.lessonId, publication.packageId, input.obligationId);
        _retainCase(item, input.termsId, input.concernRef, input.obligationId, terms);

        uint64 replyDeadline = terms.replyPeriod == 0 ? terms.replyDate : receivedAt + terms.replyPeriod;
        item.replyCutoff = _earlier(replyDeadline, terms.replyLegalDeadline);
        item.intake = Intake({
            raisedBy: msg.sender,
            receiver: input.receiver,
            subject: input.subject,
            alternativeGround: input.alternativeGround,
            receivedAt: receivedAt,
            claim: input.claim,
            subjectRef: input.subjectRef,
            partiesHash: keccak256(abi.encode(input.parties)),
            evidenceId: evidenceId
        });
        for (uint256 i; i < input.parties.length; ++i) {
            if (input.parties[i] == address(0)) revert InvalidCase();
            concernParties[caseId][input.parties[i]] = true;
        }
        emit ConcernReceived(caseId, input.obligationId, evidenceId);
    }

    function isPaymentConcern(bytes32 caseId, bytes32 lessonId, bytes32 obligationId) external view returns (bool) {
        ConcernRecord storage item = concerns[caseId];
        return obligationId != bytes32(0) && item.intake.evidenceId != 0 && item.obligationId == obligationId
            && item.lessonId == lessonId;
    }

    /// @dev Evidence payload is keccak256(abi.encode(input, filer)).
    function acknowledge(bytes32 caseId, AcknowledgmentInput calldata input, uint256 evidenceId, bytes32 authorityId)
        external
    {
        ConcernRecord storage item = concerns[caseId];
        PublishedContacts storage publication = publications[item.termsId];
        if (
            item.intake.evidenceId == 0 || item.intake.receiver != msg.sender || item.acknowledgment.evidenceId != 0
                || input.handler == address(0) || input.replyDeadline != item.replyCutoff
                || input.escalationContact != publication.terms.escalationContact
        ) revert InvalidCase();
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_ACKNOWLEDGE_CONCERN, authorityId);
        _requireNotice(input.notice, item.intake.receivedAt);
        _requireEvidence(
            evidenceId,
            publication.packageId,
            caseId,
            SparkV15ReviewActions.ACTION_ACKNOWLEDGE_CONCERN,
            keccak256(abi.encode(input, item.intake.raisedBy))
        );
        item.acknowledgment = Acknowledgment(input, authorityId, evidenceId, uint64(block.timestamp));
        emit ConcernAcknowledged(caseId, input.handler, evidenceId);
    }

    /// @dev Evidence payload is keccak256(abi.encode(input, concernPartiesHash)).
    function reply(bytes32 caseId, ReplyInput calldata input, uint256 evidenceId, bytes32 authorityId) external {
        ConcernRecord storage item = concerns[caseId];
        Acknowledgment storage acknowledgment = item.acknowledgment;
        bytes32 replyHash = keccak256(abi.encode(msg.sender, input.notice, input.outcome, input.reasons));
        if (
            acknowledgment.evidenceId == 0 || input.factCheck == bytes32(0) || input.outcome == bytes32(0)
                || input.reasons == bytes32(0) || input.checkedAt < item.intake.receivedAt
                || input.checkedAt > input.notice.sentAt || recordedReplies[caseId][replyHash]
        ) revert InvalidCase();
        if (input.reviewEvidenceId != 0) {
            ReviewFinding memory review = REVIEW_CASES.getReview(caseId);
            if (
                input.reviewEvidenceId != review.evidenceId || review.reviewer != msg.sender
                    || review.input.outcome != input.outcome || review.input.reasons != input.reasons
                    || input.checkedAt > review.decidedAt || review.decidedAt > input.notice.sentAt
            ) revert InvalidCase();
        }
        if (
            ((item.appointmentRequiredAt != 0 && item.appointmentRequiredAt <= input.notice.sentAt)
                    || acknowledgment.input.handler != msg.sender)
                && !REVIEW_CASES.isAppointedForCase(
                    caseId, AppointmentPurpose.ConcernHandling, msg.sender, input.checkedAt, true
                )
        ) {
            revert InvalidCase();
        }
        REVIEW_CASES.requireDisinterested(caseId, msg.sender, input.checkedAt);
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN, authorityId);
        _requireNotice(input.notice, acknowledgment.input.notice.sentAt);
        _requireEvidence(
            evidenceId,
            publications[item.termsId].packageId,
            caseId,
            SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN,
            keccak256(abi.encode(input, item.intake.partiesHash))
        );

        uint256 index = replies[caseId].length;
        replies[caseId].push(ReplyRecord(input, msg.sender, authorityId, evidenceId, uint64(block.timestamp)));
        recordedReplies[caseId][replyHash] = true;
        if (item.firstReplyAt == 0 || input.notice.sentAt < item.firstReplyAt) item.firstReplyAt = input.notice.sentAt;
        emit ConcernReplyRecorded(caseId, index, evidenceId);
    }

    /// @dev Evidence payload is the commitment to the verified grounds that require a decision.
    function recordDecisionNeeded(bytes32 caseId, bytes32 grounds, uint256 evidenceId, bytes32 authorityId) external {
        ConcernRecord storage item = concerns[caseId];
        if (item.intake.evidenceId == 0 || grounds == bytes32(0) || decisionNeedRecorded[evidenceId]) {
            revert InvalidCase();
        }
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_REQUIRE_CASE_APPOINTMENT, authorityId);
        _requireEvidence(
            evidenceId,
            publications[item.termsId].packageId,
            caseId,
            SparkV15ReviewActions.ACTION_REQUIRE_CASE_APPOINTMENT,
            grounds
        );
        if (item.appointmentRequiredAt == 0) item.appointmentRequiredAt = uint64(block.timestamp);
        decisionNeedRecorded[evidenceId] = true;
        emit DecisionNeedRecorded(caseId, msg.sender, evidenceId);
    }

    function requestReview(bytes32 caseId, bytes32 grounds) external {
        ConcernRecord storage item = concerns[caseId];
        (uint64 reviewedAt,) = REVIEW_CASES.reviewHistory(caseId);
        if (
            item.intake.evidenceId == 0 || grounds == bytes32(0) || item.reviewRequestedAt != 0 || reviewedAt != 0
                || (item.intake.raisedBy != msg.sender && !concernParties[caseId][msg.sender])
        ) revert InvalidCase();
        if (item.appointmentRequiredAt == 0) item.appointmentRequiredAt = uint64(block.timestamp);
        item.reviewRequestedAt = uint64(block.timestamp);
        emit ReviewRequested(caseId, msg.sender, grounds);
    }

    /// @dev Evidence payload is keccak256(abi.encode(input, concernPartiesHash, originalPartiesHash)).
    function escalate(bytes32 caseId, EscalationInput calldata input, uint256 evidenceId, bytes32 authorityId)
        external
    {
        ConcernRecord storage item = concerns[caseId];
        PublishedContacts storage publication = publications[item.termsId];
        (uint64 reviewedAt, bytes32 originalPartiesHash) = REVIEW_CASES.reviewHistory(caseId);
        bytes32 payload = keccak256(abi.encode(input, item.intake.partiesHash, originalPartiesHash));
        if (
            item.termsId == bytes32(0) || msg.sender != publication.terms.escalationContact
                || input.assignedTo == address(0) || input.progress == bytes32(0)
                || input.assignedAt < input.takenOverAt || input.assignedAt > input.newActionDate
                || input.assignedAt > block.timestamp || recordedEscalations[caseId][payload]
        ) revert InvalidCase();
        _requireNotice(input.notice, input.takenOverAt);
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_ESCALATE_CASE, authorityId);
        _requireOverdue(caseId, item, publication.terms, input, reviewedAt);
        if (input.kind == EscalationKind.Reply) {
            REVIEW_CASES.requireDisinterested(caseId, input.assignedTo, input.assignedAt);
            _requireAuthority(
                input.assignedTo, SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN, input.assignedAuthorityId
            );
        } else {
            REVIEW_CASES.requireIndependentReviewer(caseId, input.assignedTo);
            _requireAuthority(input.assignedTo, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, input.assignedAuthorityId);
        }
        _requireEvidence(evidenceId, publication.packageId, caseId, SparkV15ReviewActions.ACTION_ESCALATE_CASE, payload);

        uint256 index = escalations[caseId].length;
        escalations[caseId].push(Escalation(input, msg.sender, authorityId, evidenceId, uint64(block.timestamp)));
        recordedEscalations[caseId][payload] = true;
        emit CaseEscalated(caseId, index, evidenceId);
    }

    function _requireOverdue(
        bytes32 caseId,
        ConcernRecord storage item,
        ReviewTerms storage terms,
        EscalationInput calldata input,
        uint64 reviewedAt
    ) private view {
        uint64 triggerAt;
        uint64 completeAt;
        uint64 cutoff;
        if (input.kind == EscalationKind.Reply) {
            triggerAt = item.intake.receivedAt;
            completeAt = item.firstReplyAt;
            cutoff = item.replyCutoff;
        } else {
            completeAt = reviewedAt;
            cutoff = item.reviewCutoff;
            if (input.kind == EscalationKind.RequestedReview) {
                triggerAt = item.reviewRequestedAt;
            } else {
                if (terms.governingForm == bytes32(0)) revert InvalidCase();
                triggerAt = REVIEW_CASES.heldReviewStartedAt(caseId, item.obligationId, input.holdId, input.takenOverAt);
            }
        }
        if (
            (input.kind != EscalationKind.HeldReview && input.holdId != bytes32(0)) || triggerAt == 0
                || triggerAt > input.takenOverAt || cutoff == 0 || cutoff >= input.takenOverAt
                || (completeAt >= triggerAt && completeAt <= input.takenOverAt)
        ) revert InvalidCase();
    }

    function getConcern(bytes32 caseId) external view returns (ConcernRecord memory) {
        return concerns[caseId];
    }

    function getReply(bytes32 caseId, uint256 index) external view returns (ReplyRecord memory) {
        return replies[caseId][index];
    }

    function getEscalation(bytes32 caseId, uint256 index) external view returns (Escalation memory) {
        return escalations[caseId][index];
    }

    function getProgress(bytes32 caseId)
        external
        view
        returns (DeadlineProgress replyProgress, DeadlineProgress reviewProgress)
    {
        ConcernRecord storage item = concerns[caseId];
        replyProgress = _deadlineProgress(item.intake.receivedAt, item.replyCutoff, item.firstReplyAt);
        (uint64 reviewedAt,) = REVIEW_CASES.reviewHistory(caseId);
        reviewProgress = _deadlineProgress(item.reviewRequestedAt, item.reviewCutoff, reviewedAt);
    }

    function getPublishedContacts(bytes32 termsId) external view returns (PublishedContacts memory) {
        return publications[termsId];
    }

    function _retainCase(
        ConcernRecord storage item,
        bytes32 termsId,
        bytes32 concernRef,
        bytes32 obligationId,
        ReviewTerms storage terms
    ) private {
        if (item.termsId != bytes32(0)) {
            if (item.termsId != termsId || item.obligationId != obligationId) revert InvalidCase();
            return;
        }
        item.termsId = termsId;
        item.lessonId = terms.lessonId;
        item.concernRef = concernRef;
        item.obligationId = obligationId;
        item.reviewCutoff = _earlier(terms.reviewDeadline, terms.reviewLegalDeadline);
    }

    function _deadlineProgress(uint64 triggeredAt, uint64 cutoff, uint64 completedAt)
        private
        view
        returns (DeadlineProgress)
    {
        if (completedAt != 0) {
            if (completedAt < cutoff) return DeadlineProgress.CompletedOnTime;
            if (completedAt > cutoff) return DeadlineProgress.CompletedLate;
            return DeadlineProgress.CompletedAtUnverifiedCutoff;
        }
        if (triggeredAt == 0) return DeadlineProgress.NotTriggered;
        return block.timestamp > cutoff ? DeadlineProgress.Overdue : DeadlineProgress.Pending;
    }
}

/// @notice Independent findings and adoption for the stable Spark v1.5 review case.
contract SparkV15ReviewCases is SparkV15ReviewContext {
    struct AdoptedDisposition {
        bytes32 lessonId;
        bytes32 obligationId;
        bytes32 originalOutcome;
        bytes32 originalPaymentCommitment;
        bytes32 outcome;
        uint64 reviewedAt;
        uint64 adoptedAt;
        uint256 originalEvidenceId;
        uint256 reviewEvidenceId;
        uint256 adoptionEvidenceId;
    }

    event CaseActorAppointed(
        bytes32 indexed caseId, AppointmentPurpose indexed purpose, uint256 indexed index, uint256 evidenceId
    );
    event InitialFindingRecorded(bytes32 indexed caseId, address indexed decider, uint256 indexed evidenceId);
    event OriginalOutcomeRetained(bytes32 indexed caseId, address indexed decider, uint256 indexed evidenceId);
    event IndependentReviewRecorded(
        bytes32 indexed caseId, address indexed reviewer, ReviewDisposition disposition, uint256 evidenceId
    );
    event CorrectionAdopted(
        bytes32 indexed caseId, uint256 indexed reviewEvidenceId, uint256 indexed adoptionEvidenceId
    );

    SparkV15ConcernIntake public INTAKE;

    uint256 private constant APPOINTED_BEFORE_RECEIPT = 1;
    uint256 private constant APPOINTED_AFTER_RECEIPT = 2;

    mapping(bytes32 => CaseRecord) private cases;
    mapping(bytes32 => AdoptedDisposition) private adoptedDispositions;
    mapping(bytes32 => bytes32) public reviewedPaymentRevision;
    mapping(bytes32 => bytes32) private adoptedRevision;
    mapping(bytes32 => mapping(AppointmentPurpose => Appointment[])) private appointments;
    mapping(bytes32 => mapping(address => uint64)) private recusals;
    mapping(uint256 => uint256) private appointmentEvidenceUse;

    constructor(SparkV15Payments payments, bytes32 evidenceRole)
        SparkV15ReviewContext(payments, evidenceRole, address(this))
    {}

    function bindIntake(SparkV15ConcernIntake intake) external {
        PAYMENTS.REQUEST_ALLOCATION().IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
        if (address(INTAKE) != address(0) || address(intake.REVIEW_CASES()) != address(this)) revert InvalidCase();
        INTAKE = intake;
    }

    function caseIdFor(bytes32 lessonId, bytes32 concernRef) external pure returns (bytes32) {
        return _caseIdFor(lessonId, concernRef);
    }

    function evidenceCommitment(bytes32 subject, bytes32 action, address actor, bytes32 payload)
        external
        view
        returns (bytes32)
    {
        return _evidenceCommitment(subject, action, actor, payload);
    }

    function isPaymentConcern(bytes32 caseId, bytes32 lessonId, bytes32 obligationId) external view returns (bool) {
        return INTAKE.isPaymentConcern(caseId, lessonId, obligationId);
    }

    function requirePaymentScope(bytes32 lessonId, uint256 packageId, bytes32 obligationId)
        public
        view
        returns (bytes32)
    {
        if (obligationId == bytes32(0)) return bytes32(0);
        return _paymentChecks().paymentScope(PAYMENTS, lessonId, packageId, obligationId);
    }

    function heldReviewStartedAt(bytes32 caseId, bytes32 obligationId, bytes32 holdId, uint64 observedAt)
        external
        view
        returns (uint64)
    {
        return PAYMENTS.HOLDS().heldReviewStartedAt(caseId, obligationId, holdId, observedAt);
    }

    function getReview(bytes32 caseId) external view returns (ReviewFinding memory) {
        return cases[caseId].review;
    }

    function reviewHistory(bytes32 caseId) external view returns (uint64 decidedAt, bytes32 originalPartiesHash) {
        CaseRecord storage item = cases[caseId];
        return (item.review.decidedAt, item.original.partiesHash);
    }

    function originalRetainedAt(bytes32 caseId) external view returns (uint64) {
        return cases[caseId].original.retainedAt;
    }

    function requireDisinterested(bytes32 caseId, address actor, uint64 atTime) external view {
        _requireDisinterested(caseId, INTAKE.caseContext(caseId), actor, atTime);
    }

    function requireIndependentReviewer(bytes32 caseId, address actor) external view {
        _requireIndependentReviewer(caseId, INTAKE.caseContext(caseId), actor);
    }

    /// @dev Evidence attests the appointee's disinterest at appointment and, for recusal, disclosure
    /// to the case parties. The payload is keccak256(abi.encode(input, concernPartiesHash)).
    function appoint(bytes32 caseId, AppointmentInput calldata input, uint256 evidenceId, bytes32 authorityId)
        external
    {
        (ConcernContext memory context, PublishedContacts memory publication) = _publishedCase(caseId);
        if (
            context.termsId == bytes32(0) || input.handler == address(0) || input.handler == input.recusedActor
                || appointmentEvidenceUse[evidenceId] != 0
        ) {
            revert InvalidCase();
        }
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR, authorityId);
        _requireAuthority(input.handler, _appointmentAction(input.purpose), input.handlerAuthorityId);
        if (input.purpose == AppointmentPurpose.IndependentReview) {
            _requireIndependentReviewer(caseId, context, input.handler);
        } else {
            _requireDisinterested(caseId, context, input.handler, uint64(block.timestamp));
            if (input.purpose == AppointmentPurpose.InitialDecision) {
                _requireNotTemporarySetter(caseId, context, input.handler);
            }
        }
        _requireMaterialCaseDisinterest(caseId, input.handler);

        Appointment[] storage history = appointments[caseId][input.purpose];
        if (input.recusedActor != address(0)) {
            address previous = _defaultAppointee(context, publication.terms, input.purpose);
            if (history.length != 0) previous = history[history.length - 1].input.handler;
            if (input.recusedActor != previous) revert InvalidCase();
            _requireNotice(input.disclosure, context.receivedAt);
            recusals[caseId][input.recusedActor] = input.disclosure.sentAt;
        } else if (input.disclosure.referenceHash != bytes32(0) || input.disclosure.sentAt != 0) {
            revert InvalidCase();
        }
        _requireEvidence(
            evidenceId,
            publication.packageId,
            caseId,
            SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR,
            keccak256(
                abi.encode(
                    input, context.partiesHash == bytes32(0) ? cases[caseId].original.partiesHash : context.partiesHash
                )
            )
        );

        uint256 index = history.length;
        history.push(Appointment(input, msg.sender, authorityId, evidenceId, uint64(block.timestamp)));
        // One receipt per case. Capture whether it already existed, since the two actions can share a timestamp.
        appointmentEvidenceUse[evidenceId] =
            context.evidenceId == 0 ? APPOINTED_BEFORE_RECEIPT : APPOINTED_AFTER_RECEIPT;
        emit CaseActorAppointed(caseId, input.purpose, index, evidenceId);
    }

    /// @dev Evidence attests the finding, the current disinterest check and any admitted decision support.
    /// A fault assessment requires substantive evidence beyond silence, refusal or the filing itself.
    function decideInitial(bytes32 caseId, InitialInput calldata input, uint256 evidenceId, bytes32 authorityId)
        external
    {
        (ConcernContext memory context, PublishedContacts memory publication) = _publishedCase(caseId);
        CaseRecord storage item = cases[caseId];
        address lead = publication.terms.leadAcademicTutor;
        if (
            publication.terms.governingForm == bytes32(0) || item.initial.evidenceId != 0 || input.outcome == bytes32(0)
                || input.reasons == bytes32(0)
                || (msg.sender != lead
                    && (recusals[caseId][lead] == 0
                        || !isAppointed(
                            caseId, AppointmentPurpose.InitialDecision, msg.sender, uint64(block.timestamp)
                        )))
        ) revert InvalidCase();
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, authorityId);
        _requireDisinterested(caseId, context, msg.sender, uint64(block.timestamp));
        _requireNotTemporarySetter(caseId, context, msg.sender);
        _requireMaterialCaseDisinterest(caseId, msg.sender);
        _requireEvidence(
            evidenceId,
            publication.packageId,
            caseId,
            SparkV15ReviewActions.ACTION_DECIDE_INITIAL,
            keccak256(abi.encode(input))
        );
        item.initial = InitialFinding(input, msg.sender, authorityId, evidenceId, uint64(block.timestamp));
        emit InitialFindingRecorded(caseId, msg.sender, evidenceId);
    }

    /// @dev The original can establish a review matter before a complaint or any Allocation exists.
    /// Evidence payload is keccak256(abi.encode(input)).
    function retainOriginal(OriginalInput calldata input, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 caseId)
    {
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, authorityId);
        PublishedContacts memory publication = INTAKE.getPublishedContacts(input.termsId);
        ReviewTerms memory terms = publication.terms;
        caseId = _caseIdFor(terms.lessonId, input.concernRef);
        CaseRecord storage item = cases[caseId];
        if (
            publication.packageId == 0 || input.concernRef == bytes32(0) || input.decider == address(0)
                || input.decidedAt == 0 || input.decidedAt > block.timestamp || input.outcome == bytes32(0)
                || input.parties.length == 0 || item.original.evidenceId != 0 || item.review.decidedAt != 0
                || input.paymentCommitment
                    != requirePaymentScope(terms.lessonId, publication.packageId, input.obligationId)
        ) revert InvalidCase();
        _requireEvidence(
            evidenceId,
            publication.packageId,
            caseId,
            SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL,
            keccak256(abi.encode(input))
        );
        INTAKE.retainReviewMatter(input.termsId, input.concernRef, input.obligationId);
        item.original = OriginalOutcome({
            decider: input.decider,
            decidedAt: input.decidedAt,
            outcome: input.outcome,
            paymentCommitment: input.paymentCommitment,
            partiesHash: keccak256(abi.encode(input.parties)),
            retainedBy: msg.sender,
            authorityId: authorityId,
            evidenceId: evidenceId,
            retainedAt: uint64(block.timestamp)
        });
        emit OriginalOutcomeRetained(caseId, input.decider, evidenceId);
    }

    /// @dev Merits and evidenced neutral dispositions use keccak256(abi.encode(input)).
    /// An unavailable-source disposition uses the registry's own lifecycle checks.
    function decideReview(bytes32 caseId, ReviewInput calldata input, uint256 evidenceId, bytes32 authorityId) public {
        (ConcernContext memory context, PublishedContacts memory publication) = _publishedCase(caseId);
        CaseRecord storage item = cases[caseId];
        uint64 decidedAt = uint64(block.timestamp);
        if (
            context.termsId == bytes32(0) || item.review.decidedAt != 0 || input.disposition == ReviewDisposition.None
                || input.reasons == bytes32(0)
        ) revert InvalidCase();
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, authorityId);
        _requireIndependentReviewer(caseId, context, msg.sender);
        if (
            (context.appointmentRequiredAt != 0 || msg.sender != publication.terms.namedReviewer)
                && !isAppointedForCase(
                    caseId, AppointmentPurpose.IndependentReview, msg.sender, decidedAt, context.appointmentRequiredAt != 0
                )
        ) revert InvalidCase();
        bool merits = input.disposition == ReviewDisposition.Affirmed
            || input.disposition == ReviewDisposition.CorrectionRequired;
        if (merits) _requireMaterialCaseDisinterest(caseId, msg.sender);
        bool available = _reviewSourceAvailable(item, context.evidenceId, publication.packageId);
        if (merits != (input.outcome != bytes32(0)) || (merits && !available)) revert InvalidCase();
        if (input.disposition == ReviewDisposition.EvidenceUnavailable) {
            if (available || evidenceId != 0) revert InvalidCase();
        } else {
            _requireEvidence(
                evidenceId,
                publication.packageId,
                caseId,
                SparkV15ReviewActions.ACTION_DECIDE_REVIEW,
                keccak256(abi.encode(input))
            );
        }
        if (input.approvalRequestId != 0) {
            if (input.disposition != ReviewDisposition.CorrectionRequired || item.original.evidenceId == 0) {
                revert InvalidCase();
            }
            _paymentChecks().requireApprovalStopReview(
                PAYMENTS, caseId, input.approvalRequestId, context.obligationId, input.outcome, msg.sender
            );
        }

        item.review = ReviewFinding(input, msg.sender, authorityId, evidenceId, decidedAt);
        emit IndependentReviewRecorded(caseId, msg.sender, input.disposition, evidenceId);
    }

    function _paymentChecks() private view returns (SparkV15PaymentApprovalChecks) {
        return PAYMENTS.HOLDS().APPROVAL_CHECKS();
    }

    function decidePaymentRevision(
        bytes32 caseId,
        ReviewInput calldata input,
        SparkV15Payments.PaymentRevision calldata revision,
        uint256 evidenceId,
        bytes32 authorityId
    ) external {
        if (
            input.approvalRequestId != 0 || input.disposition != ReviewDisposition.CorrectionRequired
                || revision.obligationId != INTAKE.caseContext(caseId).obligationId
                || input.outcome != _paymentChecks().reviewPaymentRevision(PAYMENTS, caseId, revision)
        ) revert InvalidCase();
        decideReview(caseId, input, evidenceId, authorityId);
        reviewedPaymentRevision[caseId] = input.outcome;
    }

    /// @dev Evidence payload is keccak256(abi.encode(notice, originalEvidenceId, reviewEvidenceId,
    /// originalPartiesHash, concernPartiesHash)). Notice attests delivery to both sets of parties.
    function adoptCorrection(bytes32 caseId, Notice calldata notice, uint256 evidenceId, bytes32 authorityId) external {
        if (cases[caseId].review.input.approvalRequestId != 0 || reviewedPaymentRevision[caseId] != bytes32(0)) {
            revert InvalidCase();
        }
        _adoptCorrection(caseId, notice, evidenceId, authorityId, bytes32(0));
    }

    function adoptApprovalStop(
        bytes32 caseId,
        Notice calldata notice,
        uint256 evidenceId,
        bytes32 authorityId,
        uint256 requestId
    ) external {
        if (requestId == 0 || cases[caseId].review.input.approvalRequestId != requestId) {
            revert InvalidCase();
        }
        _adoptCorrection(caseId, notice, evidenceId, authorityId, bytes32(0));
        PAYMENTS.stopApproval(caseId, requestId);
    }

    /// @dev For WAGE_RECEIPT_RECHECK_EVIDENCE, hash the original adoption payload together with
    /// the hash of the latest native receipt ID, the original and corrected beneficiaries' current
    /// net receipts, and the current-version effect. The revision input remains the reviewed one.
    function adoptPaymentRevision(
        bytes32 caseId,
        Notice calldata notice,
        uint256 evidenceId,
        bytes32 authorityId,
        SparkV15Payments.PaymentRevision calldata revision
    ) external {
        (bytes32 effect, bytes32 recheck) = _paymentChecks().paymentRevisionAtAdoption(
            PAYMENTS, caseId, revision, reviewedPaymentRevision[caseId], cases[caseId].review.decidedAt,
            notice.sentAt, evidenceId
        );
        _adoptCorrection(caseId, notice, evidenceId, authorityId, recheck);
        adoptedRevision[caseId] = effect;
        SparkV15Payments.PaymentRevision memory updated = revision;
        if (recheck != bytes32(0)) ++updated.expectedVersion;
        PAYMENTS.applyPaymentRevision(caseId, updated);
    }

    function _adoptCorrection(
        bytes32 caseId, Notice calldata notice, uint256 evidenceId, bytes32 authorityId, bytes32 recheck
    ) private {
        (ConcernContext memory context, PublishedContacts memory publication) = _publishedCase(caseId);
        CaseRecord storage item = cases[caseId];
        OriginalOutcome storage original = item.original;
        ReviewFinding storage review = item.review;
        if (
            msg.sender != publication.terms.coordinator || original.evidenceId == 0
                || review.input.disposition != ReviewDisposition.CorrectionRequired
                || adoptedDispositions[caseId].adoptedAt != 0 || original.decidedAt >= review.decidedAt
                || original.decider == review.reviewer || original.outcome == review.input.outcome
                || !_available(original.evidenceId, publication.packageId)
                || !_available(review.evidenceId, publication.packageId)
        ) revert InvalidCase();
        _requireAuthority(msg.sender, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, authorityId);
        _requireNotice(notice, review.decidedAt);
        bytes32 payload = keccak256(
            abi.encode(notice, original.evidenceId, review.evidenceId, original.partiesHash, context.partiesHash)
        );
        if (recheck != bytes32(0)) payload = keccak256(abi.encode(payload, recheck));
        _requireEvidence(evidenceId, publication.packageId, caseId, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, payload);
        item.adoptionNotice = notice;
        item.adoptionAuthorityId = authorityId;
        adoptedDispositions[caseId] = AdoptedDisposition({
            lessonId: context.lessonId,
            obligationId: context.obligationId,
            originalOutcome: original.outcome,
            originalPaymentCommitment: original.paymentCommitment,
            outcome: review.input.outcome,
            reviewedAt: review.decidedAt,
            adoptedAt: uint64(block.timestamp),
            originalEvidenceId: original.evidenceId,
            reviewEvidenceId: review.evidenceId,
            adoptionEvidenceId: evidenceId
        });
        emit CorrectionAdopted(caseId, review.evidenceId, evidenceId);
    }

    function getCase(bytes32 caseId) external view returns (CaseRecord memory) {
        return cases[caseId];
    }

    function getAppointment(bytes32 caseId, AppointmentPurpose purpose, uint256 index)
        external
        view
        returns (Appointment memory)
    {
        return appointments[caseId][purpose][index];
    }

    function getAdoptedDisposition(bytes32 caseId) external view returns (AdoptedDisposition memory) {
        return adoptedDispositions[caseId];
    }

    function adoptedPaymentEffect(bytes32 caseId)
        external
        view
        returns (bytes32 obligationId, bytes32 outcome, uint64 adoptedAt)
    {
        AdoptedDisposition storage result = adoptedDispositions[caseId];
        outcome = adoptedRevision[caseId];
        if (outcome == bytes32(0)) {
            if (cases[caseId].review.input.approvalRequestId == 0) return (bytes32(0), bytes32(0), 0);
            outcome = result.outcome;
        }
        return (result.obligationId, outcome, result.adoptedAt);
    }

    function reviewSourceAvailable(bytes32 caseId) external view returns (bool) {
        (ConcernContext memory context, PublishedContacts memory publication) = _publishedCase(caseId);
        return _reviewSourceAvailable(cases[caseId], context.evidenceId, publication.packageId);
    }

    function _publishedCase(bytes32 caseId)
        private
        view
        returns (ConcernContext memory context, PublishedContacts memory publication)
    {
        context = INTAKE.caseContext(caseId);
        publication = INTAKE.getPublishedContacts(context.termsId);
    }

    function _defaultAppointee(ConcernContext memory context, ReviewTerms memory terms, AppointmentPurpose purpose)
        private
        pure
        returns (address)
    {
        if (purpose == AppointmentPurpose.ConcernHandling) return context.handler;
        if (purpose == AppointmentPurpose.InitialDecision) return terms.leadAcademicTutor;
        return terms.namedReviewer;
    }

    function _appointmentAction(AppointmentPurpose purpose) private pure returns (bytes32) {
        if (purpose == AppointmentPurpose.ConcernHandling) return SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN;
        if (purpose == AppointmentPurpose.InitialDecision) return SparkV15ReviewActions.ACTION_DECIDE_INITIAL;
        return SparkV15ReviewActions.ACTION_DECIDE_REVIEW;
    }

    function isAppointed(bytes32 caseId, AppointmentPurpose purpose, address actor, uint64 atTime)
        public
        view
        returns (bool)
    {
        return isAppointedForCase(caseId, purpose, actor, atTime, false);
    }

    /// @notice When the action depends on the complaint, require its receipt before the appointment.
    function isAppointedForCase(
        bytes32 caseId,
        AppointmentPurpose purpose,
        address actor,
        uint64 atTime,
        bool afterReceipt
    ) public view returns (bool) {
        Appointment[] storage history = appointments[caseId][purpose];
        for (uint256 i = history.length; i != 0; --i) {
            Appointment storage appointment = history[i - 1];
            if (appointment.appointedAt <= atTime) {
                if (appointment.input.handler != actor) return false;
                if (!afterReceipt || appointmentEvidenceUse[appointment.evidenceId] == APPOINTED_AFTER_RECEIPT) {
                    return true;
                }
                // A verified earlier receipt can establish order even if it was recorded later.
                ConcernContext memory context = INTAKE.caseContext(caseId);
                return context.evidenceId != 0 && context.receivedAt < appointment.appointedAt;
            }
        }
        return false;
    }

    function _requireDisinterested(bytes32 caseId, ConcernContext memory context, address actor, uint64 atTime)
        private
        view
    {
        uint64 recusedAt = recusals[caseId][actor];
        if ((actor == context.raisedBy && context.receivedAt <= atTime) || (recusedAt != 0 && recusedAt <= atTime)) {
            revert ConflictedCaseActor();
        }
    }

    function _requireMaterialCaseDisinterest(bytes32 caseId, address actor) private view {
        INTAKE.requireMaterialCaseDisinterest(caseId, actor);
    }

    function _requireIndependentReviewer(bytes32 caseId, ConcernContext memory context, address actor) private view {
        CaseRecord storage item = cases[caseId];
        if (actor == item.original.decider || actor == item.initial.decider) revert ConflictedCaseActor();
        _requireDisinterested(caseId, context, actor, uint64(block.timestamp));
        _requireNotTemporarySetter(caseId, context, actor);
    }

    function _reviewSourceAvailable(CaseRecord storage item, uint256 intakeEvidenceId, uint256 packageId)
        private
        view
        returns (bool)
    {
        return _available(intakeEvidenceId, packageId) || _available(item.original.evidenceId, packageId)
            || _available(item.initial.evidenceId, packageId);
    }

    function _requireNotTemporarySetter(bytes32 caseId, ConcernContext memory context, address actor) private view {
        if (PAYMENTS.temporarySetterFor(context.lessonId, caseId, actor)) revert ConflictedCaseActor();
    }
}
