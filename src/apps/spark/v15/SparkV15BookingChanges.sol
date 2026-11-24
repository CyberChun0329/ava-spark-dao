// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {ISparkV15BookingChanges, SparkV15Booking} from "./SparkV15Booking.sol";
import {SparkV15Payments} from "./SparkV15Payments.sol";
import {SparkV15Funds} from "./SparkV15Funds.sol";

interface ISparkV15RemedyBooking {
    function BOOKING() external view returns (address);
    function consumeBookingDiscount(bytes32 formId) external;
}

/// @notice Retains agreed amendments and cancellation evidence alongside each original booking.
contract SparkV15BookingChanges {
    enum ClockMode {
        None,
        Fixed,
        BeforeStart
    }

    struct Window {
        ClockMode closeMode;
        uint64 close;
        ClockMode openMode;
        uint64 open;
    }

    struct RefundTiming {
        uint64 due;
        uint64 executeThrough;
        uint64 postLiftDeadline;
        uint64 postLiftPeriod;
        bool fromCancellation;
    }

    struct ChangeTerms {
        Window reschedule;
        Window advanceCancellation;
        uint64 noFaultAcceptanceDeadline;
        bytes32 noFaultTermsRef;
        RefundTiming refund;
    }

    struct ReplacementTerms {
        address tutor;
        uint128 normalFee;
        bytes32 agreementRef;
        bytes32 paymentTermsRef;
        bytes32 serviceTermsRef;
        bytes32 tutorResponsibilitiesRef;
        bytes32 providerResponsibilitiesRef;
        bytes32 noticeChannelRef;
    }

    struct ArrangementTerms {
        uint64 startsAt;
        uint64 endsAt;
        uint64 effectiveAt;
        bytes32 timeZoneRef;
        ReplacementTerms replacement;
        bytes32 noOpeningRef;
    }

    struct Proposal {
        bytes32 lessonId;
        bytes32 previous;
        ArrangementTerms next;
        uint64 contactedAt;
        uint64 agreedAt;
        uint64 finalizedAt;
        uint64 tutorAcceptedAt;
        uint64 providerAcceptedAt;
        bool providerAgreementSigned;
        bool tutorAgreementSigned;
        bool scheduleChanged;
        uint256 evidenceId;
        uint256 requiredReplacementBudget;
        uint256 replacementFundingEvidenceId;
    }

    struct Revision {
        ISparkV15BookingChanges.Arrangement arrangement;
        bytes32 dateNoticeSource;
        bytes32 replacementNoticeSource;
    }

    struct Notice {
        uint64 deliveredAt;
        uint256 evidenceId;
        address sender;
    }

    struct SeparateLink {
        bytes32 originalFormId;
        bytes32 nextFormId;
        bytes32 originalDateSource;
        uint64 contactedAt;
        uint64 payerAcceptedAt;
        uint64 agreedAt;
        uint64 linkedAt;
        uint256 contactEvidenceId;
        Notice studentNotice;
    }

    error InvalidChange();
    error InvalidEvidence();
    error UnauthorisedActor();

    event ArrangementProposed(bytes32 indexed lessonId, bytes32 indexed changeId, uint256 indexed evidenceId);
    event ArrangementAccepted(bytes32 indexed changeId, address indexed actor, bytes32 indexed formId);
    event ReplacementAgreementSigned(bytes32 indexed changeId, address indexed signer);
    event ReplacementFundingVerified(bytes32 indexed changeId, uint256 indexed evidenceId, uint128 reservedUnits);
    event ArrangementAgreed(bytes32 indexed changeId, uint64 agreedAt);
    event ArrangementFinalized(bytes32 indexed lessonId, bytes32 indexed changeId, uint64 effectiveAt);
    event ChangeNoticeRecorded(bytes32 indexed changeId, bytes32 indexed formId, uint256 indexed evidenceId);
    event SeparateBookingLinked(bytes32 indexed linkId, bytes32 indexed originalFormId, bytes32 indexed nextFormId);

    SparkV15Booking public immutable BOOKING;
    SparkV15Payments public immutable PAYMENTS;
    SparkV15BookingCreditSelection public immutable CREDIT_SELECTIONS;
    SparkV15BookingCancellations public cancellations;
    ISparkV15RemedyBooking public bookingRemedyConsumer;
    AVAEvidenceRegistry private immutable EVIDENCE;

    mapping(bytes32 => ChangeTerms) private agreedTerms;
    mapping(bytes32 => bool) private termsAdmitted;
    mapping(bytes32 => Proposal) private proposals;
    mapping(bytes32 => bytes32[]) private proposalForms;
    mapping(bytes32 => mapping(bytes32 => bool)) private affectedForms;
    mapping(bytes32 => mapping(bytes32 => uint64)) public payerAcceptedAt;
    mapping(bytes32 => mapping(bytes32 => Notice)) public studentChangeNotices;
    mapping(bytes32 => Notice) public tutorChangeNotices;
    mapping(bytes32 => Revision) private revisions;
    mapping(bytes32 => bytes32[]) private arrangementHistory;
    mapping(bytes32 => SeparateLink) private separateLinks;
    mapping(bytes32 => bytes32[]) private separateLinksFor;

    constructor(SparkV15Booking booking, SparkV15Payments payments) {
        if (
            address(booking).code.length == 0 || address(payments).code.length == 0
                || address(booking.FUNDS()) != address(payments.FUNDS())
        ) revert InvalidChange();
        BOOKING = booking;
        PAYMENTS = payments;
        EVIDENCE = booking.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        CREDIT_SELECTIONS = new SparkV15BookingCreditSelection(booking, payments.FUNDS());
    }

    function bindCancellations(SparkV15BookingCancellations source) external {
        BOOKING.REQUEST_ALLOCATION().IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
        if (
            address(cancellations) != address(0) || address(source).code.length == 0
                || address(source.CHANGES()) != address(this)
        ) {
            revert InvalidChange();
        }
        cancellations = source;
    }

    function bindRemedyBooking(ISparkV15RemedyBooking source) external {
        BOOKING.REQUEST_ALLOCATION().IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
        if (
            address(bookingRemedyConsumer) != address(0) || address(source).code.length == 0
                || source.BOOKING() != address(BOOKING)
        ) revert InvalidChange();
        bookingRemedyConsumer = source;
    }

    function consumeBookedRemedy(bytes32 formId) external {
        if (msg.sender != address(BOOKING)) revert UnauthorisedActor();
        if (address(bookingRemedyConsumer) == address(0)) revert InvalidChange();
        bookingRemedyConsumer.consumeBookingDiscount(formId);
    }

    function changeTermsCommitment(ChangeTerms calldata terms) public pure returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.booking.change-terms"), terms));
    }

    function admitChangeTerms(bytes32 formId, ChangeTerms calldata terms) external {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        if (
            form.version == 0 || termsAdmitted[formId] || form.terms.changeTermsRef != changeTermsCommitment(terms)
                || !_validWindow(terms.reschedule) || !_validWindow(terms.advanceCancellation)
        ) revert InvalidChange();
        agreedTerms[formId] = terms;
        termsAdmitted[formId] = true;
    }

    function proposalCommitment(
        bytes32 lessonId,
        ArrangementTerms calldata next,
        uint64 contactedAt,
        bytes32 contactRef
    ) public view returns (bytes32) {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        bytes32 previous = _effective(lesson, uint64(block.timestamp)).changeId;
        return _proposalCommitment(lesson.commitment, previous, _scopedForms(lesson), next, contactedAt, contactRef);
    }

    function proposeArrangement(
        bytes32 lessonId,
        ArrangementTerms calldata next,
        uint64 contactedAt,
        bytes32 contactRef,
        uint256 evidenceId
    ) external returns (bytes32 changeId) {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        _requireCoordinator(lesson);
        _beforeTeaching(lessonId);
        ISparkV15BookingChanges.Arrangement memory current = _effective(lesson, uint64(block.timestamp));
        bool moved = next.startsAt != current.startsAt || next.endsAt != current.endsAt
            || next.timeZoneRef != current.timeZoneRef;
        bool replaced = next.replacement.tutor != address(0);
        if (
            current.changeId != _latestChange(lessonId) || (!moved && !replaced) || contactedAt == 0
                || contactedAt > block.timestamp || contactRef == bytes32(0) || next.effectiveAt < block.timestamp
                || next.effectiveAt <= current.effectiveAt || next.effectiveAt > next.startsAt
                || next.startsAt < lesson.terms.rosterLockAt || next.endsAt <= next.startsAt
                || next.timeZoneRef == bytes32(0)
        ) revert InvalidChange();
        if (replaced) _requireReplacement(lesson, current, next.replacement);
        bytes32[] memory formIds = _scopedForms(lesson);
        changeId = _proposalCommitment(lesson.commitment, current.changeId, formIds, next, contactedAt, contactRef);
        if (proposals[changeId].lessonId != bytes32(0)) revert InvalidChange();
        _requireEvidence(lesson.packageId, evidenceId, changeId);

        Proposal storage proposal = proposals[changeId];
        proposal.lessonId = lessonId;
        proposal.previous = current.changeId;
        proposal.next = next;
        proposal.contactedAt = contactedAt;
        proposal.scheduleChanged = moved;
        proposal.evidenceId = evidenceId;
        if (replaced && next.replacement.normalFee > lesson.terms.tutorFee) {
            proposal.requiredReplacementBudget =
                uint256(lesson.prefunding.reservedUnits) + next.replacement.normalFee - lesson.terms.tutorFee;
        }
        proposalForms[changeId] = formIds;
        for (uint256 i; i < formIds.length; ++i) {
            bytes32 formId = formIds[i];
            if (!termsAdmitted[formId] || isCancelledAt(formId, uint64(block.timestamp))) {
                revert InvalidChange();
            }
            affectedForms[changeId][formId] = true;
        }
        emit ArrangementProposed(lessonId, changeId, evidenceId);
    }

    function replacementFundingCommitment(bytes32 changeId, uint128 requiredUnits, bytes32 inventoryRef)
        public
        pure
        returns (bytes32)
    {
        return keccak256(
            abi.encode(keccak256("spark.v1.5.booking.replacement-prefunding"), changeId, requiredUnits, inventoryRef)
        );
    }

    function verifyReplacementFunding(bytes32 changeId, uint128 requiredUnits, bytes32 inventoryRef, uint256 evidenceId)
        external
    {
        BOOKING.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                msg.sender, SparkV15.APP_ID, BOOKING.VERIFIER_ROLE(), BOOKING.ACTION_VERIFY_PREFUNDING()
            );
        Proposal storage proposal = _unagreed(changeId);
        if (
            proposal.requiredReplacementBudget == 0 || requiredUnits < proposal.requiredReplacementBudget
                || inventoryRef == bytes32(0) || proposal.replacementFundingEvidenceId != 0
        ) revert InvalidChange();
        uint256 packageId = BOOKING.getLesson(proposal.lessonId).packageId;
        _requireEvidence(packageId, evidenceId, replacementFundingCommitment(changeId, requiredUnits, inventoryRef));
        proposal.replacementFundingEvidenceId = evidenceId;
        BOOKING.reserveArrangementFunding(proposal.lessonId, requiredUnits);
        emit ReplacementFundingVerified(changeId, evidenceId, requiredUnits);
    }

    function signReplacementAgreement(bytes32 changeId) external {
        Proposal storage proposal = _unagreed(changeId);
        address replacement = proposal.next.replacement.tutor;
        address provider = BOOKING.COURSE_PROVIDER();
        if (replacement == address(0) || (msg.sender != provider && msg.sender != replacement)) {
            revert UnauthorisedActor();
        }
        if (msg.sender == provider) proposal.providerAgreementSigned = true;
        if (msg.sender == replacement) proposal.tutorAgreementSigned = true;
        emit ReplacementAgreementSigned(changeId, msg.sender);
    }

    function acceptPlace(bytes32 changeId, bytes32 formId) external {
        _requireFundedReplacement(_unagreed(changeId));
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        if (msg.sender != form.terms.payer) revert UnauthorisedActor();
        if (!affectedForms[changeId][formId] || payerAcceptedAt[changeId][formId] != 0) revert InvalidChange();
        payerAcceptedAt[changeId][formId] = uint64(block.timestamp);
        emit ArrangementAccepted(changeId, msg.sender, formId);
    }

    function acceptTutor(bytes32 changeId) external {
        Proposal storage proposal = _unagreed(changeId);
        _requireFundedReplacement(proposal);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(proposal.lessonId);
        address replacement = proposal.next.replacement.tutor;
        address tutor = replacement == address(0) ? _effective(lesson, uint64(block.timestamp)).tutor : replacement;
        if (msg.sender != tutor) revert UnauthorisedActor();
        if (
            proposal.tutorAcceptedAt != 0
                || (replacement != address(0) && !(proposal.providerAgreementSigned && proposal.tutorAgreementSigned))
        ) revert InvalidChange();
        proposal.tutorAcceptedAt = uint64(block.timestamp);
        emit ArrangementAccepted(changeId, msg.sender, bytes32(0));
    }

    function acceptProvider(bytes32 changeId) external {
        Proposal storage proposal = _unagreed(changeId);
        if (msg.sender != BOOKING.COURSE_PROVIDER()) revert UnauthorisedActor();
        if (proposal.providerAcceptedAt != 0) revert InvalidChange();
        proposal.providerAcceptedAt = uint64(block.timestamp);
        emit ArrangementAccepted(changeId, msg.sender, bytes32(0));
    }

    function recordAgreement(bytes32 changeId) external {
        Proposal storage proposal = _unagreed(changeId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(proposal.lessonId);
        _requireCoordinator(lesson);
        _requireLiveProposal(changeId, proposal, lesson);
        uint64 nowAt = uint64(block.timestamp);
        uint64 previousStart = _arrangement(lesson, proposal.previous).startsAt;
        if (
            nowAt >= previousStart && (proposal.contactedAt < previousStart || proposal.next.noOpeningRef == bytes32(0))
        ) {
            revert InvalidChange();
        }
        if (proposal.tutorAcceptedAt == 0 || proposal.providerAcceptedAt == 0) revert InvalidChange();
        bytes32[] storage formIds = proposalForms[changeId];
        for (uint256 i; i < formIds.length; ++i) {
            bytes32 formId = formIds[i];
            if (payerAcceptedAt[changeId][formId] == 0 || BOOKING.getForm(formId).confirmation.confirmedAt >= nowAt) {
                revert InvalidChange();
            }
            Window storage window = agreedTerms[formId].reschedule;
            if (proposal.scheduleChanged && !_withinWindow(lesson, formId, window, nowAt)) revert InvalidChange();
        }
        proposal.agreedAt = nowAt;
        emit ArrangementAgreed(changeId, nowAt);
    }

    function studentChangeNoticeCommitment(bytes32 changeId, bytes32 formId, uint64 deliveredAt, bytes32 receipt)
        public
        pure
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.arrangement-student-notice"), changeId, formId, deliveredAt, receipt
            )
        );
    }

    function recordStudentChangeNotice(
        bytes32 changeId,
        bytes32 formId,
        uint64 deliveredAt,
        bytes32 receipt,
        uint256 evidenceId
    ) external {
        Proposal storage proposal = proposals[changeId];
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(proposal.lessonId);
        _requireCoordinator(lesson);
        if (!affectedForms[changeId][formId] || studentChangeNotices[changeId][formId].evidenceId != 0) {
            revert InvalidChange();
        }
        _requireNoticeClock(proposal.agreedAt, deliveredAt, receipt);
        _requireEvidence(
            lesson.packageId, evidenceId, studentChangeNoticeCommitment(changeId, formId, deliveredAt, receipt)
        );
        studentChangeNotices[changeId][formId] = Notice(deliveredAt, evidenceId, msg.sender);
        emit ChangeNoticeRecorded(changeId, formId, evidenceId);
    }

    function tutorChangeNoticeCommitment(bytes32 changeId, bytes32 channel, uint64 deliveredAt, bytes32 receipt)
        public
        pure
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.arrangement-tutor-notice"), changeId, channel, deliveredAt, receipt
            )
        );
    }

    function recordTutorChangeNotice(
        bytes32 changeId,
        bytes32 channel,
        uint64 deliveredAt,
        bytes32 receipt,
        uint256 evidenceId
    ) external {
        Proposal storage proposal = proposals[changeId];
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(proposal.lessonId);
        if (msg.sender != lesson.terms.provider) _requireCoordinator(lesson);
        bytes32 agreedChannel = proposal.next.replacement.tutor == address(0)
            ? _arrangement(lesson, proposal.previous).tutorNoticeChannelRef
            : proposal.next.replacement.noticeChannelRef;
        if (
            tutorChangeNotices[changeId].evidenceId != 0 || channel == bytes32(0)
                || (agreedChannel != bytes32(0) && agreedChannel != channel)
        ) revert InvalidChange();
        _requireNoticeClock(proposal.agreedAt, deliveredAt, receipt);
        _requireEvidence(
            lesson.packageId, evidenceId, tutorChangeNoticeCommitment(changeId, channel, deliveredAt, receipt)
        );
        tutorChangeNotices[changeId] = Notice(deliveredAt, evidenceId, msg.sender);
        emit ChangeNoticeRecorded(changeId, bytes32(0), evidenceId);
    }

    function finalizeArrangement(bytes32 changeId) external {
        Proposal storage proposal = proposals[changeId];
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(proposal.lessonId);
        _requireCoordinator(lesson);
        _requireLiveProposal(changeId, proposal, lesson);
        if (proposal.agreedAt == 0 || proposal.finalizedAt != 0) revert InvalidChange();
        bytes32[] storage formIds = proposalForms[changeId];
        for (uint256 i; i < formIds.length; ++i) {
            bytes32 formId = formIds[i];
            if (
                studentChangeNotices[changeId][formId].evidenceId == 0 || isCancelledAt(formId, uint64(block.timestamp))
            ) {
                revert InvalidChange();
            }
        }

        ISparkV15BookingChanges.Arrangement memory revised = _arrangement(lesson, proposal.previous);
        ArrangementTerms storage next = proposal.next;
        revised.changeId = changeId;
        revised.startsAt = next.startsAt;
        revised.endsAt = next.endsAt;
        revised.effectiveAt = next.effectiveAt;
        revised.timeZoneRef = next.timeZoneRef;
        bool replaced = next.replacement.tutor != address(0);
        if (replaced) {
            revised.tutor = next.replacement.tutor;
            revised.tutorFee = next.replacement.normalFee;
            revised.tutorAgreementRef = next.replacement.agreementRef;
            revised.tutorPayTermsRef = next.replacement.paymentTermsRef;
            revised.tutorNoticeChannelRef = next.replacement.noticeChannelRef;
        }
        Revision storage previous = revisions[proposal.previous];
        revisions[changeId] = Revision(
            revised,
            proposal.scheduleChanged ? changeId : previous.dateNoticeSource,
            replaced ? changeId : previous.replacementNoticeSource
        );
        proposal.finalizedAt = uint64(block.timestamp);
        arrangementHistory[proposal.lessonId].push(changeId);
        emit ArrangementFinalized(proposal.lessonId, changeId, next.effectiveAt);
    }

    function effectiveArrangementAt(bytes32 lessonId, uint64 at)
        external
        view
        returns (ISparkV15BookingChanges.Arrangement memory)
    {
        return _effective(BOOKING.getLesson(lessonId), at);
    }

    function deadlineAnchorAt(bytes32 lessonId, uint64 at) external view returns (uint64) {
        uint64 start = BOOKING.getLesson(lessonId).terms.startsAt;
        bytes32[] storage history = arrangementHistory[lessonId];
        for (uint256 i; i < history.length; ++i) {
            ISparkV15BookingChanges.Arrangement storage next = revisions[history[i]].arrangement;
            if (next.effectiveAt > at) break;
            if (start <= next.effectiveAt) return start;
            start = next.startsAt;
        }
        return start;
    }

    function isCancelledAt(bytes32 formId, uint64 at) public view returns (bool) {
        return address(cancellations) != address(0) && cancellations.isCancelledAt(formId, at);
    }

    function hasFinalizedArrangement(bytes32 lessonId) external view returns (bool) {
        return arrangementHistory[lessonId].length != 0;
    }

    function getChangeTerms(bytes32 formId) external view returns (ChangeTerms memory) {
        if (!termsAdmitted[formId]) revert InvalidChange();
        return agreedTerms[formId];
    }

    function withinAdvanceCancellation(bytes32 formId, uint64 at) external view returns (bool) {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        Window storage window = agreedTerms[formId].advanceCancellation;
        return termsAdmitted[formId] && window.closeMode != ClockMode.None
            && _withinWindow(BOOKING.getLesson(form.lessonId), formId, window, at);
    }

    function hasTimelyRearrangement(bytes32 formId, bytes32 disruptedChange, uint64 disruptedAt, uint64 cutoff)
        external
        view
        returns (bool)
    {
        bytes32 lessonId = BOOKING.getForm(formId).lessonId;
        bytes32[] storage history = arrangementHistory[lessonId];
        bytes32 disruptedDate = revisions[disruptedChange].dateNoticeSource;
        for (uint256 i; i < history.length; ++i) {
            bytes32 changeId = history[i];
            Proposal storage proposal = proposals[changeId];
            if (proposal.agreedAt > cutoff) break;
            if (
                affectedForms[changeId][formId] && revisions[proposal.previous].dateNoticeSource == disruptedDate
                    && (proposal.scheduleChanged || proposal.next.effectiveAt > disruptedAt)
            ) return true;
        }
        bytes32[] storage links = separateLinksFor[formId];
        for (uint256 i; i < links.length; ++i) {
            SeparateLink storage link = separateLinks[links[i]];
            if (link.originalDateSource == disruptedDate && link.agreedAt >= disruptedAt && link.agreedAt <= cutoff) {
                return true;
            }
        }
        return false;
    }

    function separateBookingCommitment(
        bytes32 originalFormId,
        bytes32 nextFormId,
        uint64 contactedAt,
        bytes32 contactRef
    ) public view returns (bytes32) {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.separate-link"),
                address(this),
                originalFormId,
                nextFormId,
                contactedAt,
                contactRef
            )
        );
    }

    function proposeSeparateBooking(
        bytes32 originalFormId,
        bytes32 nextFormId,
        uint64 contactedAt,
        bytes32 contactRef,
        uint256 evidenceId
    ) external returns (bytes32 linkId) {
        SparkV15Booking.Form memory original = BOOKING.getForm(originalFormId);
        SparkV15Booking.Form memory next = BOOKING.getForm(nextFormId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(original.lessonId);
        _requireCoordinator(lesson);
        if (
            original.confirmation.confirmedAt == 0 || next.version == 0 || original.lessonId == next.lessonId
                || contactedAt < original.confirmation.confirmedAt || contactedAt > block.timestamp
                || contactRef == bytes32(0)
        ) {
            revert InvalidChange();
        }
        linkId = separateBookingCommitment(originalFormId, nextFormId, contactedAt, contactRef);
        SeparateLink storage link = separateLinks[linkId];
        if (link.originalFormId != bytes32(0)) revert InvalidChange();
        _requireEvidence(lesson.packageId, evidenceId, linkId);
        link.originalFormId = originalFormId;
        link.nextFormId = nextFormId;
        link.contactedAt = contactedAt;
        link.contactEvidenceId = evidenceId;
    }

    function acceptSeparateBooking(bytes32 linkId) external {
        SeparateLink storage link = separateLinks[linkId];
        SparkV15Booking.Form memory original = BOOKING.getForm(link.originalFormId);
        if (msg.sender != original.terms.payer) revert UnauthorisedActor();
        if (link.payerAcceptedAt != 0 || _separateAgreementAt(link.nextFormId) != 0) revert InvalidChange();
        link.payerAcceptedAt = uint64(block.timestamp);
        emit ArrangementAccepted(linkId, msg.sender, link.originalFormId);
    }

    function separateNoticeCommitment(bytes32 linkId, uint64 deliveredAt, bytes32 receipt)
        public
        pure
        returns (bytes32)
    {
        return keccak256(
            abi.encode(keccak256("spark.v1.5.booking.separate-student-notice"), linkId, deliveredAt, receipt)
        );
    }

    function linkSeparateBooking(bytes32 linkId, uint64 deliveredAt, bytes32 receipt, uint256 evidenceId) external {
        SeparateLink storage link = separateLinks[linkId];
        SparkV15Booking.Form memory original = BOOKING.getForm(link.originalFormId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(original.lessonId);
        _requireCoordinator(lesson);
        uint64 agreedAt = _separateAgreementAt(link.nextFormId);
        if (
            agreedAt == 0 || link.payerAcceptedAt == 0 || link.payerAcceptedAt > agreedAt || link.linkedAt != 0
                || link.contactedAt > agreedAt
                || (isCancelledAt(link.originalFormId, uint64(block.timestamp))
                    && !isCancelledAt(link.originalFormId, agreedAt))
        ) {
            revert InvalidChange();
        }
        _requireRetainedConfirmation(original);
        _requireRetainedConfirmation(BOOKING.getForm(link.nextFormId));
        _requireNoticeClock(agreedAt, deliveredAt, receipt);
        _requireEvidence(lesson.packageId, evidenceId, separateNoticeCommitment(linkId, deliveredAt, receipt));
        bytes32 historyId = _effective(lesson, agreedAt).changeId;
        link.originalDateSource = revisions[historyId].dateNoticeSource;
        link.agreedAt = agreedAt;
        link.linkedAt = uint64(block.timestamp);
        link.studentNotice = Notice(deliveredAt, evidenceId, msg.sender);
        separateLinksFor[link.originalFormId].push(linkId);
        emit SeparateBookingLinked(linkId, link.originalFormId, link.nextFormId);
    }

    function getSeparateBooking(bytes32 linkId) external view returns (SeparateLink memory) {
        return separateLinks[linkId];
    }

    function hasStudentNotice(bytes32 changeId, bytes32 formId, uint64 at) external view returns (bool) {
        Revision storage revision = revisions[changeId];
        bytes32 dateId = revision.dateNoticeSource;
        if (dateId == bytes32(0)) {
            SparkV15Booking.StudentNotice memory original = BOOKING.getStudentNotice(formId);
            if (original.evidenceId == 0 || original.deliveredAt >= at) return false;
        } else if (!_noticed(studentChangeNotices[dateId][formId], at)) {
            return false;
        }
        bytes32 tutorId = revision.replacementNoticeSource;
        return tutorId == bytes32(0) || _noticed(studentChangeNotices[tutorId][formId], at);
    }

    function hasTutorNotice(bytes32 changeId, uint64 at) external view returns (bool) {
        return _noticed(tutorChangeNotices[changeId], at);
    }

    function getStudentNoticeEvidence(bytes32 changeId, bytes32 formId)
        external
        view
        returns (uint256 scheduleEvidenceId, uint256 replacementEvidenceId)
    {
        Revision storage revision = revisions[changeId];
        bytes32 dateId = revision.dateNoticeSource;
        scheduleEvidenceId = dateId == bytes32(0)
            ? BOOKING.getStudentNotice(formId).evidenceId
            : studentChangeNotices[dateId][formId].evidenceId;
        replacementEvidenceId = studentChangeNotices[revision.replacementNoticeSource][formId].evidenceId;
    }

    function usesInitialStudentNotice(bytes32 changeId) external view returns (bool) {
        return revisions[changeId].dateNoticeSource == bytes32(0);
    }

    function getAgreement(bytes32 changeId)
        external
        view
        returns (
            uint64 contactedAt,
            uint64 agreedAt,
            uint64 effectiveAt,
            uint64 finalizedAt,
            uint256 proposalEvidenceId,
            uint256 fundingEvidenceId
        )
    {
        Proposal storage item = proposals[changeId];
        return (
            item.contactedAt,
            item.agreedAt,
            item.next.effectiveAt,
            item.finalizedAt,
            item.evidenceId,
            item.replacementFundingEvidenceId
        );
    }

    function _scopedForms(SparkV15Booking.Lesson memory lesson) private view returns (bytes32[] memory list) {
        bytes32 lessonId = lesson.terms.lessonId;
        uint64 nowAt = uint64(block.timestamp);
        if (lesson.terms.rosterLockAt != 0 && nowAt >= lesson.terms.rosterLockAt) {
            list = BOOKING.getLockedForms(lessonId);
        } else {
            list = BOOKING.getConfirmedForms(lessonId);
            uint256 count;
            for (uint256 i; i < list.length; ++i) {
                bytes32 formId = list[i];
                if (!isCancelledAt(formId, nowAt)) list[count++] = formId;
            }
            assembly ("memory-safe") { mstore(list, count) }
        }
        if (list.length == 0) revert InvalidChange();
    }

    function _proposalCommitment(
        bytes32 lessonCommitment,
        bytes32 previous,
        bytes32[] memory formIds,
        ArrangementTerms calldata next,
        uint64 contactedAt,
        bytes32 contactRef
    ) private view returns (bytes32) {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.arrangement"),
                address(this),
                lessonCommitment,
                previous,
                formIds,
                next,
                contactedAt,
                contactRef
            )
        );
    }

    function _unagreed(bytes32 changeId) private view returns (Proposal storage proposal) {
        proposal = proposals[changeId];
        if (proposal.lessonId == bytes32(0) || proposal.agreedAt != 0 || block.timestamp > proposal.next.effectiveAt) {
            revert InvalidChange();
        }
    }

    function _requireLiveProposal(bytes32 changeId, Proposal storage proposal, SparkV15Booking.Lesson memory lesson)
        private
        view
    {
        _beforeTeaching(proposal.lessonId);
        if (
            proposal.previous != _latestChange(proposal.lessonId) || block.timestamp > proposal.next.effectiveAt
                || keccak256(abi.encode(proposalForms[changeId])) != keccak256(abi.encode(_scopedForms(lesson)))
        ) {
            revert InvalidChange();
        }
    }

    function _requireReplacement(
        SparkV15Booking.Lesson memory lesson,
        ISparkV15BookingChanges.Arrangement memory current,
        ReplacementTerms calldata replacement
    ) private pure {
        if (
            replacement.tutor == current.tutor || replacement.agreementRef == bytes32(0)
                || replacement.paymentTermsRef == bytes32(0)
                || replacement.serviceTermsRef != lesson.terms.serviceTermsRef
                || replacement.tutorResponsibilitiesRef == bytes32(0)
                || replacement.providerResponsibilitiesRef == bytes32(0)
        ) revert InvalidChange();
    }

    function _requireFundedReplacement(Proposal storage proposal) private view {
        if (proposal.requiredReplacementBudget != 0 && proposal.replacementFundingEvidenceId == 0) {
            revert InvalidChange();
        }
    }

    function _latestChange(bytes32 lessonId) private view returns (bytes32) {
        bytes32[] storage history = arrangementHistory[lessonId];
        return history.length == 0 ? bytes32(0) : history[history.length - 1];
    }

    function _effective(SparkV15Booking.Lesson memory lesson, uint64 at)
        private
        view
        returns (ISparkV15BookingChanges.Arrangement memory)
    {
        bytes32[] storage history = arrangementHistory[lesson.terms.lessonId];
        for (uint256 i = history.length; i != 0; --i) {
            ISparkV15BookingChanges.Arrangement storage item = revisions[history[i - 1]].arrangement;
            if (item.effectiveAt <= at) return item;
        }
        return _arrangement(lesson, bytes32(0));
    }

    function _arrangement(SparkV15Booking.Lesson memory lesson, bytes32 changeId)
        private
        view
        returns (ISparkV15BookingChanges.Arrangement memory)
    {
        if (changeId != bytes32(0)) return revisions[changeId].arrangement;
        SparkV15Booking.LessonTerms memory terms = lesson.terms;
        return ISparkV15BookingChanges.Arrangement(
            bytes32(0),
            terms.startsAt,
            terms.endsAt,
            0,
            terms.tutor,
            terms.tutorFee,
            terms.tutorAgreementRef,
            terms.tutorPayTermsRef,
            terms.tutorNoticeChannelRef,
            terms.timeZoneRef
        );
    }

    function _withinWindow(SparkV15Booking.Lesson memory lesson, bytes32 formId, Window storage window, uint64 at)
        private
        view
        returns (bool)
    {
        if (window.closeMode == ClockMode.None) return lesson.terms.rosterLockAt == 0;
        if (window.closeMode == ClockMode.Fixed) return at < window.close && (window.open == 0 || at > window.open);

        uint64 confirmed = BOOKING.getForm(formId).confirmation.confirmedAt;
        uint64 start = lesson.terms.startsAt;
        uint64 effectiveAt;
        bytes32[] storage history = arrangementHistory[lesson.terms.lessonId];
        for (uint256 i; i <= history.length; ++i) {
            uint64 nextEffect = i == history.length ? type(uint64).max : revisions[history[i]].arrangement.effectiveAt;
            if (window.close > start) return false;
            uint64 cutoff = start - window.close;
            if (window.openMode == ClockMode.None) {
                if (at >= cutoff) return false;
            } else if (window.openMode == ClockMode.Fixed || window.open <= start) {
                uint64 opening = window.openMode == ClockMode.Fixed ? window.open : start - window.open;
                if (opening < confirmed) opening = confirmed;
                if (opening < effectiveAt) opening = effectiveAt;
                if (opening < nextEffect && opening < cutoff && opening < at) return at < cutoff;
            }
            if (i == history.length || nextEffect > at) return window.openMode == ClockMode.None;
            ISparkV15BookingChanges.Arrangement storage next = revisions[history[i]].arrangement;
            start = next.startsAt;
            effectiveAt = nextEffect;
        }
        return false;
    }

    function _validWindow(Window calldata window) private pure returns (bool) {
        if (window.closeMode == ClockMode.None) {
            return window.close == 0 && window.openMode == ClockMode.None && window.open == 0;
        }
        if (window.closeMode == ClockMode.Fixed) {
            return window.close != 0 && window.openMode != ClockMode.BeforeStart && window.open < window.close;
        }
        return window.openMode != ClockMode.None || window.open == 0;
    }

    function _beforeTeaching(bytes32 lessonId) private view {
        if (BOOKING.getTeaching(lessonId).startedAt != 0) revert InvalidChange();
    }

    function _separateAgreementAt(bytes32 nextFormId) private view returns (uint64 result) {
        SparkV15Booking.PlaceTerms memory place = BOOKING.getForm(nextFormId).terms;
        uint256 required = place.customer == place.payer ? 3 : 4;
        for (uint256 i; i < required; ++i) {
            (, uint64 signedAt) = BOOKING.acceptances(nextFormId, SparkV15Booking.Acceptance(i));
            if (signedAt == 0) return 0;
            if (signedAt > result) result = signedAt;
        }
    }

    function _requireRetainedConfirmation(SparkV15Booking.Form memory form) private view {
        uint64 confirmed = form.confirmation.confirmedAt;
        uint64 started = BOOKING.getTeaching(form.lessonId).startedAt;
        if (confirmed == 0 || (started != 0 && started <= confirmed)) revert InvalidChange();
    }

    function _requireNoticeClock(uint64 agreedAt, uint64 deliveredAt, bytes32 receipt) private view {
        if (agreedAt == 0 || deliveredAt < agreedAt || deliveredAt > block.timestamp || receipt == bytes32(0)) {
            revert InvalidChange();
        }
    }

    function _noticed(Notice storage notice, uint64 at) private view returns (bool) {
        return notice.evidenceId != 0 && notice.deliveredAt < at;
    }

    function _requireCoordinator(SparkV15Booking.Lesson memory lesson) private view {
        if (msg.sender != lesson.terms.coordinator) revert UnauthorisedActor();
        BOOKING.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                msg.sender, SparkV15.APP_ID, BOOKING.COORDINATOR_ROLE(), BOOKING.ACTION_COORDINATE_BOOKING()
            );
    }

    function _requireEvidence(uint256 packageId, uint256 evidenceId, bytes32 commitment) private view {
        EVIDENCE.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        if (EVIDENCE.getEvidenceReference(evidenceId).commitment != commitment) revert InvalidEvidence();
    }
}

/// @notice Decodes and charges only the credit sources of the booking being confirmed.
contract SparkV15BookingCreditSelection {
    SparkV15Booking private immutable BOOKING;
    SparkV15Funds private immutable FUNDS;

    error InvalidCreditSelection();

    constructor(SparkV15Booking booking, SparkV15Funds funds) {
        BOOKING = booking;
        FUNDS = funds;
    }

    function charge(bytes32 formId, bytes calldata encodedSources) external {
        if (msg.sender != address(BOOKING)) revert InvalidCreditSelection();
        (
            bytes32 domain,
            SparkV15Funds.RechargeDebit[] memory recharges,
            SparkV15Funds.CompensationDebit[] memory compensation
        ) = abi.decode(encodedSources, (bytes32, SparkV15Funds.RechargeDebit[], SparkV15Funds.CompensationDebit[]));
        if (domain != keccak256("spark.v1.5.booking.credit-sources") || compensation.length == 0) {
            revert InvalidCreditSelection();
        }
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        FUNDS.chargeLessonFromCredits(
            form.lessonId, form.terms.creditAccount, form.confirmation.debitedUnits, recharges, compensation
        );
    }
}

/// @notice Customer cancellation, verified teaching valuation and the resulting original-account refund obligation.
contract SparkV15BookingCancellations {
    enum Kind {
        Unrecorded,
        Advance,
        NoFault
    }
    enum Delivery {
        Unverified,
        NoneBeforeOpening,
        NoneForPlace,
        Partial
    }

    struct RearrangementContact {
        address recipient;
        uint64 contactedAt;
        bytes32 receiptRef;
    }

    struct DisruptionWitness {
        uint64 verifiedAt;
        bool cannotProceed;
        bool anyPartyAtFault;
        bytes32 reasonRef;
        RearrangementContact[] contacts;
    }

    struct Disruption {
        bytes32 formId;
        bytes32 arrangementId;
        uint64 verifiedAt;
        uint256 evidenceId;
    }

    struct ServiceEvidence {
        Delivery delivery;
        uint128 undeliveredValue;
        bytes32 assessmentRef;
    }

    struct Cancellation {
        Kind kind;
        uint64 requestedAt;
        uint256 requestEvidenceId;
        bytes32 disruptionId;
        address requestedBy;
        Delivery delivery;
        uint128 undeliveredValue;
        uint128 refundDue;
        address assessedBy;
        uint256 assessmentEvidenceId;
        bytes32 refundObligation;
    }

    bytes32 public constant ACTION_VERIFY_CANCELLATION = keccak256("spark.action.verify-cancellation.v1.5");

    SparkV15BookingChanges public immutable CHANGES;
    SparkV15Booking public immutable BOOKING;
    SparkV15Payments public immutable PAYMENTS;
    AVAEvidenceRegistry private immutable EVIDENCE;

    mapping(bytes32 => Disruption) public disruptions;
    mapping(bytes32 => bytes32) public latestDisruption;
    mapping(bytes32 => Cancellation) private cancellations;

    error InvalidCancellation();
    error InvalidEvidence();
    error UnauthorisedActor();

    event NoFaultDisruptionRecorded(bytes32 indexed formId, bytes32 indexed disruptionId, uint256 evidenceId);
    event Cancelled(bytes32 indexed formId, address indexed customer, Kind kind, uint64 requestedAt);
    event NoFaultAssessmentRecorded(bytes32 indexed formId, uint256 indexed evidenceId, uint128 refundDue);
    event NoFaultRefundEstablished(bytes32 indexed formId, bytes32 indexed obligationId);

    constructor(SparkV15BookingChanges changes) {
        CHANGES = changes;
        BOOKING = changes.BOOKING();
        PAYMENTS = changes.PAYMENTS();
        EVIDENCE = BOOKING.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
    }

    function advanceContactCommitment(bytes32 formId, bytes32 receipt) public view returns (bytes32) {
        return
            keccak256(abi.encode(keccak256("spark.v1.5.booking.advance-cancellation"), address(this), formId, receipt));
    }

    function cancelInAdvance(bytes32 formId, bytes32 contactReceipt, uint256 evidenceId) external {
        (SparkV15Booking.Form memory form, SparkV15Booking.Lesson memory lesson) = _confirmedForm(formId);
        if (msg.sender != form.terms.customer) revert UnauthorisedActor();
        uint64 nowAt = uint64(block.timestamp);
        if (
            lesson.terms.rosterLockAt != 0 || cancellations[formId].requestedAt != 0
                || BOOKING.getTeaching(form.lessonId).startedAt != 0 || contactReceipt == bytes32(0)
                || nowAt >= BOOKING.getEffectiveArrangement(form.lessonId, nowAt).startsAt
                || !CHANGES.withinAdvanceCancellation(formId, nowAt)
        ) revert InvalidCancellation();
        _requireEvidence(lesson.packageId, evidenceId, advanceContactCommitment(formId, contactReceipt));
        Cancellation storage item = cancellations[formId];
        item.kind = Kind.Advance;
        item.requestedAt = nowAt;
        item.requestEvidenceId = evidenceId;
        item.requestedBy = msg.sender;
        emit Cancelled(formId, msg.sender, Kind.Advance, nowAt);
    }

    function disruptionCommitment(bytes32 formId, DisruptionWitness calldata facts) public view returns (bytes32) {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        return
            _disruptionCommitment(
                formId, BOOKING.getEffectiveArrangement(form.lessonId, facts.verifiedAt).changeId, facts
            );
    }

    function recordNoFaultDisruption(bytes32 formId, DisruptionWitness calldata facts, uint256 evidenceId)
        external
        returns (bytes32 disruptionId)
    {
        _requireVerifier();
        (SparkV15Booking.Form memory form, SparkV15Booking.Lesson memory lesson) = _confirmedForm(formId);
        SparkV15BookingChanges.ChangeTerms memory terms = CHANGES.getChangeTerms(formId);
        if (
            cancellations[formId].requestedAt != 0 || !facts.cannotProceed || facts.anyPartyAtFault
                || facts.verifiedAt <= form.confirmation.confirmedAt || facts.verifiedAt > block.timestamp
                || facts.verifiedAt > terms.noFaultAcceptanceDeadline || facts.reasonRef == bytes32(0)
                || terms.noFaultTermsRef == bytes32(0)
                || facts.verifiedAt < disruptions[latestDisruption[formId]].verifiedAt
        ) revert InvalidCancellation();
        ISparkV15BookingChanges.Arrangement memory arrangement =
            BOOKING.getEffectiveArrangement(form.lessonId, facts.verifiedAt);
        bool customerContacted;
        for (uint256 i; i < facts.contacts.length; ++i) {
            RearrangementContact calldata contact = facts.contacts[i];
            address recipient = contact.recipient;
            if (
                (recipient != form.terms.customer
                        && recipient != form.terms.student
                        && recipient != form.terms.payer
                        && recipient != lesson.terms.provider
                        && recipient != arrangement.tutor) || contact.contactedAt < facts.verifiedAt
                    || contact.contactedAt > terms.noFaultAcceptanceDeadline || contact.contactedAt > block.timestamp
                    || contact.receiptRef == bytes32(0)
            ) revert InvalidCancellation();
            if (recipient == form.terms.customer) customerContacted = true;
        }
        disruptionId = _disruptionCommitment(formId, arrangement.changeId, facts);
        if (!customerContacted || disruptions[disruptionId].evidenceId != 0) revert InvalidCancellation();
        _requireEvidence(lesson.packageId, evidenceId, disruptionId);
        disruptions[disruptionId] = Disruption(formId, arrangement.changeId, facts.verifiedAt, evidenceId);
        latestDisruption[formId] = disruptionId;
        emit NoFaultDisruptionRecorded(formId, disruptionId, evidenceId);
    }

    function requestNoFaultCancellation(bytes32 formId) external {
        (SparkV15Booking.Form memory form, SparkV15Booking.Lesson memory lesson) = _confirmedForm(formId);
        if (msg.sender != form.terms.customer) revert UnauthorisedActor();
        Cancellation storage item = cancellations[formId];
        bytes32 disruptionId = latestDisruption[formId];
        Disruption storage disruption = disruptions[disruptionId];
        uint64 cutoff = CHANGES.getChangeTerms(formId).noFaultAcceptanceDeadline;
        if (
            disruption.evidenceId == 0 || item.requestedAt != 0 || block.timestamp <= cutoff
                || CHANGES.hasTimelyRearrangement(formId, disruption.arrangementId, disruption.verifiedAt, cutoff)
        ) revert InvalidCancellation();
        EVIDENCE.requireUsableEvidenceReferenceForPackage(disruption.evidenceId, lesson.packageId);
        item.kind = Kind.NoFault;
        item.requestedAt = uint64(block.timestamp);
        item.disruptionId = disruptionId;
        item.requestedBy = msg.sender;
        emit Cancelled(formId, msg.sender, Kind.NoFault, item.requestedAt);
    }

    function serviceCommitment(bytes32 formId, ServiceEvidence calldata service) public view returns (bytes32) {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(form.lessonId);
        Cancellation storage item = cancellations[formId];
        return _serviceCommitment(formId, item, teaching, service);
    }

    function recordNoFaultAssessment(bytes32 formId, ServiceEvidence calldata service, uint256 evidenceId) external {
        _requireVerifier();
        (SparkV15Booking.Form memory form, SparkV15Booking.Lesson memory lesson) = _confirmedForm(formId);
        Cancellation storage item = cancellations[formId];
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(form.lessonId);
        if (
            item.kind != Kind.NoFault || item.assessmentEvidenceId != 0 || service.assessmentRef == bytes32(0)
                || service.delivery == Delivery.Unverified || msg.sender == form.terms.customer
                || msg.sender == form.terms.payer || msg.sender == form.terms.student
                || msg.sender == lesson.terms.provider || msg.sender == lesson.terms.tutor
        ) revert InvalidCancellation();
        bool taughtBefore = teaching.startedAt != 0 && teaching.startedAt < item.requestedAt;
        if (
            (service.delivery == Delivery.NoneBeforeOpening
                    && teaching.startedAt != 0
                    && teaching.startedAt <= item.requestedAt)
                || (service.delivery == Delivery.Partial && !taughtBefore)
                || (service.delivery != Delivery.Partial && service.undeliveredValue != 0)
        ) revert InvalidCancellation();
        _requireEvidence(lesson.packageId, evidenceId, _serviceCommitment(formId, item, teaching, service));
        uint128 debit = form.confirmation.debitedUnits;
        item.delivery = service.delivery;
        item.undeliveredValue = service.undeliveredValue;
        item.refundDue =
            service.delivery == Delivery.Partial && service.undeliveredValue < debit ? service.undeliveredValue : debit;
        item.assessedBy = msg.sender;
        item.assessmentEvidenceId = evidenceId;
        emit NoFaultAssessmentRecorded(formId, evidenceId, item.refundDue);
    }

    function previewNoFaultRefund(bytes32 formId)
        public
        view
        returns (SparkV15Payments.PaymentTerms memory payment, bytes32 basis, uint256 packageId)
    {
        (SparkV15Booking.Form memory form, SparkV15Booking.Lesson memory lesson) = _confirmedForm(formId);
        Cancellation storage item = cancellations[formId];
        if (item.assessmentEvidenceId == 0 || item.refundDue == 0) revert InvalidCancellation();
        SparkV15BookingChanges.RefundTiming memory timing = CHANGES.getChangeTerms(formId).refund;
        if (timing.executeThrough < timing.due || (timing.postLiftDeadline == 0) == (timing.postLiftPeriod == 0)) {
            revert InvalidCancellation();
        }
        address owner = PAYMENTS.FUNDS().creditAccount(form.terms.payer) == form.terms.creditAccount
            ? form.terms.payer
            : form.terms.customer;
        uint64 anchor = timing.fromCancellation ? item.requestedAt : 0;
        payment.lessonId = form.lessonId;
        payment.paymentPart = keccak256(abi.encode(keccak256("spark.v1.5.booking.no-fault-refund"), formId));
        payment.recipient = owner;
        payment.originalDebitAccount = form.terms.creditAccount;
        payment.originalDebitAmount = form.confirmation.debitedUnits;
        payment.amount = item.refundDue;
        payment.dueAt = anchor + timing.due;
        payment.executionDeadline = anchor + timing.executeThrough;
        payment.postLiftDeadline = timing.postLiftDeadline;
        payment.postLiftPeriod = timing.postLiftPeriod;
        payment.dueAtExact = true;
        payment.executionDeadlineExact = true;
        payment.postLiftDeadlineExact = timing.postLiftDeadline != 0;
        payment.settlementProposer = item.requestedBy;
        payment.settlementApprover = item.assessedBy;
        basis = keccak256(
            abi.encode(address(this), formId, item.kind, item.requestedAt, item.disruptionId, item.assessmentEvidenceId)
        );
        packageId = lesson.packageId;
    }

    function establishNoFaultRefund(bytes32 formId, uint256 paymentEvidenceId) external returns (bytes32 obligationId) {
        Cancellation storage item = cancellations[formId];
        if (item.refundObligation != bytes32(0)) revert InvalidCancellation();
        (SparkV15Payments.PaymentTerms memory payment, bytes32 basis, uint256 packageId) = previewNoFaultRefund(formId);
        EVIDENCE.requireUsableEvidenceReferenceForPackage(item.assessmentEvidenceId, packageId);
        obligationId = PAYMENTS.establishSettledPayment(payment, basis, paymentEvidenceId, packageId);
        item.refundObligation = obligationId;
        emit NoFaultRefundEstablished(formId, obligationId);
    }

    function isCancelledAt(bytes32 formId, uint64 at) external view returns (bool) {
        uint64 time = cancellations[formId].requestedAt;
        return time != 0 && time <= at;
    }

    function getCancellation(bytes32 formId) external view returns (Cancellation memory) {
        return cancellations[formId];
    }

    function _confirmedForm(bytes32 formId)
        private
        view
        returns (SparkV15Booking.Form memory form, SparkV15Booking.Lesson memory lesson)
    {
        form = BOOKING.getForm(formId);
        lesson = BOOKING.getLesson(form.lessonId);
        if (
            form.confirmation.confirmedAt == 0 || BOOKING.currentForm(form.lessonId, form.terms.placeId) != formId
                || (lesson.terms.rosterLockAt != 0 && BOOKING.getRosterLock(form.lessonId).evidenceId == 0)
        ) {
            revert InvalidCancellation();
        }
    }

    function _disruptionCommitment(bytes32 formId, bytes32 arrangementId, DisruptionWitness calldata facts)
        private
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(keccak256("spark.v1.5.booking.no-fault-disruption"), address(this), formId, arrangementId, facts)
        );
    }

    function _serviceCommitment(
        bytes32 formId,
        Cancellation storage item,
        SparkV15Booking.Teaching memory teaching,
        ServiceEvidence calldata service
    ) private view returns (bytes32) {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.no-fault-service"),
                address(this),
                formId,
                item.requestedAt,
                item.disruptionId,
                teaching.startEvidenceId,
                teaching.endEvidenceId,
                service
            )
        );
    }

    function _requireVerifier() private view {
        BOOKING.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                msg.sender, SparkV15.APP_ID, BOOKING.VERIFIER_ROLE(), ACTION_VERIFY_CANCELLATION
            );
    }

    function _requireEvidence(uint256 packageId, uint256 evidenceId, bytes32 commitment) private view {
        EVIDENCE.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        if (EVIDENCE.getEvidenceReference(evidenceId).commitment != commitment) revert InvalidEvidence();
    }
}
