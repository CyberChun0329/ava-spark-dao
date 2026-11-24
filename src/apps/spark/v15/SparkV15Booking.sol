// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACapabilityKeys} from "@ava-protocol/contracts/src/core/AVACapabilityKeys.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {DefaultAVACorePolicyBundle} from "@ava-protocol/contracts/src/core/modules/DefaultAVACoreRuleModules.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {IAVAApplicationModule} from "@ava-protocol/contracts/src/interfaces/IAVAApplicationModule.sol";
import {SparkV15, SparkV15ApplicationModule} from "./SparkV15ApplicationModule.sol";
import {SparkV15Funds} from "./SparkV15Funds.sol";
import {SparkV15CourseNotices} from "./SparkV15CourseNotices.sol";
import {SparkV15ServiceReports} from "./SparkV15ServiceReports.sol";
import {SparkV15TeachingEnd} from "./SparkV15TeachingEnd.sol";
import {SparkV15BookingPrefunding} from "./SparkV15BookingPrefunding.sol";

bytes32 constant COORDINATE_BOOKING_ACTION = keccak256("spark.action.coordinate-booking.v1.5");

interface ISparkV15BookingFunds {
    function REQUEST_ALLOCATION() external view returns (AVARequestAllocation);
    function WORKFLOW() external view returns (bytes32);
    function creditAccount(address owner) external view returns (bytes32);
    function lessonReserved(bytes32 lessonId) external view returns (uint256);
    function requireCommitmentFunding(bytes32 lessonId, bytes32 formId) external view;
    function reserveLessonBudget(bytes32 lessonId, uint128 requiredUnits) external;
    function chargeLesson(bytes32 lessonId, bytes32 creditAccount, uint128 amount) external;
    function chargeLessonFrom(
        bytes32 lessonId,
        bytes32 creditAccount,
        uint128 amount,
        SparkV15Funds.RechargeDebit[] calldata debits
    ) external;
}

interface ISparkV15BookingCreditSelection {
    function charge(bytes32 formId, bytes calldata encodedSources) external;
}

interface ISparkV15SettlementBinding {
    function settlementPolicy() external view returns (address);
}

interface ISparkV15BookingChanges {
    struct Arrangement {
        bytes32 changeId;
        uint64 startsAt;
        uint64 endsAt;
        uint64 effectiveAt;
        address tutor;
        uint128 tutorFee;
        bytes32 tutorAgreementRef;
        bytes32 tutorPayTermsRef;
        bytes32 tutorNoticeChannelRef;
        bytes32 timeZoneRef;
    }

    function BOOKING() external view returns (address);
    function effectiveArrangementAt(bytes32 lessonId, uint64 at) external view returns (Arrangement memory);
    function deadlineAnchorAt(bytes32 lessonId, uint64 at) external view returns (uint64);
    function isCancelledAt(bytes32 formId, uint64 at) external view returns (bool);
    function hasStudentNotice(bytes32 changeId, bytes32 formId, uint64 at) external view returns (bool);
    function hasTutorNotice(bytes32 changeId, uint64 at) external view returns (bool);
    function consumeBookedRemedy(bytes32 formId) external;
    function hasFinalizedArrangement(bytes32 lessonId) external view returns (bool);
    function CREDIT_SELECTIONS() external view returns (ISparkV15BookingCreditSelection);
}

/// @notice Versioned bookings with the agreed terms, actual wallet acceptances and Core evidence.
/// @dev Initial forms retain the agreed terms. Document and private contact commitments refer to off-chain records.
contract SparkV15Booking {
    enum Acceptance {
        Provider,
        Tutor,
        Customer,
        Payer
    }

    enum StartPermission {
        Unrecorded,
        Permitted,
        RequirementsNotMet,
        Unverified
    }

    enum ServiceStatus {
        Unreported,
        NoneDelivered,
        PartiallyDelivered,
        FullyDelivered
    }

    struct LessonTerms {
        bytes32 lessonId;
        address provider;
        address tutor;
        address coordinator;
        uint64 startsAt;
        uint64 endsAt;
        uint64 rosterLockAt;
        bytes32 rosterRef;
        bytes32 timeZoneRef;
        bytes32 tutorNoticeChannelRef;
        uint128 tutorFee;
        bytes32 tutorAgreementRef;
        bytes32 serviceTermsRef;
        bytes32 tutorPayTermsRef;
        bytes32 providerResponsibilitiesRef;
        bytes32 tutorResponsibilitiesRef;
        bytes32 startTermsRef;
        bytes32 documentsRef;
        bytes32 materialsTermsRef;
    }

    struct PlaceTerms {
        bytes32 placeId;
        address customer;
        address customerRepresentative;
        address payer;
        address student;
        bytes32 creditAccount;
        bytes32 studentNoticeChannelRef;
        uint128 normalFee;
        uint128 payableFee;
        bytes32 discountBasis;
        bytes32 rechargeDebitsHash;
        bytes32 materialsBundleRef;
        address materialPayer;
        bytes32 changeTermsRef;
        bytes32 remedyDiscountId;
    }

    struct Lesson {
        LessonTerms terms;
        uint256 packageId;
        bytes32 commitment;
        FundingCheck prefunding;
    }

    struct Form {
        PlaceTerms terms;
        bytes32 lessonId;
        uint64 version;
        bool hasAcceptance;
        Confirmation confirmation;
    }

    struct Signature {
        address signer;
        uint64 signedAt;
    }

    struct TermsProvisionConsent {
        bytes32 sourceRole;
        bytes32 sourceAuthorityId;
        uint256 disclosurePolicyId;
        bytes32 r;
        bytes32 vs;
    }

    struct FundingCheck {
        uint128 reservedUnits;
        uint64 checkedAt;
        uint256 evidenceId;
        address verifier;
        bytes32 authorityId;
    }

    struct StoredFundingCheck {
        uint128 reservedUnits;
        uint64 checkedAt;
        bool draftAdopted;
        uint256 evidenceId;
        address verifier;
        bytes32 authorityId;
    }

    struct StoredLesson {
        LessonTerms terms;
        uint256 packageId;
        bytes32 commitment;
        StoredFundingCheck prefunding;
    }

    struct Confirmation {
        uint64 confirmedAt;
        uint128 debitedUnits;
        uint256 discountEvidenceId;
    }

    struct StudentNotice {
        address sender;
        bytes32 authorityId;
        uint64 deliveredAt;
        uint64 recordedAt;
        uint256 evidenceId;
    }

    struct RosterLock {
        uint64 lockedAt;
        uint64 recordedAt;
        uint256 evidenceId;
    }

    struct TutorNotice {
        address sender;
        uint64 deliveredAt;
        uint64 recordedAt;
        bytes32 channelRef;
        uint256 evidenceId;
    }

    struct StartObservation {
        uint64 occurredAt;
        bool providerWentAhead;
        address[] studentsTakingLesson;
        bytes32 occurrenceRef;
        bytes32 unmetConditionRef;
    }

    struct Teaching {
        uint64 startedAt;
        uint64 endedAt;
        uint64 startRecordedAt;
        uint64 endRecordedAt;
        StartPermission startPermission;
        bool providerWentAhead;
        bytes32 unmetConditionRef;
        uint256 startEvidenceId;
        uint256 endEvidenceId;
    }

    struct AttendanceReport {
        bool attended;
        uint64 reportedAt;
        uint256 evidenceId;
    }

    struct ServiceFeedback {
        ServiceStatus status;
        uint64 reportedAt;
        uint256 evidenceId;
        bytes32 receivedRef;
        bytes32 notReceivedRef;
    }

    struct TutorDelivery {
        bool completed;
        uint64 reportedAt;
        uint256 evidenceId;
        bytes32 detailsRef;
    }

    bytes32 public constant ACTION_COORDINATE_BOOKING = COORDINATE_BOOKING_ACTION;
    bytes32 public constant ACTION_VERIFY_PREFUNDING = keccak256("spark.action.verify-booking-funding.v1.5");
    bytes32 public constant ACTION_VERIFY_TEACHING = keccak256("spark.action.verify-teaching-occurrence.v1.5");

    error InvalidLesson();
    error InvalidForm();
    error InvalidEvidence();
    error InvalidAcceptance();
    error InvalidPrefunding();
    error InvalidConfirmation();
    error InvalidNotice();
    error InvalidRoster();
    error InvalidTeaching();
    error InvalidReport();
    error UnauthorisedBookingActor();

    event LessonPublished(bytes32 indexed lessonId, uint256 indexed packageId, bytes32 commitment);
    event FormPublished(bytes32 indexed lessonId, bytes32 indexed placeId, bytes32 indexed formId, uint64 version);
    event RepresentativeAuthorised(bytes32 indexed formId, address indexed representative);
    event TermsProvisionRecorded(bytes32 indexed formId, address indexed recipient, uint256 indexed evidenceId);
    event TermsProvisionConsented(
        bytes32 indexed formId,
        address indexed recipient,
        address indexed source,
        bytes32 deliveryRef,
        bytes32 sourceAuthorityId
    );
    event TeachingAgreementSigned(bytes32 indexed lessonId, bytes32 indexed agreementRef, address indexed signer);
    event PrefundingVerified(bytes32 indexed lessonId, uint256 indexed evidenceId, uint128 reservedUnits);
    event FormAccepted(bytes32 indexed formId, Acceptance indexed role, address indexed signer);
    event BookingAcceptancesAdopted(bytes32 indexed formId);
    event PlaceConfirmed(
        bytes32 indexed lessonId,
        bytes32 indexed placeId,
        bytes32 indexed formId,
        uint128 debitedUnits,
        uint256 discountEvidenceId
    );
    event StudentNoticeRecorded(bytes32 indexed formId, address indexed sender, uint256 indexed evidenceId);
    event GroupRosterLocked(bytes32 indexed lessonId, uint256 indexed evidenceId, uint64 lockedAt);
    event TutorNoticeRecorded(bytes32 indexed lessonId, address indexed sender, uint256 indexed evidenceId);
    event TeachingStarted(
        bytes32 indexed lessonId, uint256 indexed evidenceId, uint64 occurredAt, StartPermission permission
    );
    event TeachingEnded(bytes32 indexed lessonId, uint256 indexed evidenceId, uint64 occurredAt);
    event AttendanceReported(
        bytes32 indexed formId, address indexed student, uint256 indexed evidenceId, bool attended
    );
    event ServiceFeedbackReported(bytes32 indexed formId, address indexed student, uint256 indexed evidenceId);
    event TutorDeliveryReported(bytes32 indexed lessonId, address indexed tutor, uint256 indexed evidenceId);

    AVARequestAllocation public immutable REQUEST_ALLOCATION;
    ISparkV15BookingFunds public immutable FUNDS;
    bytes32 public immutable WORKFLOW;
    bytes32 public immutable COORDINATOR_ROLE;
    bytes32 public immutable VERIFIER_ROLE;
    address public immutable COURSE_PROVIDER;
    address private immutable INSTALLER;
    SparkV15BookingOpening public OPENING;
    ISparkV15BookingChanges public bookingChanges;

    mapping(bytes32 => StoredLesson) private lessons;
    mapping(bytes32 => Form) private forms;
    mapping(bytes32 => mapping(bytes32 => bytes32)) public currentForm;
    mapping(bytes32 => bool) public representativeAuthorised;
    mapping(bytes32 => mapping(address => uint256)) private termsProvisions;
    mapping(bytes32 => mapping(address => uint64)) public teachingAgreementSignedAt;
    mapping(bytes32 => mapping(Acceptance => Signature)) private recordedAcceptances;
    // Single-place funding retains one form reference. Larger plans retain their
    // ordered forms and student index for direct lookups in group lessons.
    mapping(bytes32 => mapping(address => bytes32)) private fundedFormForStudent;
    mapping(bytes32 => bytes32[]) private plannedForms;
    SparkV15CourseNotices private courseNotices;
    mapping(bytes32 => RosterLock) private rosterLocks;
    mapping(bytes32 => Teaching) private teaching;
    mapping(bytes32 => address[]) private studentsAtOpening;
    mapping(bytes32 => AttendanceReport) private attendance;
    SparkV15ServiceReports private serviceReports;
    mapping(bytes32 => bytes32) private singlePlannedForm;
    SparkV15BookingPrefunding public PREFUNDING;

    constructor(
        AVARequestAllocation requests,
        ISparkV15BookingFunds funds,
        bytes32 workflow,
        bytes32 coordinatorRole,
        bytes32 verifierRole,
        address courseProvider
    ) {
        if (
            address(requests).code.length == 0 || address(funds).code.length == 0 || workflow == bytes32(0)
                || coordinatorRole == bytes32(0) || verifierRole == bytes32(0) || courseProvider == address(0)
        ) revert InvalidLesson();
        if (address(funds.REQUEST_ALLOCATION()) != address(requests) || funds.WORKFLOW() != workflow) {
            revert InvalidLesson();
        }
        REQUEST_ALLOCATION = requests;
        FUNDS = funds;
        WORKFLOW = workflow;
        COORDINATOR_ROLE = coordinatorRole;
        VERIFIER_ROLE = verifierRole;
        COURSE_PROVIDER = courseProvider;
        INSTALLER = msg.sender;
    }

    /// @notice Attach this Booking's separately deployed Opening during installation.
    function bindOpening(SparkV15BookingOpening opening) external {
        if (msg.sender != INSTALLER || address(OPENING) != address(0)) revert UnauthorisedBookingActor();
        if (opening.BOOKING() != this) revert InvalidLesson();
        OPENING = opening;
        serviceReports = opening.SERVICE_REPORTS();
        PREFUNDING = opening.PREFUNDING();
        courseNotices = opening.COURSE_NOTICES();
    }

    function bindBookingChanges(ISparkV15BookingChanges source) external {
        OPENING.requireBookingChangesBinding(bookingChanges, source, msg.sender);
        bookingChanges = source;
    }

    function reserveArrangementFunding(bytes32 lessonId, uint128 requiredUnits) external {
        if (msg.sender != address(bookingChanges)) revert UnauthorisedBookingActor();
        FUNDS.reserveLessonBudget(lessonId, requiredUnits);
    }

    function publishLesson(LessonTerms calldata terms) external {
        if (msg.sender != address(PREFUNDING)) _requireCoordinator(terms.coordinator);
        bytes32 lessonId = terms.lessonId;
        StoredLesson storage lesson = lessons[lessonId];
        if (lesson.packageId != 0) revert InvalidLesson();
        (uint256 packageId, bytes32 commitment) = OPENING.prepareLesson(terms);
        LessonTerms memory stored = terms;
        stored.lessonId = bytes32(0);
        bytes32 documents = terms.documentsRef;
        if (stored.providerResponsibilitiesRef == documents) stored.providerResponsibilitiesRef = bytes32(0);
        if (stored.tutorResponsibilitiesRef == documents) stored.tutorResponsibilitiesRef = bytes32(0);
        if (stored.startTermsRef == documents) stored.startTermsRef = bytes32(0);
        lesson.terms = stored;
        lesson.packageId = packageId;
        lesson.commitment = commitment;
        emit LessonPublished(lessonId, packageId, commitment);
    }

    function publishForm(bytes32 lessonId, PlaceTerms calldata terms) external returns (bytes32 formId) {
        StoredLesson storage lesson = lessons[lessonId];
        if (msg.sender != address(PREFUNDING)) _requireCoordinator(lesson.terms.coordinator);
        if (
            lesson.prefunding.evidenceId != 0 || block.timestamp >= _confirmationCutoff(lesson.terms)
        ) revert InvalidForm();
        Form storage previous = forms[currentForm[lessonId][terms.placeId]];
        if (previous.hasAcceptance) revert InvalidForm();

        uint64 version = previous.version + 1;
        formId = OPENING.prepareForm(terms, lesson.terms.materialsTermsRef, lesson.commitment, version);
        Form storage form = forms[formId];
        form.terms = terms;
        form.lessonId = lessonId;
        form.version = version;
        currentForm[lessonId][terms.placeId] = formId;
        emit FormPublished(lessonId, terms.placeId, formId, version);
    }

    function authoriseRepresentative(bytes32 formId) external {
        Form storage form = _currentForm(formId);
        if (msg.sender != form.terms.customer) revert UnauthorisedBookingActor();
        address representative = form.terms.customerRepresentative;
        if (representative == address(0) || representativeAuthorised[formId]) revert InvalidForm();
        representativeAuthorised[formId] = true;
        emit RepresentativeAuthorised(formId, representative);
    }

    function provisionCommitment(bytes32 formId, address recipient, bytes32 deliveryRef) public pure returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.booking.terms-provision"), formId, recipient, deliveryRef));
    }

    function recordTermsProvision(bytes32 formId, address recipient, bytes32 deliveryRef, uint256 evidenceId) external {
        uint256 packageId = _termsProvisionPackage(formId, recipient, deliveryRef);
        _requireEvidence(packageId, evidenceId, provisionCommitment(formId, recipient, deliveryRef));
        termsProvisions[formId][recipient] = evidenceId;
        emit TermsProvisionRecorded(formId, recipient, evidenceId);
    }

    /// @notice Confirm delivery using consent from a separate Source, first adopted in this transaction.
    function recordTermsProvisionWithConsent(
        bytes32 formId, address recipient, bytes32 deliveryRef, TermsProvisionConsent calldata consent
    ) external {
        uint256 packageId = _termsProvisionPackage(formId, recipient, deliveryRef);
        address source =
            PREFUNDING.adoptStandaloneTermsProvision(packageId, formId, recipient, deliveryRef, msg.sender, consent);
        emit TermsProvisionConsented(formId, recipient, source, deliveryRef, consent.sourceAuthorityId);
    }

    /// @notice The Core evidence ID for a delivery recorded using a registered receipt.
    function termsProvisionEvidence(bytes32 formId, address recipient) external view returns (uint256 evidenceId) {
        return termsProvisions[formId][recipient];
    }

    /// @notice Whether a delivery was recorded, including evidence that has since become unavailable.
    function hasTermsProvision(bytes32 formId, address recipient) public view returns (bool) {
        return termsProvisions[formId][recipient] != 0 || OPENING.hasAdoptedTermsProvision(formId, recipient);
    }

    function _termsProvisionPackage(bytes32 formId, address recipient, bytes32 deliveryRef)
        private
        view
        returns (uint256)
    {
        Form storage form = _currentForm(formId);
        StoredLesson storage lesson = lessons[form.lessonId];
        _requireCoordinator(lesson.terms.coordinator);
        if (
            recipient != form.terms.customer && recipient != lesson.terms.tutor
                && !(representativeAuthorised[formId] && recipient == form.terms.customerRepresentative)
        ) revert InvalidForm();
        if (deliveryRef == bytes32(0) || hasTermsProvision(formId, recipient)) revert InvalidEvidence();
        return lesson.packageId;
    }

    function signTeachingAgreement(bytes32 lessonId) external {
        StoredLesson storage lesson = lessons[lessonId];
        LessonTerms storage terms = lesson.terms;
        if (msg.sender != terms.provider && msg.sender != terms.tutor) revert UnauthorisedBookingActor();
        if (teachingAgreementSignedAt[lessonId][msg.sender] != 0) revert InvalidAcceptance();
        PREFUNDING.requireTeachingAgreementFunding(lessonId, lesson.prefunding.draftAdopted);
        teachingAgreementSignedAt[lessonId][msg.sender] = uint64(block.timestamp);
        emit TeachingAgreementSigned(lessonId, terms.tutorAgreementRef, msg.sender);
    }

    function prefundingCommitment(
        bytes32 lessonId,
        bytes32[] calldata formIds,
        uint128 requiredUnits,
        bytes32 fundingRef
    ) public view returns (bytes32) {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.verified-prefunding"),
                lessons[lessonId].commitment,
                formIds,
                requiredUnits,
                fundingRef
            )
        );
    }

    /// @notice Reserve spendable funds against a receipt for the checked formation and funding inventory.
    /// @dev The receipt binds the scoped inventory and amount. Detailed outcome calculations occur in the verifier's evidence.
    function verifyPrefunding(
        bytes32 lessonId,
        bytes32[] calldata formIds,
        uint128 requiredUnits,
        bytes32 fundingRef,
        uint256 evidenceId
    ) external {
        _verifyPrefunding(lessonId, formIds, requiredUnits, fundingRef, evidenceId, msg.sender);
    }

    /// @dev The installed draft module forwards the actual verifier during draft adoption.
    function verifyDraftPrefunding(
        bytes32 lessonId,
        bytes32[] calldata formIds,
        uint128 requiredUnits,
        bytes32 fundingRef,
        uint256 evidenceId,
        address verifier
    ) external {
        if (msg.sender != address(PREFUNDING)) revert UnauthorisedBookingActor();
        _verifyPrefunding(lessonId, formIds, requiredUnits, fundingRef, evidenceId, verifier);
    }

    function _verifyPrefunding(
        bytes32 lessonId,
        bytes32[] calldata formIds,
        uint128 requiredUnits,
        bytes32 fundingRef,
        uint256 evidenceId,
        address verifier
    ) private {
        StoredLesson storage lesson = lessons[lessonId];
        bytes32 authorityId =
            PREFUNDING.validateInitialCheck(lessonId, formIds, requiredUnits, fundingRef, evidenceId, verifier);
        for (uint256 i; i < formIds.length; ++i) {
            bytes32 formId = formIds[i];
            Form storage form = _currentForm(formId);
            if (form.lessonId != lessonId) revert InvalidPrefunding();
            if (formIds.length == 1) {
                singlePlannedForm[lessonId] = formId;
            } else {
                address student = form.terms.student;
                if (fundedFormForStudent[lessonId][student] != bytes32(0)) revert InvalidPrefunding();
                fundedFormForStudent[lessonId][student] = formId;
            }
        }
        if (formIds.length > 1) plannedForms[lessonId] = formIds;
        lesson.prefunding = StoredFundingCheck(
            requiredUnits, uint64(block.timestamp), msg.sender == address(PREFUNDING), evidenceId, verifier, authorityId
        );
        FUNDS.reserveLessonBudget(lessonId, requiredUnits);
        emit PrefundingVerified(lessonId, evidenceId, requiredUnits);
    }

    function acceptForm(bytes32 formId, Acceptance role) external {
        Form storage form = _currentForm(formId);
        LessonTerms storage lesson = lessons[form.lessonId].terms;
        if (role == Acceptance.Provider) {
            if (msg.sender != lesson.provider) revert UnauthorisedBookingActor();
        } else if (role == Acceptance.Tutor) {
            if (msg.sender != lesson.tutor) revert UnauthorisedBookingActor();
            if (
                !_isFundedForm(form, formId)
                    || teachingAgreementSignedAt[form.lessonId][lesson.provider] == 0
                    || teachingAgreementSignedAt[form.lessonId][lesson.tutor] == 0
            ) revert InvalidAcceptance();
        } else if (role == Acceptance.Customer) {
            if (
                msg.sender != form.terms.customer
                    && !(representativeAuthorised[formId] && msg.sender == form.terms.customerRepresentative)
            ) revert UnauthorisedBookingActor();
            if (!_isFundedForm(form, formId)) revert InvalidAcceptance();
        } else {
            if (msg.sender != form.terms.payer) revert UnauthorisedBookingActor();
        }
        if (
            block.timestamp >= _confirmationCutoff(lesson) || form.confirmation.confirmedAt != 0
                || recordedAcceptances[formId][role].signer != address(0)
        ) revert InvalidAcceptance();
        PREFUNDING.requireFormCommitmentFunding(
            form.lessonId,
            formId,
            role == Acceptance.Tutor
                ? SparkV15BookingPrefunding.CommitmentUse.TutorAcceptance
                : SparkV15BookingPrefunding.CommitmentUse.Acceptance
        );
        recordedAcceptances[formId][role] = Signature(msg.sender, uint64(block.timestamp));
        form.hasAcceptance = true;
        emit FormAccepted(formId, role, msg.sender);
    }

    function fullDiscountCommitment(bytes32 formId, bytes32 proofRef) public pure returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.booking.full-discount"), formId, proofRef));
    }

    function confirmPlace(
        bytes32 formId,
        bytes32 discountRef,
        uint256 discountEvidenceId,
        SparkV15Funds.RechargeDebit[] calldata rechargeDebits
    ) external {
        _confirmRechargePlace(formId, discountRef, discountEvidenceId, rechargeDebits, false);
    }

    /// @notice Adopt the teaching agreement and the form assents, then debit the confirmed ordinary place.
    /// @dev Both kinds of signature authorise first adoption in this transaction.
    function confirmOrdinaryPlaceWithAcceptances(
        bytes32 formId,
        SparkV15Funds.RechargeDebit[] calldata rechargeDebits,
        bytes calldata signatures,
        bytes calldata teachingSignatures
    ) external {
        OPENING.requireOrdinaryFormation(formId, signatures, teachingSignatures);
        bytes32 lessonId = forms[formId].lessonId;
        LessonTerms storage terms = lessons[lessonId].terms;
        uint64 adoptedAt = uint64(block.timestamp);
        teachingAgreementSignedAt[lessonId][terms.provider] = adoptedAt;
        teachingAgreementSignedAt[lessonId][terms.tutor] = adoptedAt;
        _confirmRechargePlace(formId, bytes32(0), 0, rechargeDebits, true);
        emit BookingAcceptancesAdopted(formId);
    }

    function _confirmRechargePlace(
        bytes32 formId,
        bytes32 discountRef,
        uint256 discountEvidenceId,
        SparkV15Funds.RechargeDebit[] calldata rechargeDebits,
        bool adoptAcceptances
    ) private {
        bytes32 sources = rechargeDebits.length == 0 ? bytes32(0) : keccak256(abi.encode(rechargeDebits));
        Form storage form = _stageConfirmation(formId, discountRef, discountEvidenceId, sources, adoptAcceptances);
        uint128 payableFee = form.confirmation.debitedUnits;
        if (payableFee != 0) {
            FUNDS.chargeLessonFrom(form.lessonId, form.terms.creditAccount, payableFee, rechargeDebits);
        }
        _emitConfirmation(formId, form);
    }

    /// @notice Charge the recharge and compensation sources committed to in the signed form.
    /// @dev `encodedSources` is `abi.encode(domain, RechargeDebit[], CompensationDebit[])`.
    function confirmPlaceFromCredits(bytes32 formId, bytes calldata encodedSources) external {
        Form storage form = _stageConfirmation(formId, bytes32(0), 0, keccak256(encodedSources), false);
        bookingChanges.CREDIT_SELECTIONS().charge(formId, encodedSources);
        _emitConfirmation(formId, form);
    }

    function _stageConfirmation(
        bytes32 formId, bytes32 discountRef, uint256 discountEvidenceId, bytes32 debitSources, bool adoptAcceptances
    )
        private
        returns (Form storage form)
    {
        form = _currentForm(formId);
        StoredLesson storage lesson = lessons[form.lessonId];
        if (!adoptAcceptances || msg.sender != address(OPENING)) _requireCoordinator(lesson.terms.coordinator);
        PlaceTerms storage place = form.terms;
        ISparkV15BookingChanges changes = bookingChanges;
        if (
            block.timestamp >= _confirmationCutoff(lesson.terms) || form.confirmation.confirmedAt != 0
                || teaching[form.lessonId].startedAt != 0 || !_isFundedForm(form, formId)
                || place.rechargeDebitsHash != debitSources
                || (address(changes) != address(0) && changes.hasFinalizedArrangement(form.lessonId))
        ) revert InvalidConfirmation();
        if (adoptAcceptances) {
            form.hasAcceptance = true;
        } else if (
            recordedAcceptances[formId][Acceptance.Provider].signer == address(0)
                || recordedAcceptances[formId][Acceptance.Tutor].signer == address(0)
                || recordedAcceptances[formId][Acceptance.Customer].signer == address(0)
                || (place.payer != place.customer && recordedAcceptances[formId][Acceptance.Payer].signer == address(0))
        ) revert InvalidConfirmation();

        uint128 payableFee = place.payableFee;
        if (payableFee == 0) {
            if (discountRef == bytes32(0) || discountEvidenceId == 0) revert InvalidConfirmation();
            _requireEvidence(lesson.packageId, discountEvidenceId, fullDiscountCommitment(formId, discountRef));
        } else if (discountRef != bytes32(0) || discountEvidenceId != 0) {
            revert InvalidConfirmation();
        }

        PREFUNDING.requireFormCommitmentFunding(
            form.lessonId,
            formId,
            adoptAcceptances
                ? SparkV15BookingPrefunding.CommitmentUse.AtomicAdoption
                : SparkV15BookingPrefunding.CommitmentUse.Confirmation
        );
        form.confirmation = Confirmation(uint64(block.timestamp), payableFee, discountEvidenceId);
        if (place.remedyDiscountId != bytes32(0)) changes.consumeBookedRemedy(formId);
    }

    function _emitConfirmation(bytes32 formId, Form storage form) private {
        emit PlaceConfirmed(
            form.lessonId,
            form.terms.placeId,
            formId,
            form.confirmation.debitedUnits,
            form.confirmation.discountEvidenceId
        );
    }

    function rosterLockCommitment(bytes32 lessonId, bytes32 registerRef) public view returns (bytes32) {
        return _rosterLockCommitment(lessons[lessonId].commitment, getConfirmedForms(lessonId), registerRef);
    }

    /// @notice Record the exact confirmed register fixed at the cutoff already agreed in Part 1.
    function lockRoster(bytes32 lessonId, bytes32 registerRef, uint256 evidenceId) external {
        StoredLesson storage lesson = lessons[lessonId];
        _requireCoordinator(lesson.terms.coordinator);
        bytes32[] memory formIds = getConfirmedForms(lessonId);
        uint64 lockedAt = lesson.terms.rosterLockAt;
        if (
            lockedAt == 0 || block.timestamp < lockedAt || rosterLocks[lessonId].evidenceId != 0 || formIds.length == 0
                || registerRef == bytes32(0)
        ) revert InvalidRoster();
        _requireEvidence(lesson.packageId, evidenceId, _rosterLockCommitment(lesson.commitment, formIds, registerRef));
        rosterLocks[lessonId] = RosterLock(lockedAt, uint64(block.timestamp), evidenceId);
        emit GroupRosterLocked(lessonId, evidenceId, lockedAt);
    }

    function studentNoticeCommitment(bytes32 formId, uint64 deliveredAt, bytes32 deliveryRef)
        public
        view
        returns (bytes32)
    {
        Form storage form = forms[formId];
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.student-notice"),
                formId,
                form.terms.student,
                form.terms.studentNoticeChannelRef,
                deliveredAt,
                deliveryRef
            )
        );
    }

    function recordStudentNotice(bytes32 formId, uint64 deliveredAt, bytes32 deliveryRef, uint256 evidenceId) external {
        if (address(courseNotices) == address(0)) revert InvalidForm();
        courseNotices.recordRegisteredStudentNotice(msg.sender, formId, deliveredAt, deliveryRef, evidenceId);
        emit StudentNoticeRecorded(formId, msg.sender, evidenceId);
    }

    function tutorNoticeCommitment(bytes32 lessonId, bytes32 channelRef, uint64 deliveredAt, bytes32 deliveryRef)
        public
        view
        returns (bytes32)
    {
        StoredLesson storage lesson = lessons[lessonId];
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.tutor-notice"),
                lesson.commitment,
                lesson.terms.tutor,
                channelRef,
                deliveredAt,
                deliveryRef
            )
        );
    }

    function recordTutorNotice(
        bytes32 lessonId,
        bytes32 channelRef,
        uint64 deliveredAt,
        bytes32 deliveryRef,
        uint256 evidenceId
    ) external {
        if (address(courseNotices) == address(0)) revert UnauthorisedBookingActor();
        courseNotices.recordRegisteredTutorNotice(msg.sender, lessonId, channelRef, deliveredAt, deliveryRef, evidenceId);
        emit TutorNoticeRecorded(lessonId, msg.sender, evidenceId);
    }

    function teachingStartCommitment(bytes32 lessonId, StartObservation calldata observation)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(keccak256("spark.v1.5.booking.teaching-start"), lessons[lessonId].commitment, observation)
        );
    }

    /// @notice Preserve a confirmed lesson's actual start independently of its permission to begin.
    function recordTeachingStarted(bytes32 lessonId, StartObservation calldata observation, uint256 evidenceId)
        external
    {
        StartPermission permission = OPENING.TEACHING_END().requireTeachingStart(
            msg.sender, lessonId, observation, evidenceId
        );
        Teaching storage occurrence = teaching[lessonId];
        occurrence.startedAt = observation.occurredAt;
        occurrence.startRecordedAt = uint64(block.timestamp);
        occurrence.startPermission = permission;
        occurrence.providerWentAhead = observation.providerWentAhead;
        occurrence.unmetConditionRef = observation.unmetConditionRef;
        occurrence.startEvidenceId = evidenceId;
        studentsAtOpening[lessonId] = observation.studentsTakingLesson;
        emit TeachingStarted(lessonId, evidenceId, observation.occurredAt, permission);
    }

    function teachingEndCommitment(bytes32 lessonId, uint64 occurredAt, bytes32 occurrenceRef)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.teaching-end"),
                lessons[lessonId].commitment,
                teaching[lessonId].startEvidenceId,
                occurredAt,
                occurrenceRef
            )
        );
    }

    function recordTeachingEnded(bytes32 lessonId, uint64 occurredAt, bytes32 occurrenceRef, uint256 evidenceId)
        external
    {
        OPENING.requireTeachingEnd(msg.sender, lessonId, occurredAt, occurrenceRef, evidenceId);
        Teaching storage occurrence = teaching[lessonId];
        occurrence.endedAt = occurredAt;
        occurrence.endRecordedAt = uint64(block.timestamp);
        occurrence.endEvidenceId = evidenceId;
        emit TeachingEnded(lessonId, evidenceId, occurredAt);
    }

    function attendanceCommitment(bytes32 formId, bool attended, bytes32 reportRef) public view returns (bytes32) {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.attendance"),
                formId,
                teaching[forms[formId].lessonId].endEvidenceId,
                attended,
                reportRef
            )
        );
    }

    /// @notice Record the student's report using Core evidence or the installed settlement's first adoption.
    function recordAttendance(bytes32 formId, bool attended, bytes32 reportRef, uint256 evidenceId) external {
        uint256 packageId;
        if (evidenceId == 0) {
            OPENING.requireSettlementWriter(msg.sender);
        } else {
            packageId = lessons[_studentReportForm(formId).lessonId].packageId;
        }
        if (attendance[formId].reportedAt != 0 || reportRef == bytes32(0)) revert InvalidReport();
        if (evidenceId != 0) {
            _requireEvidence(packageId, evidenceId, attendanceCommitment(formId, attended, reportRef));
            emit AttendanceReported(formId, msg.sender, evidenceId, attended);
        }
        attendance[formId] = AttendanceReport(attended, uint64(block.timestamp), evidenceId);
    }

    function serviceFeedbackCommitment(
        bytes32 formId,
        ServiceStatus status,
        bytes32 receivedRef,
        bytes32 notReceivedRef
    ) public view returns (bytes32) {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.service-feedback"),
                formId,
                teaching[forms[formId].lessonId].endEvidenceId,
                status,
                receivedRef,
                notReceivedRef
            )
        );
    }

    /// @notice Record the student's account of agreed service delivered or omitted, separately from attendance.
    function recordServiceFeedback(
        bytes32 formId,
        ServiceStatus status,
        bytes32 receivedRef,
        bytes32 notReceivedRef,
        uint256 evidenceId
    ) external {
        serviceReports.recordRegisteredFeedback(msg.sender, formId, status, receivedRef, notReceivedRef, evidenceId);
        emit ServiceFeedbackReported(formId, msg.sender, evidenceId);
    }

    function tutorDeliveryCommitment(bytes32 lessonId, bool completed, bytes32 detailsRef)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.booking.tutor-delivery"),
                lessons[lessonId].commitment,
                teaching[lessonId].endEvidenceId,
                completed,
                detailsRef
            )
        );
    }

    function recordTutorDelivery(bytes32 lessonId, bool completed, bytes32 detailsRef, uint256 evidenceId) external {
        serviceReports.recordRegisteredTutorDelivery(msg.sender, lessonId, completed, detailsRef, evidenceId);
        emit TutorDeliveryReported(lessonId, msg.sender, evidenceId);
    }

    function getForm(bytes32 formId) external view returns (Form memory) {
        return forms[formId];
    }

    /// @notice Whether the installed draft adopter established the original prefunding.
    function wasDraftAdopted(bytes32 lessonId) external view returns (bool) {
        return lessons[lessonId].prefunding.draftAdopted;
    }

    function acceptances(bytes32 formId, Acceptance role) external view returns (address signer, uint64 signedAt) {
        if (
            recordedAcceptances[formId][Acceptance.Provider].signer == address(0)
                && forms[formId].confirmation.confirmedAt != 0
        ) return OPENING.adoptedAcceptance(formId, role);
        Signature storage recorded = recordedAcceptances[formId][role];
        return (recorded.signer, recorded.signedAt);
    }

    function getStudentConfirmation(bytes32 lessonId, address student)
        external
        view
        returns (bytes32 formId, uint64 confirmedAt)
    {
        formId = _fundedForm(lessonId, student);
        confirmedAt = forms[formId].confirmation.confirmedAt;
    }

    function getLesson(bytes32 lessonId) external view returns (Lesson memory) {
        StoredLesson storage lesson = lessons[lessonId];
        StoredFundingCheck storage check = lesson.prefunding;
        LessonTerms memory terms = lesson.terms;
        bytes32 documents = terms.documentsRef;
        if (documents != bytes32(0)) terms.lessonId = lessonId;
        // Published references are nonzero. Here zero means the same reference as documentsRef.
        if (terms.providerResponsibilitiesRef == bytes32(0)) terms.providerResponsibilitiesRef = documents;
        if (terms.tutorResponsibilitiesRef == bytes32(0)) terms.tutorResponsibilitiesRef = documents;
        if (terms.startTermsRef == bytes32(0)) terms.startTermsRef = documents;
        return Lesson(
            terms, lesson.packageId, lesson.commitment,
            FundingCheck(check.reservedUnits, check.checkedAt, check.evidenceId, check.verifier, check.authorityId)
        );
    }

    function getEffectiveArrangement(bytes32 lessonId, uint64 at)
        public
        view
        returns (ISparkV15BookingChanges.Arrangement memory)
    {
        return OPENING.arrangementAt(lessonId, at);
    }

    function getLessonDeadlineAnchor(bytes32 lessonId, uint64 at) external view returns (uint64) {
        if (address(bookingChanges) != address(0)) return bookingChanges.deadlineAnchorAt(lessonId, at);
        return lessons[lessonId].terms.startsAt;
    }

    function isCancelledAt(bytes32 formId, uint64 at) public view returns (bool) {
        return address(bookingChanges) != address(0) && bookingChanges.isCancelledAt(formId, at);
    }

    function getPlannedForms(bytes32 lessonId) public view returns (bytes32[] memory) {
        bytes32 formId = singlePlannedForm[lessonId];
        if (formId == bytes32(0)) return plannedForms[lessonId];
        bytes32[] memory plan = new bytes32[](1);
        plan[0] = formId;
        return plan;
    }

    function getConfirmedForms(bytes32 lessonId) public view returns (bytes32[] memory result) {
        result = getPlannedForms(lessonId);
        uint256 count;
        for (uint256 i; i < result.length; ++i) {
            bytes32 formId = result[i];
            if (forms[formId].confirmation.confirmedAt != 0) {
                result[count] = formId;
                // Each iteration can add at most one result.
                unchecked { ++count; }
            }
        }
        // Return only the populated prefix, in the original plan order.
        assembly ("memory-safe") { mstore(result, count) }
    }

    function getLockedForms(bytes32 lessonId) external view returns (bytes32[] memory) {
        if (rosterLocks[lessonId].evidenceId == 0) return new bytes32[](0);
        return getConfirmedForms(lessonId);
    }

    function getRosterLock(bytes32 lessonId) external view returns (RosterLock memory) {
        return rosterLocks[lessonId];
    }

    function getStudentNotice(bytes32 formId) external view returns (StudentNotice memory) {
        if (address(courseNotices) == address(0)) {
            StudentNotice memory empty;
            return empty;
        }
        return courseNotices.getStudentNotice(formId);
    }

    function getTutorNotice(bytes32 lessonId) external view returns (TutorNotice memory) {
        if (address(courseNotices) == address(0)) {
            TutorNotice memory empty;
            return empty;
        }
        return courseNotices.getTutorNotice(lessonId);
    }

    function getTeaching(bytes32 lessonId) external view returns (Teaching memory) {
        return teaching[lessonId];
    }

    function getStudentsTakingLesson(bytes32 lessonId) external view returns (address[] memory) {
        return studentsAtOpening[lessonId];
    }

    /// @notice A zero report timestamp denotes no report. A signed report adopted in settlement has no Core ID.
    function getAttendance(bytes32 formId) external view returns (AttendanceReport memory) {
        return attendance[formId];
    }

    function getServiceFeedback(bytes32 formId) external view returns (ServiceFeedback memory) {
        return serviceReports.getServiceFeedback(formId);
    }

    function getTutorDelivery(bytes32 lessonId) external view returns (TutorDelivery memory) {
        return serviceReports.getTutorDelivery(lessonId);
    }

    function getTutorCompletedLessons(address tutor) external view returns (bytes32[] memory) {
        return serviceReports.getTutorCompletedLessons(tutor);
    }

    function _currentForm(bytes32 formId) private view returns (Form storage form) {
        form = forms[formId];
        if (form.version == 0 || currentForm[form.lessonId][form.terms.placeId] != formId) revert InvalidForm();
    }

    function _isFundedForm(Form storage form, bytes32 formId) private view returns (bool) {
        return _fundedForm(form.lessonId, form.terms.student) == formId;
    }

    function _fundedForm(bytes32 lessonId, address student) private view returns (bytes32) {
        bytes32 formId = singlePlannedForm[lessonId];
        if (formId == bytes32(0)) return fundedFormForStudent[lessonId][student];
        return forms[formId].terms.student == student ? formId : bytes32(0);
    }

    function _studentReportForm(bytes32 formId) private view returns (Form storage form) {
        form = _currentForm(formId);
        if (msg.sender != form.terms.student) revert UnauthorisedBookingActor();
        if (form.confirmation.confirmedAt == 0 || teaching[form.lessonId].endedAt == 0) revert InvalidReport();
    }

    function _rosterLockCommitment(bytes32 lessonCommitment, bytes32[] memory formIds, bytes32 registerRef)
        private
        pure
        returns (bytes32)
    {
        return
            keccak256(abi.encode(keccak256("spark.v1.5.booking.roster-lock"), lessonCommitment, formIds, registerRef));
    }

    function _requireCoordinator(address coordinator) private view returns (bytes32) {
        if (msg.sender != coordinator) revert UnauthorisedBookingActor();
        return OPENING.requireBookingActor(coordinator, COORDINATOR_ROLE, ACTION_COORDINATE_BOOKING);
    }

    function _confirmationCutoff(LessonTerms storage terms) private view returns (uint64) {
        return terms.rosterLockAt == 0 ? terms.startsAt : terms.rosterLockAt;
    }

    function _requireEvidence(uint256 packageId, uint256 evidenceId, bytes32 commitment) private view {
        OPENING.requireEvidence(packageId, evidenceId, commitment);
    }
}

/// @notice Validates booking inputs and determines start permission from the reported actual opening.
contract SparkV15BookingOpening {
    error InvalidSettlementEvidence();

    bytes32 private constant DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant TERMS_CONSENT_TYPEHASH = keccak256(
        "TermsProvisionConsent(uint256 packageId,bytes32 formId,address recipient,bytes32 deliveryRef,address coordinator,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId)"
    );
    bytes32 private constant ORDINARY_SETTLEMENT_CONSENT_TYPEHASH = keccak256(
        "OrdinarySettlementConsent(uint256 packageId,bytes32 lessonId,bytes32 basis,address approver,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId)"
    );
    bytes32 private constant ORDINARY_WAGE_EVIDENCE_TYPEHASH = keccak256(
        "OrdinaryWageEvidence(bytes32 commitment,uint256 packageId,bytes32 sourceRole,bytes32 sourceAuthorityId,uint256 disclosurePolicyId,uint64 validThrough)"
    );
    bytes32 private constant BOOKING_ACCEPTANCE_TYPEHASH =
        keccak256("AdoptBookingAcceptance(bytes32 formId,uint256 fundingEvidenceId,uint8 role)");
    bytes32 private constant TEACHING_AGREEMENT_TYPEHASH =
        keccak256("AdoptTeachingAgreement(bytes32 formId,uint256 fundingEvidenceId,uint8 role)");
    uint256 private constant SIGNATURE_S_MASK = type(uint256).max >> 1;
    uint256 private constant MAX_CANONICAL_S = 0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0;
    bytes32 private immutable DEFAULT_CORE_POLICY_CODE_HASH;
    SparkV15Booking public immutable BOOKING;
    SparkV15BookingPrefunding public immutable PREFUNDING;
    SparkV15TeachingEnd public immutable TEACHING_END;
    SparkV15ServiceReports public immutable SERVICE_REPORTS;
    SparkV15CourseNotices public immutable COURSE_NOTICES;
    AVARequestAllocation private immutable REQUEST_ALLOCATION;
    mapping(bytes32 => bool) public ordinaryAcceptanceWithdrawn;
    mapping(bytes32 => mapping(address => bool)) public adoptedTermsProvision;

    event UnusedBookingAcceptanceWithdrawn(bytes32 indexed formId, SparkV15Booking.Acceptance indexed role);

    struct OrdinarySettlementConsent {
        bytes32 sourceRole;
        bytes32 sourceAuthorityId;
        uint256 disclosurePolicyId;
        bytes32 r;
        bytes32 vs;
    }

    struct OrdinaryWageEvidence {
        bytes32 sourceRole;
        bytes32 sourceAuthorityId;
        uint256 disclosurePolicyId;
        uint64 validThrough;
        bytes32 r;
        bytes32 vs;
    }

    struct DeliveredTerms {
        bytes32 deliveryRef;
        SparkV15Booking.TermsProvisionConsent consent;
    }

    constructor(
        SparkV15Booking booking,
        SparkV15BookingPrefunding prefunding,
        SparkV15TeachingEnd teachingEnd,
        SparkV15CourseNotices courseNotices
    ) {
        if (prefunding.BOOKING() != booking || teachingEnd.BOOKING() != booking || courseNotices.BOOKING() != booking) {
            revert SparkV15Booking.InvalidLesson();
        }
        BOOKING = booking;
        COURSE_NOTICES = courseNotices;
        PREFUNDING = prefunding;
        REQUEST_ALLOCATION = booking.REQUEST_ALLOCATION();
        DEFAULT_CORE_POLICY_CODE_HASH = keccak256(type(DefaultAVACorePolicyBundle).runtimeCode);
        TEACHING_END = teachingEnd;
        SERVICE_REPORTS = new SparkV15ServiceReports(booking, this);
    }

    /// @notice Adopt verified terms deliveries before adopting the agreements and charging the reserved place.
    /// @dev Each new delivery records evidence first adopted now. Previously recorded deliveries are reused.
    function confirmOrdinaryPlaceWithDeliveries(
        bytes32 formId,
        SparkV15Funds.RechargeDebit[] calldata rechargeDebits,
        bytes calldata signatures,
        bytes calldata teachingSignatures,
        DeliveredTerms calldata customerDelivery,
        DeliveredTerms calldata tutorDelivery
    ) external {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        if (msg.sender != lesson.terms.coordinator) revert SparkV15Booking.UnauthorisedBookingActor();
        requireBookingActor(msg.sender, BOOKING.COORDINATOR_ROLE(), COORDINATE_BOOKING_ACTION);
        // These deliveries persist only if Booking accepts the current form, the ordinary
        // lesson, and the first teaching agreement and charges the reserved place.
        _adoptTermsDelivery(lesson.packageId, formId, form.terms.customer, customerDelivery);
        _adoptTermsDelivery(lesson.packageId, formId, lesson.terms.tutor, tutorDelivery);
        BOOKING.confirmOrdinaryPlaceWithAcceptances(formId, rechargeDebits, signatures, teachingSignatures);
    }

    function _adoptTermsDelivery(uint256 packageId, bytes32 formId, address recipient, DeliveredTerms calldata delivery)
        private
    {
        if (BOOKING.hasTermsProvision(formId, recipient)) return;
        if (delivery.deliveryRef == bytes32(0)) revert SparkV15Booking.InvalidEvidence();
        address source =
            _termsProvisionSource(packageId, formId, recipient, delivery.deliveryRef, msg.sender, delivery.consent);
        adoptedTermsProvision[formId][recipient] = true;
        emit SparkV15Booking.TermsProvisionConsented(
            formId, recipient, source, delivery.deliveryRef, delivery.consent.sourceAuthorityId
        );
    }

    /// @notice First publish a paid one-to-one booking draft when the verifier reserves its backing.
    /// @dev The coordinator signs for this publication only. Deliveries and acceptances take effect separately.
    function adoptOrdinaryBookingDraft(
        SparkV15Booking.LessonTerms calldata lesson,
        SparkV15Booking.PlaceTerms calldata place,
        uint128 requiredUnits,
        bytes32 fundingRef,
        uint256 evidenceId,
        uint64 validThrough,
        bytes32 r,
        bytes32 vs
    ) external returns (bytes32 formId) {
        return PREFUNDING.adoptRegisteredDraft(
            lesson, place, requiredUnits, fundingRef, evidenceId, validThrough, r, vs, msg.sender
        );
    }

    function requireDraftAgreementDelivery(bytes32 formId, address tutor) external view {
        PREFUNDING.requireDraftAgreementDelivery(formId, tutor);
    }

    /// @notice Delivery history from either signed adoption entry point.
    function hasAdoptedTermsProvision(bytes32 formId, address recipient) external view returns (bool) {
        return adoptedTermsProvision[formId][recipient] || PREFUNDING.hasStandaloneTermsProvision(formId, recipient);
    }

    /// @notice Current eligibility of the delivery already bound to this recipient and form.
    function hasUsableTermsProvision(bytes32 formId, address recipient, uint256 packageId) public view returns (bool) {
        return PREFUNDING.hasUsableTermsProvision(formId, recipient, packageId);
    }

    function hasUsableCustomerTerms(bytes32 formId, address customer, address representative, uint256 packageId)
        public
        view
        returns (bool)
    {
        return PREFUNDING.hasUsableCustomerTerms(formId, customer, representative, packageId);
    }

    function requireBookingActor(address actor, bytes32 role, bytes32 action) public view returns (bytes32) {
        return REQUEST_ALLOCATION.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(actor, SparkV15.APP_ID, role, action);
    }

    function requireBookingChangesBinding(
        ISparkV15BookingChanges current, ISparkV15BookingChanges target, address admin
    ) external view {
        REQUEST_ALLOCATION.IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(admin, SparkV15.APP_ID);
        if (
            address(current) != address(0) || address(target).code.length == 0 || target.BOOKING() != address(BOOKING)
        ) revert SparkV15Booking.InvalidLesson();
    }

    function requireSettlementWriter(address writer) external view {
        address payments = SparkV15Funds(address(BOOKING.FUNDS())).PAYMENTS();
        if (writer != ISparkV15SettlementBinding(payments).settlementPolicy()) {
            revert SparkV15Booking.UnauthorisedBookingActor();
        }
    }

    function prepareLesson(SparkV15Booking.LessonTerms calldata terms)
        external
        view
        returns (uint256 packageId, bytes32 commitment)
    {
        if (
            terms.lessonId == bytes32(0) || terms.provider != BOOKING.COURSE_PROVIDER() || terms.tutor == address(0)
                || terms.startsAt <= block.timestamp || terms.endsAt <= terms.startsAt
                || terms.timeZoneRef == bytes32(0) || terms.tutorAgreementRef == bytes32(0)
                || terms.serviceTermsRef == bytes32(0) || terms.tutorPayTermsRef == bytes32(0)
                || terms.providerResponsibilitiesRef == bytes32(0) || terms.tutorResponsibilitiesRef == bytes32(0)
                || terms.startTermsRef == bytes32(0) || terms.documentsRef == bytes32(0)
        ) revert SparkV15Booking.InvalidLesson();
        if (terms.rosterRef == bytes32(0)) {
            if (terms.rosterLockAt != 0) revert SparkV15Booking.InvalidLesson();
        } else if (terms.rosterLockAt <= block.timestamp || terms.rosterLockAt > terms.startsAt) {
            revert SparkV15Booking.InvalidLesson();
        }
        packageId = REQUEST_ALLOCATION.RULE_PACKAGE_REGISTRY().getActivePackageId(SparkV15.APP_ID, BOOKING.WORKFLOW());
        if (packageId == 0) revert SparkV15Booking.InvalidLesson();
        commitment = keccak256(abi.encode(block.chainid, address(BOOKING), packageId, terms));
    }

    function requireEvidence(uint256 packageId, uint256 evidenceId, bytes32 commitment) public view {
        AVAEvidenceRegistry registry = REQUEST_ALLOCATION.EVIDENCE_REGISTRY();
        registry.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        if (registry.getEvidenceReference(evidenceId).commitment != commitment) {
            revert SparkV15Booking.InvalidEvidence();
        }
    }

    function requireTeachingEnd(
        address actor,
        bytes32 lessonId,
        uint64 occurredAt,
        bytes32 occurrenceRef,
        uint256 evidenceId
    ) external view {
        bool adopted = actor == address(TEACHING_END);
        if (!adopted) requireBookingActor(actor, BOOKING.VERIFIER_ROLE(), BOOKING.ACTION_VERIFY_TEACHING());
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        if (
            teaching.startedAt == 0 || teaching.endedAt != 0 || occurredAt <= teaching.startedAt
                || occurredAt > block.timestamp || occurrenceRef == bytes32(0)
        ) revert SparkV15Booking.InvalidTeaching();
        if (!adopted) {
            requireEvidence(
                BOOKING.getLesson(lessonId).packageId,
                evidenceId,
                BOOKING.teachingEndCommitment(lessonId, occurredAt, occurrenceRef)
            );
        }
    }

    function requireTeachingEndEvidence(bytes32 lessonId, uint256 evidenceId, uint256 packageId) external view {
        TEACHING_END.requireAvailable(lessonId, evidenceId, packageId);
    }

    function requireTeachingStartEvidence(bytes32 lessonId, uint256 evidenceId, uint256 packageId) external view {
        TEACHING_END.requireStartAvailable(lessonId, evidenceId, packageId);
    }

    function prepareForm(
        SparkV15Booking.PlaceTerms calldata terms,
        bytes32 materialsTermsRef,
        bytes32 lessonCommitment,
        uint64 version
    ) external view returns (bytes32) {
        requireValidPlace(terms, materialsTermsRef);
        return keccak256(abi.encode(lessonCommitment, version, terms));
    }

    function requireValidPlace(SparkV15Booking.PlaceTerms calldata terms, bytes32 materialsTermsRef) public view {
        bool usesMaterials = terms.materialsBundleRef != bytes32(0);
        if (
            terms.placeId == bytes32(0) || terms.customer == address(0) || terms.payer == address(0)
                || terms.student == address(0) || terms.creditAccount == bytes32(0)
                || terms.studentNoticeChannelRef == bytes32(0) || terms.normalFee == 0
                || terms.payableFee > terms.normalFee
                || (terms.payableFee < terms.normalFee && terms.discountBasis == bytes32(0))
                || (terms.payableFee == 0 && terms.rechargeDebitsHash != bytes32(0))
                || (usesMaterials != (terms.materialPayer != address(0)))
                || (usesMaterials && materialsTermsRef == bytes32(0))
                || (terms.remedyDiscountId != bytes32(0) && terms.payableFee == terms.normalFee)
        ) revert SparkV15Booking.InvalidForm();
        ISparkV15BookingFunds funds = BOOKING.FUNDS();
        if (
            terms.payableFee != 0 && terms.creditAccount != funds.creditAccount(terms.customer)
                && terms.creditAccount != funds.creditAccount(terms.payer)
        ) revert SparkV15Booking.InvalidForm();
    }

    function requireOrdinaryFormation(bytes32 formId, bytes calldata signatures, bytes calldata teachingSignatures)
        external
        view
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        SparkV15Booking.PlaceTerms memory place = form.terms;
        bool namedPayer = place.customer != place.payer;
        uint256 acceptanceCount = namedPayer ? 4 : 3;
        uint256 evidenceId = lesson.prefunding.evidenceId;
        if (
            lesson.terms.rosterRef != bytes32(0) || lesson.terms.materialsTermsRef != bytes32(0)
                || form.hasAcceptance || ordinaryAcceptanceWithdrawn[formId]
                || place.customerRepresentative != address(0) || place.payableFee == 0
                || place.payableFee != place.normalFee || evidenceId == 0
                || BOOKING.FUNDS().lessonReserved(form.lessonId) < lesson.prefunding.reservedUnits
                || signatures.length != acceptanceCount * 64
                || !hasUsableTermsProvision(formId, place.customer, lesson.packageId)
                || !hasUsableTermsProvision(formId, lesson.terms.tutor, lesson.packageId)
        ) revert SparkV15Booking.InvalidAcceptance();
        PREFUNDING.requireAvailable(form.lessonId, evidenceId, lesson.packageId);
        address[4] memory actors = [lesson.terms.provider, lesson.terms.tutor, place.customer, place.payer];
        for (uint256 role; role < acceptanceCount; ++role) {
            bytes32 message = keccak256(abi.encode(BOOKING_ACCEPTANCE_TYPEHASH, formId, evidenceId, role));
            _requireRoleSignature(message, signatures, role, actors[role]);
        }
        if (teachingSignatures.length != 128) revert SparkV15Booking.InvalidAcceptance();
        for (uint256 role; role < 2; ++role) {
            address actor = actors[role];
            if (BOOKING.teachingAgreementSignedAt(form.lessonId, actor) != 0) revert SparkV15Booking.InvalidAcceptance();
            bytes32 message = keccak256(abi.encode(TEACHING_AGREEMENT_TYPEHASH, formId, evidenceId, role));
            _requireRoleSignature(message, teachingSignatures, role, actor);
        }
    }

    function _requireRoleSignature(bytes32 message, bytes calldata signatures, uint256 index, address actor) private view {
        bytes32 r;
        bytes32 vs;
        // The entry points check the packet length before indexing any signature.
        assembly ("memory-safe") {
            let offset := add(signatures.offset, mul(index, 64))
            r := calldataload(offset)
            vs := calldataload(add(offset, 32))
        }
        address signer = recoverSource(
            keccak256("Spark DAO Booking Acceptance"), address(BOOKING), message, r, vs
        );
        if (signer != actor) revert SparkV15Booking.InvalidAcceptance();
    }

    /// @notice Prevent first adoption of the local consents for this form.
    /// @dev Prior recorded commitments and the separate acceptance route retain their existing effect.
    function withdrawUnusedBookingAcceptance(bytes32 formId, SparkV15Booking.Acceptance role) external {
        (address signer, uint64 adoptedAt) = _formSignerAtConfirmation(formId, role);
        if (adoptedAt != 0 || signer != msg.sender || ordinaryAcceptanceWithdrawn[formId]) {
            revert SparkV15Booking.InvalidAcceptance();
        }
        ordinaryAcceptanceWithdrawn[formId] = true;
        emit UnusedBookingAcceptanceWithdrawn(formId, role);
    }

    function adoptedAcceptance(bytes32 formId, SparkV15Booking.Acceptance role)
        external
        view
        returns (address signer, uint64 adoptedAt)
    {
        if (msg.sender != address(BOOKING)) revert SparkV15Booking.InvalidAcceptance();
        return _formSignerAtConfirmation(formId, role);
    }

    function _formSignerAtConfirmation(bytes32 formId, SparkV15Booking.Acceptance role)
        private
        view
        returns (address signer, uint64 adoptedAt)
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        adoptedAt = form.confirmation.confirmedAt;
        if (role == SparkV15Booking.Acceptance.Customer) return (form.terms.customer, adoptedAt);
        if (role == SparkV15Booking.Acceptance.Payer) {
            if (form.terms.payer == form.terms.customer) return (address(0), 0);
            return (form.terms.payer, adoptedAt);
        }
        SparkV15Booking.LessonTerms memory terms = BOOKING.getLesson(form.lessonId).terms;
        return (role == SparkV15Booking.Acceptance.Provider ? terms.provider : terms.tutor, adoptedAt);
    }

    function requireTermsProvisionConsent(
        uint256 packageId,
        bytes32 formId,
        address recipient,
        bytes32 deliveryRef,
        address coordinator,
        SparkV15Booking.TermsProvisionConsent calldata consent
    ) external view returns (address source) {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        if (
            form.hasAcceptance || lesson.terms.rosterRef != bytes32(0) || lesson.terms.materialsTermsRef != bytes32(0)
                || block.timestamp >= lesson.terms.startsAt
                || BOOKING.teachingAgreementSignedAt(form.lessonId, lesson.terms.provider) != 0
                || BOOKING.teachingAgreementSignedAt(form.lessonId, lesson.terms.tutor) != 0
        ) revert SparkV15Booking.InvalidForm();

        return _termsProvisionSource(packageId, formId, recipient, deliveryRef, coordinator, consent);
    }

    function _termsProvisionSource(
        uint256 packageId,
        bytes32 formId,
        address recipient,
        bytes32 deliveryRef,
        address coordinator,
        SparkV15Booking.TermsProvisionConsent calldata consent
    ) private view returns (address source) {
        bytes32 message = keccak256(
            abi.encode(
                TERMS_CONSENT_TYPEHASH,
                packageId,
                formId,
                recipient,
                deliveryRef,
                coordinator,
                consent.sourceRole,
                consent.sourceAuthorityId,
                consent.disclosurePolicyId
            )
        );
        source = recoverSource(keccak256("Spark DAO Terms Delivery"), address(BOOKING), message, consent.r, consent.vs);
        if (source == coordinator) revert SparkV15Booking.InvalidEvidence();
        this.requireFirstUseEvidenceSource(
            packageId,
            source,
            consent.sourceRole,
            consent.sourceAuthorityId,
            consent.disclosurePolicyId,
            keccak256("spark.v1.5.booking.receipt"),
            false
        );
    }

    function requireRegisteredSettlementEvidence(
        uint256 evidenceId,
        uint256 packageId,
        bytes32 basis,
        uint64 proposedAt,
        address proposer,
        address approver
    ) external view {
        AVAEvidenceRegistry registry = REQUEST_ALLOCATION.EVIDENCE_REGISTRY();
        registry.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        AVACoreTypes.EvidenceRecord memory evidence = registry.getEvidence(evidenceId);
        if (
            evidence.commitment != basis || evidence.registeredAt < proposedAt
                || evidence.registeredBy == proposer || evidence.registeredBy == approver
        ) revert InvalidSettlementEvidence();
    }

    function requireIndependentProviderStartSource(uint256 evidenceId, bytes32 lessonId, bytes32 formId, address paidTo)
        external
        view
    {
        TEACHING_END.requireIndependentProviderStartSource(evidenceId, lessonId, formId, paidTo);
    }

    /// @notice Validate a Source signature for the calling Settlement's current ordinary proposal.
    function requireOrdinarySettlementConsent(
        uint256 packageId,
        bytes32 lessonId,
        bytes32 basis,
        address approver,
        address proposer,
        OrdinarySettlementConsent calldata consent
    ) external view returns (address source) {
        if (BOOKING.getLesson(lessonId).terms.materialsTermsRef != bytes32(0)) {
            revert SparkV15Booking.InvalidEvidence();
        }
        bytes32 message = keccak256(
            abi.encode(
                ORDINARY_SETTLEMENT_CONSENT_TYPEHASH,
                packageId,
                lessonId,
                basis,
                approver,
                consent.sourceRole,
                consent.sourceAuthorityId,
                consent.disclosurePolicyId
            )
        );
        source = recoverSource(keccak256("Spark DAO Ordinary Settlement"), msg.sender, message, consent.r, consent.vs);
        if (source == approver || source == proposer) revert SparkV15Booking.InvalidEvidence();
        this.requireFirstUseEvidenceSource(
            packageId,
            source,
            consent.sourceRole,
            consent.sourceAuthorityId,
            consent.disclosurePolicyId,
            keccak256("spark.v1.5.settlement.support"),
            false
        );
    }

    /// @notice Verify separate Source evidence for the exact new wage at first use.
    function requireOrdinaryWageEvidence(uint256 packageId, bytes32 commitment, OrdinaryWageEvidence calldata proof)
        external
        view
        returns (address source)
    {
        if (block.timestamp > proof.validThrough) revert SparkV15Booking.InvalidEvidence();
        bytes32 message = keccak256(
            abi.encode(
                ORDINARY_WAGE_EVIDENCE_TYPEHASH,
                commitment,
                packageId,
                proof.sourceRole,
                proof.sourceAuthorityId,
                proof.disclosurePolicyId,
                proof.validThrough
            )
        );
        source = recoverSource(keccak256("Spark DAO Ordinary Wage Evidence"), msg.sender, message, proof.r, proof.vs);
        this.requireFirstUseEvidenceSource(
            packageId,
            source,
            proof.sourceRole,
            proof.sourceAuthorityId,
            proof.disclosurePolicyId,
            keccak256("spark.v1.5.settlement.wage-evidence"),
            true
        );
    }

    function recoverSource(bytes32 domainName, address verifyingContract, bytes32 message, bytes32 r, bytes32 vs)
        public
        view
        returns (address source)
    {
        bytes32 domain =
            keccak256(abi.encode(DOMAIN_TYPEHASH, domainName, keccak256("1"), block.chainid, verifyingContract));
        uint256 s = uint256(vs) & SIGNATURE_S_MASK;
        if (s > MAX_CANONICAL_S) revert SparkV15Booking.InvalidEvidence();
        source = ecrecover(
            keccak256(abi.encodePacked(hex"1901", domain, message)), uint8(27 + (uint256(vs) >> 255)), r, bytes32(s)
        );
        if (source == address(0)) revert SparkV15Booking.InvalidEvidence();
    }

    function requireFirstUseEvidenceSource(
        uint256 packageId,
        address source,
        bytes32 sourceRole,
        bytes32 sourceAuthorityId,
        uint256 disclosurePolicyId,
        bytes32 evidenceTypeHash,
        bool requiresDefaultLifecycle
    ) external view {
        bytes32 appId = SparkV15.APP_ID;
        bytes32 workflow = BOOKING.WORKFLOW();
        REQUEST_ALLOCATION.AUTHORITY_MATRIX().requireAuthorisedSubject(
            source, appId, sourceRole, AVACoreTypes.ACTION_REGISTER_EVIDENCE, sourceAuthorityId
        );
        AVAEvidenceRegistry registry = REQUEST_ALLOCATION.EVIDENCE_REGISTRY();
        registry.DISCLOSURE_REGISTRY().requireActivePolicyReference(disclosurePolicyId, appId);

        bytes32[] memory keys = new bytes32[](requiresDefaultLifecycle ? 4 : 3);
        keys[0] = AVACapabilityKeys.APPLICATION;
        keys[1] = AVACapabilityKeys.EVIDENCE_POLICY;
        keys[2] = AVACapabilityKeys.DISCLOSURE_POLICY;
        if (requiresDefaultLifecycle) keys[3] = AVACapabilityKeys.EVIDENCE_LIFECYCLE;
        (, address[] memory modules) =
            registry.RULE_PACKAGE_REGISTRY().getActiveVerifiedModulesCompact(appId, workflow, packageId, keys);
        // Only the installed default policies can admit this one-use consent without a Core evidence ID.
        SparkV15ApplicationModule application = SparkV15ApplicationModule(modules[0]);
        if (
            modules[1].codehash != DEFAULT_CORE_POLICY_CODE_HASH || modules[2].codehash != DEFAULT_CORE_POLICY_CODE_HASH
                || (requiresDefaultLifecycle && modules[3].codehash != DEFAULT_CORE_POLICY_CODE_HASH)
                || sourceRole != application.SOURCE_ROLE()
        ) revert SparkV15Booking.InvalidEvidence();
        application.validateEvidence(
            IAVAApplicationModule.EvidenceContext({
                appId: appId,
                workflowKey: workflow,
                packageId: packageId,
                roleKey: sourceRole,
                subjectId: sourceAuthorityId,
                evidenceTypeHash: evidenceTypeHash,
                disclosurePolicyId: disclosurePolicyId,
                authorityId: sourceAuthorityId,
                actor: source
            })
        );
    }

    function arrangementAt(bytes32 lessonId, uint64 at)
        public
        view
        returns (ISparkV15BookingChanges.Arrangement memory arrangement)
    {
        ISparkV15BookingChanges changes = BOOKING.bookingChanges();
        if (address(changes) != address(0)) return changes.effectiveArrangementAt(lessonId, at);
        SparkV15Booking.LessonTerms memory terms = BOOKING.getLesson(lessonId).terms;
        arrangement.startsAt = terms.startsAt;
        arrangement.endsAt = terms.endsAt;
        arrangement.tutor = terms.tutor;
        arrangement.tutorFee = terms.tutorFee;
        arrangement.tutorAgreementRef = terms.tutorAgreementRef;
        arrangement.tutorPayTermsRef = terms.tutorPayTermsRef;
        arrangement.tutorNoticeChannelRef = terms.tutorNoticeChannelRef;
        arrangement.timeZoneRef = terms.timeZoneRef;
    }

    function startPermission(bytes32 lessonId, bool group, uint64 startedAt, address[] calldata students)
        external
        view
        returns (SparkV15Booking.StartPermission)
    {
        ISparkV15BookingChanges.Arrangement memory arrangement = arrangementAt(lessonId, startedAt);
        if (startedAt < arrangement.startsAt || (group && students.length == 0)) {
            return SparkV15Booking.StartPermission.RequirementsNotMet;
        }
        if (group) {
            SparkV15Booking.RosterLock memory roster = BOOKING.getRosterLock(lessonId);
            if (roster.evidenceId == 0 || roster.lockedAt >= startedAt) {
                return SparkV15Booking.StartPermission.Unverified;
            }
        }

        bool activeStudent;
        for (uint256 i; i < students.length; ++i) {
            (bytes32 formId, uint64 confirmedAt) = BOOKING.getStudentConfirmation(lessonId, students[i]);
            if (confirmedAt == 0) return SparkV15Booking.StartPermission.RequirementsNotMet;
            if (!BOOKING.isCancelledAt(formId, startedAt)) activeStudent = true;
        }
        if (group && !activeStudent) return SparkV15Booking.StartPermission.RequirementsNotMet;

        ISparkV15BookingChanges changes = BOOKING.bookingChanges();
        bytes32 changeId = arrangement.changeId;
        bool ready;
        if (changeId == bytes32(0)) {
            SparkV15Booking.TutorNotice memory notice = BOOKING.getTutorNotice(lessonId);
            ready = notice.evidenceId != 0 && notice.deliveredAt < startedAt;
        } else {
            ready = changes.hasTutorNotice(changeId, startedAt);
        }
        bytes32[] memory formIds = BOOKING.getConfirmedForms(lessonId);
        for (uint256 i; i < formIds.length; ++i) {
            bytes32 formId = formIds[i];
            uint64 confirmedAt = BOOKING.getForm(formId).confirmation.confirmedAt;
            if (confirmedAt > startedAt || (!group && BOOKING.isCancelledAt(formId, startedAt))) {
                return SparkV15Booking.StartPermission.RequirementsNotMet;
            }
            if (changeId == bytes32(0)) {
                SparkV15Booking.StudentNotice memory notice = BOOKING.getStudentNotice(formId);
                ready = ready && confirmedAt < startedAt && notice.evidenceId != 0 && notice.deliveredAt < startedAt;
            } else {
                ready = ready && confirmedAt < startedAt && changes.hasStudentNotice(changeId, formId, startedAt);
            }
        }
        return ready ? SparkV15Booking.StartPermission.Permitted : SparkV15Booking.StartPermission.Unverified;
    }
}
