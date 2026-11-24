// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVAIdentityRegistry} from "@ava-protocol/contracts/src/core/AVAIdentityRegistry.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {SparkV15Booking} from "./SparkV15Booking.sol";
import {SparkV15Funds} from "./SparkV15Funds.sol";
import {SparkV15CustomerRedress, SparkV15LessonRemedies} from "./SparkV15LessonRemedies.sol";
import {SparkV15Materials} from "./SparkV15Materials.sol";
import {SparkV15PaymentObservations} from "./SparkV15PaymentObservations.sol";
import {SparkV15Payments} from "./SparkV15Payments.sol";
import {
    SparkV15ConcernIntake,
    SparkV15ReviewActions,
    SparkV15ReviewCases,
    SparkV15ReviewContext
} from "./SparkV15ReviewCases.sol";
import {SparkV15Settlement} from "./SparkV15Settlement.sol";

interface ISparkV15MaterialRights {
    function MATERIALS() external view returns (address);
    function holderPortion(bytes32 scopeId, address holder, uint64 postingAt, uint64 knownAt)
        external
        view
        returns (uint256);
    function hasApplicableTransfer(bytes32 scopeId, uint64 postingAt, uint64 knownAt) external view returns (bool);
    function hasTransfer(bytes32 scopeId, uint64 atTime) external view returns (bool);
    function nextTransferAcceptanceOrder() external view returns (uint64);
    function nativeReceiptTransferBasis(bytes32 scopeId, uint256 receiptId) external view returns (bytes32);
    function syncMaterialScope(bytes32 scopeId) external;
    function holderPortionWithoutHeldPredecessors(bytes32 scopeId, address holder, uint64 atTime)
        external
        view
        returns (uint256);
    function holderPortionForRebase(bytes32 scopeId, address holder, uint64 atTime) external view returns (uint256);
    function scopeTransferBasisAt(bytes32 scopeId, uint64 postingAt, uint64 knownAt) external view returns (bytes32);
    function readHolderPortion(
        bytes32 scopeId,
        address holder,
        uint64 postingAt,
        uint64 knownAt,
        bool checkPredecessorHolds,
        uint256 casePackageId
    ) external view returns (uint256);
}

/// @notice Seat-scoped pending material estimates and their protection in the shared Funds vault.
contract SparkV15MaterialProvisions {
    struct ProvisionInput {
        bytes32 formId;
        bytes32 material;
        uint128 budget;
        bytes32 sourceRef;
    }

    struct Provision {
        ProvisionInput input;
        uint64 checkedAt;
        uint256 evidenceId;
        address verifiedBy;
        uint256 heldForLesson;
        uint256 availableProviderCash;
    }

    struct EntitlementInput {
        bytes32 scopeId;
        address holder;
        address recipient;
        uint64 verifiedAt;
        uint64 postLiftDeadline;
        bytes32 sourceRef;
    }

    struct Entitlement {
        EntitlementInput input;
        uint128 amount;
        uint256 evidenceId;
        address verifiedBy;
    }

    struct MaterialReceipt {
        bytes32 obligationId;
        uint64 paidAt;
        uint64 verifiedAt;
        uint256 evidenceId;
        address verifiedBy;
    }

    struct MaterialReceiptRecord {
        bytes32 obligationId;
        uint64 paidAt;
        uint64 verifiedAt;
        uint64 nextTransferAcceptanceOrder;
        uint256 evidenceId;
        address verifiedBy;
    }

    error InvalidProvision();
    error InvalidFundingEvidence();
    error InvalidEntitlement();
    error InvalidMaterialReceipt();
    error InvalidCaseChargeScope();
    error InsufficientMaterialBacking();
    error NotFunds();

    bytes32 public constant ACTION_VERIFY_PROVISION = keccak256("spark.action.verify-material-provision.v1.5");
    bytes32 public constant ACTION_VERIFY_ENTITLEMENT = keccak256("spark.action.verify-material-entitlement.v1.5");
    bytes32 public constant ACTION_VERIFY_MATERIAL_RECEIPT = keccak256("spark.action.verify-material-receipt.v1.5");
    bytes32 public constant ACTION_FILE_MATERIAL_RECEIPT = keccak256("spark.action.file-material-receipt.v1.5");

    SparkV15Payments public immutable PAYMENTS;
    SparkV15Materials public immutable MATERIALS;
    SparkV15Booking public immutable BOOKING;
    SparkV15Funds public immutable FUNDS;
    AVAEvidenceRegistry public immutable EVIDENCE_REGISTRY;
    SparkV15FundingCases public immutable FUNDING_CASES;
    SparkV15MaterialBacking public MATERIAL_BACKING;
    SparkV15ServiceReserve public SERVICE_RESERVE;
    ISparkV15MaterialRights public rights;

    mapping(bytes32 => Provision[]) private provisions;
    mapping(bytes32 => bytes32[]) private keysByLesson;
    bytes32[] private lessons;
    mapping(bytes32 => mapping(address => bytes32)) public entitlementFor;
    mapping(bytes32 => mapping(address => address)) public agreedRecipient;
    mapping(bytes32 => Entitlement) private entitlements;
    mapping(bytes32 => bytes32[]) private obligationsByScope;
    mapping(uint256 => MaterialReceiptRecord) private receipts;
    mapping(bytes32 => uint256[]) private receiptsByObligation;

    event MaterialProvisionVerified(
        bytes32 indexed lessonId, bytes32 indexed key, uint128 budget, uint64 checkedAt, uint256 evidenceId
    );
    event MaterialRecipientAgreed(bytes32 indexed scopeId, address indexed holder, address recipient);
    event MaterialEntitlementEstablished(
        bytes32 indexed scopeId, bytes32 indexed obligationId, address indexed holder, uint128 amount
    );
    event MaterialEntitlementIncreased(bytes32 indexed obligationId, uint128 amount, uint256 evidenceId);
    event MaterialReceiptVerified(
        uint256 indexed receiptId, bytes32 indexed obligationId, uint64 verifiedAt, uint256 evidenceId
    );
    constructor(SparkV15Materials materials, SparkV15Payments payments) {
        SparkV15Booking booking = materials.BOOKING();
        SparkV15Funds funds = payments.FUNDS();
        if (address(booking.FUNDS()) != address(funds)) revert InvalidProvision();
        MATERIALS = materials;
        BOOKING = booking;
        PAYMENTS = payments;
        FUNDS = funds;
        EVIDENCE_REGISTRY = booking.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        FUNDING_CASES = new SparkV15FundingCases(booking, payments, materials);
    }

    function fundingKey(bytes32 lessonId, bytes32 placeId, bytes32 material, bytes32 termsRef)
        public
        pure
        returns (bytes32)
    {
        return keccak256(abi.encode(lessonId, placeId, material, termsRef));
    }

    function getProvisions(bytes32 key) external view returns (Provision[] memory) {
        return provisions[key];
    }

    function getLessonFundingKeys(bytes32 lessonId) external view returns (bytes32[] memory) {
        return keysByLesson[lessonId];
    }

    function getLatestProvision(bytes32 key) external view returns (Provision memory current) {
        Provision[] storage history = provisions[key];
        if (history.length != 0) current = history[history.length - 1];
    }

    function getEntitlement(bytes32 obligationId) external view returns (Entitlement memory) {
        return entitlements[obligationId];
    }

    function getMaterialReceipt(uint256 receiptId) external view returns (MaterialReceipt memory) {
        MaterialReceiptRecord storage row = receipts[receiptId];
        return MaterialReceipt(row.obligationId, row.paidAt, row.verifiedAt, row.evidenceId, row.verifiedBy);
    }

    function getMaterialReceiptTiming(uint256 receiptId) external view returns (uint64 paidAt, uint64 nextOrder) {
        MaterialReceiptRecord storage row = receipts[receiptId];
        return (row.paidAt, row.nextTransferAcceptanceOrder);
    }

    function getScopeObligations(bytes32 scopeId) external view returns (bytes32[] memory) {
        return obligationsByScope[scopeId];
    }

    function getMaterialReceiptIds(bytes32 obligationId) external view returns (uint256[] memory) {
        return receiptsByObligation[obligationId];
    }

    /// @notice Read the actor's own interest in a recorded gross charge as of this decision.
    /// @dev An unrecognised reference may describe a use claim before any charge has been established.
    /// An inferred mismatch requires usable evidence for both the mapping and the recorded charge.
    function caseChargeInterest(
        bytes32 caseId,
        bytes32 lessonId,
        bytes32 scopeId,
        bytes32 obligationId,
        bytes32 omissionForm,
        address actor
    ) external view returns (bool recognised, bool interested) {
        bytes32 obligationScope = entitlements[obligationId].input.scopeId;
        uint256 originalEvidenceId;
        bool inferredScope = scopeId == bytes32(0);
        if (scopeId == bytes32(0)) {
            if (MATERIALS.REVIEW_CASES().INTAKE().caseContext(caseId).evidenceId == 0) {
                (scopeId, originalEvidenceId) = MATERIALS.MATERIAL_USE().retainedGrossScope(caseId, lessonId);
            } else {
                scopeId = obligationScope;
            }
        }
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        if (scope.recordedAt == 0 && omissionForm != bytes32(0)) {
            scopeId = MATERIAL_BACKING.caseOmissionScope(lessonId, omissionForm, scopeId);
            scope = MATERIALS.getChargeScope(scopeId);
            inferredScope = true;
        }
        if (scope.recordedAt == 0) return (false, false);
        if (scope.lessonId != lessonId || (obligationId != bytes32(0) && obligationScope != scopeId)) {
            if (inferredScope) {
                uint256 mappingEvidenceId = originalEvidenceId;
                if (mappingEvidenceId == 0) {
                    mappingEvidenceId = MATERIALS.REVIEW_CASES().INTAKE().caseContext(caseId).evidenceId;
                }
                if (!_caseEvidenceAvailable(scope.evidenceId) || !_caseEvidenceAvailable(mappingEvidenceId)) {
                    return (false, false);
                }
            }
            revert InvalidCaseChargeScope();
        }
        if (originalEvidenceId != 0 && !_caseEvidenceAvailable(originalEvidenceId)) {
            revert SparkV15ReviewContext.InvalidEvidence();
        }

        uint256 packageId = BOOKING.getLesson(lessonId).packageId;
        uint256 portion = MATERIAL_BACKING.caseHolderPortion(scopeId, scope, actor, packageId);
        uint256 retained = PAYMENTS.retainedByBeneficiary(entitlementFor[scopeId][actor], actor);
        return (true, portion > retained);
    }

    /// @notice Check the same single-seat scope used for case disinterest, with its named evidence.
    function matchesOmissionGrossScope(
        bytes32 termsId,
        bytes32 matter,
        bytes32 scopeId,
        bytes32 obligationId,
        uint256 intakeEvidenceId,
        uint256 chargeEvidenceId
    ) external view returns (bool) {
        return scopeId != bytes32(0) && (obligationId == bytes32(0) || entitlements[obligationId].input.scopeId == scopeId)
            && FUNDING_CASES.matchesOmissionGrossScope(
                MATERIAL_BACKING, termsId, matter, scopeId, intakeEvidenceId, chargeEvidenceId
            );
    }

    function _caseEvidenceAvailable(uint256 evidenceId) private view returns (bool) {
        if (evidenceId == 0) return false;
        uint256 packageId = EVIDENCE_REGISTRY.getEvidenceReference(evidenceId).packageId;
        return EVIDENCE_REGISTRY.isEvidenceAvailableForPackage(evidenceId, packageId);
    }

    function bindMaterialRights(address source) external {
        _requireApplicationAdmin();
        if (address(rights) != address(0) || ISparkV15MaterialRights(source).MATERIALS() != address(MATERIALS)) {
            revert InvalidEntitlement();
        }
        rights = ISparkV15MaterialRights(source);
    }

    function bindServiceReserveModule(SparkV15ServiceReserve source) external {
        _requireApplicationAdmin();
        if (
            address(SERVICE_RESERVE) != address(0) || address(source.PROVISIONS()) != address(this)
                || address(source.BOOKING()) != address(BOOKING) || address(source.PAYMENTS()) != address(PAYMENTS)
        ) revert InvalidProvision();
        SERVICE_RESERVE = source;
    }

    function bindMaterialBacking(SparkV15MaterialBacking source) external {
        _requireApplicationAdmin();
        if (
            address(MATERIAL_BACKING) != address(0) || address(source.PROVISIONS()) != address(this)
                || address(source.MATERIALS()) != address(MATERIALS) || address(source.BOOKING()) != address(BOOKING)
                || address(source.PAYMENTS()) != address(PAYMENTS)
        ) revert InvalidProvision();
        MATERIAL_BACKING = source;
    }

    /// @notice Lower a predecessor's current unpaid principal under an effective, verified rights transfer.
    function rebaseMaterialPart(bytes32 obligationId, bytes32 transferId) external {
        if (msg.sender != address(rights) || transferId == bytes32(0)) revert InvalidEntitlement();
        Entitlement storage item = entitlements[obligationId];
        bytes32 scopeId = item.input.scopeId;
        if (scopeId == bytes32(0)) revert InvalidEntitlement();
        uint64 nowAt = uint64(block.timestamp);
        uint256 current = rights.holderPortionForRebase(scopeId, item.input.holder, nowAt);
        SparkV15Payments.Obligation memory payment = PAYMENTS.getObligation(obligationId);
        if (current >= payment.correctAmount) return;
        PAYMENTS.applyPaymentRevision(
            transferId,
            SparkV15Payments.PaymentRevision(
                obligationId, uint128(current), payment.beneficiary, payment.destination, payment.version
            )
        );
    }

    function executeReserveEffect(bytes32 lessonId, address recipient, uint128 amount) external {
        if (msg.sender != address(SERVICE_RESERVE)) revert InvalidProvision();
        if (recipient == address(0)) FUNDS.releaseLessonBudget(lessonId, amount);
        else FUNDS.transferLessonFeesToServiceReserve(lessonId, recipient, amount);
    }

    /// @notice The holder names a recipient for this charge before its payment part is established.
    function agreeMaterialRecipient(bytes32 scopeId, address recipient) external {
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        if (
            scope.recordedAt == 0 || recipient == address(0) || entitlementFor[scopeId][msg.sender] != bytes32(0)
                || agreedRecipient[scopeId][msg.sender] != address(0)
                || MATERIAL_BACKING.holderPortion(scopeId, scope, msg.sender, uint64(block.timestamp)) == 0
        ) revert InvalidEntitlement();
        agreedRecipient[scopeId][msg.sender] = recipient;
        emit MaterialRecipientAgreed(scopeId, msg.sender, recipient);
    }

    function previewEntitlement(EntitlementInput calldata input, address verifier)
        public
        view
        returns (SparkV15Payments.PaymentTerms memory terms, bytes32 basis)
    {
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(input.scopeId);
        SparkV15Materials.AgreedTerms memory agreement = MATERIALS.getAgreedTerms(scope.lessonId);
        address namedRecipient = agreedRecipient[input.scopeId][input.holder];
        if (
            scope.recordedAt == 0 || scope.identifiedAt > input.verifiedAt || scope.recordedAt > input.verifiedAt
                || input.holder == address(0) || input.holder == verifier || input.recipient == verifier
                || input.recipient != (namedRecipient == address(0) ? input.holder : namedRecipient)
                || input.sourceRef == bytes32(0) || agreement.commitment != scope.termsRef
        ) revert InvalidEntitlement();
        uint256 portion = MATERIAL_BACKING.holderPortion(input.scopeId, scope, input.holder, input.verifiedAt);
        if (portion == 0 || portion > type(uint128).max) revert InvalidEntitlement();

        terms.lessonId = scope.lessonId;
        terms.paymentPart = keccak256(abi.encode("spark.v1.5.material-share", input.scopeId, input.holder));
        terms.recipient = input.recipient;
        terms.amount = uint128(portion);
        terms.dueAt = agreement.paymentDue;
        terms.executionDeadline = agreement.paymentDeadline;
        terms.postLiftDeadline = input.postLiftDeadline;
        terms.dueAtExact = true;
        terms.executionDeadlineExact = true;
        terms.postLiftDeadlineExact = input.postLiftDeadline != 0;
        terms.settlementProposer = verifier;
        terms.settlementApprover = agreement.payer;
        basis = _evidenceCommitment(ACTION_VERIFY_ENTITLEMENT, scope.lessonId, verifier, keccak256(abi.encode(input)));
    }

    /// @notice Establish the verified holder's independently payable material obligation.
    function establishEntitlement(EntitlementInput calldata input, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 obligationId)
    {
        _requireVerifier(ACTION_VERIFY_ENTITLEMENT, authorityId);
        if (input.verifiedAt != block.timestamp || entitlementFor[input.scopeId][input.holder] != bytes32(0)) {
            revert InvalidEntitlement();
        }
        if (address(rights) != address(0)) rights.syncMaterialScope(input.scopeId);
        (SparkV15Payments.PaymentTerms memory terms, bytes32 basis) = previewEntitlement(input, msg.sender);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(terms.lessonId);
        obligationId = keccak256(abi.encode(terms.lessonId, terms.paymentPart));
        entitlementFor[input.scopeId][input.holder] = obligationId;
        entitlements[obligationId] = Entitlement(input, terms.amount, evidenceId, msg.sender);
        obligationsByScope[input.scopeId].push(obligationId);
        PAYMENTS.establishMaterialPayment(terms, basis, evidenceId, lesson.packageId, input.verifiedAt, input.holder);
        emit MaterialEntitlementEstablished(input.scopeId, obligationId, input.holder, terms.amount);
    }

    function entitlementIncreaseCommitment(
        bytes32 obligationId,
        uint128 amount,
        uint256 version,
        bytes32 sourceRef,
        address verifier
    ) public view returns (bytes32) {
        bytes32 scopeId = entitlements[obligationId].input.scopeId;
        return _evidenceCommitment(
            ACTION_VERIFY_ENTITLEMENT,
            MATERIALS.getChargeScope(scopeId).lessonId,
            verifier,
            keccak256(abi.encode(obligationId, amount, version, sourceRef))
        );
    }

    /// @notice Verify and back an increase for the same recipient. Earlier approvals keep their original ceilings.
    function reviseEstablishedEntitlement(
        bytes32 obligationId,
        uint128 amount,
        bytes32 sourceRef,
        uint256 evidenceId,
        bytes32 authorityId
    ) external {
        _requireVerifier(ACTION_VERIFY_ENTITLEMENT, authorityId);
        (uint256 version, address holder, address destination, uint256 paid) =
            MATERIAL_BACKING.validateEntitlementIncrease(obligationId, amount, sourceRef, evidenceId, msg.sender);
        PAYMENTS.applyPaymentRevision(
            bytes32(evidenceId), SparkV15Payments.PaymentRevision(obligationId, amount, holder, destination, version)
        );
        uint256 backed = paid + FUNDS.paymentReserved(obligationId);
        if (amount > backed) FUNDS.reserveAdditionalMaterialBacking(obligationId, uint128(amount - backed));
        emit MaterialEntitlementIncreased(obligationId, amount, evidenceId);
    }

    function receiptEvidenceCommitment(uint256 receiptId, uint64 verifiedAt, address verifier)
        public
        view
        returns (bytes32)
    {
        SparkV15Payments.PaymentReceipt memory paid = PAYMENTS.getReceipt(receiptId);
        Entitlement storage entitlement = entitlements[paid.obligationId];
        bytes32 scopeId = entitlement.input.scopeId;
        bytes32 lessonId = MATERIALS.getChargeScope(scopeId).lessonId;
        return _evidenceCommitment(
            ACTION_VERIFY_MATERIAL_RECEIPT,
            lessonId,
            verifier,
            keccak256(abi.encode(receiptId, verifiedAt, scopeId, paid))
        );
    }

    /// @notice Recognise the existing native receipt at the time its material evidence becomes verified.
    function verifyMaterialReceipt(uint256 receiptId, uint64 verifiedAt, uint256 evidenceId, bytes32 authorityId)
        external
    {
        _requireVerifier(ACTION_VERIFY_MATERIAL_RECEIPT, authorityId);
        SparkV15Payments.PaymentReceipt memory paid = PAYMENTS.getReceipt(receiptId);
        Entitlement storage entitlement = entitlements[paid.obligationId];
        if (
            paid.paidAt == 0 || verifiedAt != block.timestamp || paid.paidAt > verifiedAt
                || entitlement.input.scopeId == bytes32(0)
                || paid.creditAccount != bytes32(0) || receipts[receiptId].verifiedAt != 0
                || msg.sender == entitlement.input.holder || msg.sender == paid.recipient
                || PAYMENTS.RETURNS().receiptBeneficiary(receiptId) != entitlement.input.holder
        ) revert InvalidMaterialReceipt();
        bytes32 lessonId = MATERIALS.getChargeScope(entitlement.input.scopeId).lessonId;
        _requireEvidence(
            BOOKING.getLesson(lessonId).packageId,
            evidenceId,
            receiptEvidenceCommitment(receiptId, verifiedAt, msg.sender)
        );
        ISparkV15MaterialRights source = rights;
        uint64 nextOrder = address(source) == address(0) ? 0 : source.nextTransferAcceptanceOrder();
        receipts[receiptId] =
            MaterialReceiptRecord(paid.obligationId, paid.paidAt, verifiedAt, nextOrder, evidenceId, msg.sender);
        receiptsByObligation[paid.obligationId].push(receiptId);
        emit MaterialReceiptVerified(receiptId, paid.obligationId, verifiedAt, evidenceId);
    }

    function provisionEvidenceCommitment(ProvisionInput calldata input, address verifier)
        public
        view
        returns (bytes32)
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(input.formId);
        return _evidenceCommitment(ACTION_VERIFY_PROVISION, form.lessonId, verifier, keccak256(abi.encode(input)));
    }

    /// @notice Verify the estimate and hold real cash for the latest estimate under the same seat and annex.
    function recordProvision(ProvisionInput calldata input, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 key)
    {
        _requireVerifier(ACTION_VERIFY_PROVISION, authorityId);
        SparkV15Booking.Form memory form = BOOKING.getForm(input.formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        uint64 checkedAt = uint64(block.timestamp);
        if (
            FUNDS.materialProvisions() != address(this) || input.sourceRef == bytes32(0)
                || !MATERIALS.licensedForm(input.formId, input.material)
                || BOOKING.isCancelledAt(input.formId, checkedAt)
                || (form.confirmation.confirmedAt != 0 && !FUNDING_CASES.hasInventory(form.lessonId))
        ) revert InvalidProvision();
        if (_requireEvidence(lesson.packageId, evidenceId, provisionEvidenceCommitment(input, msg.sender)) != checkedAt)
        {
            revert InvalidFundingEvidence();
        }
        key = fundingKey(form.lessonId, form.terms.placeId, input.material, lesson.terms.materialsTermsRef);
        Provision[] storage history = provisions[key];
        if (history.length == 0) {
            if (keysByLesson[form.lessonId].length == 0) lessons.push(form.lessonId);
            keysByLesson[form.lessonId].push(key);
        } else if (history[history.length - 1].checkedAt >= checkedAt) {
            revert InvalidProvision();
        }

        uint256 balance = FUNDS.TOKEN().balanceOf(address(FUNDS));
        uint256 base = FUNDS.reservedUnits();
        if (balance < base) revert InsufficientMaterialBacking();
        history.push(
            Provision(input, checkedAt, evidenceId, msg.sender, FUNDS.lessonReserved(form.lessonId), balance - base)
        );
        _requireBacking(bytes32(0), 0, balance, base, form.lessonId);
        emit MaterialProvisionVerified(form.lessonId, key, input.budget, checkedAt, evidenceId);
    }

    /// @notice Pending estimates use a full-charge check, independent of payment-time cash protection.
    function provisioningNeed(bytes32 lessonId) public view returns (uint256 required) {
        (required,) = MATERIAL_BACKING.assess(lessonId, bytes32(0), 0, true);
    }

    function requireAfterOutflow(
        bytes32 obligationId,
        uint128 proposedAmount,
        uint256 balanceAfter,
        uint256 baseReservedAfter
    ) external view {
        if (msg.sender != address(FUNDS)) revert NotFunds();
        Entitlement storage entitlement = entitlements[obligationId];
        if (proposedAmount != 0 && entitlement.input.scopeId != bytes32(0)) {
            MATERIAL_BACKING.requireCurrentPayee(obligationId, entitlement.input.scopeId, entitlement.input.holder);
        }
        _requireBacking(obligationId, proposedAmount, balanceAfter, baseReservedAfter, bytes32(0));
    }

    function _requireBacking(
        bytes32 obligationId,
        uint128 proposedAmount,
        uint256 balance,
        uint256 base,
        bytes32 provisionLesson
    ) private view {
        uint256 required = base;
        for (uint256 i; i < lessons.length; ++i) {
            bytes32 lessonId = lessons[i];
            required += MATERIAL_BACKING.requiredBeyondLessonHold(
                lessonId, obligationId, proposedAmount, lessonId == provisionLesson
            );
        }
        if (balance < required) revert InsufficientMaterialBacking();
    }

    function paymentProtection(bytes32 lessonId, bytes32 obligationId, uint128 proposedAmount)
        public
        view
        returns (uint256 required)
    {
        (required,) = MATERIAL_BACKING.assess(lessonId, obligationId, proposedAmount, false);
    }

    function _requireVerifier(bytes32 action, bytes32 authorityId) private view {
        BOOKING.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedSubject(msg.sender, SparkV15.APP_ID, BOOKING.VERIFIER_ROLE(), action, authorityId);
    }

    function _requireApplicationAdmin() private view {
        BOOKING.REQUEST_ALLOCATION().IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
    }

    function _evidenceCommitment(bytes32 action, bytes32 lessonId, address actor, bytes32 payload)
        private
        view
        returns (bytes32)
    {
        return keccak256(abi.encode(block.chainid, address(this), action, lessonId, actor, payload));
    }

    function _requireEvidence(uint256 packageId, uint256 evidenceId, bytes32 commitment) private view returns (uint64) {
        (bytes32 appId, bytes32 workflow,,,) =
            EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        if (
            appId != SparkV15.APP_ID || workflow != BOOKING.WORKFLOW()
                || EVIDENCE_REGISTRY.getEvidenceReference(evidenceId).commitment != commitment
        ) revert InvalidFundingEvidence();
        return EVIDENCE_REGISTRY.getEvidence(evidenceId).registeredAt;
    }
}

/// @notice Compute which recorded estimates and receipts affect the current custody check.
contract SparkV15MaterialBacking {
    SparkV15MaterialProvisions public immutable PROVISIONS;
    SparkV15Materials public immutable MATERIALS;
    SparkV15Booking public immutable BOOKING;
    SparkV15Payments public immutable PAYMENTS;
    SparkV15Funds public immutable FUNDS;
    SparkV15ObservedMaterialReceipts public immutable OBSERVED_RECEIPTS;

    struct Coverage {
        uint256 inside;
        uint256 outside;
        uint256 knownPayment;
        uint256 assignedBacking;
        uint256 attributedInside;
        uint256 attributedOutside;
        uint64 newestProvisionAt;
        bool pending;
        bool revised;
        bytes32 grossBasis;
    }

    struct SeatReceipt {
        bytes32 formId;
        uint128 amount;
    }

    struct ReceiptAllocationInput {
        bytes32 scopeId;
        uint256 receiptId;
        bytes32 sourceRef;
        SeatReceipt[] seats;
    }

    struct ReceiptAllocation {
        bytes32 grossBasis;
        uint256 evidenceId;
        uint128 retained;
        uint64 verifiedAt;
        bytes32 rightsBasis;
        SeatReceipt[] seats;
    }

    struct SeatCoverage {
        bytes32 formId;
        uint128 gross;
        uint128 attributed;
        uint64 provisionAt;
    }

    bytes32 public constant ACTION_VERIFY_RECEIPT_ALLOCATION =
        keccak256("spark.action.verify-material-receipt-allocation.v1.5");
    error InvalidReceiptAllocation();
    error UnavailableCaseChargeEvidence(uint256 evidenceId);
    mapping(uint256 => ReceiptAllocation) private receiptAllocations;

    event ReceiptAllocationVerified(bytes32 indexed scopeId, uint256 indexed receiptId, uint256 evidenceId);

    constructor(
        SparkV15MaterialProvisions provisions,
        SparkV15Materials materials,
        SparkV15Booking booking,
        SparkV15Payments payments
    ) {
        PROVISIONS = provisions;
        MATERIALS = materials;
        BOOKING = booking;
        PAYMENTS = payments;
        FUNDS = payments.FUNDS();
        OBSERVED_RECEIPTS = new SparkV15ObservedMaterialReceipts(provisions, payments);
    }

    function assess(bytes32 lessonId, bytes32 obligationId, uint128 proposedAmount, bool provisioning)
        public
        view
        returns (uint256 required, uint256 assigned)
    {
        bytes32[] memory keys = PROVISIONS.getLessonFundingKeys(lessonId);
        for (uint256 i; i < keys.length; ++i) {
            SparkV15MaterialProvisions.Provision memory current = PROVISIONS.getLatestProvision(keys[i]);
            if (_fullyReceivedOriginal(current)) continue;
            (uint256 gross, bool pending) = MATERIALS.activeSeatMaterialGrossAt(
                current.input.formId, current.input.material, uint64(block.timestamp)
            );
            bytes32 originalId = MATERIALS.originalFor(current.input.formId, current.input.material);
            uint64 establishedAt = MATERIALS.getChargeScope(originalId).identifiedAt;
            bool fixedGross = establishedAt != 0 && establishedAt >= current.checkedAt && !pending;
            required += !provisioning && fixedGross ? gross : _maximum(current.input.budget, gross);
        }

        bytes32[] memory scopes = MATERIALS.getLessonChargeScopes(lessonId);
        uint256 reductions;
        for (uint256 i; i < scopes.length; ++i) {
            Coverage memory coverage = _scopeCoverage(scopes[i], obligationId, proposedAmount);
            if (coverage.inside == 0 || coverage.pending) continue;
            uint256 known = provisioning ? 0 : coverage.knownPayment;
            uint256 exactInside = provisioning ? 0 : coverage.attributedInside;
            uint256 outside = coverage.outside - (provisioning ? 0 : coverage.attributedOutside);
            uint256 paidInside = _minimum(coverage.inside, exactInside + _above(known, outside));
            uint256 heldInside =
                _minimum(coverage.inside, exactInside + _above(known + coverage.assignedBacking, outside)) - paidInside;
            reductions += paidInside;
            assigned += heldInside;
        }
        required = _above(required, reductions);
    }

    function requiredBeyondLessonHold(bytes32 lessonId, bytes32 obligationId, uint128 proposedAmount, bool provisioning)
        external
        view
        returns (uint256)
    {
        (uint256 required, uint256 assigned) = assess(lessonId, obligationId, proposedAmount, provisioning);
        uint256 unassigned = _above(required, assigned);
        SparkV15FundingCases cases = PROVISIONS.FUNDING_CASES();
        if (provisioning || BOOKING.getTeaching(lessonId).startedAt == 0) {
            unassigned = _maximum(unassigned, cases.requiredForCases(lessonId, liveBudgets(lessonId), assigned));
        } else {
            unassigned += cases.independentTeachingCosts(lessonId);
        }
        return _above(unassigned, FUNDS.lessonReserved(lessonId));
    }

    function getReceiptAllocation(uint256 receiptId) external view returns (ReceiptAllocation memory) {
        return receiptAllocations[receiptId];
    }

    function receiptAllocationEvidenceCommitment(ReceiptAllocationInput calldata input, address verifier)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                ACTION_VERIFY_RECEIPT_ALLOCATION,
                address(this),
                block.chainid,
                input,
                verifier,
                _grossBasis(input.scopeId),
                _nativeRightsBasis(input.scopeId, input.receiptId)
            )
        );
    }

    /// @notice Establish exact seat attribution after a grouped receipt or changed rights or gross amount.
    function verifyReceiptAllocation(ReceiptAllocationInput calldata input, uint256 evidenceId, bytes32 authorityId)
        external
    {
        BOOKING.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, BOOKING.VERIFIER_ROLE(), ACTION_VERIFY_RECEIPT_ALLOCATION, authorityId
            );
        SparkV15MaterialProvisions.MaterialReceipt memory verified = PROVISIONS.getMaterialReceipt(input.receiptId);
        SparkV15MaterialProvisions.Entitlement memory entitlement = PROVISIONS.getEntitlement(verified.obligationId);
        if (
            input.sourceRef == bytes32(0) || verified.verifiedAt == 0 || verified.paidAt >= block.timestamp
                || entitlement.input.scopeId != input.scopeId || input.seats.length == 0
                || receiptAllocations[input.receiptId].verifiedAt >= block.timestamp
        ) revert InvalidReceiptAllocation();
        bytes32 lessonId = MATERIALS.getChargeScope(input.scopeId).lessonId;
        AVAEvidenceRegistry registry = PROVISIONS.EVIDENCE_REGISTRY();
        registry.requireUsableEvidenceReferenceForPackage(evidenceId, BOOKING.getLesson(lessonId).packageId);
        if (
            registry.getEvidenceReference(evidenceId).commitment
                != receiptAllocationEvidenceCommitment(input, msg.sender)
        ) {
            revert InvalidReceiptAllocation();
        }
        ReceiptAllocation storage attribution = receiptAllocations[input.receiptId];
        delete attribution.seats;
        uint256 total;
        for (uint256 i; i < input.seats.length; ++i) {
            SeatReceipt calldata row = input.seats[i];
            (uint128 gross, bool pending) =
                MATERIALS.activeScopeGrossAt(input.scopeId, row.formId, uint64(block.timestamp));
            if (pending || row.amount == 0 || row.amount > gross) revert InvalidReceiptAllocation();
            for (uint256 j; j < i; ++j) {
                if (input.seats[j].formId == row.formId) revert InvalidReceiptAllocation();
            }
            total += row.amount;
            attribution.seats.push(row);
        }
        uint128 retained =
            PAYMENTS.getReceipt(input.receiptId).amount - PAYMENTS.RETURNS().returnedForReceipt(input.receiptId);
        if (total != retained) revert InvalidReceiptAllocation();
        attribution.retained = retained;
        attribution.verifiedAt = uint64(block.timestamp);
        attribution.evidenceId = evidenceId;
        attribution.grossBasis = _grossBasis(input.scopeId);
        attribution.rightsBasis = _nativeRightsBasis(input.scopeId, input.receiptId);
        emit ReceiptAllocationVerified(input.scopeId, input.receiptId, evidenceId);
    }

    function liveBudgets(bytes32 lessonId) public view returns (SparkV15FundingCases.MaterialBudget[] memory budgets) {
        bytes32[] memory keys = PROVISIONS.getLessonFundingKeys(lessonId);
        budgets = new SparkV15FundingCases.MaterialBudget[](keys.length);
        bytes32 termsRef = BOOKING.getLesson(lessonId).terms.materialsTermsRef;
        for (uint256 i; i < keys.length; ++i) {
            SparkV15MaterialProvisions.Provision memory current = PROVISIONS.getLatestProvision(keys[i]);
            if (_fullyReceivedOriginal(current)) continue;
            (uint256 gross,) = MATERIALS.activeSeatMaterialGrossAt(
                current.input.formId, current.input.material, uint64(block.timestamp)
            );
            budgets[i] = SparkV15FundingCases.MaterialBudget(
                current.input.formId, current.input.material, termsRef, _maximum(current.input.budget, gross)
            );
        }
    }

    function _scopeCoverage(bytes32 scopeId, bytes32 obligationId, uint128 proposedAmount)
        private
        view
        returns (Coverage memory coverage)
    {
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        bytes32[] memory forms = MATERIALS.getScopeForms(scopeId);
        SeatCoverage[] memory seats = new SeatCoverage[](forms.length);
        coverage.grossBasis = scopeId;
        for (uint256 i; i < forms.length; ++i) {
            (uint128 charge, bool pending) = MATERIALS.activeScopeGrossAt(scopeId, forms[i], uint64(block.timestamp));
            coverage.grossBasis = keccak256(abi.encode(coverage.grossBasis, forms[i], charge, pending));
            coverage.pending = coverage.pending || pending;
            if (charge != MATERIALS.getHistoricalCharge(scopeId, forms[i]).amount) coverage.revised = true;
            if (charge == 0) continue;
            seats[i].formId = forms[i];
            seats[i].gross = charge;
            SparkV15Booking.Form memory form = BOOKING.getForm(forms[i]);
            bytes32 key = PROVISIONS.fundingKey(scope.lessonId, form.terms.placeId, scope.material, scope.termsRef);
            SparkV15MaterialProvisions.Provision memory current = PROVISIONS.getLatestProvision(key);
            if (current.checkedAt == 0 || _fullyReceivedOriginal(current)) {
                coverage.outside += charge;
            } else {
                coverage.inside += charge;
                uint64 checkedAt = current.checkedAt;
                seats[i].provisionAt = checkedAt;
                if (checkedAt > coverage.newestProvisionAt) coverage.newestProvisionAt = checkedAt;
            }
        }
        if (coverage.inside == 0 || coverage.pending) return coverage;
        bytes32[] memory parts = PROVISIONS.getScopeObligations(scopeId);
        for (uint256 i; i < parts.length; ++i) {
            coverage.assignedBacking += FUNDS.paymentReserved(parts[i]);
            if (parts[i] == obligationId) coverage.knownPayment += proposedAmount;
            _countReceipts(scopeId, parts[i], seats, coverage);
        }
    }

    function _countReceipts(
        bytes32 scopeId,
        bytes32 obligationId,
        SeatCoverage[] memory seats,
        Coverage memory coverage
    ) private view {
        uint256[] memory ids = PROVISIONS.getMaterialReceiptIds(obligationId);
        for (uint256 i; i < ids.length; ++i) {
            uint256 id = ids[i];
            SparkV15MaterialProvisions.MaterialReceipt memory receipt = PROVISIONS.getMaterialReceipt(id);
            if (receipt.paidAt > block.timestamp || receipt.verifiedAt > block.timestamp) continue;
            uint128 net = PAYMENTS.getReceipt(id).amount - PAYMENTS.RETURNS().returnedForReceipt(id);
            ReceiptAllocation storage attribution = receiptAllocations[id];
            bytes32 rightsBasis = _nativeRightsBasis(scopeId, id);
            if (
                attribution.verifiedAt != 0 && attribution.retained == net
                    && attribution.grossBasis == coverage.grossBasis && attribution.rightsBasis == rightsBasis
            ) {
                for (uint256 j; j < attribution.seats.length; ++j) {
                    SeatReceipt storage allocation = attribution.seats[j];
                    for (uint256 k; k < seats.length; ++k) {
                        SeatCoverage memory seat = seats[k];
                        if (seat.formId != allocation.formId) continue;
                        uint128 available = seat.gross - seat.attributed;
                        uint128 amount = available < allocation.amount ? available : allocation.amount;
                        if (seat.provisionAt == 0) coverage.attributedOutside += amount;
                        else if (receipt.paidAt > seat.provisionAt) coverage.attributedInside += amount;
                        seats[k].attributed += amount;
                        break;
                    }
                }
            } else if (!coverage.revised && rightsBasis == bytes32(0) && receipt.paidAt > coverage.newestProvisionAt) {
                coverage.knownPayment += net;
            }
        }
        if (!coverage.revised) {
            coverage.knownPayment += _observedRetained(scopeId, obligationId, coverage.newestProvisionAt);
        }
    }

    function _grossBasis(bytes32 scopeId) private view returns (bytes32 digest) {
        digest = scopeId;
        bytes32[] memory forms = MATERIALS.getScopeForms(scopeId);
        for (uint256 i; i < forms.length; ++i) {
            (uint128 charge, bool pending) = MATERIALS.activeScopeGrossAt(scopeId, forms[i], uint64(block.timestamp));
            digest = keccak256(abi.encode(digest, forms[i], charge, pending));
        }
    }

    function _rightsBasis(bytes32 scopeId, uint64 paidAt) private view returns (bytes32) {
        ISparkV15MaterialRights source = PROVISIONS.rights();
        return address(source) == address(0)
            ? bytes32(0)
            : source.scopeTransferBasisAt(scopeId, paidAt, uint64(block.timestamp));
    }

    function _nativeRightsBasis(bytes32 scopeId, uint256 receiptId) private view returns (bytes32) {
        ISparkV15MaterialRights source = PROVISIONS.rights();
        return address(source) == address(0) ? bytes32(0) : source.nativeReceiptTransferBasis(scopeId, receiptId);
    }

    function isFullyReceivedOriginal(bytes32 fundingKey) external view returns (bool) {
        return _fullyReceivedOriginal(PROVISIONS.getLatestProvision(fundingKey));
    }

    function _fullyReceivedOriginal(SparkV15MaterialProvisions.Provision memory current) private view returns (bool) {
        bytes32 originalId = MATERIALS.originalFor(current.input.formId, current.input.material);
        bytes32[] memory parts = PROVISIONS.getScopeObligations(originalId);
        if (parts.length == 0) return false;
        SparkV15Materials.ChargeScope memory original = MATERIALS.getChargeScope(originalId);
        bytes32[] memory forms = MATERIALS.getScopeForms(originalId);
        for (uint256 i; i < forms.length; ++i) {
            (uint128 currentGross, bool pending) =
                MATERIALS.activeScopeGrossAt(originalId, forms[i], uint64(block.timestamp));
            (uint256 total, bool waiting) =
                MATERIALS.activeSeatMaterialGrossAt(forms[i], original.material, uint64(block.timestamp));
            if (
                pending || waiting || currentGross != MATERIALS.getHistoricalCharge(originalId, forms[i]).amount
                    || total != currentGross
            ) return false;
        }
        uint256 allEntitled;
        for (uint256 i; i < parts.length; ++i) {
            uint128 amount = PROVISIONS.getEntitlement(parts[i]).amount;
            // A later transfer leaves receipts under the original payment terms in place.
            if (_retainedReceiptAmount(parts[i], current.checkedAt) < amount) return false;
            allEntitled += amount;
        }
        return allEntitled == original.total;
    }

    function _retainedReceiptAmount(bytes32 obligationId, uint64 checkedAt) private view returns (uint256 amount) {
        bytes32 scopeId = PROVISIONS.getEntitlement(obligationId).input.scopeId;
        uint256[] memory ids = PROVISIONS.getMaterialReceiptIds(obligationId);
        for (uint256 i; i < ids.length; ++i) {
            uint256 id = ids[i];
            SparkV15MaterialProvisions.MaterialReceipt memory receipt = PROVISIONS.getMaterialReceipt(id);
            // Verification already put this receipt on the list, including within the current second.
            if (receipt.paidAt <= checkedAt || receipt.paidAt > block.timestamp || receipt.verifiedAt > block.timestamp)
            {
                continue;
            }
            if (_nativeRightsBasis(scopeId, id) != bytes32(0)) continue;
            amount += PAYMENTS.getReceipt(id).amount - PAYMENTS.RETURNS().returnedForReceipt(id);
        }
        amount += _observedRetained(scopeId, obligationId, checkedAt);
    }

    function _observedRetained(bytes32 scopeId, bytes32 obligationId, uint64 checkedAt)
        private
        view
        returns (uint256 retained)
    {
        bytes32[] memory ids = OBSERVED_RECEIPTS.receiptsForObligation(obligationId);
        for (uint256 i; i < ids.length; ++i) {
            (uint128 amount, uint64 occurredAt, uint64 qualifiedAt,) =
                OBSERVED_RECEIPTS.retainedPayment(obligationId, ids[i]);
            if (
                amount != 0 && occurredAt > checkedAt && occurredAt < block.timestamp && qualifiedAt <= block.timestamp
                    && _rightsBasis(scopeId, occurredAt) == bytes32(0)
            ) retained += amount;
        }
    }

    function requireCurrentPayee(bytes32 obligationId, bytes32 scopeId, address holder)
        external
        view
    {
        uint64 nowAt = uint64(block.timestamp);
        ISparkV15MaterialRights source = PROVISIONS.rights();
        uint256 portion = address(source) == address(0)
            ? holderPortion(scopeId, MATERIALS.getChargeScope(scopeId), holder, nowAt)
            : source.holderPortionWithoutHeldPredecessors(scopeId, holder, nowAt);
        SparkV15Payments.Obligation memory payment = PAYMENTS.getObligation(obligationId);
        // Payments uses the destination of the currently approved beneficiary version.
        if (payment.paid > portion || payment.beneficiary != holder) {
            revert SparkV15MaterialProvisions.InvalidEntitlement();
        }
    }

    function validateEntitlementIncrease(
        bytes32 obligationId,
        uint128 amount,
        bytes32 sourceRef,
        uint256 evidenceId,
        address verifier
    ) external returns (uint256 version, address holder, address destination, uint256 paid) {
        SparkV15MaterialProvisions.Entitlement memory entitlement = PROVISIONS.getEntitlement(obligationId);
        bytes32 scopeId = entitlement.input.scopeId;
        holder = entitlement.input.holder;
        if (scopeId == bytes32(0) || sourceRef == bytes32(0) || verifier == holder) {
            revert SparkV15MaterialProvisions.InvalidEntitlement();
        }
        ISparkV15MaterialRights source = PROVISIONS.rights();
        if (address(source) != address(0)) source.syncMaterialScope(scopeId);
        SparkV15Payments.Obligation memory payment = PAYMENTS.getObligation(obligationId);
        destination = payment.destination;
        if (
            amount <= payment.correctAmount || payment.beneficiary != holder || verifier == destination
                || amount != holderPortion(scopeId, MATERIALS.getChargeScope(scopeId), holder, uint64(block.timestamp))
        ) revert SparkV15MaterialProvisions.InvalidEntitlement();
        version = payment.version;
        paid = payment.paid;
        AVAEvidenceRegistry registry = PROVISIONS.EVIDENCE_REGISTRY();
        registry.requireUsableEvidenceReferenceForPackage(evidenceId, payment.packageId);
        if (
            registry.getEvidenceReference(evidenceId).commitment
                != PROVISIONS.entitlementIncreaseCommitment(obligationId, amount, version, sourceRef, verifier)
        ) revert SparkV15MaterialProvisions.InvalidFundingEvidence();
    }

    function caseOmissionScope(bytes32 lessonId, bytes32 formId, bytes32 matter) external view returns (bytes32) {
        bytes32[] memory materials = MATERIALS.getLicensedMaterials(lessonId);
        for (uint256 i; i < materials.length; ++i) {
            bytes32 material = materials[i];
            if (MATERIALS.useMatter(formId, material) != matter) continue;
            bytes32 scopeId = MATERIALS.originalFor(formId, material);
            bytes32[] memory forms = MATERIALS.getScopeForms(scopeId);
            if (forms.length != 1 || forms[0] != formId) return bytes32(0);

            uint64 nowAt = uint64(block.timestamp);
            (uint128 gross, bool originalPending) = MATERIALS.activeScopeGrossAt(scopeId, formId, nowAt);
            (uint256 total, bool pending) = MATERIALS.activeSeatMaterialGrossAt(formId, material, nowAt);
            // A seat-only claim can consume a single identified amount. Separate shortfalls need their own binding.
            return !originalPending && !pending && gross != 0 && total == gross ? scopeId : bytes32(0);
        }
        return bytes32(0);
    }

    function caseHolderPortion(
        bytes32 scopeId,
        SparkV15Materials.ChargeScope calldata scope,
        address holder,
        uint256 packageId
    ) external view returns (uint256) {
        AVAEvidenceRegistry registry = MATERIALS.EVIDENCE_REGISTRY();
        _requireCaseChargeEvidence(registry, scope.evidenceId, packageId);
        if (scope.originalScopeId != bytes32(0)) {
            _requireCaseChargeEvidence(registry, MATERIALS.getChargeScope(scope.originalScopeId).evidenceId, packageId);
        }
        _requireCaseGrossReviewEvidence(registry, scopeId, packageId);
        bytes32[] memory obligations = PROVISIONS.getScopeObligations(scopeId);
        for (uint256 i; i < obligations.length; ++i) {
            OBSERVED_RECEIPTS.requireCurrentEvidence(obligations[i]);
        }

        uint64 nowAt = uint64(block.timestamp);
        ISparkV15MaterialRights source = PROVISIONS.rights();
        return address(source) == address(0)
            ? holderPortion(scopeId, scope, holder, nowAt)
            : source.readHolderPortion(scopeId, holder, nowAt, nowAt, false, packageId);
    }

    function _requireCaseGrossReviewEvidence(AVAEvidenceRegistry registry, bytes32 scopeId, uint256 packageId)
        private
        view
    {
        bytes32[] memory reviews = MATERIALS.MATERIAL_USE().getScopeReviewCases(scopeId);
        if (reviews.length == 0) return;
        bytes32[] memory forms = MATERIALS.getScopeForms(scopeId);
        SparkV15ReviewCases cases = MATERIALS.REVIEW_CASES();
        for (uint256 i; i < reviews.length; ++i) {
            SparkV15ReviewCases.AdoptedDisposition memory adoption = cases.getAdoptedDisposition(reviews[i]);
            if (adoption.adoptedAt == 0) continue;
            _requireCaseChargeEvidence(registry, adoption.reviewEvidenceId, packageId);
            _requireCaseChargeEvidence(registry, adoption.adoptionEvidenceId, packageId);
            for (uint256 j; j < forms.length; ++j) {
                SparkV15Materials.GrossAttribution memory row = MATERIALS.getGrossAttribution(reviews[i], forms[j]);
                if (row.evidenceId != 0 && row.input.availableAt <= block.timestamp) {
                    _requireCaseChargeEvidence(registry, row.evidenceId, packageId);
                }
            }
        }
    }

    function _requireCaseChargeEvidence(AVAEvidenceRegistry registry, uint256 evidenceId, uint256 packageId)
        private
        view
    {
        if (!registry.isEvidenceAvailableForPackage(evidenceId, packageId)) {
            revert UnavailableCaseChargeEvidence(evidenceId);
        }
    }

    function holderPortion(bytes32 scopeId, SparkV15Materials.ChargeScope memory scope, address holder, uint64 atTime)
        public
        view
        returns (uint256 amount)
    {
        ISparkV15MaterialRights source = PROVISIONS.rights();
        if (address(source) != address(0)) return source.holderPortion(scopeId, holder, atTime, atTime);
        SparkV15Materials.HolderShare[] memory holders =
        MATERIALS.getMaterialTerms(scope.lessonId, scope.material).holders;
        uint256 denominator;
        uint256 beforeHolder;
        uint256 holderUnits;
        for (uint256 i; i < holders.length; ++i) {
            if (holders[i].holder == holder) {
                beforeHolder = denominator;
                holderUnits = holders[i].units;
            }
            denominator += holders[i].units;
        }
        if (holderUnits == 0) return 0;
        bytes32[] memory forms = MATERIALS.getScopeForms(scopeId);
        for (uint256 i; i < forms.length; ++i) {
            (uint128 gross, bool pending) = MATERIALS.activeScopeGrossAt(scopeId, forms[i], atTime);
            if (pending) revert SparkV15MaterialProvisions.InvalidEntitlement();
            amount += uint256(gross) * (beforeHolder + holderUnits) / denominator - uint256(gross) * beforeHolder
            / denominator;
        }
    }

    function _maximum(uint256 first, uint256 second) private pure returns (uint256) {
        return first > second ? first : second;
    }

    function _above(uint256 total, uint256 deducted) private pure returns (uint256) {
        return total > deducted ? total - deducted : 0;
    }

    function _minimum(uint256 first, uint256 second) private pure returns (uint256) {
        return first < second ? first : second;
    }
}

/// @notice Retained material receipts verified by this installation's designated ERC-20 observer.
contract SparkV15ObservedMaterialReceipts {
    SparkV15MaterialProvisions public immutable PROVISIONS;
    SparkV15Payments public immutable PAYMENTS;
    error UnavailableCaseReceiptEvidence(uint256 evidenceId);

    constructor(SparkV15MaterialProvisions provisions, SparkV15Payments payments) {
        PROVISIONS = provisions;
        PAYMENTS = payments;
    }

    function requireCurrentEvidence(bytes32 obligationId) external view {
        SparkV15PaymentObservations observer = SparkV15PaymentObservations(PAYMENTS.paymentObservations());
        if (address(observer) == address(0)) return;
        AVAEvidenceRegistry registry = PROVISIONS.EVIDENCE_REGISTRY();
        bytes32[] memory receipts = observer.getQualifiedPaymentIds(obligationId);
        for (uint256 i; i < receipts.length; ++i) {
            SparkV15PaymentObservations.PaymentObservation memory observed = observer.getPaymentObservation(receipts[i]);
            _requireCurrentVerification(registry, observed.verification);
            if (observed.terms.attributionRef == bytes32(0)) {
                _requireCurrentVerification(registry, observer.getPaymentAttribution(receipts[i]).verification);
            }
            SparkV15PaymentObservations.Verification memory recipient =
            observer.getAgreedRecipient(receipts[i]).verification;
            if (recipient.evidenceId != 0) _requireCurrentVerification(registry, recipient);
            bytes32[] memory recoveryIds = observer.getReturnIds(receipts[i]);
            for (uint256 j; j < recoveryIds.length; ++j) {
                _requireCurrentVerification(registry, observer.getReturnObservation(recoveryIds[j]).verification);
            }
        }
    }

    function _requireCurrentVerification(
        AVAEvidenceRegistry registry,
        SparkV15PaymentObservations.Verification memory verification
    ) private view {
        if (!registry.isEvidenceAvailableForPackage(verification.evidenceId, verification.evidencePackageId)) {
            revert UnavailableCaseReceiptEvidence(verification.evidenceId);
        }
    }

    function receiptsForObligation(bytes32 obligationId) external view returns (bytes32[] memory) {
        SparkV15PaymentObservations observer = SparkV15PaymentObservations(PAYMENTS.paymentObservations());
        if (address(observer) == address(0)) return new bytes32[](0);
        return observer.getQualifiedPaymentIds(obligationId);
    }

    function retainedPayment(bytes32 obligationId, bytes32 receiptId)
        external
        view
        returns (uint128 retained, uint64 occurredAt, uint64 qualifiedAt, uint64 archivedAt)
    {
        SparkV15PaymentObservations observer = SparkV15PaymentObservations(PAYMENTS.paymentObservations());
        if (address(observer) == address(0)) return (0, 0, 0, 0);
        (uint128 amount, uint64 at, uint64 verifiedAt) = _qualifyingPayment(observer, obligationId, receiptId);
        if (verifiedAt == 0) return (0, 0, 0, 0);
        return (amount - observer.returnedForReceipt(receiptId), at, verifiedAt, observer.archivedAt(receiptId));
    }

    /// @notice Read known receipt and return effects at the earlier business cutoff.
    function retainedPaymentBefore(bytes32 obligationId, bytes32 receiptId, uint64 cutoff, uint64 knownAt)
        external
        view
        returns (uint128 retained)
    {
        SparkV15PaymentObservations observer = SparkV15PaymentObservations(PAYMENTS.paymentObservations());
        if (address(observer) == address(0)) return 0;
        (uint128 amount, uint64 occurredAt, uint64 qualifiedAt) = _qualifyingPayment(observer, obligationId, receiptId);
        if (qualifiedAt == 0 || occurredAt >= cutoff || qualifiedAt > knownAt) return 0;
        retained = amount;
        bytes32[] memory recoveryIds = observer.getReturnIds(receiptId);
        for (uint256 i; i < recoveryIds.length; ++i) {
            SparkV15PaymentObservations.ReturnObservation memory returned =
                observer.getReturnObservation(recoveryIds[i]);
            if (returned.terms.transfer.occurredAt < cutoff && returned.verification.verifiedAt <= knownAt) {
                retained -= returned.terms.transfer.amount;
            }
        }
    }

    function _qualifyingPayment(SparkV15PaymentObservations observer, bytes32 obligationId, bytes32 receiptId)
        private
        view
        returns (uint128 amount, uint64 occurredAt, uint64 qualifiedAt)
    {
        SparkV15PaymentObservations.PaymentObservation memory observed = observer.getPaymentObservation(receiptId);
        SparkV15MaterialProvisions.Entitlement memory entitlement = PROVISIONS.getEntitlement(obligationId);
        if (
            !observed.qualifies || entitlement.input.scopeId == bytes32(0)
                || observed.terms.obligationId != obligationId
                || observed.terms.transfer.occurredAt < entitlement.input.verifiedAt
        ) return (0, 0, 0);
        address beneficiary = observed.terms.beneficiary;
        qualifiedAt = observed.verification.verifiedAt;
        if (observed.terms.attributionRef == bytes32(0)) {
            SparkV15PaymentObservations.PaymentAttribution memory attribution = observer.getPaymentAttribution(receiptId);
            beneficiary = attribution.terms.beneficiary;
            qualifiedAt = attribution.verification.verifiedAt;
        }
        if (beneficiary != entitlement.input.holder) return (0, 0, 0);
        SparkV15PaymentObservations.AgreedRecipientObservation memory recipient = observer.getAgreedRecipient(receiptId);
        if (
            observed.terms.transfer.destination != entitlement.input.holder
                && observed.terms.transfer.destination != entitlement.input.recipient
                && recipient.terms.payee != entitlement.input.holder
        ) return (0, 0, 0);
        if (recipient.verification.verifiedAt > qualifiedAt) qualifiedAt = recipient.verification.verifiedAt;
        return (observed.terms.transfer.amount, observed.terms.transfer.occurredAt, qualifiedAt);
    }
}

interface ISparkV15LessonRedressStatus {
    function BOOKING() external view returns (address);
    function PAYMENTS() external view returns (address);
    function REMEDIES() external view returns (SparkV15LessonRemedies);
    function lessonRedressDelivered(bytes32 lessonId) external view returns (bool hasKnownFault, bool delivered);
    function mayPayRedressPart(bytes32 obligationId) external view returns (bool);
}

/// @notice Verified release of idle provider backing and actual transfers into the service reserve.
contract SparkV15ServiceReserve {
    struct ServiceInput {
        bytes32 formId;
        uint128 amount;
        uint64 accountedAt;
        bytes32 accountingRef;
    }

    struct ServiceTransfer {
        ServiceInput input;
        bytes32 lessonId;
        address recipient;
        uint256 evidenceId;
        uint64 paidAt;
        uint64 filedAt;
    }

    struct DeliveryFinding {
        bytes32 lessonId;
        bytes32 formId;
        bytes32 caseId;
        uint256 revision;
        uint64 startedAt;
        uint64 endedAt;
    }

    struct DeliveryConcernLink {
        bytes32 concernId;
        bytes32 verificationRef;
        address verifiedBy;
        uint64 verifiedAt;
        bytes32 authorityId;
        uint256 packageId;
        uint256 intakeEvidenceId;
        uint256 acknowledgmentEvidenceId;
        uint256 evidenceId;
    }

    enum DeliveryConcernStatus {
        Unlinked,
        Pending,
        Verified
    }

    error InvalidReserveOperation();

    bytes32 public constant ACTION_VERIFY_RESERVE_RELEASE = keccak256("spark.action.verify-reserve-release.v1.5");
    bytes32 public constant ACTION_VERIFY_SERVICE_RESERVE = keccak256("spark.action.verify-service-reserve.v1.5");
    bytes32 public constant ACTION_FILE_SERVICE_RESERVE = keccak256("spark.action.file-service-reserve.v1.5");

    SparkV15MaterialProvisions public immutable PROVISIONS;
    SparkV15Booking public immutable BOOKING;
    SparkV15Payments public immutable PAYMENTS;
    SparkV15Funds public immutable FUNDS;
    ISparkV15LessonRedressStatus public redress;
    address public reserveRecipient;

    mapping(uint256 => bool) public usedAccountingEvidence;
    mapping(bytes32 => uint64) public lastServiceTransferAt;
    mapping(uint256 => ServiceTransfer) private transfers;
    mapping(bytes32 => DeliveryConcernLink[]) private deliveryConcerns;
    mapping(uint256 => bool) private retainedDeliveryConcernEvidence;

    event FundingReserveReleased(bytes32 indexed lessonId, uint128 amount, uint256 evidenceId, uint64 releasedAt);
    event ServiceReserveTransferred(
        uint256 indexed transferId, bytes32 indexed lessonId, address recipient, uint128 amount
    );
    event ServiceReserveFiled(uint256 indexed transferId, uint64 filedAt);
    event DeliveryConcernConfirmed(
        bytes32 indexed concernId,
        bytes32 indexed findingCaseId,
        bytes32 indexed formId,
        uint256 revision,
        uint256 evidenceId
    );

    constructor(SparkV15MaterialProvisions provisions, SparkV15Booking booking, SparkV15Payments payments) {
        PROVISIONS = provisions;
        BOOKING = booking;
        PAYMENTS = payments;
        FUNDS = payments.FUNDS();
    }

    function bindServiceReserve(address redressSource, address recipient) external {
        BOOKING.REQUEST_ALLOCATION().IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
        ISparkV15LessonRedressStatus source = ISparkV15LessonRedressStatus(redressSource);
        if (
            address(redress) != address(0) || recipient == address(0) || recipient == address(FUNDS)
                || source.BOOKING() != address(BOOKING) || source.PAYMENTS() != address(PAYMENTS)
        ) revert InvalidReserveOperation();
        redress = source;
        reserveRecipient = recipient;
    }

    function getTransfer(uint256 transferId) external view returns (ServiceTransfer memory) {
        return transfers[transferId];
    }

    /// @notice Evidence for an affirmative fact-check of a separately recorded concern's scope.
    function deliveryConcernEvidenceCommitment(
        bytes32 concernId,
        DeliveryFinding calldata finding,
        bytes32 verificationRef,
        address handler
    ) public view returns (bytes32) {
        return redress.REMEDIES().CASES()
            .evidenceCommitment(
                concernId,
                SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN,
                handler,
                keccak256(
                    abi.encode(
                        keccak256("spark.v1.5.review.delivery-concern-scope-verified"),
                        address(this),
                        finding,
                        verificationRef
                    )
                )
            );
    }

    function getDeliveryConcerns(DeliveryFinding calldata finding)
        external
        view
        returns (DeliveryConcernLink[] memory)
    {
        return _concernsFor(finding);
    }

    /// @notice Confirm the factual scope atomically. The existing case procedure governs its merits.
    function confirmDeliveryConcern(
        bytes32 concernId,
        DeliveryFinding calldata finding,
        bytes32 verificationRef,
        uint256 evidenceId,
        bytes32 authorityId
    ) external {
        if (
            address(redress) == address(0) || concernId == finding.caseId || verificationRef == bytes32(0)
                || retainedDeliveryConcernEvidence[evidenceId]
        ) revert InvalidReserveOperation();
        SparkV15LessonRemedies remedies = redress.REMEDIES();
        AVAEvidenceRegistry registry = BOOKING.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(finding.lessonId);
        _requireCurrentDeliveryFinding(remedies, registry, finding, lesson);
        DeliveryConcernLink memory link = _verifiedDeliveryConcern(
            remedies.CASES(),
            registry,
            concernId,
            finding,
            verificationRef,
            evidenceId,
            authorityId,
            lesson.terms.provider
        );

        retainedDeliveryConcernEvidence[evidenceId] = true;
        _concernsFor(finding).push(link);
        emit DeliveryConcernConfirmed(concernId, finding.caseId, finding.formId, finding.revision, evidenceId);
    }

    function _requireCurrentDeliveryFinding(
        SparkV15LessonRemedies remedies,
        AVAEvidenceRegistry registry,
        DeliveryFinding calldata finding,
        SparkV15Booking.Lesson memory lesson
    ) private view {
        if (
            remedies.placeFaultCase(finding.formId) != finding.caseId
                || !remedies.isOperative(finding.caseId, finding.revision)
                || !_onCourseRoster(finding.lessonId, finding.formId, lesson.terms.rosterRef)
        ) revert InvalidReserveOperation();
        SparkV15LessonRemedies.FaultRecord memory fault = remedies.getFault(finding.caseId, finding.revision);
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(finding.lessonId);
        SparkV15Booking.RosterLock memory roster = BOOKING.getRosterLock(finding.lessonId);
        if (
            roster.evidenceId == 0 || roster.lockedAt >= teaching.startedAt || teaching.endedAt == 0
                || teaching.startedAt != finding.startedAt || teaching.endedAt != finding.endedAt
                || fault.lessonId != finding.lessonId || fault.originalLessonAt != finding.endedAt
        ) revert InvalidReserveOperation();
        uint256 packageId = lesson.packageId;
        registry.requireUsableEvidenceReferenceForPackage(roster.evidenceId, packageId);
        registry.requireUsableEvidenceReferenceForPackage(teaching.startEvidenceId, packageId);
        registry.requireUsableEvidenceReferenceForPackage(teaching.endEvidenceId, packageId);
        registry.requireUsableEvidenceReferenceForPackage(fault.caseEvidenceId, packageId);
    }

    function _verifiedDeliveryConcern(
        SparkV15ReviewCases cases,
        AVAEvidenceRegistry registry,
        bytes32 concernId,
        DeliveryFinding calldata finding,
        bytes32 verificationRef,
        uint256 evidenceId,
        bytes32 authorityId,
        address provider
    ) private view returns (DeliveryConcernLink memory link) {
        SparkV15ConcernIntake intake = cases.INTAKE();
        SparkV15ReviewContext.ConcernRecord memory concern = intake.getConcern(concernId);
        SparkV15Booking.PlaceTerms memory place = BOOKING.getForm(finding.formId).terms;
        SparkV15ReviewContext.PublishedContacts memory publication = intake.getPublishedContacts(concern.termsId);
        if (
            concern.acknowledgment.evidenceId == 0 || concern.lessonId != finding.lessonId
                || concern.intake.subject != SparkV15ReviewContext.ConcernSubject.StudentService
                || concern.intake.raisedBy != place.student
                || (publication.terms.governingForm != bytes32(0) && publication.terms.governingForm != finding.formId)
                || msg.sender == place.customer || msg.sender == place.payer || msg.sender == provider
        ) revert InvalidReserveOperation();

        uint64 verifiedAt = uint64(block.timestamp);
        _requireDeliveryConcernHandler(cases, registry, concernId, concern, verifiedAt, authorityId);
        uint256 packageId = publication.packageId;
        registry.requireUsableEvidenceReferenceForPackage(concern.intake.evidenceId, packageId);
        registry.requireUsableEvidenceReferenceForPackage(concern.acknowledgment.evidenceId, packageId);
        registry.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        AVAEvidenceRegistry.EvidenceReference memory proof = registry.getEvidenceReference(evidenceId);
        AVAIdentityRegistry identities = registry.IDENTITY_REGISTRY();
        AVAIdentityRegistry.SubjectContext memory source = identities.getSubjectContext(proof.authorityId);
        bytes32 intakeAuthority = registry.getEvidenceReference(concern.intake.evidenceId).authorityId;
        // The intake checked the installed evidence role for this concern and package.
        if (
            source.appId != SparkV15.APP_ID || source.roleKey != identities.getSubjectContext(intakeAuthority).roleKey
                || proof.commitment
                    != deliveryConcernEvidenceCommitment(concernId, finding, verificationRef, msg.sender)
        ) revert InvalidReserveOperation();
        return DeliveryConcernLink(
            concernId,
            verificationRef,
            msg.sender,
            verifiedAt,
            authorityId,
            packageId,
            concern.intake.evidenceId,
            concern.acknowledgment.evidenceId,
            evidenceId
        );
    }

    function _requireDeliveryConcernHandler(
        SparkV15ReviewCases cases,
        AVAEvidenceRegistry registry,
        bytes32 concernId,
        SparkV15ReviewContext.ConcernRecord memory concern,
        uint64 at,
        bytes32 authorityId
    ) private view {
        if (
            ((concern.appointmentRequiredAt != 0 && concern.appointmentRequiredAt <= at)
                    || concern.acknowledgment.input.handler != msg.sender)
                && !cases.isAppointedForCase(
                    concernId, SparkV15ReviewContext.AppointmentPurpose.ConcernHandling, msg.sender, at, true
                )
        ) revert InvalidReserveOperation();
        cases.requireDisinterested(concernId, msg.sender, at);
        bytes32 role = registry.IDENTITY_REGISTRY().requireActiveSubjectContext(authorityId, SparkV15.APP_ID).roleKey;
        registry.AUTHORITY_MATRIX()
            .requireAuthorisedSubject(
                msg.sender, SparkV15.APP_ID, role, SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN, authorityId
            );
    }

    /// @notice Read the operative, originally undisputed partial-delivery finding for a locked seat.
    function hasVerifiedPartialDelivery(bytes32 lessonId, bytes32 formId, bytes32 matter) external view returns (bool) {
        if (address(redress) == address(0)) return false;
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        SparkV15Booking.RosterLock memory roster = BOOKING.getRosterLock(lessonId);
        if (
            teaching.endedAt == 0 || roster.evidenceId == 0 || roster.lockedAt >= teaching.startedAt
                || BOOKING.getEffectiveArrangement(lessonId, teaching.startedAt).changeId != bytes32(0)
        ) return false;
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        if (!_onCourseRoster(lessonId, formId, lesson.terms.rosterRef)) return false;

        SparkV15LessonRemedies remedies = redress.REMEDIES();
        SparkV15ReviewCases cases = remedies.CASES();
        bytes32 caseId = remedies.placeFaultCase(formId);
        if (caseId != cases.caseIdFor(lessonId, matter) || !remedies.isOperative(caseId, 1)) return false;

        SparkV15LessonRemedies.FaultRecord memory fault = remedies.getFault(caseId, 1);
        if (
            fault.lessonId != lessonId || fault.originalLessonAt != teaching.endedAt
                || fault.decidedBy != lesson.terms.coordinator || fault.adoptionEvidenceId != 0
                || fault.kind < SparkV15LessonRemedies.FaultKind.ProviderArrangementError
                || fault.kind > SparkV15LessonRemedies.FaultKind.ProviderAdministrationError
                || cases.getCase(caseId).initial.evidenceId != 0 || cases.INTAKE().caseContext(caseId).evidenceId != 0
        ) return false;

        AVAEvidenceRegistry registry = BOOKING.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        uint256 packageId = lesson.packageId;
        return registry.isEvidenceAvailableForPackage(lesson.prefunding.evidenceId, packageId)
            && registry.isEvidenceAvailableForPackage(roster.evidenceId, packageId)
            && registry.isEvidenceAvailableForPackage(teaching.startEvidenceId, packageId)
            && registry.isEvidenceAvailableForPackage(teaching.endEvidenceId, packageId)
            && registry.isEvidenceAvailableForPackage(fault.caseEvidenceId, packageId)
            && remedies.getPlaceFinding(caseId, 1, formId).teaching
                == SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered
            && _deliveryConcernStatus(
                registry,
                _concernsFor(DeliveryFinding(lessonId, formId, caseId, 1, teaching.startedAt, teaching.endedAt))
            ) == DeliveryConcernStatus.Unlinked;
    }

    /// @notice A retained link stays in history if its evidence or original version stops being current.
    function deliveryConcernStatus(DeliveryFinding calldata finding) external view returns (DeliveryConcernStatus) {
        DeliveryConcernLink[] storage links = _concernsFor(finding);
        if (links.length == 0) return DeliveryConcernStatus.Unlinked;
        SparkV15LessonRemedies remedies = redress.REMEDIES();
        if (
            remedies.placeFaultCase(finding.formId) != finding.caseId
                || !remedies.isOperative(finding.caseId, finding.revision)
        ) {
            return DeliveryConcernStatus.Pending;
        }
        AVAEvidenceRegistry registry = BOOKING.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        uint256 faultEvidence = remedies.getFault(finding.caseId, finding.revision).caseEvidenceId;
        if (!registry.isEvidenceAvailableForPackage(faultEvidence, BOOKING.getLesson(finding.lessonId).packageId)) {
            return DeliveryConcernStatus.Pending;
        }
        return _deliveryConcernStatus(registry, links);
    }

    function _concernsFor(DeliveryFinding memory finding) private view returns (DeliveryConcernLink[] storage) {
        return deliveryConcerns[keccak256(abi.encode(finding))];
    }

    function _deliveryConcernStatus(AVAEvidenceRegistry registry, DeliveryConcernLink[] storage links)
        private
        view
        returns (DeliveryConcernStatus)
    {
        for (uint256 i; i < links.length; ++i) {
            DeliveryConcernLink storage link = links[i];
            if (
                registry.isEvidenceAvailableForPackage(link.intakeEvidenceId, link.packageId)
                    && registry.isEvidenceAvailableForPackage(link.acknowledgmentEvidenceId, link.packageId)
                    && registry.isEvidenceAvailableForPackage(link.evidenceId, link.packageId)
            ) return DeliveryConcernStatus.Verified;
        }
        return links.length == 0 ? DeliveryConcernStatus.Unlinked : DeliveryConcernStatus.Pending;
    }

    function releasableProviderHold(bytes32 lessonId) public view returns (uint256) {
        uint256 fees = FUNDS.lessonFeeBalance(lessonId);
        uint256 held = FUNDS.lessonReserved(lessonId);
        SparkV15MaterialBacking backing = PROVISIONS.MATERIAL_BACKING();
        (uint256 needed, uint256 assigned) = backing.assess(lessonId, bytes32(0), 0, true);
        uint256 retained = needed > assigned ? needed - assigned : 0;
        uint256 cases = PROVISIONS.FUNDING_CASES().requiredForCases(lessonId, backing.liveBudgets(lessonId), assigned);
        if (cases > retained) retained = cases;
        if (fees > retained) retained = fees;
        return held > retained ? held - retained : 0;
    }

    function releaseEvidenceCommitment(bytes32 lessonId, uint128 amount, bytes32 releaseRef, address verifier)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                ACTION_VERIFY_RESERVE_RELEASE, block.chainid, address(this), lessonId, amount, releaseRef, verifier
            )
        );
    }

    /// @notice Release only verified idle provider backing. Held lesson fees remain in custody.
    function releaseBudget(
        bytes32 lessonId,
        uint128 amount,
        bytes32 releaseRef,
        uint256 evidenceId,
        bytes32 authorityId
    ) external {
        _requireVerifier(ACTION_VERIFY_RESERVE_RELEASE, authorityId);
        if (releaseRef == bytes32(0) || amount == 0 || amount > releasableProviderHold(lessonId)) {
            revert InvalidReserveOperation();
        }
        _consumeProof(lessonId, evidenceId, releaseEvidenceCommitment(lessonId, amount, releaseRef, msg.sender));
        PROVISIONS.executeReserveEffect(lessonId, address(0), amount);
        emit FundingReserveReleased(lessonId, amount, evidenceId, uint64(block.timestamp));
    }

    function transferableServiceFees(bytes32 lessonId) public view returns (uint256) {
        uint256 fees = FUNDS.lessonFeeBalance(lessonId);
        if (fees == 0) return 0;
        uint256 retained = FUNDS.remainingCompensationCreditByLesson(lessonId);
        bytes32[] memory obligations = PAYMENTS.getLessonObligations(lessonId);
        for (uint256 i; i < obligations.length; ++i) {
            bytes32 id = obligations[i];
            SparkV15Payments.Obligation memory payment = PAYMENTS.getObligation(id);
            uint256 settledOrBacked = payment.paid + FUNDS.paymentReserved(id);
            if (settledOrBacked >= payment.correctAmount) continue;
            if (address(redress) != address(0) && !redress.mayPayRedressPart(id)) continue;
            retained += payment.correctAmount - settledOrBacked;
        }
        return fees > retained ? fees - retained : 0;
    }

    function serviceEvidenceCommitment(ServiceInput calldata input, address verifier) public view returns (bytes32) {
        return keccak256(
            abi.encode(ACTION_VERIFY_SERVICE_RESERVE, block.chainid, address(this), reserveRecipient, input, verifier)
        );
    }

    /// @notice Transfer verified fee cash after actual fault redress and retain the effect for later filing.
    function transferToServiceReserve(ServiceInput calldata input, uint256 evidenceId, bytes32 authorityId)
        external
        returns (uint256 transferId)
    {
        _requireVerifier(ACTION_VERIFY_SERVICE_RESERVE, authorityId);
        SparkV15Booking.Form memory form = BOOKING.getForm(input.formId);
        uint64 nowAt = uint64(block.timestamp);
        bytes32 lessonId = form.lessonId;
        if (
            address(redress) == address(0) || form.confirmation.confirmedAt == 0
                || !_onCourseRoster(lessonId, input.formId, BOOKING.getLesson(lessonId).terms.rosterRef)
                || input.accountedAt != nowAt || input.accountingRef == bytes32(0)
                || lastServiceTransferAt[lessonId] >= nowAt || input.amount != transferableServiceFees(lessonId)
        ) revert InvalidReserveOperation();
        (bool hasFault, bool delivered) = redress.lessonRedressDelivered(lessonId);
        if (!hasFault || !delivered) revert InvalidReserveOperation();
        _consumeProof(lessonId, evidenceId, serviceEvidenceCommitment(input, msg.sender));
        lastServiceTransferAt[lessonId] = nowAt;
        transferId = evidenceId;
        transfers[transferId] = ServiceTransfer(input, lessonId, reserveRecipient, evidenceId, nowAt, 0);
        if (input.amount != 0) PROVISIONS.executeReserveEffect(lessonId, reserveRecipient, input.amount);
        emit ServiceReserveTransferred(transferId, lessonId, reserveRecipient, input.amount);
    }

    function fileServiceReserve(uint256 transferId) external {
        ServiceTransfer storage transfer = transfers[transferId];
        if (
            transfer.paidAt == 0 || transfer.filedAt != 0
                || msg.sender != BOOKING.getLesson(transfer.lessonId).terms.coordinator
        ) revert InvalidReserveOperation();
        BOOKING.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                msg.sender, SparkV15.APP_ID, BOOKING.COORDINATOR_ROLE(), ACTION_FILE_SERVICE_RESERVE
            );
        transfer.filedAt = uint64(block.timestamp);
        emit ServiceReserveFiled(transferId, transfer.filedAt);
    }

    function _onCourseRoster(bytes32 lessonId, bytes32 formId, bytes32 rosterRef) private view returns (bool) {
        bytes32[] memory forms =
            rosterRef == bytes32(0) ? BOOKING.getPlannedForms(lessonId) : BOOKING.getLockedForms(lessonId);
        for (uint256 i; i < forms.length; ++i) {
            if (forms[i] == formId) return true;
        }
        return false;
    }

    function _requireVerifier(bytes32 action, bytes32 authorityId) private view {
        BOOKING.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedSubject(msg.sender, SparkV15.APP_ID, BOOKING.VERIFIER_ROLE(), action, authorityId);
    }

    function _consumeProof(bytes32 lessonId, uint256 evidenceId, bytes32 expected) private {
        AVAEvidenceRegistry registry = BOOKING.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        registry.requireUsableEvidenceReferenceForPackage(evidenceId, BOOKING.getLesson(lessonId).packageId);
        if (usedAccountingEvidence[evidenceId] || registry.getEvidenceReference(evidenceId).commitment != expected) {
            revert InvalidReserveOperation();
        }
        usedAccountingEvidence[evidenceId] = true;
    }
}

/// @notice The possible joint cases from the exact funding inventory accepted at booking.
contract SparkV15FundingCases {
    struct MaterialPortion {
        bytes32 formId;
        uint128 units;
    }

    struct Expense {
        bytes32 referenceId;
        bytes32 obligationId;
        bytes32 material;
        bytes32 termsRef;
        uint128 units;
        MaterialPortion[] portions;
    }

    struct FundingScenario {
        bool teachingBegan;
        bytes32[] forms;
        bytes32[] outcomes;
        Expense[] expenses;
    }

    struct MaterialBudget {
        bytes32 formId;
        bytes32 material;
        bytes32 termsRef;
        uint256 units;
    }

    struct SeatExposure {
        uint128 refund;
        uint128 credit;
        uint128 discount;
    }

    error InvalidFundingInventory();

    uint8 private constant ORIGINAL_REFUND = 0;
    uint8 private constant COURSE_CREDIT = 1;
    uint8 private constant LATER_DISCOUNT = 2;

    SparkV15Booking public immutable BOOKING;
    SparkV15Payments public immutable PAYMENTS;
    SparkV15Funds public immutable FUNDS;
    SparkV15Materials private immutable MATERIALS;

    mapping(bytes32 => FundingScenario[]) private casesByLesson;
    mapping(bytes32 => uint256) public bookingCoverageRequired;
    mapping(bytes32 => mapping(bytes32 => uint128)) private postedBookingCredit;
    mapping(bytes32 => bytes32) private deliveryForm;
    mapping(bytes32 => mapping(uint256 => bool)) private replacesUndeliveredDiscount;

    event FundingInventoryRetained(bytes32 indexed lessonId, bytes32 indexed inventoryRef, uint256 evidenceId);

    constructor(SparkV15Booking booking, SparkV15Payments payments, SparkV15Materials materials) {
        BOOKING = booking;
        PAYMENTS = payments;
        FUNDS = payments.FUNDS();
        MATERIALS = materials;
    }

    function matchesOmissionGrossScope(
        SparkV15MaterialBacking backing,
        bytes32 termsId,
        bytes32 matter,
        bytes32 scopeId,
        uint256 intakeEvidenceId,
        uint256 chargeEvidenceId
    ) external view returns (bool) {
        SparkV15ReviewContext.PublishedContacts memory publication =
            MATERIALS.REVIEW_CASES().INTAKE().getPublishedContacts(termsId);
        AVAEvidenceRegistry registry = MATERIALS.EVIDENCE_REGISTRY();
        return backing.caseOmissionScope(publication.terms.lessonId, publication.terms.governingForm, matter) == scopeId
            && registry.isEvidenceAvailableForPackage(intakeEvidenceId, publication.packageId)
            && registry.isEvidenceAvailableForPackage(chargeEvidenceId, publication.packageId);
    }

    function inventoryReference(bytes32 lessonId, FundingScenario[] calldata scenarios) public pure returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.booking.funding-inventory"), lessonId, scenarios));
    }

    /// @notice Bind an outcome in the verified inventory to the teaching received at an exact form.
    function deliveryOutcome(bytes32 formId, uint8 teachingReceived) public pure returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.booking.delivery-outcome"), formId, teachingReceived));
    }

    /// @notice Use this matter for the original teaching interval of a funded place.
    function deliveryMatter(bytes32 formId) public pure returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.booking.delivery-matter"), formId));
    }

    /// @notice Identify a non-material expense for this form. Categories 0, 1 and 2 denote refund, credit and discount.
    function bookingExposureReference(bytes32 formId, uint8 category) public pure returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.booking.expense"), formId, category));
    }

    function hasInventory(bytes32 lessonId) external view returns (bool) {
        return casesByLesson[lessonId].length != 0;
    }

    function getScenarios(bytes32 lessonId) external view returns (FundingScenario[] memory) {
        return casesByLesson[lessonId];
    }

    /// @dev Called only from the authorized credit issuance, for the same already-backed expense.
    function markPostedBookingCredit(
        bytes32 lessonId,
        bytes32 placeId,
        address customer,
        uint128 amount,
        address issuer
    ) external returns (bool) {
        if (msg.sender != address(FUNDS)) revert InvalidFundingInventory();
        FundingScenario[] storage scenarios = casesByLesson[lessonId];
        uint256 held = FUNDS.lessonReserved(lessonId);
        if (scenarios.length == 0 || held < FUNDS.lessonFeeBalance(lessonId) + amount) return false;
        bool ordinary = address(MATERIALS) == address(0);
        if (!ordinary) {
            // Only the installed Redress transition has checked the customer's operative acceptance.
            SparkV15ServiceReserve reserve = SparkV15MaterialProvisions(FUNDS.materialProvisions()).SERVICE_RESERVE();
            if (address(reserve) == address(0) || address(reserve.redress()) != issuer) return false;
        }
        bytes32 formId = BOOKING.currentForm(lessonId, placeId);
        if (!_contains(BOOKING.getPlannedForms(lessonId), formId)) return false;
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        if (form.confirmation.confirmedAt == 0 || form.terms.customer != customer || form.terms.normalFee != amount) {
            return false;
        }
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        if (ordinary) {
            if (
                lesson.terms.materialsTermsRef != bytes32(0) || bookingCoverageRequired[lessonId] == 0
                    || !_issuingOrdinaryCredit(formId, issuer)
            ) return false;
        } else if (lesson.terms.materialsTermsRef != bytes32(0) && bookingCoverageRequired[lessonId] == 0) {
            return false;
        }
        try BOOKING.PREFUNDING().requireAvailable(lessonId, lesson.prefunding.evidenceId, lesson.packageId) {}
        catch {
            return false;
        }
        bytes32 ref = bookingExposureReference(formId, COURSE_CREDIT);
        bool started = ordinary && BOOKING.getTeaching(lessonId).startedAt != 0;
        for (uint256 i; i < scenarios.length; ++i) {
            FundingScenario storage scenario = scenarios[i];
            if ((started && !scenario.teachingBegan) || !_contains(scenario.forms, formId)) continue;
            for (uint256 j; j < scenario.expenses.length; ++j) {
                Expense storage expense = scenario.expenses[j];
                if (
                    expense.referenceId == ref && expense.material == bytes32(0) && expense.obligationId == bytes32(0)
                        && expense.units == amount
                ) {
                    postedBookingCredit[lessonId][ref] = amount;
                    if (!ordinary) return true;
                    // Reuse the current compatible inventory after this exact expense has been covered.
                    try this.requiredForCases(lessonId, new MaterialBudget[](0), 0) returns (uint256 remaining) {
                        if (held - amount >= remaining) return true;
                    } catch {}
                    delete postedBookingCredit[lessonId][ref];
                    return false;
                }
            }
        }
        return false;
    }

    function _issuingOrdinaryCredit(bytes32 formId, address issuer) private view returns (bool) {
        SparkV15Settlement settlement = SparkV15Settlement(address(PAYMENTS.settlementPolicy()));
        if (address(settlement) == address(0)) return false;
        SparkV15LessonRemedies remedies = SparkV15LessonRemedies(address(settlement.remedyPolicy()));
        if (address(remedies) == address(0)) return false;
        SparkV15CustomerRedress redress = remedies.customerRedress();
        return address(redress) == issuer && redress.getRedress(formId).creditIssuedAt == block.timestamp;
    }

    /// @notice Recheck the retained funding evidence and its backing before a material booking commitment.
    function requireBookingCoverage(bytes32 lessonId, bytes32 formId) external view returns (bool) {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        if (lesson.terms.materialsTermsRef == bytes32(0)) return false;
        if (
            FUNDS.materialBookingCoverage() != address(this) || bookingCoverageRequired[lessonId] == 0
                || FUNDS.lessonReserved(lessonId) < lesson.prefunding.reservedUnits
                || (formId != bytes32(0) && !_contains(BOOKING.getPlannedForms(lessonId), formId))
        ) revert InvalidFundingInventory();
        BOOKING.REQUEST_ALLOCATION().EVIDENCE_REGISTRY()
            .requireUsableEvidenceReferenceForPackage(lesson.prefunding.evidenceId, lesson.packageId);
        return true;
    }

    /// @notice Decode the verified scenarios whose digest was used for the lesson's original prefunding check.
    function retainInventory(bytes32 lessonId, FundingScenario[] calldata scenarios) external {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        if (lesson.prefunding.evidenceId == 0 || casesByLesson[lessonId].length != 0 || scenarios.length == 0) {
            revert InvalidFundingInventory();
        }
        bytes32 inventoryRef = inventoryReference(lessonId, scenarios);
        bytes32[] memory planned = BOOKING.getPlannedForms(lessonId);
        uint256 evidenceId = lesson.prefunding.evidenceId;
        if (!BOOKING.PREFUNDING().matchesRetainedBasis(
            lessonId,
            evidenceId,
            lesson.packageId,
            BOOKING.prefundingCommitment(lessonId, planned, lesson.prefunding.reservedUnits, inventoryRef)
        )) revert InvalidFundingInventory();
        uint256 maximum;
        for (uint256 i; i < scenarios.length; ++i) {
            FundingScenario calldata supplied = scenarios[i];
            uint256 seatCount = supplied.forms.length;
            if (seatCount == 0 || seatCount != supplied.outcomes.length) revert InvalidFundingInventory();
            FundingScenario storage saved = casesByLesson[lessonId].push();
            saved.teachingBegan = supplied.teachingBegan;
            for (uint256 j; j < seatCount; ++j) {
                bytes32 formId = supplied.forms[j];
                if (supplied.outcomes[j] == bytes32(0) || !_contains(planned, formId)) {
                    revert InvalidFundingInventory();
                }
                for (uint256 k; k < j; ++k) {
                    if (supplied.forms[k] == formId) revert InvalidFundingInventory();
                }
                saved.forms.push(formId);
                saved.outcomes.push(supplied.outcomes[j]);
            }
            uint256 gross = _retainExpenses(lesson.terms.materialsTermsRef, supplied, saved);
            if (gross > maximum) maximum = gross;
        }
        address coverage = FUNDS.materialBookingCoverage();
        if (address(MATERIALS) == address(0)) {
            if (
                lesson.terms.materialsTermsRef != bytes32(0) || FUNDS.ordinaryBookingCoverage() != address(this)
                    || maximum > lesson.prefunding.reservedUnits
            ) revert InvalidFundingInventory();
            bookingCoverageRequired[lessonId] = maximum;
        } else if (lesson.terms.materialsTermsRef != bytes32(0) && coverage != address(0)) {
            if (coverage != address(this) || maximum > lesson.prefunding.reservedUnits) {
                revert InvalidFundingInventory();
            }
            _requireBookingOutcomes(lessonId, lesson.terms.materialsTermsRef, planned, scenarios);
            if (lesson.terms.rosterLockAt != 0) _retainDeliveryOutcomes(lessonId, scenarios);
            bookingCoverageRequired[lessonId] = maximum;
        }
        emit FundingInventoryRetained(lessonId, inventoryRef, evidenceId);
    }

    // This inventory compares one place and shares the same material costs in every started outcome.
    function _retainDeliveryOutcomes(bytes32 lessonId, FundingScenario[] calldata scenarios) private {
        uint8[] memory deliveryByScenario = new uint8[](scenarios.length);
        bytes32 formId;
        for (uint256 i; i < scenarios.length; ++i) {
            FundingScenario calldata scenario = scenarios[i];
            if (!scenario.teachingBegan) continue;
            for (uint256 j; j < scenario.forms.length; ++j) {
                bytes32 candidate = scenario.forms[j];
                for (
                    uint8 received = uint8(SparkV15LessonRemedies.TeachingReceived.NoneDelivered);
                    received <= uint8(SparkV15LessonRemedies.TeachingReceived.FullyDelivered);
                    ++received
                ) {
                    if (scenario.outcomes[j] != deliveryOutcome(candidate, received)) continue;
                    if (formId != bytes32(0) && formId != candidate) revert InvalidFundingInventory();
                    formId = candidate;
                    deliveryByScenario[i] = received;
                    break;
                }
            }
        }
        if (formId == bytes32(0)) return;

        bytes32 sharedMaterial;
        bool found;
        for (uint256 i; i < scenarios.length; ++i) {
            FundingScenario calldata scenario = scenarios[i];
            if (!scenario.teachingBegan) continue;
            bytes32 material;
            for (uint256 j; j < scenario.expenses.length; ++j) {
                Expense calldata expense = scenario.expenses[j];
                if (expense.material != bytes32(0)) material = keccak256(abi.encode(material, expense));
            }
            if (found && material != sharedMaterial) revert InvalidFundingInventory();
            sharedMaterial = material;
            found = true;
        }

        bytes32 discountRef = bookingExposureReference(formId, LATER_DISCOUNT);
        uint128 discount = BOOKING.getForm(formId).terms.normalFee / 2;
        bytes32[] memory expenseKeys = new bytes32[](scenarios.length);
        bool[] memory includesDiscount = new bool[](scenarios.length);
        for (uint256 i; i < scenarios.length; ++i) {
            if (deliveryByScenario[i] == 0) continue;
            (expenseKeys[i], includesDiscount[i]) = _deliveryPairKey(scenarios[i], formId, discountRef, discount);
        }
        for (uint256 i; i < scenarios.length; ++i) {
            if (
                deliveryByScenario[i] != uint8(SparkV15LessonRemedies.TeachingReceived.NoneDelivered)
                    || !includesDiscount[i]
            ) continue;
            for (uint256 j; j < scenarios.length; ++j) {
                if (
                    deliveryByScenario[j] == uint8(SparkV15LessonRemedies.TeachingReceived.PartiallyDelivered)
                        && !includesDiscount[j] && expenseKeys[i] == expenseKeys[j]
                ) {
                    replacesUndeliveredDiscount[lessonId][i] = true;
                    deliveryForm[lessonId] = formId;
                    break;
                }
            }
        }
    }

    // An exact partial-delivery row must carry all other costs, under the same other-place outcomes.
    function _deliveryPairKey(FundingScenario calldata scenario, bytes32 formId, bytes32 discountRef, uint128 discount)
        private
        pure
        returns (bytes32 key, bool includesDiscount)
    {
        key = keccak256(abi.encode(scenario.forms));
        for (uint256 i; i < scenario.forms.length; ++i) {
            if (scenario.forms[i] != formId) key = keccak256(abi.encode(key, scenario.outcomes[i]));
        }
        for (uint256 i; i < scenario.expenses.length; ++i) {
            Expense calldata expense = scenario.expenses[i];
            if (
                expense.referenceId == discountRef && expense.obligationId == bytes32(0)
                    && expense.material == bytes32(0) && expense.units == discount
            ) {
                includesDiscount = true;
            } else {
                key = keccak256(abi.encode(key, expense));
            }
        }
    }

    function _retainExpenses(bytes32 termsRef, FundingScenario calldata supplied, FundingScenario storage saved)
        private
        returns (uint256 gross)
    {
        for (uint256 i; i < supplied.expenses.length; ++i) {
            Expense calldata expense = supplied.expenses[i];
            if (expense.referenceId == bytes32(0) || expense.units == 0) revert InvalidFundingInventory();
            for (uint256 j; j < i; ++j) {
                Expense calldata prior = supplied.expenses[j];
                if (
                    prior.referenceId == expense.referenceId
                        || (expense.obligationId != bytes32(0) && expense.obligationId == prior.obligationId)
                ) revert InvalidFundingInventory();
            }
            if (
                (expense.material == bytes32(0) && (expense.termsRef != bytes32(0) || expense.portions.length != 0))
                    || (expense.material != bytes32(0) && (termsRef == bytes32(0) || expense.termsRef != termsRef))
            ) revert InvalidFundingInventory();
            Expense storage retained = saved.expenses.push();
            retained.referenceId = expense.referenceId;
            retained.obligationId = expense.obligationId;
            retained.material = expense.material;
            retained.termsRef = expense.termsRef;
            retained.units = expense.units;
            uint256 total;
            for (uint256 j; j < expense.portions.length; ++j) {
                MaterialPortion calldata portion = expense.portions[j];
                if (!_contains(supplied.forms, portion.formId)) revert InvalidFundingInventory();
                for (uint256 k; k < j; ++k) {
                    if (expense.portions[k].formId == portion.formId) revert InvalidFundingInventory();
                }
                total += portion.units;
                retained.portions.push(portion);
            }
            if (total > expense.units) revert InvalidFundingInventory();
            gross += expense.units;
        }
    }

    // The verifier supplies the compatible outcomes, the other agreed costs and any exclusions.
    function _requireBookingOutcomes(
        bytes32 lessonId,
        bytes32 termsRef,
        bytes32[] memory planned,
        FundingScenario[] calldata scenarios
    ) private view {
        SparkV15Materials.AgreedTerms memory annex = MATERIALS.getAgreedTerms(lessonId);
        if (annex.commitment != termsRef) revert InvalidFundingInventory();
        bytes32[] memory licensed = MATERIALS.getLicensedMaterials(lessonId);
        for (uint256 i; i < planned.length; ++i) {
            bytes32 formId = planned[i];
            SparkV15Booking.PlaceTerms memory place = BOOKING.getForm(formId).terms;
            uint256[] memory materialPrices = new uint256[](0);
            if (place.materialsBundleRef != bytes32(0)) {
                if (!MATERIALS.licensedForm(formId, licensed[0])) revert InvalidFundingInventory();
                materialPrices = MATERIALS.bookingMaterialPrices(lessonId, place.placeId, place.normalFee);
            }
            _requireSeatOutcomes(formId, place, licensed, materialPrices, scenarios);
        }
    }

    function _requireSeatOutcomes(
        bytes32 formId,
        SparkV15Booking.PlaceTerms memory place,
        bytes32[] memory licensed,
        uint256[] memory materialPrices,
        FundingScenario[] calldata scenarios
    ) private pure {
        uint128 half = place.normalFee / 2;
        uint128 halfRefund = half < place.payableFee ? half : place.payableFee;
        bool taughtStandard;
        bool untaughtStandard;
        bool taughtFullRefund;
        bool untaughtFullRefund;
        uint256 expectedMaterials;
        uint256 coveredMaterials;
        for (uint256 i; i < materialPrices.length; ++i) {
            if (materialPrices[i] != 0) expectedMaterials |= uint256(1) << i;
        }
        for (uint256 i; i < scenarios.length; ++i) {
            FundingScenario calldata scenario = scenarios[i];
            if (!_contains(scenario.forms, formId)) continue;
            SeatExposure memory exposure = _seatExposure(formId, scenario);
            if (exposure.refund > place.payableFee) revert InvalidFundingInventory();
            bool fullRefundOnly = exposure.refund == place.payableFee && exposure.credit == 0 && exposure.discount == 0;
            bool fullCredit = exposure.credit == place.normalFee;
            if (scenario.teachingBegan) {
                taughtStandard =
                    taughtStandard || (fullCredit && exposure.refund >= halfRefund && exposure.discount == 0);
                taughtFullRefund = taughtFullRefund || fullRefundOnly;
                coveredMaterials |= _seatMaterialsCovered(formId, licensed, materialPrices, scenario);
            } else {
                untaughtStandard = untaughtStandard
                    || (fullCredit && exposure.refund == place.payableFee && exposure.discount == half);
                untaughtFullRefund = untaughtFullRefund || fullRefundOnly;
            }
        }
        if (
            !taughtStandard || !untaughtStandard || !taughtFullRefund || !untaughtFullRefund
                || coveredMaterials != expectedMaterials
        ) {
            revert InvalidFundingInventory();
        }
    }

    function _seatExposure(bytes32 formId, FundingScenario calldata scenario)
        private
        pure
        returns (SeatExposure memory exposure)
    {
        bytes32 refundRef = bookingExposureReference(formId, ORIGINAL_REFUND);
        bytes32 creditRef = bookingExposureReference(formId, COURSE_CREDIT);
        bytes32 discountRef = bookingExposureReference(formId, LATER_DISCOUNT);
        for (uint256 i; i < scenario.expenses.length; ++i) {
            Expense calldata expense = scenario.expenses[i];
            bytes32 ref = expense.referenceId;
            if (ref != refundRef && ref != creditRef && ref != discountRef) continue;
            if (expense.material != bytes32(0)) revert InvalidFundingInventory();
            if (ref == refundRef) exposure.refund = expense.units;
            else if (ref == creditRef) exposure.credit = expense.units;
            else exposure.discount = expense.units;
        }
    }

    // A licensed item must be represented. The verifier determines which uses can occur together.
    function _seatMaterialsCovered(
        bytes32 formId,
        bytes32[] memory licensed,
        uint256[] memory prices,
        FundingScenario calldata scenario
    ) private pure returns (uint256 result) {
        for (uint256 i; i < prices.length; ++i) {
            if (prices[i] == 0) continue;
            uint256 covered;
            for (uint256 j; j < scenario.expenses.length; ++j) {
                Expense calldata expense = scenario.expenses[j];
                if (expense.material != licensed[i]) continue;
                for (uint256 k; k < expense.portions.length; ++k) {
                    if (expense.portions[k].formId == formId) covered += expense.portions[k].units;
                }
            }
            if (covered == prices[i]) result |= uint256(1) << i;
        }
    }

    /// @notice Check each verified compatible outcome separately against the same actual lesson funds.
    function requiredForCases(bytes32 lessonId, MaterialBudget[] calldata budgets, uint256 assignedMaterials)
        external
        view
        returns (uint256 maximum)
    {
        FundingScenario[] storage scenarios = casesByLesson[lessonId];
        bool started = BOOKING.getTeaching(lessonId).startedAt != 0;
        bool partialDelivery = _hasVerifiedPartialDelivery(lessonId);
        for (uint256 i; i < scenarios.length; ++i) {
            FundingScenario storage scenario = scenarios[i];
            if ((started && !scenario.teachingBegan) || (partialDelivery && replacesUndeliveredDiscount[lessonId][i])) {
                continue;
            }
            uint256 required = _requiredForCase(lessonId, scenario, budgets, assignedMaterials);
            if (required > maximum) maximum = required;
        }
    }

    function independentTeachingCosts(bytes32 lessonId) external view returns (uint256 maximum) {
        FundingScenario[] storage scenarios = casesByLesson[lessonId];
        bool partialDelivery = _hasVerifiedPartialDelivery(lessonId);
        for (uint256 i; i < scenarios.length; ++i) {
            FundingScenario storage scenario = scenarios[i];
            if (!scenario.teachingBegan || (partialDelivery && replacesUndeliveredDiscount[lessonId][i])) continue;
            uint256 required;
            for (uint256 j; j < scenario.expenses.length; ++j) {
                Expense storage expense = scenario.expenses[j];
                if (expense.material != bytes32(0)) continue;
                uint256 units = expense.units;
                required += units - _protectedUnits(lessonId, expense, units);
            }
            if (required > maximum) maximum = required;
        }
    }

    function _hasVerifiedPartialDelivery(bytes32 lessonId) private view returns (bool) {
        bytes32 formId = deliveryForm[lessonId];
        if (formId == bytes32(0)) return false;
        SparkV15ServiceReserve reserve = SparkV15MaterialProvisions(FUNDS.materialProvisions()).SERVICE_RESERVE();
        return
            address(reserve) != address(0)
                && reserve.hasVerifiedPartialDelivery(lessonId, formId, deliveryMatter(formId));
    }

    function _requiredForCase(
        bytes32 lessonId,
        FundingScenario storage scenario,
        MaterialBudget[] calldata budgets,
        uint256 assignedMaterials
    ) private view returns (uint256 required) {
        uint256[] memory covered = new uint256[](budgets.length);
        for (uint256 i; i < scenario.expenses.length; ++i) {
            Expense storage expense = scenario.expenses[i];
            if (
                scenario.teachingBegan && expense.material != bytes32(0) && expense.obligationId == bytes32(0)
                    && _matchesReceivedMaterial(lessonId, scenario, i)
            ) continue;
            uint256 units = expense.units;
            uint256 protectedUnits = _protectedUnits(lessonId, expense, units);
            required += units - protectedUnits;
            if (!scenario.teachingBegan || expense.material == bytes32(0)) continue;
            for (uint256 j; j < expense.portions.length; ++j) {
                MaterialPortion storage portion = expense.portions[j];
                for (uint256 k; k < budgets.length; ++k) {
                    MaterialBudget calldata budget = budgets[k];
                    if (
                        budget.formId == portion.formId && budget.material == expense.material
                            && budget.termsRef == expense.termsRef && portion.units > protectedUnits
                    ) covered[k] += portion.units - protectedUnits;
                }
            }
        }
        if (!scenario.teachingBegan) return required;
        uint256 additional;
        for (uint256 i; i < budgets.length; ++i) {
            if (budgets[i].units > covered[i]) additional += budgets[i].units - covered[i];
        }
        if (additional > assignedMaterials) required += additional - assignedMaterials;
    }

    /// @dev Match an estimated cost only to a uniquely attributable, fully received original charge.
    function _matchesReceivedMaterial(bytes32 lessonId, FundingScenario storage scenario, uint256 index)
        private
        view
        returns (bool)
    {
        Expense storage expense = scenario.expenses[index];
        if (expense.portions.length != 1 || expense.portions[0].units != expense.units) return false;
        for (uint256 i; i < scenario.expenses.length; ++i) {
            if (i != index && scenario.expenses[i].material == expense.material) return false;
        }

        bytes32 formId = expense.portions[0].formId;
        bytes32 scopeId = MATERIALS.originalFor(formId, expense.material);
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        if (
            scope.lessonId != lessonId || scope.termsRef != expense.termsRef || scope.total != expense.units
                || scope.sourceRef != expense.referenceId
        ) return false;
        bytes32[] memory forms = MATERIALS.getScopeForms(scopeId);
        if (forms.length != 1 || forms[0] != formId) return false;

        SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(FUNDS.materialProvisions());
        bytes32 key =
            provisions.fundingKey(lessonId, BOOKING.getForm(formId).terms.placeId, expense.material, expense.termsRef);
        return provisions.MATERIAL_BACKING().isFullyReceivedOriginal(key);
    }

    function _protectedUnits(bytes32 lessonId, Expense storage expense, uint256 units) private view returns (uint256) {
        bytes32 obligationId = expense.obligationId;
        if (obligationId == bytes32(0)) {
            uint256 posted = postedBookingCredit[lessonId][expense.referenceId];
            return posted < units ? posted : units;
        }
        SparkV15Payments.Obligation memory payment = PAYMENTS.getObligation(obligationId);
        if (payment.packageId == 0) return 0;
        if (payment.terms.lessonId != lessonId) revert InvalidFundingInventory();
        if (expense.material != bytes32(0)) _requireMaterialExpense(lessonId, expense);
        uint256 paid = payment.paid < units ? payment.paid : units;
        uint256 backing = FUNDS.paymentReserved(obligationId);
        return backing > units - paid ? units : paid + backing;
    }

    function _requireMaterialExpense(bytes32 lessonId, Expense storage expense) private view {
        SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(FUNDS.materialProvisions());
        bytes32 scopeId = provisions.getEntitlement(expense.obligationId).input.scopeId;
        SparkV15Materials materials = provisions.MATERIALS();
        SparkV15Materials.ChargeScope memory scope = materials.getChargeScope(scopeId);
        if (
            scopeId == bytes32(0) || scope.lessonId != lessonId || scope.material != expense.material
                || scope.termsRef != expense.termsRef
        ) revert InvalidFundingInventory();
        bytes32[] memory forms = materials.getScopeForms(scopeId);
        for (uint256 i; i < expense.portions.length; ++i) {
            if (!_contains(forms, expense.portions[i].formId)) revert InvalidFundingInventory();
        }
    }

    function _contains(bytes32[] memory forms, bytes32 formId) private pure returns (bool) {
        for (uint256 i; i < forms.length; ++i) {
            if (forms[i] == formId) return true;
        }
        return false;
    }
}
