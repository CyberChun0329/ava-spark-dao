// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {ISparkV15BookingChanges, SparkV15Booking} from "./SparkV15Booking.sol";
import {SparkV15Funds} from "./SparkV15Funds.sol";
import {SparkV15ReviewCases, SparkV15ReviewContext} from "./SparkV15ReviewCases.sol";

interface ISparkV15MaterialInterests {
    function MATERIALS() external view returns (address);
    function isEconomicHolder(bytes32 lessonId, bytes32 material, address actor) external view returns (bool);
}

interface ISparkV15OmissionGrossScope {
    function matchesOmissionGrossScope(
        bytes32 termsId,
        bytes32 matter,
        bytes32 scopeId,
        bytes32 obligationId,
        uint256 intakeEvidenceId,
        uint256 chargeEvidenceId
    ) external view returns (bool);
}

/// @notice Materials terms, verified use and recognised gross charges for one Spark v1.5 installation.
contract SparkV15Materials {
    struct HolderShare {
        address holder;
        uint32 units;
    }

    struct MaterialTerms {
        bytes32 material;
        uint32 rateNumerator;
        HolderShare[] holders;
        address[] contributors;
    }

    /// @dev The materials mask refers to the ordered MaterialTerms array; charges are in ascending bit order.
    struct PriceRow {
        bytes32 placeId;
        uint128 normalFee;
        uint256 materials;
        uint128[] charges;
    }

    struct Terms {
        bytes32 lessonId;
        bytes32 bundleRef;
        address payer;
        bytes32 contactRef;
        bytes32 licenceRef;
        bytes32 sharesAndAdjustmentsRef;
        uint64 paymentDue;
        uint64 paymentDeadline;
        uint32 rateDenominator;
        MaterialTerms[] materials;
        PriceRow[] otherPrices;
    }

    struct AgreedTerms {
        bytes32 commitment;
        bytes32 bundleRef;
        address payer;
        bytes32 contactRef;
        bytes32 licenceRef;
        bytes32 sharesAndAdjustmentsRef;
        uint64 adoptedAt;
        uint64 paymentDue;
        uint64 paymentDeadline;
        uint32 rateDenominator;
    }

    struct TutorMaterialsReport {
        uint256 expected;
        uint256 reported;
        uint64 listedAt;
        uint64 reportedAt;
    }

    enum UseSource {
        LessonRecord,
        StudentFeedback,
        OtherVerifiable
    }

    struct UseCheck {
        bytes32 formId;
        bytes32 material;
        uint64 usedAt;
        uint64 checkedAt;
        UseSource source;
        bytes32 serviceRef;
        bytes32 sourceRef;
        bool citeTutorReport;
        bool resolveReportOmission;
        bytes32 appointmentCaseId;
    }

    struct UseFinding {
        UseCheck check;
        uint64 availableAt;
        uint64 recordedAt;
        address verifiedBy;
        uint256 evidenceId;
    }

    struct CombinationSeat {
        bytes32 formId;
        uint256 materials;
    }

    struct CombinationInput {
        bytes32 lessonId;
        uint64 checkedAt;
        bytes32 sourceRef;
        CombinationSeat[][] options;
    }

    struct CombinationCheck {
        uint64 checkedAt;
        uint64 availableAt;
        uint64 recordedAt;
        uint256 evidenceId;
    }

    struct GrossInput {
        bytes32 lessonId;
        bytes32 material;
        bytes32 originalScopeId;
        bytes32 sourceRef;
        uint64 identifiedAt;
        bytes32[] forms;
    }

    struct ChargeScope {
        bytes32 lessonId;
        bytes32 material;
        bytes32 termsRef;
        bytes32 originalScopeId;
        bytes32 sourceRef;
        uint64 identifiedAt;
        uint64 recordedAt;
        address assessedBy;
        uint256 evidenceId;
        uint256 total;
    }

    struct ChargeRow {
        bytes32 formId;
        uint128 amount;
        bool present;
    }

    struct GrossReview {
        bytes32 scopeId;
        uint256 previousTotal;
        uint256 revisedTotal;
        uint256 attributedTotal;
        uint256 attributedSeats;
        uint64 reviewedAt;
    }

    struct GrossAttributionInput {
        bytes32 caseId;
        bytes32 formId;
        uint128 previous;
        uint128 revised;
        uint64 availableAt;
        bytes32 sourceRef;
    }

    struct GrossAttribution {
        GrossAttributionInput input;
        address verifier;
        uint256 evidenceId;
        uint64 recordedAt;
    }

    struct ReviewFollowUp {
        bytes32 caseId;
        bytes32 formId;
        uint256 useEvidenceId;
        bytes32 sourceRef;
        uint64 checkedAt;
    }

    error InvalidMaterialsInstallation();
    error InvalidMaterialsTerms();
    error InvalidMaterialsAuthority();
    error InvalidMaterialsEvidence();
    error InvalidMaterialsUse();
    error InvalidMaterialsCombination();
    error InvalidMaterialCharge();
    error MaterialsCapExceeded();
    error OutOfOrderMaterialCharge();
    error InvalidGrossReview();

    event MaterialsTermsAccepted(bytes32 indexed commitment, address indexed signer);
    event MaterialsTermsAdopted(bytes32 indexed lessonId, bytes32 indexed commitment, address indexed payer);
    event ExpectedMaterialsListed(bytes32 indexed lessonId, uint256 materials);
    event ActualMaterialsReported(bytes32 indexed lessonId, uint256 materials);
    event MaterialsCombinationChecked(bytes32 indexed lessonId, bytes32 indexed optionId, uint256 indexed evidenceId);
    event MaterialUseVerified(bytes32 indexed formId, bytes32 indexed material, uint256 indexed evidenceId);
    event MaterialsGrossRecorded(bytes32 indexed scopeId, bytes32 indexed originalScopeId, uint256 indexed evidenceId);
    event MaterialsGrossReviewBound(bytes32 indexed scopeId, bytes32 indexed caseId, uint256 revisedTotal);
    event MaterialsGrossAttributed(
        bytes32 indexed scopeId, bytes32 indexed caseId, bytes32 indexed formId, uint256 evidenceId
    );
    event MaterialsReviewUseRechecked(
        bytes32 indexed caseId, bytes32 indexed formId, uint256 indexed useEvidenceId, uint256 evidenceId
    );

    bytes32 public constant ACTION_CHECK_COMBINATIONS = keccak256("spark.action.check-material-combinations.v1.5");
    bytes32 public constant ACTION_VERIFY_USE = keccak256("spark.action.verify-material-use.v1.5");
    bytes32 public constant ACTION_RECORD_GROSS = keccak256("spark.action.record-material-gross.v1.5");
    bytes32 public constant ACTION_VERIFY_ATTRIBUTION =
        keccak256("spark.action.verify-material-gross-attribution.v1.5");
    bytes32 public constant ACTION_VERIFY_REVIEW_FOLLOW_UP =
        keccak256("spark.action.verify-material-review-follow-up.v1.5");

    SparkV15Booking public immutable BOOKING;
    SparkV15ReviewCases public immutable REVIEW_CASES;
    AVAEvidenceRegistry public immutable EVIDENCE_REGISTRY;
    address private immutable INSTALLER;
    SparkV15MaterialsUse public MATERIAL_USE;
    ISparkV15MaterialInterests public materialInterests;

    mapping(bytes32 => mapping(address => uint64)) public termsAcceptedAt;
    mapping(bytes32 => mapping(bytes32 => uint256)) public materialBit;
    mapping(bytes32 => AgreedTerms) private agreedTerms;
    mapping(bytes32 => bytes32[]) private licensedMaterials;
    mapping(bytes32 => mapping(bytes32 => MaterialTerms)) private materialTerms;
    mapping(bytes32 => mapping(bytes32 => uint128[])) private nonstandardPrices;
    mapping(bytes32 => mapping(bytes32 => uint256[])) private nonstandardMasks;
    mapping(bytes32 => ChargeScope) private chargeScopes;
    mapping(bytes32 => bytes32[]) private originalForms;
    mapping(bytes32 => mapping(bytes32 => bytes32)) public originalFor;
    mapping(bytes32 => mapping(bytes32 => ChargeRow)) private historicalCharges;
    mapping(bytes32 => mapping(bytes32 => uint64)) private lastPositiveShortfall;
    mapping(bytes32 => bytes32[]) private shortfalls;
    mapping(bytes32 => bytes32[]) private lessonScopes;

    constructor(SparkV15Booking booking, SparkV15ReviewCases reviewCases) {
        if (address(booking).code.length == 0 || address(reviewCases).code.length == 0) {
            revert InvalidMaterialsInstallation();
        }
        BOOKING = booking;
        REVIEW_CASES = reviewCases;
        EVIDENCE_REGISTRY = booking.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        INSTALLER = msg.sender;
    }

    /// @notice Attach this installation's evidence and use module.
    function bindMaterialUse(SparkV15MaterialsUse use) external {
        if (msg.sender != INSTALLER || address(MATERIAL_USE) != address(0) || use.MATERIALS() != this) {
            revert InvalidMaterialsInstallation();
        }
        MATERIAL_USE = use;
    }

    function bindMaterialInterests(ISparkV15MaterialInterests interests) external {
        BOOKING.REQUEST_ALLOCATION().IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .requireApplicationAdmin(msg.sender, SparkV15.APP_ID);
        if (address(materialInterests) != address(0) || interests.MATERIALS() != address(this)) {
            revert InvalidMaterialsInstallation();
        }
        materialInterests = interests;
    }

    function termsCommitment(Terms calldata terms) public view returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.materials.terms"), block.chainid, address(this), terms));
    }

    function acceptTerms(bytes32 commitment) external {
        if (commitment == bytes32(0) || termsAcceptedAt[commitment][msg.sender] != 0) revert InvalidMaterialsTerms();
        termsAcceptedAt[commitment][msg.sender] = uint64(block.timestamp);
        emit MaterialsTermsAccepted(commitment, msg.sender);
    }

    function adoptTerms(Terms calldata terms) external {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(terms.lessonId);
        bytes32 commitment = termsCommitment(terms);
        uint256 materialCount = terms.materials.length;
        if (
            msg.sender != lesson.terms.provider || lesson.terms.materialsTermsRef != commitment
                || lesson.prefunding.evidenceId != 0 || block.timestamp >= lesson.terms.startsAt
                || agreedTerms[terms.lessonId].adoptedAt != 0 || terms.payer == address(0)
                || (terms.payer != msg.sender && termsAcceptedAt[commitment][terms.payer] == 0)
                || terms.bundleRef == bytes32(0) || terms.contactRef == bytes32(0) || terms.licenceRef == bytes32(0)
                || terms.sharesAndAdjustmentsRef == bytes32(0) || terms.paymentDue < lesson.terms.endsAt
                || terms.paymentDeadline < terms.paymentDue || materialCount == 0 || materialCount > 256
                || (terms.rateDenominator == 0) != (terms.otherPrices.length != 0)
        ) revert InvalidMaterialsTerms();

        uint256 rateSum;
        for (uint256 i; i < materialCount; ++i) {
            MaterialTerms calldata item = terms.materials[i];
            _adoptMaterial(terms.lessonId, commitment, item, uint256(1) << i);
            rateSum += item.rateNumerator;
        }
        if (rateSum * 10 > terms.rateDenominator) revert InvalidMaterialsTerms();
        for (uint256 i; i < terms.otherPrices.length; ++i) {
            PriceRow calldata row = terms.otherPrices[i];
            bytes32 key = _priceKey(row.placeId, row.normalFee, row.materials);
            if (
                row.placeId == bytes32(0) || row.normalFee == 0 || row.materials == 0
                    || row.materials >> materialCount != 0 || _countMaterials(row.materials) != row.charges.length
                    || nonstandardPrices[terms.lessonId][key].length != 0
            ) revert InvalidMaterialsTerms();
            nonstandardPrices[terms.lessonId][key] = row.charges;
            nonstandardMasks[terms.lessonId][keccak256(abi.encode(row.placeId, row.normalFee))].push(row.materials);
        }
        agreedTerms[terms.lessonId] = AgreedTerms({
            commitment: commitment,
            bundleRef: terms.bundleRef,
            payer: terms.payer,
            contactRef: terms.contactRef,
            licenceRef: terms.licenceRef,
            sharesAndAdjustmentsRef: terms.sharesAndAdjustmentsRef,
            adoptedAt: uint64(block.timestamp),
            paymentDue: terms.paymentDue,
            paymentDeadline: terms.paymentDeadline,
            rateDenominator: terms.rateDenominator
        });
        emit MaterialsTermsAdopted(terms.lessonId, commitment, terms.payer);
    }

    function getAgreedTerms(bytes32 lessonId) external view returns (AgreedTerms memory) {
        return agreedTerms[lessonId];
    }

    function getMaterialTerms(bytes32 lessonId, bytes32 material) external view returns (MaterialTerms memory) {
        return materialTerms[lessonId][material];
    }

    /// @notice The adopted materials agreement matches the current booking version, including its named payer.
    function licensedForm(bytes32 formId, bytes32 material) external view returns (bool) {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        return _matchesAnnex(form, formId) && materialBit[form.lessonId][material] != 0;
    }

    function operationEvidenceCommitment(bytes32 lessonId, bytes32 action, address actor, bytes32 payload)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.materials.evidence"),
                block.chainid,
                address(this),
                lessonId,
                action,
                actor,
                payload
            )
        );
    }

    function listExpectedMaterials(bytes32 lessonId, uint256 mask) external {
        if (mask >> licensedMaterials[lessonId].length != 0 || agreedTerms[lessonId].adoptedAt == 0) {
            revert InvalidMaterialsUse();
        }
        MATERIAL_USE.listExpectedMaterials(msg.sender, lessonId, mask);
        emit ExpectedMaterialsListed(lessonId, mask);
    }

    function reportMaterialsUsed(bytes32 lessonId, uint256 mask) external {
        if (mask >> licensedMaterials[lessonId].length != 0) revert InvalidMaterialsUse();
        MATERIAL_USE.reportMaterialsUsed(msg.sender, lessonId, mask);
        emit ActualMaterialsReported(lessonId, mask);
    }

    /// @notice Retain each prospective whole-lesson option under the accepted price terms.
    function recordCombinationCheck(CombinationInput calldata input, uint256 evidenceId) external {
        bytes32[] memory options = MATERIAL_USE.recordCombinationCheck(msg.sender, input, evidenceId);
        for (uint256 i; i < options.length; ++i) {
            emit MaterialsCombinationChecked(input.lessonId, options[i], evidenceId);
        }
    }

    function verifyUse(UseCheck calldata input, uint256 evidenceId) external {
        MATERIAL_USE.verifyUse(msg.sender, input, evidenceId);
        emit MaterialUseVerified(input.formId, input.material, evidenceId);
    }

    function getUseFindings(bytes32 formId) external view returns (UseFinding[] memory) {
        return MATERIAL_USE.getUseFindings(formId);
    }

    function getLicensedMaterials(bytes32 lessonId) external view returns (bytes32[] memory) {
        return licensedMaterials[lessonId];
    }

    function getCombinationPrice(bytes32 formId, uint256 mask) external view returns (uint256 total) {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        if (!_matchesAnnex(form, formId)) revert InvalidMaterialsCombination();
        uint128[] storage prices = _otherPrice(form, mask);
        for (uint256 i; i < prices.length; ++i) {
            total += prices[i];
        }
    }

    function requireDisinterestedMaterialActor(bytes32 formId, bytes32 material, address actor) external view {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        _requireDisinterested(form, BOOKING.getLesson(form.lessonId), material, actor);
    }

    function getLessonChargeScopes(bytes32 lessonId) external view returns (bytes32[] memory) {
        return lessonScopes[lessonId];
    }

    function activeSeatMaterialGrossAt(bytes32 formId, bytes32 material, uint64 atTime)
        external
        view
        returns (uint256 total, bool pending)
    {
        bytes32 original = originalFor[formId][material];
        if (original == bytes32(0)) return (0, false);
        (uint128 gross, bool waiting) = MATERIAL_USE.scopeGross(original, formId, atTime);
        total = gross;
        pending = waiting;
        bytes32[] storage supplements = shortfalls[original];
        for (uint256 i; i < supplements.length; ++i) {
            (gross, waiting) = MATERIAL_USE.scopeGross(supplements[i], formId, atTime);
            total += gross;
            pending = pending || waiting;
        }
    }

    function useMatter(bytes32 formId, bytes32 material) public view returns (bytes32) {
        return keccak256(abi.encode(address(this), formId, material));
    }

    function getChargeScope(bytes32 scopeId) external view returns (ChargeScope memory) {
        return chargeScopes[scopeId];
    }

    function getScopeForms(bytes32 scopeId) external view returns (bytes32[] memory) {
        bytes32 originalScope = chargeScopes[scopeId].originalScopeId;
        return originalForms[originalScope == bytes32(0) ? scopeId : originalScope];
    }

    function getHistoricalCharge(bytes32 scopeId, bytes32 formId) external view returns (ChargeRow memory) {
        return historicalCharges[scopeId][formId];
    }

    function grossReviewBasis(bytes32 scopeId, uint256 gross) public view returns (bytes32) {
        return keccak256(
            abi.encode(keccak256("spark.v1.5.materials.review-basis"), block.chainid, address(this), scopeId, gross)
        );
    }

    function grossReviewOutcome(bytes32 caseId, bytes32 scopeId, uint256 previous, uint256 revised)
        public
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                keccak256("spark.v1.5.materials.review-outcome"), caseId, grossReviewBasis(scopeId, previous), revised
            )
        );
    }

    /// @notice Link the exact independent finding. It changes the amount only upon ReviewCases adoption.
    function bindGrossReview(bytes32 caseId, bytes32 scopeId, uint256 previousTotal, uint256 revisedTotal) external {
        MATERIAL_USE.bindGrossReview(caseId, scopeId, previousTotal, revisedTotal);
        emit MaterialsGrossReviewBound(scopeId, caseId, revisedTotal);
    }

    function getGrossAttribution(bytes32 caseId, bytes32 formId) external view returns (GrossAttribution memory) {
        return MATERIAL_USE.getGrossAttribution(caseId, formId);
    }

    /// @notice Attach verified attribution to an adopted correction, including an originally uncharged seat.
    function recordGrossAttribution(GrossAttributionInput calldata input, uint256 evidenceId) external {
        bytes32 scopeId = MATERIAL_USE.recordGrossAttribution(msg.sender, input, evidenceId);
        emit MaterialsGrossAttributed(scopeId, input.caseId, input.formId, evidenceId);
    }

    function verifyReviewFollowUp(ReviewFollowUp calldata input, uint256 evidenceId) external {
        MATERIAL_USE.verifyReviewFollowUp(msg.sender, input, evidenceId);
        emit MaterialsReviewUseRechecked(input.caseId, input.formId, input.useEvidenceId, evidenceId);
    }

    function activeScopeGrossAt(bytes32 scopeId, bytes32 formId, uint64 atTime)
        public
        view
        returns (uint128 amount, bool pending)
    {
        return MATERIAL_USE.scopeGross(scopeId, formId, atTime);
    }

    function activeLessonGrossAt(bytes32 lessonId, uint64 atTime) public view returns (uint256 total, uint256 cap) {
        bytes32[] storage scopes = lessonScopes[lessonId];
        for (uint256 i; i < scopes.length; ++i) {
            total += MATERIAL_USE.scopeTotalAt(scopes[i], atTime);
        }
        cap = MATERIAL_USE.capAt(lessonId, atTime);
    }

    function previewCharges(GrossInput calldata input) external view returns (ChargeRow[] memory rows, uint256 total) {
        return _previewCharges(input);
    }

    /// @notice Record an original settlement or a later strictly positive shortfall for its scoped places.
    function recordGross(GrossInput calldata input, uint256 evidenceId) external returns (bytes32 scopeId) {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(input.lessonId);
        _requireCoordinator(lesson, ACTION_RECORD_GROSS);
        if (
            this.requireMaterialEvidence(
                input.lessonId,
                lesson.packageId,
                ACTION_RECORD_GROSS,
                keccak256(abi.encode(input)),
                input.identifiedAt,
                evidenceId,
                msg.sender
            ) != input.identifiedAt
        ) revert InvalidMaterialsEvidence();
        (ChargeRow[] memory rows, uint256 total) = _previewCharges(input);
        bool original = input.originalScopeId == bytes32(0);
        if (!original && total == 0) return bytes32(0);
        scopeId = keccak256(abi.encode(address(this), input.lessonId, input.material, input.sourceRef));
        if (chargeScopes[scopeId].identifiedAt != 0) revert InvalidMaterialCharge();
        for (uint256 i; i < input.forms.length; ++i) {
            bytes32 formId = input.forms[i];
            _requireDisinterested(BOOKING.getForm(formId), lesson, input.material, msg.sender);
            if (original) {
                originalFor[formId][input.material] = scopeId;
            } else if (rows[i].amount != 0) {
                lastPositiveShortfall[input.originalScopeId][formId] = input.identifiedAt;
            }
            if (rows[i].present) historicalCharges[scopeId][formId] = rows[i];
        }
        if (original) originalForms[scopeId] = input.forms;
        else shortfalls[input.originalScopeId].push(scopeId);
        chargeScopes[scopeId] = ChargeScope(
            input.lessonId,
            input.material,
            agreedTerms[input.lessonId].commitment,
            input.originalScopeId,
            input.sourceRef,
            input.identifiedAt,
            uint64(block.timestamp),
            msg.sender,
            evidenceId,
            total
        );
        lessonScopes[input.lessonId].push(scopeId);
        emit MaterialsGrossRecorded(scopeId, input.originalScopeId, evidenceId);
    }

    function _previewCharges(GrossInput calldata input) private view returns (ChargeRow[] memory rows, uint256 total) {
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(input.lessonId);
        uint256 bit = materialBit[input.lessonId][input.material];
        bool original = input.originalScopeId == bytes32(0);
        ChargeScope storage originalScope = chargeScopes[input.originalScopeId];
        if (
            bit == 0 || teaching.endedAt == 0 || input.identifiedAt <= teaching.endedAt
                || input.identifiedAt > block.timestamp || input.sourceRef == bytes32(0) || input.forms.length == 0
                || (!original
                    && (originalScope.lessonId != input.lessonId
                        || originalScope.material != input.material
                        || originalScope.originalScopeId != bytes32(0)
                        || originalScope.identifiedAt >= input.identifiedAt))
        ) revert InvalidMaterialCharge();
        if (agreedTerms[input.lessonId].rateDenominator == 0) {
            MATERIAL_USE.requireCheckedPricing(input.lessonId, input.identifiedAt);
        }

        rows = new ChargeRow[](input.forms.length);
        for (uint256 i; i < rows.length; ++i) {
            bytes32 formId = input.forms[i];
            SparkV15Booking.Form memory form = BOOKING.getForm(formId);
            if (
                form.lessonId != input.lessonId || !_matchesAnnex(form, formId) || form.confirmation.confirmedAt == 0
                    || originalFor[formId][input.material] != input.originalScopeId
            ) revert InvalidMaterialCharge();
            for (uint256 j; j < i; ++j) {
                if (input.forms[j] == formId) revert InvalidMaterialCharge();
            }
            uint256 used = MATERIAL_USE.usedMaskAt(input.lessonId, formId, input.identifiedAt);
            if ((used & bit) == 0) continue;
            uint128 charge = _charge(form, input.material, bit, used);
            if (!original) charge = _shortfallAt(input.originalScopeId, formId, input.identifiedAt, charge);
            rows[i] = ChargeRow(formId, charge, true);
            total += charge;
        }
        (uint256 current, uint256 cap) = activeLessonGrossAt(input.lessonId, input.identifiedAt);
        if (current + total > cap) revert MaterialsCapExceeded();
        if (total > 0 && input.identifiedAt < block.timestamp) {
            (current, cap) = activeLessonGrossAt(input.lessonId, uint64(block.timestamp));
            if (current + total > cap) revert MaterialsCapExceeded();
        }
    }

    function _shortfallAt(bytes32 originalScope, bytes32 formId, uint64 atTime, uint128 verifiedCharge)
        private
        view
        returns (uint128)
    {
        (uint128 amount, bool pending) = MATERIAL_USE.scopeGrossForShortfall(originalScope, formId, atTime);
        if (pending) return 0;
        uint256 established = amount;
        bytes32[] storage prior = shortfalls[originalScope];
        for (uint256 i; i < prior.length; ++i) {
            if (chargeScopes[prior[i]].identifiedAt >= atTime) continue;
            (amount, pending) = MATERIAL_USE.scopeGrossForShortfall(prior[i], formId, atTime);
            if (pending) return 0;
            established += amount;
        }
        if (verifiedCharge <= established) return 0;
        if (lastPositiveShortfall[originalScope][formId] >= atTime) revert OutOfOrderMaterialCharge();
        return verifiedCharge - uint128(established);
    }

    function _adoptMaterial(bytes32 lessonId, bytes32 commitment, MaterialTerms calldata item, uint256 bit) private {
        if (item.material == bytes32(0) || materialBit[lessonId][item.material] != 0 || item.holders.length == 0) {
            revert InvalidMaterialsTerms();
        }
        MaterialTerms storage line = materialTerms[lessonId][item.material];
        line.material = item.material;
        line.rateNumerator = item.rateNumerator;
        for (uint256 i; i < item.holders.length; ++i) {
            HolderShare calldata share = item.holders[i];
            if (share.units == 0 || termsAcceptedAt[commitment][share.holder] == 0) revert InvalidMaterialsTerms();
            for (uint256 j; j < i; ++j) {
                if (item.holders[j].holder == share.holder) revert InvalidMaterialsTerms();
            }
            line.holders.push(share);
        }
        for (uint256 i; i < item.contributors.length; ++i) {
            if (termsAcceptedAt[commitment][item.contributors[i]] == 0) revert InvalidMaterialsTerms();
        }
        line.contributors = item.contributors;
        materialBit[lessonId][item.material] = bit;
        licensedMaterials[lessonId].push(item.material);
    }

    function _matchesAnnex(SparkV15Booking.Form memory form, bytes32 formId) private view returns (bool) {
        AgreedTerms storage terms = agreedTerms[form.lessonId];
        return terms.adoptedAt != 0 && form.terms.materialsBundleRef == terms.bundleRef
            && form.terms.materialPayer == terms.payer
            && BOOKING.currentForm(form.lessonId, form.terms.placeId) == formId;
    }

    function _requireCoordinator(SparkV15Booking.Lesson memory lesson, bytes32 action) private view {
        if (msg.sender != lesson.terms.coordinator) revert InvalidMaterialsAuthority();
        BOOKING.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(msg.sender, SparkV15.APP_ID, BOOKING.COORDINATOR_ROLE(), action);
    }

    function _requireDisinterested(
        SparkV15Booking.Form memory form,
        SparkV15Booking.Lesson memory lesson,
        bytes32 material,
        address actor
    ) private view {
        SparkV15Booking.PlaceTerms memory place = form.terms;
        if (
            actor == place.student || actor == place.payer || actor == place.customer
                || actor == place.customerRepresentative || actor == place.materialPayer || actor == lesson.terms.tutor
        ) revert InvalidMaterialsAuthority();
        HolderShare[] storage holders = materialTerms[form.lessonId][material].holders;
        for (uint256 i; i < holders.length; ++i) {
            if (actor == holders[i].holder) revert InvalidMaterialsAuthority();
        }
        if (
            address(materialInterests) != address(0)
                && materialInterests.isEconomicHolder(form.lessonId, material, actor)
        ) {
            revert InvalidMaterialsAuthority();
        }
    }

    /// @dev The materials and use modules supply the lesson's applicable package.
    function requireMaterialEvidence(
        bytes32 lessonId,
        uint256 packageId,
        bytes32 action,
        bytes32 payload,
        uint64 businessAt,
        uint256 evidenceId,
        address actor
    ) external view returns (uint64 availableAt) {
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
        if (
            EVIDENCE_REGISTRY.getEvidenceReference(evidenceId).commitment
                != operationEvidenceCommitment(lessonId, action, actor, payload)
        ) revert InvalidMaterialsEvidence();
        availableAt = EVIDENCE_REGISTRY.getEvidence(evidenceId).registeredAt;
        if (businessAt == 0 || businessAt > availableAt) revert InvalidMaterialsEvidence();
    }

    /// @notice Highest adopted price by licensed material, across the available combinations for this seat.
    function bookingMaterialPrices(bytes32 lessonId, bytes32 placeId, uint128 normalFee)
        external
        view
        returns (uint256[] memory prices)
    {
        bytes32[] storage licensed = licensedMaterials[lessonId];
        prices = new uint256[](licensed.length);
        uint32 denominator = agreedTerms[lessonId].rateDenominator;
        if (denominator != 0) {
            for (uint256 i; i < licensed.length; ++i) {
                uint256 numerator = uint256(normalFee) * materialTerms[lessonId][licensed[i]].rateNumerator;
                if (numerator % denominator != 0) revert InvalidMaterialCharge();
                prices[i] = numerator / denominator;
            }
            return prices;
        }
        uint256[] storage masks = nonstandardMasks[lessonId][keccak256(abi.encode(placeId, normalFee))];
        if (masks.length == 0) revert InvalidMaterialsCombination();
        for (uint256 i; i < masks.length; ++i) {
            uint256 mask = masks[i];
            uint128[] storage charges = nonstandardPrices[lessonId][_priceKey(placeId, normalFee, mask)];
            uint256 charge;
            for (uint256 j; j < licensed.length; ++j) {
                if (mask & (uint256(1) << j) == 0) continue;
                uint128 amount = charges[charge++];
                if (amount > prices[j]) prices[j] = amount;
            }
        }
    }

    function _charge(SparkV15Booking.Form memory form, bytes32 material, uint256 bit, uint256 used)
        private
        view
        returns (uint128)
    {
        uint32 denominator = agreedTerms[form.lessonId].rateDenominator;
        if (denominator == 0) return _otherPrice(form, used)[_countMaterials(used & (bit - 1))];
        uint256 numerator = uint256(form.terms.normalFee) * materialTerms[form.lessonId][material].rateNumerator;
        if (numerator % denominator != 0) revert InvalidMaterialCharge();
        return uint128(numerator / denominator);
    }

    function _otherPrice(SparkV15Booking.Form memory form, uint256 mask)
        private
        view
        returns (uint128[] storage prices)
    {
        prices = nonstandardPrices[form.lessonId][_priceKey(form.terms.placeId, form.terms.normalFee, mask)];
        if (prices.length == 0) revert InvalidMaterialsCombination();
    }

    function _priceKey(bytes32 placeId, uint128 normalFee, uint256 mask) private pure returns (bytes32) {
        return keccak256(abi.encode(placeId, normalFee, mask));
    }

    function _countMaterials(uint256 mask) private pure returns (uint256 count) {
        while (mask != 0) {
            mask &= mask - 1;
            ++count;
        }
    }
}

/// @notice Evidence and checked combinations used by the materials settlement.
contract SparkV15MaterialsUse {
    SparkV15Materials public immutable MATERIALS;
    SparkV15Booking private immutable BOOKING;
    SparkV15ReviewCases private immutable REVIEW_CASES;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;

    mapping(bytes32 => SparkV15Materials.TutorMaterialsReport) public tutorMaterialsReports;
    mapping(bytes32 => SparkV15Materials.CombinationCheck) public combinationChecks;
    mapping(bytes32 => mapping(bytes32 => uint256)) private combinationMasks;
    mapping(bytes32 => bytes32[]) private lessonOptions;
    mapping(bytes32 => SparkV15Materials.UseFinding[]) private useFindings;
    mapping(bytes32 => bytes32[]) private verifiedForms;
    mapping(uint256 => bool) private usedFindingEvidence;
    mapping(bytes32 => bytes32[]) private reviewsByScope;
    mapping(bytes32 => SparkV15Materials.GrossReview) public grossReviews;
    mapping(bytes32 => mapping(bytes32 => SparkV15Materials.GrossAttribution)) private grossAttributions;
    mapping(bytes32 => mapping(bytes32 => uint64)) public reviewFollowUpAvailableAt;
    mapping(bytes32 => mapping(address => SparkV15Materials.TutorMaterialsReport)) public replacementTutorMaterialsReports;

    constructor(SparkV15Materials materials) {
        MATERIALS = materials;
        BOOKING = materials.BOOKING();
        REVIEW_CASES = materials.REVIEW_CASES();
        EVIDENCE_REGISTRY = materials.EVIDENCE_REGISTRY();
    }

    modifier onlyMaterials() {
        if (msg.sender != address(MATERIALS)) revert SparkV15Materials.InvalidMaterialsAuthority();
        _;
    }

    function _requireCoordinator(SparkV15Booking.Lesson memory lesson, bytes32 action, address actor) private view {
        if (actor != lesson.terms.coordinator) revert SparkV15Materials.InvalidMaterialsAuthority();
        BOOKING.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(actor, SparkV15.APP_ID, BOOKING.COORDINATOR_ROLE(), action);
    }

    function _requireEvidence(
        SparkV15Booking.Lesson memory lesson,
        bytes32 action,
        bytes32 payload,
        uint64 businessAt,
        uint256 evidenceId,
        address actor
    ) private view returns (uint64) {
        return MATERIALS.requireMaterialEvidence(
            lesson.terms.lessonId, lesson.packageId, action, payload, businessAt, evidenceId, actor
        );
    }

    function capAt(bytes32 lessonId, uint64 atTime) external view returns (uint256 cap) {
        bytes32[] storage verified = verifiedForms[lessonId];
        for (uint256 i; i < verified.length; ++i) {
            if (_useMask(lessonId, verified[i], atTime, type(uint64).max) != 0) {
                cap += BOOKING.getForm(verified[i]).terms.normalFee;
            }
        }
        cap /= 10;
    }

    function usedMaskAt(bytes32 lessonId, bytes32 formId, uint64 atTime) external view returns (uint256) {
        return _useMask(lessonId, formId, atTime, type(uint64).max);
    }

    function listExpectedMaterials(address actor, bytes32 lessonId, uint256 mask) external onlyMaterials {
        ISparkV15BookingChanges.Arrangement memory arrangement =
            BOOKING.getEffectiveArrangement(lessonId, uint64(block.timestamp));
        if (actor != arrangement.tutor) {
            // A finalized future assignment may begin at the exact opening time.
            arrangement = BOOKING.getEffectiveArrangement(lessonId, type(uint64).max);
        }
        SparkV15Materials.TutorMaterialsReport storage report = _tutorMaterialsReport(lessonId, actor);
        if (
            actor != arrangement.tutor || block.timestamp >= arrangement.startsAt || report.listedAt != 0
        ) revert SparkV15Materials.InvalidMaterialsUse();
        report.expected = mask;
        report.listedAt = uint64(block.timestamp);
    }

    function reportMaterialsUsed(address actor, bytes32 lessonId, uint256 mask) external onlyMaterials {
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(lessonId);
        SparkV15Materials.TutorMaterialsReport storage report = _tutorMaterialsReport(lessonId, actor);
        if (
            actor != BOOKING.getEffectiveArrangement(lessonId, teaching.startedAt).tutor || teaching.endedAt == 0
                || block.timestamp <= teaching.endedAt || report.listedAt == 0 || report.listedAt >= teaching.startedAt
                || report.reportedAt != 0
        ) revert SparkV15Materials.InvalidMaterialsUse();
        report.reported = mask;
        report.reportedAt = uint64(block.timestamp);
    }

    function _tutorMaterialsReport(bytes32 lessonId, address tutor)
        private
        view
        returns (SparkV15Materials.TutorMaterialsReport storage)
    {
        if (tutor == BOOKING.getLesson(lessonId).terms.tutor) return tutorMaterialsReports[lessonId];
        return replacementTutorMaterialsReports[lessonId][tutor];
    }

    function recordCombinationCheck(
        address actor,
        SparkV15Materials.CombinationInput calldata input,
        uint256 evidenceId
    ) external onlyMaterials returns (bytes32[] memory options) {
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(input.lessonId);
        _requireCoordinator(lesson, MATERIALS.ACTION_CHECK_COMBINATIONS(), actor);
        SparkV15Materials.AgreedTerms memory terms = MATERIALS.getAgreedTerms(input.lessonId);
        if (
            input.sourceRef == bytes32(0) || input.options.length == 0 || terms.adoptedAt == 0
                || terms.rateDenominator != 0 || input.checkedAt < terms.adoptedAt
        ) revert SparkV15Materials.InvalidMaterialsCombination();
        uint64 availableAt = _requireEvidence(
            lesson,
            MATERIALS.ACTION_CHECK_COMBINATIONS(),
            keccak256(abi.encode(input)),
            input.checkedAt,
            evidenceId,
            actor
        );
        options = new bytes32[](input.options.length);
        for (uint256 i; i < input.options.length; ++i) {
            SparkV15Materials.CombinationSeat[] memory option = input.options[i];
            bytes32 optionId = _combinationId(input.lessonId, option);
            if (combinationChecks[optionId].evidenceId != 0 || option.length == 0) {
                revert SparkV15Materials.InvalidMaterialsCombination();
            }
            uint256 total;
            uint256 normalFees;
            for (uint256 j; j < option.length; ++j) {
                SparkV15Materials.CombinationSeat memory seat = option[j];
                SparkV15Booking.Form memory form = BOOKING.getForm(seat.formId);
                if (
                    form.lessonId != input.lessonId || form.confirmation.confirmedAt == 0
                        || form.confirmation.confirmedAt > input.checkedAt || seat.materials == 0
                        || combinationMasks[optionId][seat.formId] != 0
                ) revert SparkV15Materials.InvalidMaterialsCombination();
                total += MATERIALS.getCombinationPrice(seat.formId, seat.materials);
                normalFees += form.terms.normalFee;
                combinationMasks[optionId][seat.formId] = seat.materials;
            }
            if (total > normalFees / 10) revert SparkV15Materials.MaterialsCapExceeded();
            combinationChecks[optionId] =
                SparkV15Materials.CombinationCheck(input.checkedAt, availableAt, uint64(block.timestamp), evidenceId);
            lessonOptions[input.lessonId].push(optionId);
            options[i] = optionId;
        }
    }

    function verifyUse(address actor, SparkV15Materials.UseCheck calldata input, uint256 evidenceId)
        external
        onlyMaterials
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(input.formId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(form.lessonId);
        SparkV15Booking.Teaching memory teaching = BOOKING.getTeaching(form.lessonId);
        uint256 bit = MATERIALS.materialBit(form.lessonId, input.material);
        if (
            !MATERIALS.licensedForm(input.formId, input.material) || bit == 0 || form.confirmation.confirmedAt == 0
                || teaching.startedAt == 0 || teaching.endedAt <= teaching.startedAt
                || input.usedAt < teaching.startedAt || input.usedAt > teaching.endedAt
                || input.checkedAt < teaching.endedAt
                || MATERIALS.getAgreedTerms(form.lessonId).adoptedAt >= input.usedAt || input.serviceRef == bytes32(0)
                || input.sourceRef == bytes32(0) || usedFindingEvidence[evidenceId]
        ) revert SparkV15Materials.InvalidMaterialsUse();
        _requireUseHandler(lesson, input, actor);
        MATERIALS.requireDisinterestedMaterialActor(input.formId, input.material, actor);
        address tutor = BOOKING.getEffectiveArrangement(form.lessonId, teaching.startedAt).tutor;
        if (actor == tutor) revert SparkV15Materials.InvalidMaterialsAuthority();
        if (input.source == SparkV15Materials.UseSource.StudentFeedback) {
            SparkV15Booking.ServiceFeedback memory feedback = BOOKING.getServiceFeedback(input.formId);
            if (
                feedback.status < SparkV15Booking.ServiceStatus.PartiallyDelivered || input.usedAt > feedback.reportedAt
                    || feedback.reportedAt > input.checkedAt || input.serviceRef != feedback.receivedRef
            ) revert SparkV15Materials.InvalidMaterialsUse();
        }
        if (input.citeTutorReport) {
            SparkV15Materials.TutorMaterialsReport storage report = _tutorMaterialsReport(form.lessonId, tutor);
            if (
                report.reportedAt == 0 || report.reportedAt > input.checkedAt
                    || input.resolveReportOmission != ((report.reported & bit) == 0)
            ) revert SparkV15Materials.InvalidMaterialsUse();
        } else if (input.resolveReportOmission) {
            revert SparkV15Materials.InvalidMaterialsUse();
        }
        uint64 availableAt = _requireEvidence(
            lesson, MATERIALS.ACTION_VERIFY_USE(), keccak256(abi.encode(input)), input.checkedAt, evidenceId, actor
        );
        if (useFindings[input.formId].length == 0) verifiedForms[form.lessonId].push(input.formId);
        usedFindingEvidence[evidenceId] = true;
        useFindings[input.formId].push(
            SparkV15Materials.UseFinding(input, availableAt, uint64(block.timestamp), actor, evidenceId)
        );
    }

    function getUseFindings(bytes32 formId) external view returns (SparkV15Materials.UseFinding[] memory) {
        return useFindings[formId];
    }

    function _requireUseHandler(
        SparkV15Booking.Lesson memory lesson,
        SparkV15Materials.UseCheck calldata input,
        address actor
    ) private view {
        if (actor == lesson.terms.coordinator && input.appointmentCaseId == bytes32(0)) {
            _requireCoordinator(lesson, MATERIALS.ACTION_VERIFY_USE(), actor);
            return;
        }
        SparkV15ReviewContext.ConcernRecord memory concern = REVIEW_CASES.INTAKE().getConcern(input.appointmentCaseId);
        if (
            concern.lessonId != lesson.terms.lessonId
                || concern.intake.subject != SparkV15ReviewContext.ConcernSubject.MaterialOmission
                || concern.intake.subjectRef != MATERIALS.useMatter(input.formId, input.material)
                || !REVIEW_CASES.isAppointed(
                    input.appointmentCaseId,
                    SparkV15ReviewContext.AppointmentPurpose.InitialDecision,
                    actor,
                    input.checkedAt
                )
        ) revert SparkV15Materials.InvalidMaterialsAuthority();
        REVIEW_CASES.requireDisinterested(input.appointmentCaseId, actor, input.checkedAt);
    }

    function _useMask(bytes32 lessonId, bytes32 formId, uint64 availableBy, uint64 usedThrough)
        private
        view
        returns (uint256 used)
    {
        SparkV15Materials.UseFinding[] storage findings = useFindings[formId];
        for (uint256 i; i < findings.length; ++i) {
            SparkV15Materials.UseFinding storage finding = findings[i];
            if (finding.availableAt <= availableBy && finding.check.usedAt <= usedThrough) {
                used |= MATERIALS.materialBit(lessonId, finding.check.material);
            }
        }
    }

    function requireCheckedPricing(bytes32 lessonId, uint64 atTime) external view {
        bytes32[] storage forms = verifiedForms[lessonId];
        SparkV15Materials.CombinationSeat[] memory combination = new SparkV15Materials.CombinationSeat[](forms.length);
        uint256 count;
        for (uint256 i; i < forms.length; ++i) {
            uint256 mask = _useMask(lessonId, forms[i], atTime, type(uint64).max);
            if (mask != 0) combination[count++] = SparkV15Materials.CombinationSeat(forms[i], mask);
        }
        if (count == 0) revert SparkV15Materials.InvalidMaterialsCombination();
        // Allocate only the actual seats, excluding forms whose verification was unavailable at the business time.
        SparkV15Materials.CombinationSeat[] memory actual = new SparkV15Materials.CombinationSeat[](count);
        for (uint256 i; i < count; ++i) {
            actual[i] = combination[i];
        }
        SparkV15Materials.CombinationCheck storage finalCheck = combinationChecks[_combinationId(lessonId, actual)];
        if (finalCheck.evidenceId == 0 || finalCheck.availableAt > atTime) {
            revert SparkV15Materials.InvalidMaterialsCombination();
        }

        bool checkPrecedesUse;
        for (uint256 i; i < forms.length; ++i) {
            SparkV15Materials.UseFinding[] storage findings = useFindings[forms[i]];
            for (uint256 j; j < findings.length; ++j) {
                SparkV15Materials.UseFinding storage finding = findings[j];
                if (finding.availableAt > atTime) continue;
                uint64 usedAt = finding.check.usedAt;
                if (finalCheck.checkedAt < usedAt) {
                    if (!checkPrecedesUse) checkPrecedesUse = _isFirstVerifiedUse(findings, finding, atTime);
                } else if (!_prospectiveOptionCovers(lessonId, atTime, usedAt)) {
                    revert SparkV15Materials.InvalidMaterialsCombination();
                }
            }
        }
        if (!checkPrecedesUse) revert SparkV15Materials.InvalidMaterialsCombination();
    }

    function _isFirstVerifiedUse(
        SparkV15Materials.UseFinding[] storage findings,
        SparkV15Materials.UseFinding storage candidate,
        uint64 atTime
    ) private view returns (bool) {
        for (uint256 i; i < findings.length; ++i) {
            SparkV15Materials.UseFinding storage finding = findings[i];
            if (
                finding.availableAt <= atTime && finding.check.material == candidate.check.material
                    && finding.check.usedAt < candidate.check.usedAt
            ) return false;
        }
        return true;
    }

    function _prospectiveOptionCovers(bytes32 lessonId, uint64 atTime, uint64 usedThrough) private view returns (bool) {
        bytes32[] storage options = lessonOptions[lessonId];
        bytes32[] storage forms = verifiedForms[lessonId];
        for (uint256 i; i < options.length; ++i) {
            bytes32 option = options[i];
            SparkV15Materials.CombinationCheck storage check = combinationChecks[option];
            if (check.availableAt > atTime || check.checkedAt >= usedThrough) continue;
            bool covers = true;
            for (uint256 j; j < forms.length; ++j) {
                bytes32 formId = forms[j];
                if (_useMask(lessonId, formId, atTime, usedThrough) & ~combinationMasks[option][formId] != 0) {
                    covers = false;
                    break;
                }
            }
            if (covers) return true;
        }
        return false;
    }

    function _combinationId(bytes32 lessonId, SparkV15Materials.CombinationSeat[] memory seats)
        private
        pure
        returns (bytes32)
    {
        for (uint256 i = 1; i < seats.length; ++i) {
            SparkV15Materials.CombinationSeat memory seat = seats[i];
            uint256 j = i;
            while (j != 0 && seats[j - 1].formId > seat.formId) {
                seats[j] = seats[j - 1];
                --j;
            }
            seats[j] = seat;
        }
        return keccak256(abi.encode(lessonId, seats));
    }

    function scopeTotalAt(bytes32 scopeId, uint64 atTime) external view returns (uint256) {
        return _scopeTotalAt(scopeId, atTime);
    }

    function getScopeReviewCases(bytes32 scopeId) external view returns (bytes32[] memory) {
        return reviewsByScope[scopeId];
    }

    /// @notice Resolve a retained original decision before the independent review is made.
    function retainedGrossScope(bytes32 caseId, bytes32 lessonId)
        external
        view
        returns (bytes32 scopeId, uint256 evidenceId)
    {
        bytes32[] memory scopes = MATERIALS.getLessonChargeScopes(lessonId);
        if (scopes.length == 0) return (bytes32(0), 0);
        SparkV15ReviewContext.OriginalOutcome memory original = REVIEW_CASES.getCase(caseId).original;
        for (uint256 i; i < scopes.length; ++i) {
            SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopes[i]);
            if (
                scope.identifiedAt != original.decidedAt || scope.assessedBy != original.decider
                    || MATERIALS.grossReviewBasis(scopes[i], scope.total) != original.outcome
            ) continue;
            return (scopes[i], original.evidenceId);
        }
        return (bytes32(0), 0);
    }

    function scopeGross(bytes32 scopeId, bytes32 formId, uint64 atTime)
        external
        view
        returns (uint128 amount, bool pending)
    {
        return _scopeGross(scopeId, formId, atTime, bytes32(0), false);
    }

    function scopeGrossForShortfall(bytes32 scopeId, bytes32 formId, uint64 atTime)
        external
        view
        returns (uint128 amount, bool pending)
    {
        return _scopeGross(scopeId, formId, atTime, bytes32(0), true);
    }

    function _originalId(bytes32 scopeId, SparkV15Materials.ChargeScope memory scope) private pure returns (bytes32) {
        return scope.originalScopeId == bytes32(0) ? scopeId : scope.originalScopeId;
    }

    function bindGrossReview(bytes32 caseId, bytes32 scopeId, uint256 previousTotal, uint256 revisedTotal)
        external
        onlyMaterials
    {
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        SparkV15ReviewContext.CaseRecord memory reviewCase = REVIEW_CASES.getCase(caseId);
        SparkV15ReviewContext.ConcernRecord memory concern = REVIEW_CASES.INTAKE().getConcern(caseId);
        bytes32[] storage prior = reviewsByScope[scopeId];
        if (
            scope.identifiedAt == 0 || grossReviews[caseId].scopeId != bytes32(0) || concern.lessonId != scope.lessonId
                || !_matchesGrossConcern(scopeId, scope.evidenceId, concern)
                || reviewCase.original.outcome != MATERIALS.grossReviewBasis(scopeId, previousTotal)
                || reviewCase.original.decidedAt != scope.identifiedAt
                || reviewCase.original.decider != scope.assessedBy || reviewCase.review.decidedAt <= scope.identifiedAt
                || reviewCase.review.input.disposition != SparkV15ReviewContext.ReviewDisposition.CorrectionRequired
                || reviewCase.review.input.approvalRequestId != 0
                || reviewCase.review.input.outcome
                    != MATERIALS.grossReviewOutcome(caseId, scopeId, previousTotal, revisedTotal)
                || _scopeTotalAt(scopeId, reviewCase.review.decidedAt) != previousTotal
                || (prior.length != 0 && _adoptedGrossAt(prior[prior.length - 1], reviewCase.review.decidedAt) == 0)
        ) revert SparkV15Materials.InvalidGrossReview();
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(scope.lessonId);
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(reviewCase.original.evidenceId, lesson.packageId);
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(reviewCase.review.evidenceId, lesson.packageId);
        bytes32[] memory forms = MATERIALS.getScopeForms(scopeId);
        for (uint256 i; i < forms.length; ++i) {
            MATERIALS.requireDisinterestedMaterialActor(forms[i], scope.material, reviewCase.review.reviewer);
        }
        grossReviews[caseId] =
            SparkV15Materials.GrossReview(scopeId, previousTotal, revisedTotal, 0, 0, reviewCase.review.decidedAt);
        prior.push(caseId);
    }

    function _matchesGrossConcern(
        bytes32 scopeId,
        uint256 chargeEvidenceId,
        SparkV15ReviewContext.ConcernRecord memory concern
    ) private view returns (bool) {
        if (concern.intake.evidenceId == 0) return true;
        bool omission = concern.intake.subject == SparkV15ReviewContext.ConcernSubject.MaterialOmission;
        if (concern.intake.subjectRef == scopeId) {
            return omission || concern.intake.subject == SparkV15ReviewContext.ConcernSubject.RevenueShare;
        }
        if (!omission) return false;
        address provisions = SparkV15Funds(address(BOOKING.FUNDS())).materialProvisions();
        return provisions != address(0) && ISparkV15OmissionGrossScope(provisions).matchesOmissionGrossScope(
            concern.termsId, concern.intake.subjectRef, scopeId, concern.obligationId,
            concern.intake.evidenceId, chargeEvidenceId
        );
    }

    function getGrossAttribution(bytes32 caseId, bytes32 formId)
        external
        view
        returns (SparkV15Materials.GrossAttribution memory)
    {
        return grossAttributions[caseId][formId];
    }

    function recordGrossAttribution(
        address actor,
        SparkV15Materials.GrossAttributionInput calldata input,
        uint256 evidenceId
    ) external onlyMaterials returns (bytes32 scopeId) {
        SparkV15Materials.GrossReview storage review = grossReviews[input.caseId];
        scopeId = review.scopeId;
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(scope.lessonId);
        _requireCoordinator(lesson, MATERIALS.ACTION_VERIFY_ATTRIBUTION(), actor);
        if (
            _adoptedGrossAt(input.caseId, uint64(block.timestamp)) == 0
                || MATERIALS.originalFor(input.formId, scope.material) != _originalId(scopeId, scope)
                || grossAttributions[input.caseId][input.formId].evidenceId != 0
                || input.availableAt < review.reviewedAt || input.sourceRef == bytes32(0)
        ) revert SparkV15Materials.InvalidGrossReview();
        MATERIALS.requireDisinterestedMaterialActor(input.formId, scope.material, actor);
        if (
            _requireEvidence(
                    lesson,
                    MATERIALS.ACTION_VERIFY_ATTRIBUTION(),
                    keccak256(abi.encode(input)),
                    input.availableAt,
                    evidenceId,
                    actor
                ) != input.availableAt
        ) revert SparkV15Materials.InvalidMaterialsEvidence();
        (uint128 beforeGross, bool pending) = _scopeGross(scopeId, input.formId, input.availableAt, input.caseId, false);
        uint256 newTotal = review.attributedTotal + input.revised;
        uint256 attributedSeats = review.attributedSeats + 1;
        if (
            beforeGross != input.previous || pending || newTotal > review.revisedTotal
                || (attributedSeats == MATERIALS.getScopeForms(scopeId).length && newTotal != review.revisedTotal)
        ) revert SparkV15Materials.InvalidGrossReview();
        review.attributedTotal = newTotal;
        review.attributedSeats = attributedSeats;
        grossAttributions[input.caseId][input.formId] =
            SparkV15Materials.GrossAttribution(input, actor, evidenceId, uint64(block.timestamp));
    }

    function verifyReviewFollowUp(address actor, SparkV15Materials.ReviewFollowUp calldata input, uint256 evidenceId)
        external
        onlyMaterials
    {
        bytes32 scopeId = grossReviews[input.caseId].scopeId;
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(scope.lessonId);
        bytes32 action = MATERIALS.ACTION_VERIFY_REVIEW_FOLLOW_UP();
        _requireCoordinator(lesson, action, actor);
        SparkV15Materials.GrossAttribution storage attribution = grossAttributions[input.caseId][input.formId];
        uint64 adoptedAt = _adoptedGrossAt(input.caseId, input.checkedAt);
        if (
            input.sourceRef == bytes32(0) || adoptedAt == 0 || attribution.evidenceId == 0
                || attribution.input.previous <= attribution.input.revised
                || reviewFollowUpAvailableAt[input.caseId][input.formId] != 0
        ) {
            revert SparkV15Materials.InvalidGrossReview();
        }
        MATERIALS.requireDisinterestedMaterialActor(input.formId, scope.material, actor);
        SparkV15Materials.UseFinding[] storage findings = useFindings[input.formId];
        bool verified;
        for (uint256 i; i < findings.length; ++i) {
            SparkV15Materials.UseFinding storage finding = findings[i];
            if (
                finding.evidenceId == input.useEvidenceId && finding.check.checkedAt >= adoptedAt
                    && finding.availableAt <= input.checkedAt
            ) {
                verified = true;
                break;
            }
        }
        if (!verified) revert SparkV15Materials.InvalidGrossReview();
        reviewFollowUpAvailableAt[input.caseId][input.formId] =
            _requireEvidence(lesson, action, keccak256(abi.encode(input)), input.checkedAt, evidenceId, actor);
    }

    function _scopeGross(bytes32 scopeId, bytes32 formId, uint64 atTime, bytes32 beforeCase, bool forShortfall)
        private
        view
        returns (uint128 amount, bool pending)
    {
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        if (
            scope.identifiedAt == 0 || scope.identifiedAt > atTime
                || MATERIALS.originalFor(formId, scope.material) != _originalId(scopeId, scope)
        ) {
            return (0, false);
        }
        amount = MATERIALS.getHistoricalCharge(scopeId, formId).amount;
        bytes32[] storage reviews = reviewsByScope[scopeId];
        for (uint256 i; i < reviews.length; ++i) {
            bytes32 caseId = reviews[i];
            if (caseId == beforeCase) break;
            if (_adoptedGrossAt(caseId, atTime) == 0) continue;
            SparkV15Materials.GrossAttribution storage attribution = grossAttributions[caseId][formId];
            if (
                attribution.evidenceId != 0 && attribution.input.availableAt <= atTime
                    && attribution.input.previous == amount
            ) {
                amount = attribution.input.revised;
                if (forShortfall && amount < attribution.input.previous) {
                    uint64 followUp = reviewFollowUpAvailableAt[caseId][formId];
                    if (followUp == 0 || followUp > atTime) return (amount, true);
                }
            } else if (grossReviews[caseId].previousTotal != grossReviews[caseId].revisedTotal) {
                return (amount, true);
            }
        }
    }

    function _scopeTotalAt(bytes32 scopeId, uint64 atTime) private view returns (uint256 total) {
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        if (scope.identifiedAt == 0 || scope.identifiedAt > atTime) return 0;
        total = scope.total;
        bytes32[] storage reviews = reviewsByScope[scopeId];
        for (uint256 i; i < reviews.length; ++i) {
            bytes32 caseId = reviews[i];
            // The review and adoption evidence bind the whole scope even when seat attribution is pending.
            if (_adoptedGrossAt(caseId, atTime) != 0) total = grossReviews[caseId].revisedTotal;
        }
    }

    function _adoptedGrossAt(bytes32 caseId, uint64 upperTime) private view returns (uint64) {
        SparkV15ReviewCases.AdoptedDisposition memory adoption = REVIEW_CASES.getAdoptedDisposition(caseId);
        return adoption.adoptedAt <= upperTime ? adoption.adoptedAt : 0;
    }
}
