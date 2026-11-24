// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {SparkV15Booking} from "./SparkV15Booking.sol";
import {SparkV15Funds} from "./SparkV15Funds.sol";
import {SparkV15MaterialProvisions, SparkV15ObservedMaterialReceipts} from "./SparkV15MaterialProvisions.sol";
import {SparkV15Materials} from "./SparkV15Materials.sol";
import {SparkV15Payments} from "./SparkV15Payments.sol";
import {SparkV15Returns} from "./SparkV15Returns.sol";

/// @notice Consented material share transfers under a lesson's adopted materials agreement.
contract SparkV15MaterialRights {
    enum TransferKind {
        Voluntary,
        DaoBuyback
    }

    /// @dev Fraction of the transferor's affected amount assigned to the transferee. Zero retains it.
    struct Assignment {
        uint32 numerator;
        uint32 denominator;
    }

    struct TransferTerms {
        bytes32 lessonId;
        bytes32 material;
        bytes32 publishedTermsRef;
        bytes32 sourceRef;
        address transferor;
        address transferee;
        uint32 units;
        uint64 effectiveAt;
        uint64 acceptThrough;
        TransferKind kind;
        Assignment unsettledEarlierUse;
        Assignment settledUncollected;
        Assignment laterShortfall;
    }

    struct Transfer {
        TransferTerms terms;
        uint64 recordedAt;
        address verifiedBy;
        bytes32 authorityId;
        uint256 evidenceId;
    }

    struct TransferAcceptance {
        uint64 acceptedAt;
        uint64 order;
    }

    struct Holding {
        address holder;
        uint256 units;
        uint64 lastTransferAt;
        uint256 portion;
        uint256 blocked;
        uint256 timingPending;
        bool pending;
    }

    struct AssignmentAmounts {
        uint256 assigned;
        uint256 timingPending;
        bool unallocated;
    }

    struct CollectionAmounts {
        uint256 collected;
        uint256 timingPending;
        bool unallocated;
    }

    struct ChargeRead {
        bytes32 scopeId;
        bytes32 formId;
        uint64 postingAt;
        uint64 knownAt;
        uint64 firstUse;
        uint64 establishedAt;
        bool shortfall;
        bool checkPredecessorHolds;
        uint256 casePackageId;
    }

    struct SeatCollection {
        bytes32 formId;
        uint128 amount;
    }

    struct CollectionInput {
        bytes32 transferId;
        bytes32 scopeId;
        uint256 receiptId;
        address holder;
        bytes32 sourceRef;
        SeatCollection[] seats;
    }

    struct CollectionRecord {
        uint64 verifiedAt;
        address verifiedBy;
        bytes32 authorityId;
        uint256 evidenceId;
        bytes32 sourceRef;
    }

    struct CollectionBasis {
        bytes32 key;
        bytes32 lessonId;
        bytes32 material;
        bytes32 originalId;
        uint64 paidAt;
        uint256 retained;
        uint128 timingPending;
    }

    error InvalidTransfer();
    error InvalidTransferEvidence();
    error MaterialAllocationPending();
    error UnavailableCaseRightsEvidence(uint256 evidenceId);

    event MaterialTransferAccepted(bytes32 indexed transferId, address indexed holder, uint64 acceptedAt);
    event MaterialTransferVerified(
        bytes32 indexed transferId,
        bytes32 indexed lessonId,
        bytes32 indexed material,
        uint64 effectiveAt,
        uint64 recordedAt,
        uint256 evidenceId
    );
    event MaterialCollectionVerified(
        bytes32 indexed transferId, bytes32 indexed scopeId, uint256 indexed receiptId, uint256 evidenceId
    );

    bytes32 public constant ACTION_VERIFY_TRANSFER = keccak256("spark.action.verify-material-transfer.v1.5");
    bytes32 public constant ACTION_VERIFY_TRANSFER_COLLECTION =
        keccak256("spark.action.verify-transfer-collection.v1.5");

    SparkV15Materials public immutable MATERIALS;
    SparkV15Booking public immutable BOOKING;
    SparkV15Funds public immutable FUNDS;
    AVAEvidenceRegistry public immutable EVIDENCE_REGISTRY;
    SparkV15MaterialCollectionReader public immutable COLLECTION_READER;
    address public immutable SPARK_DAO;

    mapping(bytes32 => mapping(address => TransferAcceptance)) private acceptances;
    mapping(bytes32 => Transfer) private transfers;
    mapping(bytes32 => mapping(bytes32 => bytes32[])) private transferHistory;
    mapping(bytes32 => mapping(bytes32 => bytes32)) private transferBySource;
    mapping(bytes32 => CollectionRecord) private collectionRecords;
    mapping(bytes32 => mapping(bytes32 => uint128)) private collectionAmounts;
    uint64 public nextTransferAcceptanceOrder = 1;

    constructor(SparkV15Materials materials, address sparkDao) {
        if (address(materials).code.length == 0 || sparkDao == address(0)) revert InvalidTransfer();
        MATERIALS = materials;
        BOOKING = materials.BOOKING();
        FUNDS = SparkV15Funds(address(BOOKING.FUNDS()));
        EVIDENCE_REGISTRY = BOOKING.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        COLLECTION_READER = new SparkV15MaterialCollectionReader(materials, FUNDS);
        SPARK_DAO = sparkDao;
    }

    function transferCommitment(TransferTerms calldata terms) public view returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.material-transfer"), block.chainid, address(this), terms));
    }

    function transferEvidenceCommitment(bytes32 transferId, address verifier) public pure returns (bytes32) {
        return keccak256(abi.encode(keccak256("spark.v1.5.material-transfer.evidence"), transferId, verifier));
    }

    /// @notice Accept the exact transfer and all three income dispositions as one wallet action.
    function acceptTransfer(bytes32 transferId) external {
        if (transferId == bytes32(0) || acceptedAt(transferId, msg.sender) != 0) revert InvalidTransfer();
        acceptances[transferId][msg.sender] = TransferAcceptance(uint64(block.timestamp), nextTransferAcceptanceOrder++);
        emit MaterialTransferAccepted(transferId, msg.sender, uint64(block.timestamp));
    }

    function acceptedAt(bytes32 transferId, address holder) public view returns (uint64) {
        return acceptances[transferId][holder].acceptedAt;
    }

    /// @notice Verify the signed dispositions and the published terms which permit them.
    function verifyTransfer(TransferTerms calldata terms, uint256 evidenceId, bytes32 authorityId)
        external
        returns (bytes32 transferId)
    {
        _requireVerifier(ACTION_VERIFY_TRANSFER, authorityId);
        transferId = transferCommitment(terms);
        SparkV15Materials.AgreedTerms memory agreement = MATERIALS.getAgreedTerms(terms.lessonId);
        SparkV15Materials.MaterialTerms memory item = MATERIALS.getMaterialTerms(terms.lessonId, terms.material);
        if (
            item.material == bytes32(0) || agreement.sharesAndAdjustmentsRef != terms.publishedTermsRef
                || terms.sourceRef == bytes32(0) || transferBySource[terms.material][terms.sourceRef] != bytes32(0)
                || terms.transferor == address(0) || terms.transferee == address(0)
                || terms.transferor == terms.transferee || msg.sender == terms.transferor
                || msg.sender == terms.transferee || terms.units == 0
                || (terms.kind == TransferKind.DaoBuyback && terms.transferee != SPARK_DAO)
                || terms.effectiveAt <= agreement.adoptedAt || terms.acceptThrough > terms.effectiveAt
                || !_consented(transferId, terms.transferor, terms.acceptThrough)
                || !_consented(transferId, terms.transferee, terms.acceptThrough)
                || !_validAssignment(terms.unsettledEarlierUse) || !_validAssignment(terms.settledUncollected)
                || !_validAssignment(terms.laterShortfall)
        ) revert InvalidTransfer();
        COLLECTION_READER.requireTransferEvidence(
            terms.lessonId, evidenceId, transferEvidenceCommitment(transferId, msg.sender)
        );

        uint64 recordedAt = uint64(block.timestamp);
        transfers[transferId] = Transfer(terms, recordedAt, msg.sender, authorityId, evidenceId);
        transferBySource[terms.material][terms.sourceRef] = transferId;
        bytes32[] storage history = transferHistory[terms.lessonId][terms.material];
        history.push(transferId);
        uint256 position = history.length - 1;
        while (position != 0 && transfers[history[position - 1]].terms.effectiveAt > terms.effectiveAt) {
            history[position] = history[position - 1];
            --position;
        }
        history[position] = transferId;
        _holdingsAt(item.holders, history, type(uint64).max, recordedAt);
        emit MaterialTransferVerified(
            transferId, terms.lessonId, terms.material, terms.effectiveAt, recordedAt, evidenceId
        );
    }

    function getTransfer(bytes32 transferId) external view returns (Transfer memory) {
        return transfers[transferId];
    }

    function getTransfers(bytes32 lessonId, bytes32 material) external view returns (bytes32[] memory) {
        return transferHistory[lessonId][material];
    }

    function collectionEvidenceCommitment(CollectionInput calldata input, address verifier)
        public
        view
        returns (bytes32)
    {
        return keccak256(abi.encode(ACTION_VERIFY_TRANSFER_COLLECTION, block.chainid, address(this), input, verifier));
    }

    /// @notice Attribute an earlier receipt's retained amount to its actual seats at the transfer's effective time.
    function verifyTransferCollection(CollectionInput calldata input, uint256 evidenceId, bytes32 authorityId)
        external
    {
        _requireVerifier(ACTION_VERIFY_TRANSFER_COLLECTION, authorityId);
        CollectionBasis memory basis = _collectionBasis(input);
        COLLECTION_READER.requireTransferEvidence(
            basis.lessonId, evidenceId, collectionEvidenceCommitment(input, msg.sender)
        );
        _recordCollectedSeats(input, basis);
        collectionRecords[basis.key] =
            CollectionRecord(uint64(block.timestamp), msg.sender, authorityId, evidenceId, input.sourceRef);
        emit MaterialCollectionVerified(input.transferId, input.scopeId, input.receiptId, evidenceId);
    }

    function _collectionBasis(CollectionInput calldata input) private view returns (CollectionBasis memory basis) {
        bytes32 key = _collectionKey(input.transferId, input.scopeId, input.receiptId);
        if (input.sourceRef == bytes32(0) || collectionRecords[key].verifiedAt != 0) revert InvalidTransfer();
        basis = COLLECTION_READER.collectionBasis(input.transferId, input.scopeId, input.receiptId, input.holder, msg.sender);
        basis.key = key;
    }

    function _recordCollectedSeats(CollectionInput calldata input, CollectionBasis memory basis) private {
        uint256 allocated;
        for (uint256 i; i < input.seats.length; ++i) {
            SeatCollection calldata row = input.seats[i];
            (uint128 gross, bool pending) = MATERIALS.activeScopeGrossAt(input.scopeId, row.formId, basis.paidAt);
            if (
                MATERIALS.originalFor(row.formId, basis.material) != basis.originalId || pending || row.amount == 0
                    || row.amount > gross || collectionAmounts[basis.key][row.formId] != 0
            ) revert InvalidTransfer();
            collectionAmounts[basis.key][row.formId] = row.amount;
            allocated += row.amount;
        }
        uint256 possiblyRetained = basis.retained + basis.timingPending;
        if (possiblyRetained == 0 || allocated < basis.retained || allocated > possiblyRetained) {
            revert InvalidTransfer();
        }
        if (allocated != basis.retained && allocated != possiblyRetained) {
            COLLECTION_READER.requireReturnPrefixAtCutoff(
                input.receiptId, transfers[input.transferId].terms.effectiveAt, uint128(possiblyRetained - allocated)
            );
        }
    }

    function getTransferCollection(bytes32 transferId, bytes32 scopeId, uint256 receiptId, bytes32 formId)
        external
        view
        returns (CollectionRecord memory record, uint128 amount)
    {
        bytes32 key = _collectionKey(transferId, scopeId, receiptId);
        return (collectionRecords[key], collectionAmounts[key][formId]);
    }

    /// @notice Reconcile prior native payment principals at the current effective time before providing a new part.
    function syncMaterialScope(bytes32 scopeId) external {
        uint64 nowAt = uint64(block.timestamp);
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        if (_latestTransfer(scope, nowAt, nowAt) == bytes32(0)) return;
        SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(FUNDS.materialProvisions());
        if (address(provisions) == address(0) || address(provisions.rights()) != address(this)) return;
        uint64 firstUse = _firstUse(scope.lessonId, scope.material, nowAt, nowAt, 0);
        if (firstUse == 0) return;

        bytes32[] memory obligations = provisions.getScopeObligations(scopeId);
        bytes32[] storage history = transferHistory[scope.lessonId][scope.material];
        for (uint256 i; i < obligations.length; ++i) {
            address holder = provisions.getEntitlement(obligations[i]).input.holder;
            for (uint256 j = history.length; j != 0; --j) {
                bytes32 transferId = history[j - 1];
                TransferTerms storage deal = transfers[transferId].terms;
                if (
                    deal.effectiveAt <= nowAt && deal.transferor == holder
                        && (deal.effectiveAt <= firstUse || _disposition(scope, deal).numerator != 0)
                ) {
                    try provisions.rebaseMaterialPart(obligations[i], transferId) {}
                    catch (bytes memory reason) {
                        if (bytes4(reason) != MaterialAllocationPending.selector) {
                            assembly ("memory-safe") {
                                revert(add(reason, 0x20), mload(reason))
                            }
                        }
                    }
                    break;
                }
            }
        }
    }

    /// @notice An operative transfer governs this settlement under the same lesson materials agreement.
    function hasTransfer(bytes32 scopeId, uint64 atTime) external view returns (bool) {
        _requireQueryTime(atTime, atTime);
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        return _latestTransfer(scope, atTime, atTime) != bytes32(0);
    }

    /// @notice A known transfer can change which actual receipts discharge this gross charge at posting.
    function hasApplicableTransfer(bytes32 scopeId, uint64 postingAt, uint64 knownAt) external view returns (bool) {
        return scopeTransferBasisAt(scopeId, postingAt, knownAt) != bytes32(0);
    }

    function scopeTransferBasisAt(bytes32 scopeId, uint64 postingAt, uint64 knownAt)
        public
        view
        returns (bytes32 basis)
    {
        return _scopeTransferBasisAt(scopeId, postingAt, knownAt, 0);
    }

    function nativeReceiptTransferBasis(bytes32 scopeId, uint256 receiptId) external view returns (bytes32) {
        (uint64 postingAt, uint64 nextOrder) = COLLECTION_READER.nativeReceiptTiming(receiptId);
        return _scopeTransferBasisAt(scopeId, postingAt, uint64(block.timestamp), nextOrder);
    }

    function _scopeTransferBasisAt(bytes32 scopeId, uint64 postingAt, uint64 knownAt, uint64 nextOrder)
        private
        view
        returns (bytes32 basis)
    {
        _requireQueryTime(postingAt, knownAt);
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        if (_latestTransfer(scope, postingAt, knownAt) == bytes32(0)) return bytes32(0);
        uint64 firstUse = _firstUse(scope.lessonId, scope.material, postingAt, knownAt, 0);
        if (firstUse == 0) return bytes32(0);
        uint64 scopeFirstUse;
        bytes32[] memory forms = MATERIALS.getScopeForms(scopeId);
        for (uint256 i; i < forms.length; ++i) {
            (uint64 useAt,) = _firstSeatUse(forms[i], scope.material, postingAt, knownAt);
            if (useAt != 0 && (scopeFirstUse == 0 || useAt < scopeFirstUse)) scopeFirstUse = useAt;
        }
        if (scopeFirstUse == 0) return bytes32(0);
        bytes32[] storage history = transferHistory[scope.lessonId][scope.material];
        for (uint256 i; i < history.length; ++i) {
            bytes32 id = history[i];
            Transfer storage row = transfers[id];
            uint64 effectiveAt = row.terms.effectiveAt;
            if (effectiveAt > postingAt) break;
            if (
                row.recordedAt <= knownAt && (effectiveAt <= firstUse || scopeFirstUse < effectiveAt)
                    && (effectiveAt != postingAt || !_receiptVerifiedBeforeAssent(id, row.terms, nextOrder))
            ) {
                basis = keccak256(abi.encode(basis, id));
            }
        }
    }

    /// @notice Gross payable portion under the verified use and dispositions known for the requested posting time.
    function holderPortion(bytes32 scopeId, address holder, uint64 postingAt, uint64 knownAt)
        external
        view
        returns (uint256)
    {
        return this.readHolderPortion(scopeId, holder, postingAt, knownAt, false, 0);
    }

    /// @notice Current gross portion available after preserving holds on assigned predecessor amounts.
    function holderPortionWithoutHeldPredecessors(bytes32 scopeId, address holder, uint64 atTime)
        external
        view
        returns (uint256)
    {
        return this.readHolderPortion(scopeId, holder, atTime, atTime, true, 0);
    }

    /// @notice Read a gross portion, rechecking the operative evidence for a current case read.
    /// @dev All three callers use the same implementation to fit within the EVM runtime size limit.
    function readHolderPortion(
        bytes32 scopeId,
        address holder,
        uint64 postingAt,
        uint64 knownAt,
        bool checkPredecessorHolds,
        uint256 casePackageId
    ) external view returns (uint256 portion) {
        uint256 timingPending;
        (portion, timingPending) =
            this.readHolderAmounts(scopeId, holder, postingAt, knownAt, checkPredecessorHolds, casePackageId);
        if (casePackageId != 0) return portion + timingPending;
        if (portion == 0 && timingPending != 0) revert MaterialAllocationPending();
    }

    /// @notice Reduce previous backing only for an assignment already established in every supported order.
    function holderPortionForRebase(bytes32 scopeId, address holder, uint64 atTime) external view returns (uint256) {
        (uint256 portion, uint256 timingPending) = this.readHolderAmounts(scopeId, holder, atTime, atTime, false, 0);
        return portion + timingPending;
    }

    /// @notice Read the determined portion and the exact additional amount awaiting a receipt/transfer order.
    function readHolderAmounts(
        bytes32 scopeId,
        address holder,
        uint64 postingAt,
        uint64 knownAt,
        bool checkPredecessorHolds,
        uint256 casePackageId
    ) external view returns (uint256 portion, uint256 timingPending) {
        _requireQueryTime(postingAt, knownAt);
        if ((checkPredecessorHolds || casePackageId != 0) && postingAt != block.timestamp) revert InvalidTransfer();
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        if (scope.recordedAt == 0 || scope.recordedAt > knownAt || scope.identifiedAt > postingAt) {
            revert InvalidTransfer();
        }
        SparkV15Materials.HolderShare[] memory initial =
        MATERIALS.getMaterialTerms(scope.lessonId, scope.material).holders;
        bytes32[] storage history = transferHistory[scope.lessonId][scope.material];
        bytes32[] memory forms = MATERIALS.getScopeForms(scopeId);
        uint64 firstUse;
        if (_latestTransfer(scope, postingAt, knownAt) != bytes32(0)) {
            if (casePackageId != 0) _requireCaseTransfers(history, postingAt, casePackageId);
            firstUse = _firstUse(scope.lessonId, scope.material, postingAt, knownAt, casePackageId);
        }
        ChargeRead memory reading = ChargeRead(
            scopeId,
            bytes32(0),
            postingAt,
            knownAt,
            firstUse,
            scope.identifiedAt,
            scope.originalScopeId != bytes32(0),
            checkPredecessorHolds,
            casePackageId
        );
        for (uint256 i; i < forms.length; ++i) {
            (uint128 gross, bool pending) = MATERIALS.activeScopeGrossAt(scopeId, forms[i], postingAt);
            if (pending) revert MaterialAllocationPending();
            if (gross == 0) continue;
            reading.formId = forms[i];
            uint64 seatFirstUse;
            if (firstUse != 0) (seatFirstUse,) = _firstSeatUse(forms[i], scope.material, postingAt, knownAt);
            (uint256 seatPortion, uint256 seatPending) = _seatPortion(initial, history, reading, seatFirstUse, holder, gross);
            portion += seatPortion;
            timingPending += seatPending;
        }
    }

    function _requireCaseTransfers(bytes32[] storage history, uint64 atTime, uint256 packageId) private view {
        for (uint256 i; i < history.length; ++i) {
            Transfer storage row = transfers[history[i]];
            if (row.terms.effectiveAt > atTime) break;
            _requireCaseRightsEvidence(row.evidenceId, packageId);
        }
    }

    function _requireCaseRightsEvidence(uint256 evidenceId, uint256 packageId) private view {
        if (!EVIDENCE_REGISTRY.isEvidenceAvailableForPackage(evidenceId, packageId)) {
            revert UnavailableCaseRightsEvidence(evidenceId);
        }
    }

    /// @notice Share units in force at `effectiveBy`, according to documents recorded by `knownAt`.
    function unitsAt(bytes32 lessonId, bytes32 material, address holder, uint64 effectiveBy, uint64 knownAt)
        public
        view
        returns (uint256)
    {
        _requireQueryTime(effectiveBy, knownAt);
        if (MATERIALS.getAgreedTerms(lessonId).adoptedAt > effectiveBy) return 0;
        SparkV15Materials.HolderShare[] memory initial = MATERIALS.getMaterialTerms(lessonId, material).holders;
        Holding[] memory holdings = _holdingsAt(initial, transferHistory[lessonId][material], effectiveBy, knownAt);
        for (uint256 i; i < holdings.length; ++i) {
            if (holdings[i].holder == holder) return holdings[i].units;
        }
        return 0;
    }

    /// @notice Read the actor's nominal interest for a current material check or review.
    function isEconomicHolder(bytes32 lessonId, bytes32 material, address actor) external view returns (bool) {
        uint64 nowAt = uint64(block.timestamp);
        return unitsAt(lessonId, material, actor, nowAt, nowAt) != 0;
    }

    function _holdingsAt(
        SparkV15Materials.HolderShare[] memory initial,
        bytes32[] storage history,
        uint64 effectiveBy,
        uint64 knownAt
    ) private view returns (Holding[] memory holdings) {
        holdings = _initialHoldings(initial, history.length);
        for (uint256 i; i < history.length; ++i) {
            Transfer storage row = transfers[history[i]];
            if (row.terms.effectiveAt > effectiveBy) break;
            if (row.recordedAt > knownAt) continue;
            _moveUnits(holdings, row.terms);
        }
    }

    function _initialHoldings(SparkV15Materials.HolderShare[] memory initial, uint256 transferCount)
        private
        pure
        returns (Holding[] memory holdings)
    {
        holdings = new Holding[](initial.length + transferCount * 2);
        for (uint256 i; i < initial.length; ++i) {
            holdings[i].holder = initial[i].holder;
            holdings[i].units = initial[i].units;
        }
    }

    function _seatPortion(
        SparkV15Materials.HolderShare[] memory initial,
        bytes32[] storage history,
        ChargeRead memory reading,
        uint64 seatFirstUse,
        address holder,
        uint128 gross
    ) private view returns (uint256 portion, uint256 timingPending) {
        Holding[] memory holdings = _initialHoldings(initial, history.length);
        uint256 accruedTransfers = _applyTransfersThroughFirstUse(holdings, history, reading);
        _allocateGross(holdings, gross);
        if (reading.firstUse != 0) {
            _applyAccruedTransfers(holdings, history, accruedTransfers, reading, seatFirstUse);
        }
        for (uint256 i; i < holdings.length; ++i) {
            if (holdings[i].holder == holder) {
                if (holdings[i].pending) revert MaterialAllocationPending();
                Holding memory item = holdings[i];
                portion = item.portion > item.blocked ? item.portion - item.blocked : 0;
                return (portion, item.timingPending);
            }
        }
        return (0, 0);
    }

    function _applyTransfersThroughFirstUse(
        Holding[] memory holdings,
        bytes32[] storage history,
        ChargeRead memory reading
    ) private view returns (uint256 i) {
        for (; i < history.length; ++i) {
            Transfer storage row = transfers[history[i]];
            TransferTerms storage deal = row.terms;
            if (deal.effectiveAt > reading.firstUse) break;
            if (row.recordedAt > reading.knownAt) continue;
            (uint256 from, uint256 to) = _moveUnits(holdings, deal);
            if (reading.checkPredecessorHolds) _moveBlocked(holdings, from, to, deal.units, reading.scopeId);
        }
    }

    function _allocateGross(Holding[] memory holdings, uint128 gross) private pure {
        uint256 totalUnits;
        for (uint256 i; i < holdings.length; ++i) {
            totalUnits += holdings[i].units;
        }
        for (uint256 i; i < holdings.length; ++i) {
            Holding memory item = holdings[i];
            (item.portion, item.pending) = _allocate(gross, item.units, totalUnits);
            // Preserve the held fraction until the smallest whole additional unit can be paid.
            if (item.blocked != 0) item.blocked = (uint256(gross) * item.blocked + totalUnits - 1) / totalUnits;
            holdings[i] = item;
        }
    }

    function _applyAccruedTransfers(
        Holding[] memory holdings,
        bytes32[] storage history,
        uint256 start,
        ChargeRead memory reading,
        uint64 seatFirstUse
    ) private view {
        for (uint256 i = start; i < history.length; ++i) {
            bytes32 transferId = history[i];
            Transfer storage row = transfers[transferId];
            TransferTerms storage deal = row.terms;
            if (deal.effectiveAt > reading.postingAt) break;
            if (row.recordedAt > reading.knownAt) continue;
            (uint256 from, uint256 to) = _moveUnits(holdings, deal);
            AssignmentAmounts memory amounts = _assignedPortion(reading, holdings[from], deal, transferId, seatFirstUse);
            if (amounts.unallocated) {
                holdings[from].pending = true;
                holdings[to].pending = true;
            } else {
                if (reading.checkPredecessorHolds && amounts.assigned != 0) {
                    _moveBlocked(holdings, from, to, amounts.assigned, reading.scopeId);
                }
                holdings[from].portion -= amounts.assigned + amounts.timingPending;
                holdings[to].portion += amounts.assigned;
                holdings[from].timingPending += amounts.timingPending;
                holdings[to].timingPending += amounts.timingPending;
            }
        }
    }

    function _moveBlocked(Holding[] memory holdings, uint256 from, uint256 to, uint256 assigned, bytes32 scopeId)
        private
        view
    {
        uint256 inherited = assigned < holdings[from].blocked ? assigned : holdings[from].blocked;
        holdings[from].blocked -= inherited;
        holdings[to].blocked += _partHeld(scopeId, holdings[from].holder) ? assigned : inherited;
    }

    function _partHeld(bytes32 scopeId, address holder) private view returns (bool) {
        SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(FUNDS.materialProvisions());
        if (address(provisions) == address(0)) return false;
        bytes32 obligationId = provisions.entitlementFor(scopeId, holder);
        return obligationId != bytes32(0) && SparkV15Payments(FUNDS.PAYMENTS()).HOLDS().getStatus(obligationId).active;
    }

    function _assignedPortion(
        ChargeRead memory reading,
        Holding memory outgoing,
        TransferTerms storage deal,
        bytes32 transferId,
        uint64 seatFirstUse
    ) private view returns (AssignmentAmounts memory result) {
        if (seatFirstUse == 0 || seatFirstUse >= deal.effectiveAt) return result;
        bool established = reading.establishedAt < deal.effectiveAt;
        Assignment storage disposition =
            reading.shortfall ? deal.laterShortfall : established ? deal.settledUncollected : deal.unsettledEarlierUse;
        if (disposition.numerator == 0) return result;
        if (outgoing.pending || outgoing.timingPending != 0) {
            result.unallocated = true;
            return result;
        }

        CollectionAmounts memory received;
        if (established) received = _collectionsBefore(reading, deal, transferId);
        uint256 possiblyCollected = received.collected + received.timingPending;
        if (received.unallocated || possiblyCollected > outgoing.portion) {
            result.unallocated = true;
            return result;
        }
        (result.assigned, result.unallocated) =
            _allocate(outgoing.portion - possiblyCollected, disposition.numerator, disposition.denominator);
        if (!result.unallocated && received.timingPending != 0) {
            (result.timingPending, result.unallocated) =
                _allocate(received.timingPending, disposition.numerator, disposition.denominator);
        }
    }

    function _collectionsBefore(ChargeRead memory reading, TransferTerms storage deal, bytes32 transferId)
        private
        view
        returns (CollectionAmounts memory result)
    {
        SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(FUNDS.materialProvisions());
        if (address(provisions) == address(0)) return result;
        bytes32 obligationId = provisions.entitlementFor(reading.scopeId, deal.transferor);
        if (obligationId == bytes32(0)) return result;
        SparkV15Payments payments = SparkV15Payments(FUNDS.PAYMENTS());
        uint256[] memory receiptIds = payments.RETURNS().getPaymentReceiptIds(obligationId);
        uint256 nativeRetained;
        for (uint256 i; i < receiptIds.length; ++i) {
            uint256 receiptId = receiptIds[i];
            SparkV15MaterialCollectionReader.NativeCollection memory cash = COLLECTION_READER.nativeReceiptBefore(
                transferId, receiptId, deal.effectiveAt, deal.transferor, reading.knownAt
            );
            nativeRetained += cash.currentlyRetained;
            if (cash.retainedBefore == 0 && cash.timingPending == 0) continue;

            bytes32 key = _collectionKey(transferId, reading.scopeId, receiptId);
            uint64 verifiedAt = collectionRecords[key].verifiedAt;
            if (verifiedAt != 0 && verifiedAt <= reading.knownAt) {
                if (reading.casePackageId != 0) {
                    _requireCaseRightsEvidence(collectionRecords[key].evidenceId, reading.casePackageId);
                }
                result.collected += collectionAmounts[key][reading.formId];
            } else {
                bytes32 single = COLLECTION_READER.onlyPaidSeat(reading.scopeId, cash.paidAt);
                if (single == bytes32(0)) {
                    result.unallocated = true;
                    return result;
                }
                if (single == reading.formId) {
                    result.collected += cash.retainedBefore;
                    result.timingPending += cash.timingPending;
                }
            }
        }
        (uint256 observed, uint256 observedRetained, bool waiting) = COLLECTION_READER.observedBefore(
            reading.scopeId, reading.formId, obligationId, deal.effectiveAt, reading.knownAt
        );
        result.collected += observed;
        result.unallocated =
            waiting || payments.retainedByBeneficiary(obligationId, deal.transferor) != nativeRetained + observedRetained;
    }

    function receiptVerifiedBeforeAssent(bytes32 transferId, uint64 nextOrder) external view returns (bool) {
        return _receiptVerifiedBeforeAssent(transferId, transfers[transferId].terms, nextOrder);
    }

    /// @dev A required assent within the effective second sets a lower bound on the effective order.
    function _receiptVerifiedBeforeAssent(bytes32 transferId, TransferTerms storage deal, uint64 nextOrder)
        private
        view
        returns (bool)
    {
        if (nextOrder == 0) return false;
        TransferAcceptance storage from = acceptances[transferId][deal.transferor];
        TransferAcceptance storage to = acceptances[transferId][deal.transferee];
        return (from.acceptedAt == deal.effectiveAt && from.order >= nextOrder)
            || (to.acceptedAt == deal.effectiveAt && to.order >= nextOrder);
    }

    function _collectionKey(bytes32 transferId, bytes32 scopeId, uint256 receiptId) private pure returns (bytes32) {
        return keccak256(abi.encode(transferId, scopeId, receiptId));
    }

    function _disposition(SparkV15Materials.ChargeScope memory scope, TransferTerms storage deal)
        private
        view
        returns (Assignment storage)
    {
        if (scope.originalScopeId != bytes32(0)) return deal.laterShortfall;
        return scope.identifiedAt < deal.effectiveAt ? deal.settledUncollected : deal.unsettledEarlierUse;
    }

    function _latestTransfer(SparkV15Materials.ChargeScope memory scope, uint64 postingAt, uint64 knownAt)
        private
        view
        returns (bytes32)
    {
        if (scope.recordedAt == 0 || scope.recordedAt > knownAt) return bytes32(0);
        bytes32[] storage history = transferHistory[scope.lessonId][scope.material];
        for (uint256 i = history.length; i != 0; --i) {
            bytes32 transferId = history[i - 1];
            Transfer storage row = transfers[transferId];
            if (row.terms.effectiveAt <= postingAt && row.recordedAt <= knownAt) return transferId;
        }
        return bytes32(0);
    }

    function _firstUse(bytes32 lessonId, bytes32 material, uint64 postingAt, uint64 knownAt, uint256 casePackageId)
        private
        view
        returns (uint64 first)
    {
        bytes32[] memory forms = BOOKING.getPlannedForms(lessonId);
        for (uint256 i; i < forms.length; ++i) {
            (uint64 useAt, uint256 evidenceId) = _firstSeatUse(forms[i], material, postingAt, knownAt);
            if (casePackageId != 0 && evidenceId != 0) _requireCaseRightsEvidence(evidenceId, casePackageId);
            if (useAt != 0 && (first == 0 || useAt < first)) first = useAt;
        }
    }

    function _firstSeatUse(bytes32 formId, bytes32 material, uint64 postingAt, uint64 knownAt)
        private
        view
        returns (uint64 first, uint256 evidenceId)
    {
        SparkV15Materials.UseFinding[] memory findings = MATERIALS.getUseFindings(formId);
        for (uint256 i; i < findings.length; ++i) {
            SparkV15Materials.UseFinding memory finding = findings[i];
            if (
                finding.check.material == material && finding.recordedAt <= knownAt && finding.availableAt <= knownAt
                    && finding.check.usedAt <= postingAt && (first == 0 || finding.check.usedAt < first)
            ) {
                first = finding.check.usedAt;
                evidenceId = finding.evidenceId;
            }
        }
    }

    function _allocate(uint256 base, uint256 numerator, uint256 denominator) private pure returns (uint256, bool) {
        if (denominator == 0) return (0, true);
        uint256 scaled = base * numerator;
        if (scaled % denominator != 0) return (0, true);
        return (scaled / denominator, false);
    }

    function _moveUnits(Holding[] memory holdings, TransferTerms storage terms)
        private
        view
        returns (uint256 from, uint256 to)
    {
        from = _holdingIndex(holdings, terms.transferor);
        if (holdings[from].units < terms.units) revert InvalidTransfer();
        to = _holdingIndex(holdings, terms.transferee);
        if (holdings[from].lastTransferAt == terms.effectiveAt || holdings[to].lastTransferAt == terms.effectiveAt) {
            revert InvalidTransfer();
        }
        holdings[from].units -= terms.units;
        holdings[from].lastTransferAt = terms.effectiveAt;
        holdings[to].holder = terms.transferee;
        holdings[to].units += terms.units;
        holdings[to].lastTransferAt = terms.effectiveAt;
    }

    function _holdingIndex(Holding[] memory holdings, address wallet) private pure returns (uint256 index) {
        while (holdings[index].holder != wallet && holdings[index].holder != address(0)) {
            ++index;
        }
    }

    function _requireQueryTime(uint64 effectiveBy, uint64 knownAt) private view {
        if (effectiveBy > knownAt || knownAt > block.timestamp) revert InvalidTransfer();
    }

    function _consented(bytes32 transferId, address wallet, uint64 cutoff) private view returns (bool) {
        uint64 time = acceptedAt(transferId, wallet);
        return time != 0 && time <= cutoff;
    }

    function _validAssignment(Assignment calldata assignment) private pure returns (bool) {
        return assignment.denominator != 0 && assignment.numerator <= assignment.denominator;
    }

    function _requireVerifier(bytes32 action, bytes32 authorityId) private view {
        BOOKING.REQUEST_ALLOCATION().AUTHORITY_MATRIX()
            .requireAuthorisedSubject(msg.sender, SparkV15.APP_ID, BOOKING.VERIFIER_ROLE(), action, authorityId);
    }
}

/// @notice Identifies the seat and historical amount of cash received under the original material obligation.
contract SparkV15MaterialCollectionReader {
    struct NativeCollection {
        uint64 paidAt;
        uint128 currentlyRetained;
        uint128 retainedBefore;
        uint128 timingPending;
    }

    SparkV15Materials private immutable MATERIALS;
    SparkV15Funds private immutable FUNDS;
    SparkV15Booking private immutable BOOKING;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;
    SparkV15MaterialRights private immutable RIGHTS;

    constructor(SparkV15Materials materials, SparkV15Funds funds) {
        MATERIALS = materials;
        FUNDS = funds;
        BOOKING = materials.BOOKING();
        EVIDENCE_REGISTRY = BOOKING.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
        RIGHTS = SparkV15MaterialRights(msg.sender);
    }

    function requireTransferEvidence(bytes32 lessonId, uint256 evidenceId, bytes32 commitment) external view {
        (bytes32 appId, bytes32 workflowKey,,,) = EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(
            evidenceId, BOOKING.getLesson(lessonId).packageId
        );
        if (
            appId != SparkV15.APP_ID || workflowKey != BOOKING.WORKFLOW()
                || EVIDENCE_REGISTRY.getEvidenceReference(evidenceId).commitment != commitment
        ) {
            revert SparkV15MaterialRights.InvalidTransferEvidence();
        }
    }

    function nativeReceiptTiming(uint256 receiptId) public view returns (uint64 paidAt, uint64 nextOrder) {
        SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(FUNDS.materialProvisions());
        if (address(provisions) != address(0) && address(provisions.rights()) == address(RIGHTS)) {
            return provisions.getMaterialReceiptTiming(receiptId);
        }
        return (SparkV15Payments(FUNDS.PAYMENTS()).getReceipt(receiptId).paidAt, 0);
    }

    function collectionBasis(bytes32 transferId, bytes32 scopeId, uint256 receiptId, address holder, address verifier)
        external
        view
        returns (SparkV15MaterialRights.CollectionBasis memory basis)
    {
        SparkV15MaterialRights.Transfer memory transfer = RIGHTS.getTransfer(transferId);
        SparkV15Materials.ChargeScope memory scope = MATERIALS.getChargeScope(scopeId);
        SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(FUNDS.materialProvisions());
        SparkV15Payments payments = SparkV15Payments(FUNDS.PAYMENTS());
        SparkV15Payments.PaymentReceipt memory receipt = payments.getReceipt(receiptId);
        if (
            transfer.recordedAt == 0 || transfer.terms.effectiveAt > block.timestamp || scope.recordedAt == 0
                || transfer.terms.lessonId != scope.lessonId || transfer.terms.material != scope.material
                || holder != transfer.terms.transferor || verifier == holder || verifier == receipt.recipient
                || receipt.paidAt == 0 || address(provisions) == address(0)
                || !_nativePaymentBefore(transferId, receiptId, receipt.paidAt, transfer.terms.effectiveAt)
                || provisions.entitlementFor(scopeId, holder) != receipt.obligationId
                || payments.RETURNS().receiptBeneficiary(receiptId) != holder
        ) revert SparkV15MaterialRights.InvalidTransfer();
        basis.paidAt = receipt.paidAt;
        basis.lessonId = scope.lessonId;
        basis.material = scope.material;
        basis.originalId = scope.originalScopeId == bytes32(0) ? scopeId : scope.originalScopeId;
        (basis.retained, basis.timingPending) =
            _retainedAtCutoff(payments.RETURNS(), receiptId, receipt.amount, transfer.terms.effectiveAt);
        if (basis.timingPending != 0 && verifier == transfer.terms.transferee) {
            revert SparkV15MaterialRights.InvalidTransfer();
        }
    }

    function _nativePaymentBefore(bytes32 transferId, uint256 receiptId, uint64 paidAt, uint64 effectiveAt)
        private
        view
        returns (bool)
    {
        if (paidAt != effectiveAt) return paidAt < effectiveAt;
        (, uint64 nextOrder) = nativeReceiptTiming(receiptId);
        return RIGHTS.receiptVerifiedBeforeAssent(transferId, nextOrder);
    }

    function nativeReceiptBefore(
        bytes32 transferId,
        uint256 receiptId,
        uint64 cutoff,
        address holder,
        uint64 knownAt
    ) external view returns (NativeCollection memory result) {
        SparkV15Payments payments = SparkV15Payments(FUNDS.PAYMENTS());
        SparkV15Payments.PaymentReceipt memory receipt = payments.getReceipt(receiptId);
        SparkV15Returns returnsLedger = payments.RETURNS();
        if (returnsLedger.receiptBeneficiary(receiptId) != holder) {
            return result;
        }
        result.paidAt = receipt.paidAt;
        result.currentlyRetained = receipt.amount - returnsLedger.returnedForReceipt(receiptId);
        if (_nativePaymentBefore(transferId, receiptId, result.paidAt, cutoff)) {
            (result.retainedBefore, result.timingPending) =
                _retainedAtCutoff(returnsLedger, receiptId, receipt.amount, cutoff);
        } else if (result.paidAt == cutoff) {
            SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(FUNDS.materialProvisions());
            if (address(provisions) != address(0)) {
                uint64 verifiedAt = provisions.getMaterialReceipt(receiptId).verifiedAt;
                if (verifiedAt != 0 && verifiedAt <= knownAt) result.timingPending = receipt.amount;
            }
        }
    }

    function _retainedAtCutoff(SparkV15Returns returnsLedger, uint256 receiptId, uint128 amount, uint64 cutoff)
        private
        view
        returns (uint128 retained, uint128 timingPending)
    {
        (uint128 beforeCutoff, uint128 atCutoff) = returnsLedger.returnedForReceiptAtCutoff(receiptId, cutoff);
        // Until the transfer order is verified, only the return in its effective second can change the allocation.
        return (amount - beforeCutoff - atCutoff, atCutoff);
    }

    function requireReturnPrefixAtCutoff(uint256 receiptId, uint64 cutoff, uint128 amount) external view {
        SparkV15Returns returnsLedger = SparkV15Payments(FUNDS.PAYMENTS()).RETURNS();
        if (!returnsLedger.hasReturnPrefixAtCutoff(receiptId, cutoff, amount)) {
            revert SparkV15MaterialRights.InvalidTransfer();
        }
    }

    function observedBefore(bytes32 scopeId, bytes32 formId, bytes32 obligationId, uint64 cutoff, uint64 knownAt)
        external
        view
        returns (uint256 collected, uint256 current, bool pending)
    {
        SparkV15Payments payments = SparkV15Payments(FUNDS.PAYMENTS());
        if (payments.paymentObservations() == address(0)) return (0, 0, false);
        SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(FUNDS.materialProvisions());
        SparkV15ObservedMaterialReceipts source = provisions.MATERIAL_BACKING().OBSERVED_RECEIPTS();
        bytes32[] memory ids = source.receiptsForObligation(obligationId);
        for (uint256 i; i < ids.length; ++i) {
            (uint128 retained, uint64 occurredAt, uint64 qualifiedAt,) = source.retainedPayment(obligationId, ids[i]);
            if (qualifiedAt == 0) return (0, 0, true);
            current += retained;
            uint128 earlier = source.retainedPaymentBefore(obligationId, ids[i], cutoff, knownAt);
            if (earlier == 0) continue;
            bytes32 single = onlyPaidSeat(scopeId, occurredAt);
            if (single == bytes32(0)) return (0, 0, true);
            if (single == formId) collected += earlier;
        }
    }

    function onlyPaidSeat(bytes32 scopeId, uint64 paidAt) public view returns (bytes32 single) {
        bytes32[] memory forms = MATERIALS.getScopeForms(scopeId);
        for (uint256 i; i < forms.length; ++i) {
            (uint128 gross, bool pending) = MATERIALS.activeScopeGrossAt(scopeId, forms[i], paidAt);
            if (pending) return bytes32(0);
            if (gross == 0) continue;
            if (single != bytes32(0)) return bytes32(0);
            single = forms[i];
        }
    }
}
