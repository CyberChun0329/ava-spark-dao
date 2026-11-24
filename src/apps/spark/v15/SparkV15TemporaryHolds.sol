// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

/// @notice Fixed-expiry hold history of one Spark payment installation.
contract SparkV15TemporaryHolds {
    struct Terms {
        bytes32 obligationId;
        bytes32 caseId;
        bytes32 noticeHash;
        uint64 authorisedAt;
        uint64 expiresAt;
        uint256 expectedVersion;
    }

    struct Hold {
        Terms terms;
        address setter;
        bytes32 authorityId;
        uint256 evidenceId;
        uint128 amount;
        uint64 imposedAt;
        bytes32 replacedBy;
    }

    struct Link {
        bytes32 previous;
        bytes32 next;
    }

    error InvalidTemporaryHold();

    address public immutable PAYMENTS;
    mapping(bytes32 => Hold) private holds;
    mapping(bytes32 => mapping(bytes32 => mapping(address => bool))) public setterFor;
    mapping(bytes32 => mapping(bytes32 => bytes32)) private latestInCase;
    mapping(bytes32 => bytes32) private latestForObligation;
    mapping(bytes32 => Link) private links;

    constructor(address payments) {
        if (payments == address(0)) revert InvalidTemporaryHold();
        PAYMENTS = payments;
    }

    modifier onlyPayments() {
        if (msg.sender != PAYMENTS) revert InvalidTemporaryHold();
        _;
    }

    function get(bytes32 id) external view returns (Hold memory) {
        return holds[id];
    }

    function latestExpiry(bytes32 obligationId) external view returns (uint64) {
        return holds[latestForObligation[obligationId]].terms.expiresAt;
    }

    function record(bytes32 id, bytes32 lessonId, Hold calldata hold) external onlyPayments {
        bytes32 obligationId = hold.terms.obligationId;
        bytes32 caseId = hold.terms.caseId;
        if (_inForce(holds[latestInCase[obligationId][caseId]])) revert InvalidTemporaryHold();
        holds[id] = hold;
        setterFor[lessonId][caseId][hold.setter] = true;
        latestInCase[obligationId][caseId] = id;
        _link(obligationId, id, hold.terms.expiresAt);
    }

    function replace(bytes32 obligationId, bytes32 caseId, bytes32 formalId) external onlyPayments {
        bytes32 temporaryId = latestInCase[obligationId][caseId];
        Hold storage hold = holds[temporaryId];
        if (!_inForce(hold)) return;
        hold.replacedBy = formalId;
        Link memory link = links[temporaryId];
        if (link.previous == bytes32(0)) latestForObligation[obligationId] = link.next;
        else links[link.previous].next = link.next;
        if (link.next != bytes32(0)) links[link.next].previous = link.previous;
        delete links[temporaryId];
    }

    function _inForce(Hold storage hold) private view returns (bool) {
        return hold.replacedBy == bytes32(0) && hold.terms.expiresAt > block.timestamp;
    }

    /// @dev Latest expiry stays at the head. Payment checks do not scan the case history.
    function _link(bytes32 obligationId, bytes32 id, uint64 expiry) private {
        bytes32 previous;
        bytes32 next = latestForObligation[obligationId];
        while (next != bytes32(0) && holds[next].terms.expiresAt > expiry) {
            previous = next;
            next = links[next].next;
        }
        links[id] = Link(previous, next);
        if (previous == bytes32(0)) latestForObligation[obligationId] = id;
        else links[previous].next = id;
        if (next != bytes32(0)) links[next].previous = id;
    }
}
