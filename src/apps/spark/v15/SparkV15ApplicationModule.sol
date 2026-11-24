// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {IAVAApplicationModule} from "@ava-protocol/contracts/src/interfaces/IAVAApplicationModule.sol";
import {RuleModuleIdentity} from "@ava-protocol/contracts/src/interfaces/IRuleModuleIdentity.sol";

library SparkV15 {
    bytes32 internal constant APP_ID = keccak256("ava.application.spark-dao.v1.5");
    bytes32 internal constant WORKFLOW = keccak256("ava.spark.workflow.teaching.v1.5");
    bytes32 internal constant OBJECT_PAYMENT_APPROVAL = keccak256("spark.object.payment-approval.v1.5");
    bytes32 internal constant RESPONSE_APPROVE_PAYMENT = keccak256("spark.response.approve-payment.v1.5");
    bytes32 internal constant APPROVAL_BURDEN = keccak256("spark.burden.payment-approval.v1.5");
    bytes32 internal constant ACTION_ESTABLISH_PAYMENT = keccak256("spark.action.establish-payment.v1.5");
    bytes32 internal constant ACTION_AUTHORISE_PAYMENT_RETURN = keccak256("spark.action.authorise-payment-return.v1.5");
    bytes32 internal constant ACTION_TEMPORARY_HOLD = keccak256("spark.action.temporary-hold.v1.5");
    bytes32 internal constant ALTERNATIVE_CONTACT_ROLE = keccak256("ava.spark.role.alternative-contact.v1.5");
    bytes32 internal constant ACTION_FORMAL_HOLD = keccak256("spark.action.formal-hold.v1.5");
    bytes32 internal constant ACTION_LIFT_HOLD = keccak256("spark.action.lift-hold.v1.5");
    bytes32 internal constant ACTION_VERIFY_POST_LIFT_CLOCK = keccak256("spark.action.verify-post-lift-clock.v1.5");
}

/// @notice Application validator for payment approvals in a single workflow.
contract SparkV15ApplicationModule is IAVAApplicationModule, RuleModuleIdentity {
    bytes32 public immutable WORKFLOW_KEY;
    bytes32 public immutable SOURCE_ROLE;
    bytes32 public immutable VERIFIER_ROLE;
    bytes32 public immutable ALLOCATOR_ROLE;

    constructor(bytes32 workflowKey, bytes32 sourceRole, bytes32 verifierRole, bytes32 allocatorRole) {
        if (
            workflowKey == bytes32(0) || sourceRole == bytes32(0) || verifierRole == bytes32(0)
                || allocatorRole == bytes32(0)
        ) {
            revert AVACoreTypes.EmptyValue();
        }
        WORKFLOW_KEY = workflowKey;
        SOURCE_ROLE = sourceRole;
        VERIFIER_ROLE = verifierRole;
        ALLOCATOR_ROLE = allocatorRole;
    }

    function applicationId() external pure returns (bytes32) {
        return SparkV15.APP_ID;
    }

    function validateGovernedObject(GovernedObjectContext calldata c) external view {
        _scope(c.appId, c.workflowKey);
        if (c.roleKey != SOURCE_ROLE || c.objectTypeKey != SparkV15.OBJECT_PAYMENT_APPROVAL || c.parentObjectId != 0) {
            revert AVACoreTypes.InvalidState(c.packageId);
        }
    }

    function validateRecognisedStateFormation(RecognisedStateFormationContext calldata c) external view {
        _scope(c.appId, c.workflowKey);
        if (
            c.objectTypeKey != SparkV15.OBJECT_PAYMENT_APPROVAL || c.roleKey != VERIFIER_ROLE
                || c.stage != AVACoreTypes.Stage.Verification
                || c.status != AVACoreTypes.RecognisedStateStatus.Provisional
        ) revert AVACoreTypes.InvalidState(c.governedObjectId);
    }

    function validateRecognisedStateTransition(RecognisedStateTransitionContext calldata c) external view {
        _scope(c.appId, c.workflowKey);
        if (
            c.objectTypeKey != SparkV15.OBJECT_PAYMENT_APPROVAL || c.roleKey != VERIFIER_ROLE
                || c.stage != AVACoreTypes.Stage.Verification
        ) {
            revert AVACoreTypes.InvalidState(c.recognisedStateId);
        }
        if (
            c.actionKey == AVACoreTypes.ACTION_TRANSITION_RECOGNISED_STATE
                && c.transitionKind == AVACoreTypes.TransitionKind.Generic
                && c.fromStatus == AVACoreTypes.RecognisedStateStatus.Provisional
                && c.toStatus == AVACoreTypes.RecognisedStateStatus.Challengeable
        ) return;
        if (
            c.actionKey == AVACoreTypes.ACTION_VEST_RECOGNISED_STATE
                && c.transitionKind == AVACoreTypes.TransitionKind.Vesting
                && c.fromStatus == AVACoreTypes.RecognisedStateStatus.Challengeable
                && c.toStatus == AVACoreTypes.RecognisedStateStatus.Vested
        ) return;
        revert AVACoreTypes.InvalidState(c.recognisedStateId);
    }

    function validateEvidence(EvidenceContext calldata c) external view {
        _scope(c.appId, c.workflowKey);
        if (c.roleKey != SOURCE_ROLE) revert AVACoreTypes.InvalidState(c.packageId);
    }

    function validateDownstreamRecord(DownstreamRecordContext calldata c) external view {
        _scope(c.appId, c.workflowKey);
        if (
            c.objectTypeKey != SparkV15.OBJECT_PAYMENT_APPROVAL || c.recordTypeKey != SparkV15.RESPONSE_APPROVE_PAYMENT
                || c.actionKey != AVACoreTypes.ACTION_RECORD_ALLOCATION || c.roleKey != ALLOCATOR_ROLE
        ) revert AVACoreTypes.InvalidState(c.recognisedStateId);
    }

    function _scope(bytes32 appId, bytes32 workflowKey) private view {
        if (appId != SparkV15.APP_ID || workflowKey != WORKFLOW_KEY) revert AVACoreTypes.InvalidState(0);
    }

    function _moduleConfigurationHash() internal view override returns (bytes32) {
        return keccak256(abi.encode(WORKFLOW_KEY, SOURCE_ROLE, VERIFIER_ROLE, ALLOCATOR_ROLE));
    }
}
