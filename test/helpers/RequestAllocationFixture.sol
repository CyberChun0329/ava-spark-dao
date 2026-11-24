// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAApplicationRegistry} from "@ava-protocol/contracts/src/AVAApplicationRegistry.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAAuthorityMatrix} from "@ava-protocol/contracts/src/core/AVAAuthorityMatrix.sol";
import {AVAIdentityRegistry} from "@ava-protocol/contracts/src/core/AVAIdentityRegistry.sol";
import {AVACoreRulePackageRegistry} from "@ava-protocol/contracts/src/core/AVACoreRulePackageRegistry.sol";
import {AVADisclosurePolicyRegistry} from "@ava-protocol/contracts/src/core/AVADisclosurePolicyRegistry.sol";
import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {AVAGovernanceKernel} from "@ava-protocol/contracts/src/core/AVAGovernanceKernel.sol";
import {AVAWorkflowPolicyRouter} from "@ava-protocol/contracts/src/core/AVAWorkflowPolicyRouter.sol";
import {IAVAApplicationModule} from "@ava-protocol/contracts/src/interfaces/IAVAApplicationModule.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {M14CorePackageFixture} from "./M14CorePackageFixture.sol";

interface RequestVm {
    function prank(address sender) external;
    function startPrank(address sender) external;
    function stopPrank() external;
    function warp(uint256 timestamp) external;
    function expectRevert() external;
    function expectRevert(bytes4 selector) external;
    function chainId(uint256 chainId) external;
    function etch(address target, bytes calldata code) external;
}

/// @notice Real Core fixture; only callers and time use standard test cheatcodes.
abstract contract RequestAllocationFixture is M14CorePackageFixture {
    RequestVm internal constant requestVm = RequestVm(address(uint160(uint256(keccak256("hevm cheat code")))));
    bytes32 internal constant REQUEST_WORKFLOW = keccak256("ava.test.request.workflow.v1");
    bytes32 internal constant ROLE_SOURCE = keccak256("ava.test.request.role.source.v1");
    bytes32 internal constant ROLE_VERIFIER = keccak256("ava.test.request.role.verifier.v1");
    bytes32 internal constant ROLE_ALLOCATOR = keccak256("ava.test.request.role.allocator.v1");
    bytes32 internal constant ROLE_PACKAGE = keccak256("ava.test.request.role.package.v1");
    address internal constant SOURCE_ACTOR = address(0xC1);
    address internal constant VERIFIER_ACTOR = address(0xC2);
    address internal constant ALLOCATOR_ACTOR = address(0xA1);

    AVAApplicationRegistry internal applicationRegistry;
    AVAIdentityRegistry internal identityRegistry;
    AVAAuthorityMatrix internal authorityMatrix;
    AVACoreRulePackageRegistry internal packageRegistry;
    AVADisclosurePolicyRegistry internal disclosureRegistry;
    AVAEvidenceRegistry internal evidenceRegistry;
    AVAGovernanceKernel internal kernel;
    AVARequestAllocation internal requestAllocation;
    bytes32 internal requestAppId;
    bytes32 internal requestObjectTypeKey;
    uint256 internal requestPackageId;
    uint256 internal requestPolicyId;

    function _setUpRequestAllocation(bytes32 appId, IAVAApplicationModule module, bytes32 objectTypeKey) internal {
        requestAppId = appId;
        requestObjectTypeKey = objectTypeKey;
        applicationRegistry = new AVAApplicationRegistry(address(this));
        applicationRegistry.registerApplication(
            appId, keccak256("request.app"), keccak256("request.authority"), address(this), "test:app"
        );
        identityRegistry = new AVAIdentityRegistry(applicationRegistry);
        authorityMatrix = new AVAAuthorityMatrix(applicationRegistry, identityRegistry);
        identityRegistry.assignSubject(address(this), appId, ROLE_PACKAGE, _authority(ROLE_PACKAGE), "test:package");
        identityRegistry.assignSubject(SOURCE_ACTOR, appId, ROLE_SOURCE, _authority(ROLE_SOURCE), "test:source");
        identityRegistry.assignSubject(VERIFIER_ACTOR, appId, ROLE_VERIFIER, _authority(ROLE_VERIFIER), "test:verifier");
        identityRegistry.assignSubject(
            ALLOCATOR_ACTOR, appId, ROLE_ALLOCATOR, _authority(ROLE_ALLOCATOR), "test:allocator"
        );
        _grant(ROLE_PACKAGE, AVACoreTypes.ACTION_REGISTER_RULE_PACKAGE);
        _grant(ROLE_SOURCE, AVACoreTypes.ACTION_REGISTER_DISCLOSURE_POLICY);
        _grant(ROLE_SOURCE, AVACoreTypes.ACTION_REGISTER_EVIDENCE);
        _grant(ROLE_SOURCE, AVACoreTypes.ACTION_RECORD_EVIDENCE_LIFECYCLE);
        _grant(ROLE_SOURCE, AVACoreTypes.ACTION_REGISTER_GOVERNED_OBJECT);
        _grant(ROLE_SOURCE, keccak256("ava.extension.request.create.v1"));
        _grant(ROLE_VERIFIER, AVACoreTypes.ACTION_FORM_RECOGNISED_STATE);
        _grant(ROLE_VERIFIER, AVACoreTypes.ACTION_TRANSITION_RECOGNISED_STATE);
        _grant(ROLE_VERIFIER, AVACoreTypes.ACTION_VEST_RECOGNISED_STATE);
        _grant(ROLE_ALLOCATOR, AVACoreTypes.ACTION_RECORD_ALLOCATION);
        packageRegistry = new AVACoreRulePackageRegistry(applicationRegistry, authorityMatrix);
        requestPackageId = _registerRequestPackage(module, 1);
        disclosureRegistry = new AVADisclosurePolicyRegistry(applicationRegistry, authorityMatrix);
        evidenceRegistry =
            new AVAEvidenceRegistry(authorityMatrix, identityRegistry, packageRegistry, disclosureRegistry);
        kernel = new AVAGovernanceKernel(
            authorityMatrix,
            identityRegistry,
            packageRegistry,
            evidenceRegistry,
            disclosureRegistry,
            new AVAWorkflowPolicyRouter(packageRegistry, evidenceRegistry, disclosureRegistry)
        );
        requestAllocation = new AVARequestAllocation(kernel);
        kernel.CORRECTIONS().bindRequestOrigin(appId, address(requestAllocation));
        requestVm.prank(SOURCE_ACTOR);
        requestPolicyId = disclosureRegistry.registerPolicy(
            appId, ROLE_SOURCE, _authority(ROLE_SOURCE), keccak256("request.disclosure"), "Request", "test:disclosure"
        );
    }

    function _registerRequestPackage(IAVAApplicationModule module, uint64 version) internal returns (uint256) {
        AVACoreRulePackageRegistry.PackageRegistrationInput memory input = _corePackageInput(
            requestAppId,
            REQUEST_WORKFLOW,
            ROLE_PACKAGE,
            _authority(ROLE_PACKAGE),
            version,
            keccak256("request.compatibility"),
            "test:rules"
        );
        if (version == 1) return packageRegistry.registerRulePackage(input, _coreBindings(module));
        return packageRegistry.supersedeRulePackage(
            input, packageRegistry.getActivePackageId(requestAppId, REQUEST_WORKFLOW), _coreBindings(module)
        );
    }

    function _createRequestState(
        address executor,
        bytes32 responseClass,
        bytes32 parametersHash,
        bytes32 burdenHash,
        uint64 validUntil
    ) internal returns (uint256) {
        return _createStateForCommitment(
            requestAllocation.commitmentFor(
                requestAppId, executor, responseClass, parametersHash, burdenHash, validUntil
            )
        );
    }

    function _createStateForCommitment(bytes32 commitment) internal returns (uint256 stateId) {
        requestVm.startPrank(SOURCE_ACTOR);
        uint256 evidenceId = evidenceRegistry.registerEvidence(
            AVAEvidenceRegistry.EvidenceRegistrationInput({
                appId: requestAppId,
                workflowKey: REQUEST_WORKFLOW,
                packageId: requestPackageId,
                roleKey: ROLE_SOURCE,
                subjectId: _authority(ROLE_SOURCE),
                commitment: keccak256(abi.encode(commitment, "evidence")),
                evidenceTypeHash: keccak256("request.support"),
                disclosurePolicyId: requestPolicyId,
                authorityId: _authority(ROLE_SOURCE),
                uri: "test:evidence"
            })
        );
        uint256 objectId = kernel.registerGovernedObject(
            AVAGovernanceKernel.GovernedObjectInput({
                appId: requestAppId,
                workflowKey: REQUEST_WORKFLOW,
                packageId: requestPackageId,
                roleKey: ROLE_SOURCE,
                objectTypeKey: requestObjectTypeKey,
                objectCommitment: commitment,
                parentObjectId: 0,
                subjectId: _authority(ROLE_SOURCE),
                evidenceReceiptId: evidenceId,
                disclosurePolicyId: requestPolicyId,
                metadataHash: commitment,
                authorityId: _authority(ROLE_SOURCE),
                uri: "test:request-object"
            })
        );
        requestVm.stopPrank();
        requestVm.startPrank(VERIFIER_ACTOR);
        stateId = kernel.formRecognisedState(
            AVAGovernanceKernel.RecognisedStateFormationInput({
                governedObjectId: objectId,
                roleKey: ROLE_VERIFIER,
                authorityId: _authority(ROLE_VERIFIER),
                stage: AVACoreTypes.Stage.Verification,
                status: AVACoreTypes.RecognisedStateStatus.Provisional,
                reasonHash: keccak256("request.formation"),
                reasonURI: "test:formation"
            })
        );
        kernel.transitionRecognisedState(_transitionInput(stateId, AVACoreTypes.RecognisedStateStatus.Challengeable));
        kernel.vestRecognisedState(_transitionInput(stateId, AVACoreTypes.RecognisedStateStatus.Vested));
        requestVm.stopPrank();
    }

    function _transitionInput(uint256 stateId, AVACoreTypes.RecognisedStateStatus toStatus)
        internal
        view
        returns (AVAGovernanceKernel.RecognisedStateTransitionInput memory)
    {
        return AVAGovernanceKernel.RecognisedStateTransitionInput({
            recognisedStateId: stateId,
            roleKey: ROLE_VERIFIER,
            authorityId: _authority(ROLE_VERIFIER),
            toStatus: toStatus,
            reasonHash: keccak256(abi.encode(stateId, toStatus)),
            reasonURI: "test:transition"
        });
    }

    function _createRequest(AVARequestAllocation.RequestInput memory input) internal returns (uint256) {
        requestVm.prank(SOURCE_ACTOR);
        return requestAllocation.createRequest(input, ROLE_SOURCE, _authority(ROLE_SOURCE));
    }

    function _approveRequest(uint256 requestId) internal {
        requestVm.prank(ALLOCATOR_ACTOR);
        requestAllocation.approve(requestId, ROLE_ALLOCATOR, _authority(ROLE_ALLOCATOR));
    }

    function _authority(bytes32 roleKey) internal view returns (bytes32) {
        return keccak256(abi.encode(requestAppId, roleKey));
    }

    function _grant(bytes32 roleKey, bytes32 actionKey) private {
        authorityMatrix.setPermission(requestAppId, roleKey, actionKey, true);
    }
}
