// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVACapabilityKeys} from "@ava-protocol/contracts/src/core/AVACapabilityKeys.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVACoreRulePackageRegistry} from "@ava-protocol/contracts/src/core/AVACoreRulePackageRegistry.sol";
import {DefaultAVACorePolicyBundle} from "@ava-protocol/contracts/src/core/modules/DefaultAVACoreRuleModules.sol";
import {IAVAApplicationModule} from "@ava-protocol/contracts/src/interfaces/IAVAApplicationModule.sol";
import {IRuleModuleIdentity} from "@ava-protocol/contracts/src/interfaces/IRuleModuleIdentity.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";

/// @notice Reuse the installer-verified capability layout of the standard Spark package.
/// @dev The installer supplies its four concrete, caller-independent modules. Identities and active scope stay live.
contract SparkV15FirstUsePackage {
    AVACoreRulePackageRegistry private immutable REGISTRY;
    uint256 private immutable PACKAGE_ID;
    address private immutable APPLICATION;
    address private immutable CORE_POLICY;
    address private immutable EXTENSION_POLICY;
    address private immutable REQUEST_POLICY;
    bytes32 private immutable IDENTITIES;
    bytes32 private immutable CORE_CODE_HASH;

    constructor(
        AVACoreRulePackageRegistry registry,
        uint256 packageId,
        address application,
        address corePolicy,
        address extensionPolicy,
        address requestPolicy
    ) {
        REGISTRY = registry;
        PACKAGE_ID = packageId;
        APPLICATION = application;
        CORE_POLICY = corePolicy;
        EXTENSION_POLICY = extensionPolicy;
        REQUEST_POLICY = requestPolicy;
        CORE_CODE_HASH = keccak256(type(DefaultAVACorePolicyBundle).runtimeCode);

        bytes32[] memory keys = registry.getCapabilityKeys(packageId);
        (, address[] memory modules) =
            registry.getActiveVerifiedModulesCompact(SparkV15.APP_ID, SparkV15.WORKFLOW, packageId, keys);
        if (corePolicy.codehash != CORE_CODE_HASH) revert AVACoreTypes.InvalidState(packageId);
        for (uint256 i; i < keys.length; ++i) {
            address module = modules[i];
            bytes32 key = keys[i];
            if (key == AVACapabilityKeys.APPLICATION) {
                if (module != application) revert AVACoreTypes.InvalidState(packageId);
            } else if (
                key == AVACapabilityKeys.EVIDENCE_POLICY || key == AVACapabilityKeys.DISCLOSURE_POLICY
                    || key == AVACapabilityKeys.EVIDENCE_LIFECYCLE
            ) {
                if (module != corePolicy) revert AVACoreTypes.InvalidState(packageId);
            } else if (module != application && module != corePolicy && module != extensionPolicy && module != requestPolicy) {
                revert AVACoreTypes.InvalidState(packageId);
            }
        }
        IDENTITIES = _liveIdentities();
    }

    function activeApplication(uint256 packageId) external view returns (address) {
        if (packageId != PACKAGE_ID) return address(0);

        if (REGISTRY.getActivePackageId(SparkV15.APP_ID, SparkV15.WORKFLOW) != packageId) {
            revert AVACoreTypes.InvalidState(packageId);
        }
        REGISTRY.APPLICATION_REGISTRY().requireApplicationReference(SparkV15.APP_ID);
        if (
            _liveIdentities() != IDENTITIES || IAVAApplicationModule(APPLICATION).applicationId() != SparkV15.APP_ID
                || CORE_POLICY.codehash != CORE_CODE_HASH
        ) revert AVACoreTypes.InvalidState(packageId);
        return APPLICATION;
    }

    function _liveIdentities() private view returns (bytes32) {
        return keccak256(
            abi.encode(
                IRuleModuleIdentity(APPLICATION).moduleIdentityHash(),
                IRuleModuleIdentity(CORE_POLICY).moduleIdentityHash(),
                IRuleModuleIdentity(EXTENSION_POLICY).moduleIdentityHash(),
                IRuleModuleIdentity(REQUEST_POLICY).moduleIdentityHash()
            )
        );
    }
}
