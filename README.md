# AVA Spark DAO

AVA Spark DAO uses AVA Protocol to run the Spark DAO v1.5 rules for course booking, teaching, materials, review and settlement. This developer preview uses test accounts and test assets on a local chain with ID 31337.

> **Does this step change state that multiple parties must rely on?**
>
> **这一步是否更新多方必须共同依赖的状态？**

The app uses the public chain for changes that parties need to verify or enforce independently, such as reserving shared funds, placing a payment on hold or recording an actual transfer. Participants keep original documents and routine records locally. When an on-chain action depends on a document, the app checks the relevant proof at that step. The v1.5 recognised-state Lean model guides the app's treatment of effective decisions and the facts later actions can rely on.

To open the app and connect a test wallet, follow the [local installation guide](docs/local-installation.md). For the ordinary one-to-one workflow, see [participant commands](docs/ordinary-participant-pilot.md), [terms delivery](docs/terms-delivery-pilot.md) and [settlement](docs/settlement-support-pilot.md).

## Rule specification

The [v1.5 specification](spec/v1.5/README.md) follows the English rules through the direct and recognised-state Lean models to the app. It also explains how to build the two projects and the scope of their proofs.

The [v1.5 research evidence](research/spark-v1.5/README.md) contains executable Lean witnesses, the synthetic payment readbacks and the gas ledgers used in the study.

## Run the tests

Use Node.js 24 or later with npm, Foundry and the Solidity compiler, solc 0.8.26. The test run used Foundry 1.5.1. Run these commands from the repository root.

```sh
(cd artifacts && shasum -a 256 -c SHA256SUMS)
npm ci --ignore-scripts
npm test
```

If Foundry cannot find solc 0.8.26, set `FOUNDRY_SOLC` to the compiler's path. `npm test` checks TypeScript and loads the installed AVA modules. It also runs the Core and Spark installers and the v1.5 business tests inside Forge, using a test token. Run the participant adapter tests with `node --import tsx --test test/spark/v15/*.test.mjs`. All these checks run without Anvil or a browser.

## Package versions

| Component | Version |
| --- | --- |
| AVA Spark DAO | `0.1.0-preview.3` |
| Spark DAO rules | `1.5` |
| AVA contracts, SDK and local service | `0.1.0-preview.12` |
| AVA Workbench browser toolkit | `0.1.0-preview.5` |

The contracts, SDK and local service archives in `artifacts/` come from the [AVA Protocol Preview 12 release](https://github.com/CyberChun0329/ava-protocol/releases/tag/v0.1.0-preview.12). The Workbench archive provides the browser's wallet controls. The npm lockfile pins all four archives.

## Upgrade AVA Protocol

Each Spark release keeps the AVA versions it was tested with. To try a newer version, create a Spark branch and replace the contracts, SDK and local service archives with the ones from the same AVA release. Update `artifacts/SHA256SUMS`, `package.json` and `package-lock.json` to match.

Check for changes to contract interfaces, SDK calls and installation. Repeat the installation and tests above. Use the SDK to check the deployment the new Spark version will use before releasing it. Update the Spark rules version separately if the rules change.

AVA-authored source is licensed under Apache-2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE). Distributed dependencies carry their own terms and notices.
