# Run AVA Spark DAO locally

Start Anvil at `http://127.0.0.1:8545` with chain ID `31337`, the chain ID the Spark installer accepts. Use Anvil test accounts and test assets. Keep Anvil running and use a separate terminal for the commands below. Run `npm ci --ignore-scripts` from the repository root if you have yet to install the packages.

## Install AVA Core and a test token

Export `AVA_ROOT_ADMIN` with the address of a funded, unlocked Anvil account. Install Core from the contracts package and deploy the test ERC-20.

```sh
forge build --offline
forge script node_modules/@ava-protocol/contracts/script/DeployAVACore.s.sol:DeployAVACore \
  --offline --rpc-url http://127.0.0.1:8545 --chain-id 31337 \
  --sender "$AVA_ROOT_ADMIN" --unlocked --broadcast --slow
forge create test/spark/mocks/MockERC20.sol:MockERC20 --offline \
  --rpc-url http://127.0.0.1:8545 --from "$AVA_ROOT_ADMIN" --unlocked --broadcast \
  --constructor-args "Spark Test Token" SPARK 6
```

From the Core broadcast receipt, save the addresses of `AVAGovernanceKernel` and `AVARequestAllocation`. Save the test token address printed by `forge create` as well.

## Install Spark

Keep `AVA_ROOT_ADMIN` set to the administrator's account. Export the addresses from the previous step.

| Environment variable | Address |
| --- | --- |
| `AVA_EXISTING_KERNEL` | `AVAGovernanceKernel` |
| `AVA_EXISTING_REQUESTS` | `AVARequestAllocation` |
| `SPARK_V15_TOKEN` | Test token |

Choose the roles needed for the workflow you want to try. Export the corresponding variables.

- **Payments**. Set `SPARK_V15_SOURCE`, `SPARK_V15_VERIFIER`, `SPARK_V15_ALLOCATOR` and `SPARK_V15_REVIEWER` to four different addresses. These are the only roles needed to test payments by themselves.
- **Course booking and settlement**. Also set `SPARK_V15_COURSE_PROVIDER`, `SPARK_V15_BOOKING_COORDINATOR` and `SPARK_V15_CORE_PARTNER`. Spark records what is owed through course settlement and other authorised course operations. Use distinct addresses for the course and payment roles. The provider and allocator can share an address under the materials option below.
- **Course materials**. With course booking enabled, set both `SPARK_V15_MATERIALS_DAO` and `SPARK_V15_SERVICE_RESERVE`. The agreed payer needs the allocator role to approve a material charge. If the course provider is the payer, use the same address for the provider and allocator.

If you set `SPARK_V15_ALTERNATIVE_CONTACT`, use an address separate from the payment and course roles.

Run the Spark installer. In the export command, replace the two broadcast placeholders with the successful `run-latest.json` paths printed by Forge. They are normally in `broadcast/DeployAVACore.s.sol/31337/` and `broadcast/DeploySparkV15OnExistingCore.s.sol/31337/`. Keep `.build/out/` from the same build for this export.

```sh
forge script script/DeploySparkV15OnExistingCore.s.sol:DeploySparkV15OnExistingCore \
  --offline --rpc-url http://127.0.0.1:8545 --chain-id 31337 \
  --sender "$AVA_ROOT_ADMIN" --unlocked --broadcast --slow
node scripts/export_deployment.mjs --verify-local http://127.0.0.1:8545 \
  .local/spark-v15/deployment.json path/to/core-broadcast.json path/to/v15-broadcast.json
```

The export checks the deployment transactions and receipts against Anvil. It writes the contract addresses and package details to `.local/spark-v15/deployment.json` for the two services below.

## Start the relay

For the first start, run the full block from the repository root. It creates `relay.token` and `relay.json` in `.local/spark-v15/` and starts the relay on `127.0.0.1:8787`. To restart the relay, run only the last `node` command with the existing `relay.json`. Relative paths in `relay.json` start at the repository root.

```sh
node --input-type=module <<'JS'
import { randomBytes } from 'node:crypto';
import { readFile, writeFile } from 'node:fs/promises';

const directory = '.local/spark-v15';
const exported = JSON.parse(await readFile(`${directory}/deployment.json`, 'utf8'));
const spark = Object.values(exported.apps).find(app => app.contracts.SparkV15Payments);
if (!spark) throw new Error('Spark v1.5 installation missing from deployment export');
const tokenPath = `${directory}/relay.token`;
await writeFile(tokenPath, randomBytes(32).toString('base64url'), { mode: 0o600, flag: 'wx' });
const config = {
  deployment: exported.deployment,
  rpcUrl: 'http://127.0.0.1:8545',
  port: 8787,
  tokenPath,
  databasePath: `${directory}/relay.sqlite`,
  additionalSources: { SparkV15Payments: spark.contracts.SparkV15Payments },
};
await writeFile(`${directory}/relay.json`, JSON.stringify(config, null, 2), { mode: 0o600, flag: 'wx' });
JS
node "$(node --input-type=module -e 'import { fileURLToPath } from "node:url"; console.log(fileURLToPath(import.meta.resolve("@ava-protocol/local-service/cli")))')" .local/spark-v15/relay.json
```

## Open the browser app

In another terminal, save the JSON below as `.local/spark-v15/participant.json`. Replace `token` with the test token address. `requestAudience` ties wallet-signed requests to this installation. You can keep the example value for one local test installation. Use a distinct, nonzero 32-byte value for each installation you want to distinguish.

Relative paths in `participant.json` start in its folder. The app needs one Vault credential to start. For the setup shown, save 32 random bytes in `vault.key` beside `participant.json` and set its permissions to `0600`. If you already have a Vault credential profile, set `storage.credentialProfileFile` in place of `storage.masterKeyFile`.

For private materials, install the Python dependency below and replace `storage.pythonPath` with the absolute path to `.local/spark-v15/privacy-venv/bin/python`. For a run without private materials, you can remove `storage.pythonPath` from the example. If you have private notices, set `storage.noticeIndexPath` to a private JSON file with an array of `{ "receipt": <Vault material receipt>, "noticeHash": <on-chain notice commitment> }` entries. Otherwise leave the field out or supply an empty array.

```sh
python3 -m venv .local/spark-v15/privacy-venv
.local/spark-v15/privacy-venv/bin/python -m pip install 'cryptography==50.0.2'
```

```json
{
  "deploymentPath": "deployment.json",
  "rpcUrl": "http://127.0.0.1:8545",
  "token": "0x0000000000000000000000000000000000000001",
  "requestAudience": "0x1111111111111111111111111111111111111111111111111111111111111111",
  "port": 8879,
  "relay": { "url": "http://127.0.0.1:8787", "tokenFile": "relay.token" },
  "storage": { "databasePath": "participant.sqlite", "vaultPath": "vault", "masterKeyFile": "vault.key", "pythonPath": "/absolute/path/to/privacy-venv/bin/python" }
}
```

At startup the SDK checks that the app and the relay are using the same Anvil installation. Run the following from the repository root, using the path to `participant.json`.

```sh
npm start -- path/to/config.json
```

Open the address printed by `npm start`. The example uses `http://127.0.0.1:8879`. Connect a test wallet on chain `31337`. The wallet signs and sends transactions, and the app reads the receipts from Anvil.

To try a course operation, connect the account set in `SPARK_V15_COURSE_PROVIDER` and select **Publish recharge terms**. Use another test account as the customer. Enter a positive amount in the token's smallest units, set the refund cap and deadline to `0`, and supply a nonzero 32-byte agreement reference. Preview the transaction and confirm it in the wallet. Once the app confirms the transaction, switch to the customer account. A **Recharge terms** card should show the amount offered.

## Keep a local installation for later

Save Anvil's chain state with the private `.local/spark-v15/` folder. It holds the configuration, relay token and database, participant database, Vault files and any notice index. Keep the transaction IDs you need to look up again with that copy.

## File a verified material payment receipt

In `participant.json`, set `storage.materialArchivePath` to the archive file, such as `material-receipts.sqlite` beside the configuration. Keep the archive with the private installation records. If you move the installation, prepare any pending filing again. The signature binds the original archive path.

After payment verification, have the lesson's recorded coordinator sign the exact UTF-8 `message` from `prepare`. File the signed record, then read it back.

```sh
archive=examples/spark-dao/v15/participant-material-archive-cli.ts
config=.local/spark-v15/participant.json
node --import tsx "$archive" "$config" prepare RECEIPT_ID COORDINATOR_ADDRESS > prepared.json
node --import tsx "$archive" "$config" file prepared.json COORDINATOR_SIGNATURE
node --import tsx "$archive" "$config" read RECEIPT_ID
```

To link a local document, pass its hash as the final `prepare` argument. The archive keeps the payment and verification timestamps, the chain checkpoint and the local filing time. Earlier installations continue to use their chain archive. Service reserves have a separate filing procedure.

## File a verified external payment or return

Use the same archive file. Pass `payment` with the payment observation ID or `return` with the return observation ID. Once the observation is verified on chain, use a wallet with the payment-observation Verifier permission to sign the exact UTF-8 `message` from `prepare` using `personal_sign`.

```sh
archive=examples/spark-dao/v15/participant-observation-archive-cli.ts
config=.local/spark-v15/participant.json
node --import tsx "$archive" "$config" prepare payment OBSERVATION_ID VERIFIER_ADDRESS > prepared.json
node --import tsx "$archive" "$config" file prepared.json VERIFIER_SIGNATURE
node --import tsx "$archive" "$config" read payment OBSERVATION_ID
```

To link a local document, pass its hash as the final `prepare` argument. The signature binds the observation, evidence, installation, archive path and preparation block. At filing, the app rechecks the observation and the signer's authority. It saves the preparation and filing blocks, the transfer and verification times, and the local filing time. Eligibility for credit and the unpaid balance are read from the chain.

`read` displays the local filing and any earlier on-chain filing time separately. New installations file each observation once in the configured database. Their on-chain `archivedAt` getter returns zero. Earlier installations can still file on chain.

### A student's account when teaching has not started

After the effective agreed start time, a student on a confirmed form may leave a signed account of attendance or of what happened. Store it in the installation's configured local archive. An attendance file contains `{"attended":true,"text":"I joined at the agreed time and waited."}`. A feedback file contains a `text` field.

```sh
report=examples/spark-dao/v15/participant-student-report-cli.ts
node --import tsx "$report" "$config" prepare FORM_ID STUDENT_ADDRESS attendance details.json > prepared.json
node --import tsx "$report" "$config" file prepared.json STUDENT_SIGNATURE
node --import tsx "$report" "$config" read MESSAGE_HASH
```

The student signs the exact `message` from `prepare`. The archive preserves the form, its effective arrangement, the chain checkpoints and the local filing time. The student can later give this record to the person handling a concern. The existing verification of absence, service and any resulting fees remains a separate decision.

## Confirm a one-to-one lesson and approve tutor pay

The student and the assigned coordinator each use their own wallet to **Confirm one-to-one completion** after the end of teaching is recorded. The teacher's own delivery report remains a separate operation. Each confirmation uses a Source evidence ID that binds its signer and report to the same booked form and teaching end.

Use the participant command below to prepare and check the evidence and the existing AVA approval steps. Keep the original report or evidence in the local records. The command takes commitments and public references, so use those fields for hashes and references rather than private material.

```sh
node --import tsx examples/spark-dao/v15/participant-approval-cli.ts \
  .local/spark-v15/participant.json prepare action.json > intent.json
```

Choose an action and set `account` to the address of the actor who will sign. Represent unsigned integers as decimal strings in the JSON. Reuse exactly the same `terms` and `validUntil` for the approval steps from `object` through `allocate`. The terms are `obligationId`, `executor`, `ceiling`, `validThrough` and `replacesRequestId`. Use `"0"` for `replacesRequestId` on an ordinary first approval. `validUntil` controls the Core request, while `validThrough` limits the App approval used at payment.

| Action | Signing wallet | Additional input |
| --- | --- | --- |
| `evidence` | Source | `commitment` from the relevant installed contract and `evidenceTypeHash` |
| `completion-evidence` | Source | `formId`, `reportRef`, `confirmingAccount` and `evidenceTypeHash`. Prepare separately for the student and coordinator. |
| `object` | Source | `terms`, `validUntil` and the already registered support `evidenceId` |
| `form` | Verifier | `terms`, `validUntil`, `objectId` and `reasonHash` |
| `challengeable`, then `vest` | Verifier | `terms`, `validUntil`, `stateId` and the reason hash for each step |
| `request` | Source | `terms`, `validUntil` and the vested `stateId` |
| `allocate` | Allocator | `terms`, `validUntil` and `requestId` |

Review the intent before signing. Use your own wallet on the indicated chain to send exactly `call.to`, `call.data` and `call.value` from the indicated account. Save the intent beside the transaction hash so the command can check the signed transaction and read the event from the same chain.

```sh
node --import tsx examples/spark-dao/v15/participant-approval-cli.ts \
  .local/spark-v15/participant.json observe intent.json TRANSACTION_HASH
```

Use the returned ID in the next action or in the workbench. After allocation, the Allocator uses **Record payment approval** with the request ID and the original terms. Check the payment record before paying. It should show the approval and the unpaid balance. The designated executor later uses the payment action. Check the actual transfer and the payment receipt separately.
