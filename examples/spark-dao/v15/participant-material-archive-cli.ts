import { isDeepStrictEqual } from 'node:util';
import { closeSync, openSync } from 'node:fs';
import { readFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { DatabaseSync } from 'node:sqlite';
import { pathToFileURL } from 'node:url';
import { AvaSdk, jsonValue, localClient, withCanonicalSnapshot, type CanonicalSnapshot } from '@ava-protocol/sdk';
import type { PublicDeployment } from '@ava-protocol/sdk/deployment';
import { decodeAbiParameters, encodeFunctionData, hashMessage, keccak256, parseAbi, parseAbiParameters, recoverMessageAddress,
  size, toHex, zeroHash, type Address, type Hex } from 'viem';
import { participantAddress, participantHash, participantObject } from './participant-payments.ts';
import { sparkV15 } from './payments.ts';

const { appId, workflowKey } = sparkV15;
const domain = 'ava.spark.local.material-receipt-archive.v1';
const filingAction = keccak256(toHex('spark.action.file-material-receipt.v1.5'));
const same = (a: unknown, b: string) => typeof a === 'string' && a.toLowerCase() === b.toLowerCase();
const readJson = async (path: string): Promise<unknown> => JSON.parse(await readFile(path, 'utf8'));
const receiptSelector = parseAbi(['function getMaterialReceipt(uint256 receiptId) view']);
const receiptFields = parseAbiParameters('bytes32, uint64, uint64, uint256, address');
const legacyReceiptFields = parseAbiParameters('bytes32, uint64, uint64, uint64, uint256, address');
const contractWallet = parseAbi(['function isValidSignature(bytes32 hash, bytes signature) view returns (bytes4)']);

function hash(value: unknown, label: string): Hex {
  if (!participantHash(value) || same(value, zeroHash)) throw new Error(`${label} must be a nonzero bytes32`);
  return value.toLowerCase() as Hex;
}

function address(value: unknown): Address {
  return participantAddress(value).toLowerCase() as Address;
}

function uint(value: unknown, label: string, allowZero = false): bigint {
  if (typeof value === 'string' && /^(0|[1-9][0-9]{0,77})$/.test(value)) {
    const number = BigInt(value);
    if ((allowZero || number > 0n) && number < 1n << 256n) return number;
  }
  throw new Error(`${label} must be a ${allowZero ? 'nonnegative' : 'positive'} decimal uint256 string`);
}

async function loadArchiveConfiguration(configPath: string, archiveDomain: string) {
  const config = participantObject(await readJson(configPath));
  if (typeof config.rpcUrl !== 'string' || typeof config.deploymentPath !== 'string' || !config.deploymentPath.trim()) {
    throw new Error('The participant configuration needs rpcUrl and deploymentPath');
  }
  const rpc = new URL(config.rpcUrl);
  if (rpc.protocol !== 'http:' || rpc.hostname !== '127.0.0.1' || rpc.username || rpc.password
    || rpc.pathname !== '/' || rpc.search || rpc.hash) throw new Error('Use an HTTP loopback origin');

  const directory = dirname(configPath);
  const storage = config.storage === undefined ? {} : participantObject(config.storage);
  if (typeof storage.materialArchivePath !== 'string' || !storage.materialArchivePath.trim()) {
    throw new Error('Configure storage.materialArchivePath in participant.json');
  }
  const archivePath = resolve(directory, storage.materialArchivePath);
  if (typeof storage.databasePath === 'string' && archivePath === resolve(directory, storage.databasePath)) {
    throw new Error('Configure a separate archive database in storage.materialArchivePath');
  }
  const requestAudience = hash(config.requestAudience, 'Local installation request audience');
  const archiveScope = keccak256(toHex(JSON.stringify([archiveDomain, requestAudience, archivePath])));
  const declaration = await readJson(resolve(directory, config.deploymentPath)) as PublicDeployment;
  const profile = declaration.workflows?.[appId]?.[workflowKey] ?? declaration.apps?.[appId];
  if (declaration.schemaVersion !== 1 || declaration.deployment?.chainId !== 31337
    || !profile || !same(profile.appId, appId) || !same(profile.workflowKey, workflowKey)) {
    throw new Error('Expected the exported local Spark v1.5 deployment');
  }
  return { client: localClient(rpc.origin), sdk: new AvaSdk(declaration.deployment),
    token: config.token, profile, archivePath, archiveScope };
}

async function loadInstallation(configPath: string) {
  const { client, sdk, profile, archivePath, archiveScope } = await loadArchiveConfiguration(configPath, domain);
  const { SparkV15MaterialProvisions: provisions, SparkV15Materials: materials,
    SparkV15Booking: booking, SparkV15Payments: payments, SparkV15Funds: funds } = profile.contracts;
  for (const contract of [provisions, materials, booking, payments, funds]) {
    if (!contract || !Array.isArray(contract.abi)) throw new Error('The materials path is missing from the deployment export');
    participantAddress(contract.address);
  }
  return { client, sdk, provisions, materials, booking, payments, funds, archivePath, archiveScope };
}

type Installation = Awaited<ReturnType<typeof loadInstallation>>;
type PaymentReceipt = { obligationId: Hex; approvalRequestId: bigint; executor: Address; recipient: Address;
  creditAccount: Hex; amount: bigint; approvedOutstandingBefore: bigint; paidAt: bigint; promptCutoff: bigint; promptCutoffMet: boolean };

async function chainIdentity({ client, sdk }: Pick<Installation, 'client' | 'sdk'>) {
  const [chainId, genesis] = await Promise.all([client.getChainId(), client.getBlock({ blockNumber: 0n })]);
  if (chainId !== sdk.deployment.chainId) throw new Error('The chain differs from the deployment export');
  return { chainId, genesisHash: hash(genesis.hash, 'Genesis hash') };
}

async function installationIdentity(installation: Installation) {
  return { ...await chainIdentity(installation), provisions: address(installation.provisions.address) };
}

async function readVerification({ client, provisions }: Installation, receiptId: bigint, { point }: CanonicalSnapshot) {
  // The selector is unchanged. Check return length so even a stale export cannot hide legacy filedAt.
  const { data } = await client.call({ to: provisions.address, data: encodeFunctionData({
    abi: receiptSelector, functionName: 'getMaterialReceipt', args: [receiptId],
  }), ...point });
  if (data && size(data) === 6 * 32) {
    const [, , , filedAt] = decodeAbiParameters(legacyReceiptFields, data);
    if (filedAt !== 0n) throw new Error('Material receipt was filed on chain');
    throw new Error('This legacy installation files material receipts on chain');
  }
  if (!data || size(data) !== 5 * 32) throw new Error('Unexpected material receipt response');
  const [obligationId, paidAt, verifiedAt, evidenceId, verifiedBy] = decodeAbiParameters(receiptFields, data);
  return { obligationId, paidAt, verifiedAt, evidenceId, verifiedBy };
}

async function filingBasis(installation: Installation, receiptId: bigint, coordinator: Address, snapshot: CanonicalSnapshot) {
  const { client, sdk, provisions, materials, booking, payments, funds } = installation;
  const { point } = snapshot;
  const core = sdk.contracts(client);
  const links = [
    [provisions, 'MATERIALS', materials.address], [provisions, 'PAYMENTS', payments.address],
    [provisions, 'BOOKING', booking.address], [provisions, 'FUNDS', funds.address],
    [funds, 'materialProvisions', provisions.address], [booking, 'REQUEST_ALLOCATION', core.requests.address],
    [booking, 'WORKFLOW', workflowKey], [provisions, 'ACTION_FILE_MATERIAL_RECEIPT', filingAction],
  ] as const;
  const [verified, payment, roleKey, authorityMatrix, ...linked] = await Promise.all([
    readVerification(installation, receiptId, snapshot),
    client.readContract({ ...payments, functionName: 'getReceipt', args: [receiptId], ...point }) as Promise<PaymentReceipt>,
    client.readContract({ ...booking, functionName: 'COORDINATOR_ROLE', ...point }),
    core.requests.read.AUTHORITY_MATRIX(point),
    ...links.map(async ([contract, functionName, expected]) =>
      same(await client.readContract({ ...contract, functionName, ...point }), expected)),
  ]);
  if (!linked.every(Boolean) || !same(authorityMatrix, core.authority.address)) {
    throw new Error('The chain differs from the exported Spark materials installation');
  }
  if (verified.verifiedAt === 0n || verified.verifiedAt > snapshot.timestamp || verified.evidenceId === 0n
    || payment.paidAt === 0n || payment.paidAt > verified.verifiedAt || payment.paidAt !== verified.paidAt
    || payment.amount === 0n || !same(payment.obligationId, verified.obligationId) || !same(payment.creditAccount, zeroHash)) {
    throw new Error('Expected a verified material receipt for an actual payment');
  }
  const obligationId = hash(verified.obligationId, 'Obligation ID');
  const [entitlement, obligation] = await Promise.all([
    client.readContract({ ...provisions, functionName: 'getEntitlement', args: [obligationId], ...point }) as
      Promise<{ input: { scopeId: Hex } }>,
    client.readContract({ ...payments, functionName: 'getObligation', args: [obligationId], ...point }) as
      Promise<{ packageId: bigint; terms: { lessonId: Hex } }>,
  ]);
  const scopeId = hash(entitlement.input.scopeId, 'Material scope ID');
  const scope = await client.readContract({ ...materials, functionName: 'getChargeScope', args: [scopeId], ...point }) as
    { lessonId: Hex; recordedAt: bigint };
  const lessonId = hash(scope.lessonId, 'Lesson ID');
  const [lesson, actor] = await Promise.all([
    client.readContract({ ...booking, functionName: 'getLesson', args: [lessonId], ...point }) as
      Promise<{ packageId: bigint; terms: { coordinator: Address } }>,
    sdk.actorContext(client, { appId, account: coordinator, roleKey: hash(roleKey, 'Coordinator role'),
      actionKeys: [filingAction] }, point),
  ]);
  if (scope.recordedAt === 0n || !same(obligation.terms.lessonId, lessonId)
    || lesson.packageId === 0n || lesson.packageId !== obligation.packageId) {
    throw new Error('The receipt and obligation must belong to the same booked lesson');
  }
  if (!same(lesson.terms.coordinator, coordinator) || !actor.authority || !actor.permissions[0]?.allowed) {
    throw new Error('The recorded lesson coordinator must have permission to file material receipts');
  }
  return { receiptId, obligationId, scopeId, lessonId, packageId: lesson.packageId,
    verification: { verifiedAt: verified.verifiedAt, evidenceId: verified.evidenceId, verifiedBy: address(verified.verifiedBy) },
    payment, coordinator, ...actor.authority };
}

function checkpoint({ blockHash, blockNumber, timestamp }: CanonicalSnapshot) {
  return { blockNumber, blockHash, timestamp };
}

async function readPreparationCheckpoint(client: Installation['client'], saved: Record<string, unknown>,
  filing: CanonicalSnapshot): Promise<CanonicalSnapshot> {
  const blockNumber = uint(saved.blockNumber, 'Preparation block number', true);
  const blockHash = hash(saved.blockHash, 'Preparation block hash');
  if (blockNumber > filing.blockNumber) throw new Error('Preparation block is newer than the filing checkpoint');
  const block = await client.getBlock({ blockNumber });
  if (!same(block.hash, blockHash) || saved.timestamp !== block.timestamp.toString()) {
    throw new Error('The preparation block is no longer canonical');
  }
  return { blockNumber, blockHash, timestamp: block.timestamp, point: { blockHash, requireCanonical: true } };
}

async function signedBy(client: Installation['client'], account: Address, message: string, signature: Hex,
  snapshot: CanonicalSnapshot) {
  const code = await client.getCode({ address: account, blockNumber: snapshot.blockNumber });
  if (!code || code === '0x') return size(signature) === 65
    && same(await recoverMessageAddress({ message, signature }), account);
  const magic = await client.readContract({ address: account, abi: contractWallet, functionName: 'isValidSignature',
    args: [hashMessage(message), signature], ...snapshot.point });
  return magic === '0x1626ba7e';
}

async function prepare(installation: Installation, receiptId: bigint, coordinator: Address, localContentHash: Hex | null) {
  return withCanonicalSnapshot(installation.client, async snapshot => {
    const [identity, basis] = await Promise.all([
      installationIdentity(installation), filingBasis(installation, receiptId, coordinator, snapshot),
    ]);
    const intent = jsonValue({ domain, appId, workflowKey, action: filingAction, installation: identity,
      archiveScope: installation.archiveScope,
      preparedAt: checkpoint(snapshot), ...basis, localContentHash });
    return { intent, message: JSON.stringify(intent) };
  });
}

async function file(installation: Installation, databasePath: string, prepared: Record<string, unknown>, signature: Hex) {
  const intent = participantObject(prepared.intent), saved = participantObject(intent.preparedAt);
  const receiptId = uint(intent.receiptId, 'Receipt ID'), coordinator = address(intent.coordinator);
  const localContentHash = intent.localContentHash === null ? null : hash(intent.localContentHash, 'Local content hash');
  const { client } = installation;
  const record = await withCanonicalSnapshot(client, async snapshot => {
    const historical = await readPreparationCheckpoint(client, saved, snapshot);
    const [identity, basis] = await Promise.all([
      installationIdentity(installation), filingBasis(installation, receiptId, coordinator, historical),
    ]);
    const expected = jsonValue({ domain, appId, workflowKey, action: filingAction, installation: identity,
      archiveScope: installation.archiveScope,
      preparedAt: checkpoint(historical), ...basis, localContentHash });
    const message = JSON.stringify(expected);
    if (!isDeepStrictEqual(intent, expected) || prepared.message !== message
      || !await signedBy(client, coordinator, message, signature, snapshot)) {
      throw new Error('The coordinator signature must match the prepared filing');
    }
    const current = historical.blockHash === snapshot.blockHash ? basis
      : await filingBasis(installation, receiptId, coordinator, snapshot);
    if (!isDeepStrictEqual(current, basis)) throw new Error('The material receipt or coordinator authority differs from preparation');
    return { identity, payload: { intent: expected, signature, filingCheckpoint: checkpoint(snapshot) } };
  });

  closeSync(openSync(databasePath, 'a', 0o600));
  const db = new DatabaseSync(databasePath, { timeout: 5000 });
  try {
    db.exec(`CREATE TABLE IF NOT EXISTS material_receipt_archive (
      chain_id INTEGER NOT NULL, genesis_hash TEXT NOT NULL, provisions TEXT NOT NULL, receipt_id TEXT NOT NULL,
      record TEXT NOT NULL, PRIMARY KEY (chain_id, genesis_hash, provisions, receipt_id)
    ) STRICT`);
    const receipt = jsonValue({ ...record.payload, filedAt: new Date().toISOString() });
    const { chainId, genesisHash, provisions } = record.identity;
    // A single atomic insert preserves the original under concurrent or repeated filing.
    const inserted = db.prepare(`INSERT INTO material_receipt_archive VALUES (?, ?, ?, ?, ?)
      ON CONFLICT (chain_id, genesis_hash, provisions, receipt_id) DO NOTHING`).run(
      chainId, genesisHash, provisions, receiptId.toString(), JSON.stringify(receipt));
    if (inserted.changes === 0) throw new Error('Material receipt was already filed in this archive');
    return receipt;
  } finally {
    db.close();
  }
}

export { address, chainIdentity, checkpoint, hash, loadArchiveConfiguration, readJson, readPreparationCheckpoint, signedBy };

async function read(installation: Installation, databasePath: string, receiptId: bigint) {
  const { chainId, genesisHash, provisions } = await installationIdentity(installation);
  const db = new DatabaseSync(databasePath, { readOnly: true });
  try {
    const row = db.prepare(`SELECT record FROM material_receipt_archive
      WHERE chain_id = ? AND genesis_hash = ? AND provisions = ? AND receipt_id = ?`).get(
      chainId, genesisHash, provisions, receiptId.toString());
    if (!row) throw new Error('Material receipt is absent from this archive');
    return JSON.parse(row.record as string) as unknown;
  } finally {
    db.close();
  }
}

const usage = `Usage: node --import tsx examples/spark-dao/v15/participant-material-archive-cli.ts <participant.json> <command>
  prepare <receipt-id> <coordinator> [<local-content-hash>]
  file <prepared.json> <signature>
  read <receipt-id>

Save the prepare output and personal-sign its exact UTF-8 message string with the recorded coordinator's wallet.
Set storage.materialArchivePath in participant.json to the installation's separate local archive database.
The optional content hash is a local reference.`;

async function run(args: string[]) {
  if (args.length === 1 && args[0] === '--help') return console.log(usage);
  const [configPath, command, first, second, third, ...extra] = args;
  if (!configPath || !first || extra.length || !((command === 'prepare' && second)
    || (command === 'file' && second && !third) || (command === 'read' && !second && !third))) throw new Error(usage);
  const installation = await loadInstallation(resolve(configPath));
  let result: unknown;
  if (command === 'prepare') {
    result = await prepare(installation, uint(first, 'Receipt ID'), address(second), third ? hash(third, 'Local content hash') : null);
  } else {
    const { archivePath } = installation;
    if (command === 'file') {
      if (!/^0x(?:[0-9a-f]{2})+$/i.test(second)) throw new Error('Expected a wallet message signature');
      result = await file(installation, archivePath, participantObject(await readJson(first)), second.toLowerCase() as Hex);
    } else {
      result = await read(installation, archivePath, uint(first, 'Receipt ID'));
    }
  }
  console.log(JSON.stringify(result, null, 2));
}

if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try {
    await run(process.argv.slice(2));
  } catch (error) {
    console.error(error instanceof Error ? error.message : 'Spark material receipt archive operation failed');
    process.exitCode = 1;
  }
}
