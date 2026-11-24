import { closeSync, existsSync, openSync } from 'node:fs';
import { resolve } from 'node:path';
import { DatabaseSync } from 'node:sqlite';
import { pathToFileURL } from 'node:url';
import { isDeepStrictEqual } from 'node:util';
import { jsonValue, withCanonicalSnapshot, type CanonicalSnapshot } from '@ava-protocol/sdk';
import { keccak256, toHex, type Address, type Hex } from 'viem';
import { connectSparkV15PaymentObservations } from './observed-receipts.ts';
import { address, chainIdentity, checkpoint, hash, loadArchiveConfiguration, readJson, readPreparationCheckpoint,
  signedBy } from './participant-material-archive-cli.ts';
import { participantObject } from './participant-payments.ts';
import { sparkV15 } from './payments.ts';

const { appId, workflowKey, verifierRole } = sparkV15;
const domain = 'ava.spark.local.payment-observation-archive.v1';
const filingAction = keccak256(toHex('spark.action.verify-payment-observation.v1.5'));
type ObservationKind = 'payment' | 'return';

function observationKind(value: unknown): ObservationKind {
  if (value !== 'payment' && value !== 'return') throw new Error('Expected observation kind payment or return');
  return value;
}

async function loadInstallation(configPath: string) {
  const { client, sdk, token: configuredToken, profile, archivePath, archiveScope } =
    await loadArchiveConfiguration(configPath, domain);
  const { SparkV15PaymentObservations: observations, SparkV15Payments: payments } = profile.contracts;
  if (!observations || !Array.isArray(observations.abi) || !payments) {
    throw new Error('The payment observation path is missing from the deployment export');
  }
  const observerAddress = address(observations.address);
  const paymentsAddress = address(payments.address);
  const token = address(configuredToken);
  const observed = await connectSparkV15PaymentObservations({
    client, sdk, installation: { payments: paymentsAddress, observations: { ...observations, address: observerAddress }, token },
  });
  const legacyArchive = observations.abi.some(entry => entry.type === 'function' && entry.name === 'archiveObservation');
  const supportsSupplementalAttribution = observations.abi.some(entry =>
    entry.type === 'function' && entry.name === 'getPaymentAttribution');
  return { client, sdk, observed, observerAddress, paymentsAddress, token, archivePath, archiveScope, legacyArchive,
    supportsSupplementalAttribution };
}

type Installation = Awaited<ReturnType<typeof loadInstallation>>;

async function installationIdentity(installation: Installation) {
  const { observerAddress, paymentsAddress, token } = installation;
  return { ...await chainIdentity(installation), observations: observerAddress, payments: paymentsAddress, token };
}

async function observedTransfer({ observed }: Installation, kind: ObservationKind, observationId: Hex,
  { point, timestamp }: CanonicalSnapshot) {
  const [record, onchainArchivedAt] = await Promise.all([
    kind === 'payment' ? observed.payment(observationId, point) : observed.returned(observationId, point),
    observed.archivedAt(observationId, point),
  ]);
  const { terms, verification } = record;
  if (verification.evidenceId === 0n || verification.verifiedAt === 0n || verification.verifiedAt > timestamp) {
    throw new Error('No verified observation of that kind and ID at the checkpoint');
  }
  // Qualification can change later without changing the verified transfer being filed.
  return { terms, verification, onchainArchivedAt, payment: 'qualifies' in record ? record : undefined };
}

async function paymentQualification({ observed }: Installation, observationId: Hex,
  payment: Awaited<ReturnType<Installation['observed']['payment']>>, point: CanonicalSnapshot['point']) {
  const [attribution, agreedRecipient, returnedUnits, returnIds] = await Promise.all([
    observed.attribution(observationId, point),
    observed.agreedRecipient(observationId, point), observed.returnedForReceipt(observationId, point),
    observed.returnIds(observationId, point),
  ]);
  return {
    qualifies: payment.qualifies,
    attribution: attribution.verification.evidenceId === 0n ? null : attribution,
    agreedRecipient: agreedRecipient.verification.evidenceId === 0n ? null : agreedRecipient,
    returnIds, returnedUnits, qualifiedUnits: payment.qualifies ? payment.terms.transfer.amount - returnedUnits : 0n,
  };
}

async function filingBasis(installation: Installation, kind: ObservationKind, observationId: Hex,
  archivedBy: Address, snapshot: CanonicalSnapshot) {
  const { client, sdk } = installation;
  const { point } = snapshot;
  const core = sdk.contracts(client);
  const [fact, actor, authorityMatrix] = await Promise.all([
    observedTransfer(installation, kind, observationId, snapshot),
    sdk.actorContext(client, { appId, account: archivedBy, roleKey: verifierRole, actionKeys: [filingAction] }, point),
    core.requests.read.AUTHORITY_MATRIX(point),
  ]);
  if (fact.onchainArchivedAt !== 0n) throw new Error('Observation was already archived on chain');
  if (installation.legacyArchive) throw new Error('This installation files observations on chain');
  if (authorityMatrix.toLowerCase() !== core.authority.address.toLowerCase()) {
    throw new Error('The chain differs from the exported Spark payment observation installation');
  }
  if (!actor.authority || !actor.permissions[0]?.allowed) {
    throw new Error('The archive signer must have permission to verify payment observations');
  }
  return { observationKind: kind, observationId, terms: fact.terms, verification: fact.verification,
    archivedBy, archiveAuthority: actor.authority };
}

type Identity = Awaited<ReturnType<typeof installationIdentity>>;
type Basis = Awaited<ReturnType<typeof filingBasis>>;

function archiveIntent(installation: Installation, identity: Identity, basis: Basis, snapshot: CanonicalSnapshot,
  localContentHash: Hex | null) {
  return jsonValue({ domain, appId, workflowKey, action: filingAction, installation: identity,
    archiveScope: installation.archiveScope, preparedAt: checkpoint(snapshot), ...basis, localContentHash });
}

export async function prepareObservationArchive(installation: Installation, kind: ObservationKind, observationId: Hex,
  archivedBy: Address, localContentHash: Hex | null) {
  return withCanonicalSnapshot(installation.client, async snapshot => {
    const [identity, basis] = await Promise.all([
      installationIdentity(installation), filingBasis(installation, kind, observationId, archivedBy, snapshot),
    ]);
    const intent = archiveIntent(installation, identity, basis, snapshot, localContentHash);
    return { intent, message: JSON.stringify(intent) };
  });
}

function archiveKey(identity: Identity, observationId: Hex) {
  return [identity.chainId, identity.genesisHash, identity.observations, observationId] as const;
}

export async function fileObservationArchive(installation: Installation, prepared: unknown, signature: Hex) {
  if (!/^0x(?:[0-9a-f]{2})+$/i.test(signature)) throw new Error('Expected a wallet message signature');
  const signed = participantObject(prepared), intent = participantObject(signed.intent);
  const saved = participantObject(intent.preparedAt);
  const kind = observationKind(intent.observationKind), observationId = hash(intent.observationId, 'Observation ID');
  const archivedBy = address(intent.archivedBy);
  const localContentHash = intent.localContentHash === null ? null : hash(intent.localContentHash, 'Local content hash');
  const { client, archivePath } = installation;
  const record = await withCanonicalSnapshot(client, async snapshot => {
    const historical = await readPreparationCheckpoint(client, saved, snapshot);
    const [identity, basis] = await Promise.all([
      installationIdentity(installation), filingBasis(installation, kind, observationId, archivedBy, historical),
    ]);
    const expected = archiveIntent(installation, identity, basis, historical, localContentHash);
    const message = JSON.stringify(expected);
    if (!isDeepStrictEqual(intent, expected) || signed.message !== message
      || !await signedBy(client, archivedBy, message, signature, snapshot)) {
      throw new Error('The verifier signature must match the prepared filing');
    }
    const current = historical.blockHash === snapshot.blockHash ? basis
      : await filingBasis(installation, kind, observationId, archivedBy, snapshot);
    if (!isDeepStrictEqual(current, basis)) throw new Error('The observation or verifier authority differs from preparation');
    return { identity, intent: expected, filingCheckpoint: checkpoint(snapshot) };
  });

  closeSync(openSync(archivePath, 'a', 0o600));
  const db = new DatabaseSync(archivePath, { timeout: 5000 });
  try {
    db.exec(`CREATE TABLE IF NOT EXISTS payment_observation_archive (
      chain_id INTEGER NOT NULL, genesis_hash TEXT NOT NULL, observations TEXT NOT NULL, observation_id TEXT NOT NULL,
      record TEXT NOT NULL, PRIMARY KEY (chain_id, genesis_hash, observations, observation_id)
    ) STRICT`);
    const { identity, ...payload } = record;
    const archive = jsonValue({ ...payload, signature, localFiledAt: new Date().toISOString() });
    const inserted = db.prepare(`INSERT INTO payment_observation_archive VALUES (?, ?, ?, ?, ?)
      ON CONFLICT (chain_id, genesis_hash, observations, observation_id) DO NOTHING`).run(
      ...archiveKey(identity, observationId), JSON.stringify(archive));
    if (inserted.changes === 0) throw new Error('Observation was already filed in this archive');
    return archive;
  } finally {
    db.close();
  }
}

function readLocalArchive(archivePath: string, identity: Identity, observationId: Hex) {
  if (!existsSync(archivePath)) return null;
  const db = new DatabaseSync(archivePath, { readOnly: true });
  try {
    const table = db.prepare("SELECT name FROM sqlite_schema WHERE type = 'table' AND name = 'payment_observation_archive'").get();
    if (!table) return null;
    const row = db.prepare(`SELECT record FROM payment_observation_archive
      WHERE chain_id = ? AND genesis_hash = ? AND observations = ? AND observation_id = ?`).get(
      ...archiveKey(identity, observationId));
    return row ? JSON.parse(row.record as string) as unknown : null;
  } finally {
    db.close();
  }
}

export async function readObservationArchive(installation: Installation, kind: ObservationKind, observationId: Hex) {
  const { identity, ...record } = await withCanonicalSnapshot(installation.client, async snapshot => {
    const [identity, { payment, ...fact }] = await Promise.all([
      installationIdentity(installation), observedTransfer(installation, kind, observationId, snapshot),
    ]);
    const currentQualification = payment && installation.supportsSupplementalAttribution
      ? await paymentQualification(installation, observationId, payment, snapshot.point)
      : undefined;
    return { identity, observationKind: kind, observationId, ...fact, currentQualification,
      checkpoint: checkpoint(snapshot) };
  });
  return jsonValue({ installation: identity, ...record,
    localArchive: readLocalArchive(installation.archivePath, identity, observationId) });
}

const usage = `Usage: node --import tsx examples/spark-dao/v15/participant-observation-archive-cli.ts <participant.json> <command>
  prepare <payment|return> <observation-id> <verifier> [<local-content-hash>]
  file <prepared.json> <signature>
  read <payment|return> <observation-id>

Set storage.materialArchivePath to the installation's existing local archive database.
Save the prepare output and personal-sign its exact UTF-8 message string with an authorised verifier's wallet.`;

async function run(args: string[]) {
  if (args.length === 1 && args[0] === '--help') return console.log(usage);
  const [configPath, command, first, second, third, fourth, ...extra] = args;
  if (!configPath || !first || !second || extra.length || !((command === 'prepare' && third)
    || ((command === 'file' || command === 'read') && !third && !fourth))) throw new Error(usage);
  const installation = await loadInstallation(resolve(configPath));
  const result = command === 'file'
    ? await fileObservationArchive(installation, await readJson(first), second.toLowerCase() as Hex)
    : command === 'prepare'
      ? await prepareObservationArchive(installation, observationKind(first), hash(second, 'Observation ID'), address(third),
        fourth ? hash(fourth, 'Local content hash') : null)
      : await readObservationArchive(installation, observationKind(first), hash(second, 'Observation ID'));
  console.log(JSON.stringify(result, null, 2));
}

if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try {
    await run(process.argv.slice(2));
  } catch (error) {
    console.error(error instanceof Error ? error.message : 'Spark payment observation archive operation failed');
    process.exitCode = 1;
  }
}
