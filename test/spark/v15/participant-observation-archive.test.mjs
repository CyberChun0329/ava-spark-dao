import assert from 'node:assert/strict';
import { existsSync, mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { hashMessage, keccak256, toHex } from 'viem';
import { fileObservationArchive, prepareObservationArchive, readObservationArchive }
  from '../../../examples/spark-dao/v15/participant-observation-archive-cli.ts';
import { sparkV15 } from '../../../examples/spark-dao/v15/payments.ts';

const hash = digit => `0x${digit.repeat(64)}`;
const address = digit => `0x${digit.repeat(40)}`;
const observationId = hash('1');
const returnId = hash('2');
const verifier = address('1');
const signature = '0x1234';
const verifierAction = keccak256(toHex('spark.action.verify-payment-observation.v1.5'));

function installationFixture(t) {
  const folder = mkdtempSync(join(tmpdir(), 'spark-observation-archive-'));
  t.after(() => rmSync(folder, { recursive: true }));
  const genesis = { number: 0n, hash: hash('d'), timestamp: 1n };
  const prepared = { number: 8n, hash: hash('8'), timestamp: 2_500_000_003n };
  const filed = { number: 9n, hash: hash('9'), timestamp: 2_500_000_004n };
  const state = { latest: prepared, approvedHash: '', authorised: true, archivedAt: 0n, preparationHash: prepared.hash };
  const authorityAddress = address('2');
  const verification = { evidenceId: 17n, evidencePackageId: 3n, verifier: address('4'),
    authorityId: hash('4'), verifiedAt: 2_500_000_002n };
  const transfer = { transactionHash: hash('e'), blockHash: hash('6'), blockNumber: 6n, logIndex: 1n,
    occurredAt: 2_500_000_000n, sender: address('e'), destination: address('f'), amount: 8n };
  const payment = { terms: { obligationId: hash('3'), beneficiary: address('f'), transfer,
    evidenceAvailableAt: 2_500_000_001n, attributionRef: hash('6'), returnDestination: address('e') },
    verification, obligationPackageId: 3n, qualifies: true, afterOriginalExecutionDeadline: false, afterLegalDeadline: false };
  const returned = { terms: { paymentReceiptId: observationId,
    transfer: { ...transfer, transactionHash: hash('f'), sender: address('f'), destination: address('e'), amount: 2n },
    evidenceAvailableAt: 2_500_000_001n, recoveryRef: hash('7') }, verification: { ...verification, evidenceId: 18n } };
  const installation = {
    archivePath: join(folder, 'configured.sqlite'), archiveScope: hash('5'),
    observerAddress: address('a'), paymentsAddress: address('b'), token: address('c'),
    legacyArchive: false,
    client: {
      getChainId: async () => 31337,
      getBlock: async ({ blockNumber }) => blockNumber === 0n ? genesis
        : blockNumber === prepared.number ? { ...prepared, hash: state.preparationHash }
          : blockNumber === filed.number ? filed : state.latest,
      getCode: async () => '0x01',
      readContract: async ({ address, functionName, args }) => functionName === 'isValidSignature'
        && address === verifier && args[0] === state.approvedHash && args[1] === signature ? '0x1626ba7e' : '0xffffffff',
    },
    sdk: {
      deployment: { chainId: 31337 },
      contracts: () => ({ authority: { address: authorityAddress },
        requests: { read: { AUTHORITY_MATRIX: async () => authorityAddress } } }),
      actorContext: async (_client, { account, appId, roleKey, actionKeys }, { blockHash }) => {
        assert.equal(appId, sparkV15.appId);
        assert.equal(roleKey, sparkV15.verifierRole);
        assert.deepEqual(actionKeys, [verifierAction]);
        const allowed = account === verifier && (blockHash !== filed.hash || state.authorised);
        return { authority: allowed ? { roleKey, authorityId: hash('2') } : null,
          permissions: [{ actionKey: actionKeys[0], allowed }] };
      },
    },
    observed: {
      payment: async id => id === observationId ? payment : { verification: { evidenceId: 0n } },
      returned: async id => id === returnId ? returned : { verification: { evidenceId: 0n } },
      archivedAt: async (id, { blockHash }) => id === observationId && blockHash === filed.hash ? state.archivedAt : 0n,
    },
  };
  return { installation, state, prepared, filed, payment };
}

test('the current verifier can sign, file and read one exact verified payment in the configured archive', async t => {
  const { installation, state, filed } = installationFixture(t);
  const prepared = await prepareObservationArchive(installation, 'payment', observationId, verifier, hash('c'));
  assert.equal(prepared.intent.verification.evidenceId, '17');
  assert.equal(prepared.intent.verification.verifier, address('4'));
  assert.equal(prepared.intent.archivedBy, verifier);
  assert.equal(prepared.intent.preparedAt.blockNumber, '8');
  state.approvedHash = hashMessage(prepared.message);
  state.latest = filed;

  const archived = await fileObservationArchive(installation, prepared, signature);
  assert.equal(archived.filingCheckpoint.blockNumber, '9');
  assert.equal(archived.filingCheckpoint.timestamp, '2500000004');
  assert.equal(archived.intent.verification.verifiedAt, '2500000002');
  assert.ok(Number.isFinite(Date.parse(archived.localFiledAt)));
  const readback = await readObservationArchive(installation, 'payment', observationId);
  assert.equal(readback.onchainArchivedAt, '0');
  assert.deepEqual(readback.localArchive, archived);
  await assert.rejects(fileObservationArchive(installation, prepared, signature), /already filed/);
  assert.deepEqual((await readObservationArchive(installation, 'payment', observationId)).localArchive, archived);
});

test('a verified return has its own evidence and archive while the original payment keeps its status', async t => {
  const { installation, state } = installationFixture(t);
  await assert.rejects(prepareObservationArchive(installation, 'return', observationId, verifier, null), /No verified observation/);
  await assert.rejects(prepareObservationArchive(installation, 'payment', returnId, verifier, null), /No verified observation/);
  const prepared = await prepareObservationArchive(installation, 'return', returnId, verifier, null);
  assert.equal(prepared.intent.terms.paymentReceiptId, observationId);
  assert.equal(prepared.intent.verification.evidenceId, '18');
  state.approvedHash = hashMessage(prepared.message);
  const saved = await fileObservationArchive(installation, prepared, signature);
  assert.deepEqual((await readObservationArchive(installation, 'return', returnId)).localArchive, saved);
  assert.equal((await readObservationArchive(installation, 'payment', observationId)).localArchive, null);
});

test('payment lookup shows later qualification and actual returns beside the signed original filing', async t => {
  const { installation, state, filed, payment } = installationFixture(t);
  payment.terms.attributionRef = hash('0');
  payment.qualifies = false;
  const prepared = await prepareObservationArchive(installation, 'payment', observationId, verifier, null);
  state.approvedHash = hashMessage(prepared.message);
  const archived = await fileObservationArchive(installation, prepared, signature);

  installation.supportsSupplementalAttribution = true;
  state.latest = filed;
  payment.qualifies = true;
  const setAt = (evidenceId, verifiedAt) => ({ ...payment.verification, evidenceId, verifiedAt });
  installation.observed.attribution = async (id, point) => {
    assert.equal(id, observationId);
    assert.equal(point.blockHash, filed.hash);
    return { terms: { paymentReceiptId: id, attributionRef: hash('6') }, verification: setAt(19n, 2_500_000_003n) };
  };
  installation.observed.agreedRecipient = async () => ({
    terms: { paymentReceiptId: observationId }, verification: setAt(20n, 2_500_000_004n),
  });
  installation.observed.returnedForReceipt = async () => 2n;
  installation.observed.returnIds = async () => [returnId];
  const record = await readObservationArchive(installation, 'payment', observationId);
  assert.deepEqual(record.localArchive, archived);
  assert.equal(record.verification.verifiedAt, '2500000002');
  assert.equal(record.currentQualification.attribution.verification.verifiedAt, '2500000003');
  assert.equal(record.currentQualification.agreedRecipient.verification.verifiedAt, '2500000004');
  assert.equal(record.currentQualification.qualifiedUnits, '6');
  assert.equal(record.currentQualification.returnedUnits, '2');
  assert.deepEqual(record.currentQualification.returnIds, [returnId]);
});

test('legacy filing after preparation is read back without creating a duplicate local archive', async t => {
  const { installation, state, filed } = installationFixture(t);
  const prepared = await prepareObservationArchive(installation, 'payment', observationId, verifier, null);
  state.approvedHash = hashMessage(prepared.message);
  state.latest = filed;
  state.archivedAt = 2_500_000_004n;
  await assert.rejects(fileObservationArchive(installation, prepared, signature), /already archived on chain/);
  await assert.rejects(prepareObservationArchive(installation, 'payment', observationId, verifier, null), /already archived on chain/);
  const readback = await readObservationArchive(installation, 'payment', observationId);
  assert.equal(readback.onchainArchivedAt, '2500000004');
  assert.equal(readback.localArchive, null);
  assert.equal(existsSync(installation.archivePath), false);
});

test('a deployment that can file on chain can use readback before filing', async t => {
  const { installation } = installationFixture(t);
  installation.legacyArchive = true;
  await assert.rejects(prepareObservationArchive(installation, 'payment', observationId, verifier, null), /files observations on chain/);
  const readback = await readObservationArchive(installation, 'payment', observationId);
  assert.equal(readback.onchainArchivedAt, '0');
  assert.equal(readback.localArchive, null);
  assert.equal(existsSync(installation.archivePath), false);
});

test('filing requires the exact evidence, signature, archive scope and current authority', async t => {
  const { installation, state, filed } = installationFixture(t);
  await assert.rejects(prepareObservationArchive(installation, 'payment', observationId, address('4'), null), /must have permission/);
  const prepared = await prepareObservationArchive(installation, 'payment', observationId, verifier, null);
  state.approvedHash = hashMessage(prepared.message);
  state.latest = filed;
  const altered = structuredClone(prepared);
  altered.intent.verification.evidenceId = '18';
  await assert.rejects(fileObservationArchive(installation, altered, signature), /signature must match/);
  await assert.rejects(fileObservationArchive(installation, prepared, '0x4321'), /signature must match/);
  await assert.rejects(fileObservationArchive({ ...installation, archiveScope: hash('f') }, prepared, signature),
    /signature must match/);
  state.authorised = false;
  await assert.rejects(fileObservationArchive(installation, prepared, signature), /must have permission/);
  assert.equal((await readObservationArchive(installation, 'payment', observationId)).localArchive, null);
});

test('an orphaned preparation is refused while distinct later payment qualification may change', async t => {
  const { installation, state, filed, prepared: original, payment } = installationFixture(t);
  payment.qualifies = false;
  const prepared = await prepareObservationArchive(installation, 'payment', observationId, verifier, null);
  state.approvedHash = hashMessage(prepared.message);
  state.latest = filed;
  state.preparationHash = hash('b');
  await assert.rejects(fileObservationArchive(installation, prepared, signature), /no longer canonical/);
  state.preparationHash = original.hash;
  payment.qualifies = true;
  const results = await Promise.allSettled([
    fileObservationArchive(installation, prepared, signature), fileObservationArchive(installation, prepared, signature),
  ]);
  const stored = results.filter(result => result.status === 'fulfilled');
  assert.equal(stored.length, 1);
  assert.match(results.find(result => result.status === 'rejected').reason.message, /already filed/);
  assert.deepEqual((await readObservationArchive(installation, 'payment', observationId)).localArchive, stored[0].value);
});
