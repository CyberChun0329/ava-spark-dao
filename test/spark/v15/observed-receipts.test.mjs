import assert from 'node:assert/strict';
import test from 'node:test';
import { createPublicClient, custom, encodeAbiParameters, encodeEventTopics, parseAbi, toHex, zeroHash } from 'viem';
import { connectSparkV15PaymentObservations }
  from '../../../examples/spark-dao/v15/observed-receipts.ts';
import { sparkV15 } from '../../../examples/spark-dao/v15/payments.ts';

const hash = digit => `0x${digit.repeat(64)}`;
const address = digit => `0x${digit.repeat(40)}`;
const paymentReceiptId = hash('1');
const payments = address('a'), observer = address('b'), token = address('c'), requests = address('d');
const beforeAdoption = { number: 10n, hash: hash('a'), timestamp: 1010n };
const adoption = { number: 11n, hash: hash('b'), timestamp: 1011n };
const snapshot = { number: 15n, hash: hash('f'), timestamp: 1015n };
const findings = { paymentReceiptId, actualExecutor: address('1'), namedExecutor: address('2'),
  approvalRequestId: 3n, applicableDeadline: 1000n, approvalCoverage: 1, heldAtExecution: 2,
  paidByDeadline: 1, fullyPaidByDeadline: 1, executorEvidenceRef: hash('5'), approvalEvidenceRef: hash('6'),
  holdEvidenceRef: hash('7'), deadlineEvidenceRef: hash('8') };
const verification = { evidenceId: 12n, evidencePackageId: 9n, verifier: address('4'), authorityId: hash('9'),
  verifiedAt: adoption.timestamp };
const assessment = { findings, verification };
const assessmentLog = { address: observer, blockNumber: adoption.number, blockHash: adoption.hash,
  transactionHash: hash('e'), logIndex: 1, removed: false, args: { paymentReceiptId, ...assessment } };

function fixture(legacy = false, decodeEvents) {
  const blocks = [beforeAdoption, adoption, snapshot];
  const abi = parseAbi([
    'struct Findings { bytes32 paymentReceiptId; address actualExecutor; address namedExecutor; uint256 approvalRequestId; uint64 applicableDeadline; uint8 approvalCoverage; uint8 heldAtExecution; uint8 paidByDeadline; uint8 fullyPaidByDeadline; bytes32 executorEvidenceRef; bytes32 approvalEvidenceRef; bytes32 holdEvidenceRef; bytes32 deadlineEvidenceRef; }',
    'struct Verification { uint256 evidenceId; uint256 evidencePackageId; address verifier; bytes32 authorityId; uint64 verifiedAt; }',
    ...(legacy ? ['function executionAssessment(bytes32) view returns ((Findings findings, Verification verification))']
      : ['function executionAssessmentBlock(bytes32) view returns (uint256)',
        'event PaymentExecutionAssessed(bytes32 indexed paymentReceiptId, Findings findings, Verification verification)']),
  ]);
  const sdk = { deployment: { chainId: 31337, addresses: { requests } } };
  const installation = { payments, observations: { address: observer, abi }, token };
  const state = { logs: [assessmentLog], afterLogs: () => {} };
  const client = {
    getChainId: async () => 31337,
    getBlock: async ({ blockHash, blockNumber, blockTag }) => {
      if (blockTag === 'latest') return blocks.at(-1);
      const result = blocks.find(block => block.hash === blockHash || block.number === blockNumber);
      assert.ok(result, 'block lookup must refer to a known block');
      return result;
    },
    readContract: async ({ address: emitter, functionName, args, blockHash, requireCanonical }) => {
      const block = blocks.find(block => block.hash === blockHash);
      assert.ok(block, 'contract reads must use the selected canonical block');
      assert.equal(requireCanonical, true);
      switch (functionName) {
        case 'paymentObservations': return observer;
        case 'PAYMENTS': return payments;
        case 'TOKEN': return token;
        case 'REQUEST_ALLOCATION': return requests;
        case 'WORKFLOW': return sparkV15.workflowKey;
        case 'VERIFIER_ROLE': return sparkV15.verifierRole;
        case 'executionAssessment':
          assert.ok(legacy, 'the legacy getter is available only on the legacy installation');
          assert.deepEqual(args, [paymentReceiptId]);
          assert.equal(emitter, observer);
          return assessment;
        case 'executionAssessmentBlock':
          assert.ok(!legacy, 'the adoption marker is available only on the new installation');
          assert.deepEqual(args, [paymentReceiptId]);
          assert.equal(emitter, observer);
          return block.number >= adoption.number ? adoption.number : 0n;
        default: assert.fail(`unexpected contract read ${functionName}`);
      }
    },
    getContractEvents: async filter => {
      assert.ok(!legacy, 'the legacy installation reads its stored assessment');
      assert.equal(filter.address, observer);
      assert.equal(filter.blockHash, adoption.hash);
      assert.equal(filter.eventName, 'PaymentExecutionAssessed');
      assert.deepEqual(filter.args, { paymentReceiptId });
      assert.equal(filter.strict, true);
      state.afterLogs();
      return decodeEvents ? decodeEvents(filter) : state.logs;
    },
  };
  return { connect: () => connectSparkV15PaymentObservations({ client, sdk, installation }), state, blocks };
}

test('legacy observers read the full stored execution assessment at the requested checkpoint', async () => {
  const observed = await fixture(true).connect();
  assert.deepEqual(await observed.execution(paymentReceiptId, { blockHash: snapshot.hash, requireCanonical: true }),
    assessment);
});

test('new observers return exact receipt findings and verification only after adoption', async () => {
  const observed = await fixture(false, filter => {
    const event = filter.abi.find(item => item.type === 'event' && item.name === filter.eventName);
    const topics = encodeEventTopics({ abi: [event], eventName: event.name, args: { paymentReceiptId } });
    const data = encodeAbiParameters(event.inputs.filter(input => !input.indexed), [findings, verification]);
    const client = createPublicClient({
      transport: custom({
        request: async ({ method, params }) => {
          assert.equal(method, 'eth_getLogs');
          assert.deepEqual(params, [{ address: observer, blockHash: adoption.hash, topics }]);
          return [{ address: observer, data, topics, blockHash: adoption.hash, blockNumber: toHex(adoption.number),
            transactionHash: assessmentLog.transactionHash, transactionIndex: '0x0', logIndex: '0x1', removed: false }];
        },
      }),
    });
    return client.getContractEvents(filter);
  }).connect();
  const earlier = await observed.execution(paymentReceiptId, beforeAdoption.number);
  assert.equal(earlier.verification.evidenceId, 0n);
  assert.equal(earlier.findings.paymentReceiptId, zeroHash);
  assert.deepEqual(await observed.execution(paymentReceiptId, { blockHash: snapshot.hash, requireCanonical: true }),
    assessment);
});

test('an adopted assessment with unavailable or inconsistent logs fails the audit read', async () => {
  const { connect, state } = fixture();
  const observed = await connect();
  state.logs = [];
  await assert.rejects(observed.execution(paymentReceiptId), { code: 'event_missing' });
  state.logs = [assessmentLog, assessmentLog];
  await assert.rejects(observed.execution(paymentReceiptId), { code: 'event_ambiguous' });
  state.logs = [{ ...assessmentLog, args: { ...assessmentLog.args, findings: { ...findings, paymentReceiptId: hash('2') } } }];
  await assert.rejects(observed.execution(paymentReceiptId), { code: 'receipt_mismatch' });
});

test('a checkpoint that changes canonical branch during lookup cannot return an assessment', async () => {
  const { connect, state, blocks } = fixture();
  const observed = await connect();
  state.afterLogs = () => { blocks[2] = { ...snapshot, hash: hash('0') }; };
  await assert.rejects(observed.execution(paymentReceiptId), { code: 'orphaned' });
});
