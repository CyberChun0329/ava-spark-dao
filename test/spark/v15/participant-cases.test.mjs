import assert from 'node:assert/strict';
import test from 'node:test';
import { parseAbi, zeroHash } from 'viem';
import { createParticipantCases } from '../../../examples/spark-dao/v15/participant-cases.ts';

const address = digit => `0x${digit.repeat(40)}`;
const hash = digit => `0x${digit.repeat(64)}`;
const account = address('1');
const received = {
  termsId: hash('2'), lessonId: hash('3'), obligationId: hash('4'), reviewRequestedAt: 20n,
  appointmentRequiredAt: 20n, replyCutoff: 50n, reviewCutoff: 60n, firstReplyAt: 0n,
  intake: { raisedBy: address('2'), receiver: account, receivedAt: 20n, evidenceId: 9n },
  acknowledgment: { input: { handler: address('3') }, evidenceId: 0n },
};
const snapshot = { number: 3n, hash: hash('6'), timestamp: 25n };

function inboxFixture({ afterReceipt, reviewAt = 0n, revision = zeroHash }) {
  const intake = { address: address('4') };
  const cases = { address: address('5'), abi: parseAbi([
    'function isAppointedForCase(bytes32, uint8, address, uint64, bool) view returns (bool)',
    'function decidePaymentRevision()',
    'function reviewedPaymentRevision(bytes32) view returns (bytes32)',
  ]) };
  const client = {
    getBlock: async () => snapshot,
    getContractEvents: async ({ eventName }) => {
      assert.equal(eventName, 'ConcernReceived');
      return [{ args: { caseId: hash('7') }, transactionHash: hash('8'), blockNumber: 2n, logIndex: 0 }];
    },
  };
  const reads = {
    getConcern: received,
    getPublishedContacts: { terms: { coordinator: account, namedReviewer: account,
      leadAcademicTutor: address('3'), escalationContact: address('4') } },
    getProgress: [3, 3],
    getCase: { initial: { evidenceId: 0n }, review: {
      input: { disposition: reviewAt === 0n ? 0 : 2, approvalRequestId: 0n, outcome: hash('9') }, decidedAt: reviewAt,
    }, original: { evidenceId: 7n }, adoptionNotice: { sentAt: 0n, referenceHash: zeroHash } },
    reviewedPaymentRevision: revision,
  };
  const course = {
    authority: async () => ({ allowed: new Set(['decide-independent-review', 'adopt-review-correction']) }),
    offer: (operationId, args) => ({ operationId, args }),
    read: async (_contract, functionName, _point, args) => {
      if (functionName === 'isAppointedForCase') {
        if (args[1] !== 2) return false;
        assert.deepEqual(args, [hash('7'), 2, account, snapshot.timestamp, true]);
        return afterReceipt;
      }
      assert.ok(Object.hasOwn(reads, functionName), functionName);
      return reads[functionName];
    },
  };
  return createParticipantCases({ client, modules: { intake, cases, coordinator: hash('a') }, course }).inbox(account);
}

test('an open review offers the typed payment decision only to the reviewer appointed after intake', async () => {
  const active = (await inboxFixture({ afterReceipt: true })).records[0].offers;
  const early = (await inboxFixture({ afterReceipt: false })).records[0].offers;
  assert.deepEqual(active.map(offer => offer.operationId), ['decideReview', 'decidePaymentRevision']);
  assert.deepEqual(early, []);
});

test('a payment case may adopt a change to the record or a typed change to the money', async () => {
  const args = { afterReceipt: true, reviewAt: 24n };
  for (const [revision, expected] of [[zeroHash, 'adoptCorrection'], [hash('9'), 'adoptPaymentRevision']]) {
    const { offers } = (await inboxFixture({ ...args, revision })).records[0];
    assert.deepEqual(offers.map(offer => offer.operationId), [expected]);
  }
});
