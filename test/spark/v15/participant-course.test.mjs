import assert from 'node:assert/strict';
import test from 'node:test';
import { AvaSigningError } from '@ava-protocol/sdk';
import { parseAbi, zeroAddress, zeroHash } from 'viem';
import { createParticipantCourse } from '../../../examples/spark-dao/v15/participant-course.ts';
import { sparkV15 } from '../../../examples/spark-dao/v15/payments.ts';

const hash = digit => `0x${digit.repeat(64)}`;
const address = digit => `0x${digit.repeat(40)}`;
const lessonId = hash('1');
const installation = hash('2');
const block = { number: 4n, hash: hash('3'), timestamp: 150n };

function fixture({ supportsLateNotices = true, verified = true, startPermission = 3 } = {}) {
  const settlement = { address: address('1'), abi: parseAbi([
    'struct Seat { uint8 disposition; }',
    'struct Assessment { uint8 route; Seat[] seats; }',
    'function approveOrdinaryGroup(bytes32 lessonId, Assessment assessment)',
  ]) };
  const earlyStart = { address: address('2'), abi: supportsLateNotices
    ? parseAbi(['function hasUsableLateOpeningNotices(bytes32) view returns (bool)']) : [] };
  const booking = { address: address('3'), abi: [] };
  const intake = { address: address('4'), abi: [] };
  const reads = [];
  const preview = { totalTutorPay: 8n };
  const client = {
    getBlock: async () => block,
    readContract: async ({ functionName, blockHash, requireCanonical, args }) => {
      assert.equal(blockHash, block.hash);
      assert.equal(requireCanonical, true);
      reads.push(functionName);
      if (functionName === 'getTeaching') return { startPermission, startedAt: 100n, endedAt: 130n };
      if (functionName === 'hasUsableLateOpeningNotices') {
        assert.deepEqual(args, [lessonId]);
        return verified;
      }
      if (functionName === 'previewOrdinaryGroup') return preview;
      assert.fail(functionName);
    },
  };
  const course = createParticipantCourse({
    client, sdk: { deployment: { chainId: 31337 } }, modules: { booking, settlement, earlyStart, intake },
    genesisHash: hash('4'), installationHash: installation, packageId: 1n, previewLifetime: 60,
  });
  return {
    reads, preview, quote: () => course.quote({
      account: address('5'), appId: sparkV15.appId, workflowKey: sparkV15.workflowKey, operationId: 'approveOrdinaryGroup',
      input: { installation, requestedAt: Math.floor(Date.now() / 1000),
        arguments: { lessonId, assessment: { route: '2', seats: [{ disposition: '1' }] } } },
    }),
  };
}

test('ordinary settlement reads the later independent determination at the same pinned block', async () => {
  const example = fixture();
  assert.deepEqual(await example.quote(), example.preview);
  assert.deepEqual(example.reads, ['getTeaching', 'hasUsableLateOpeningNotices', 'previewOrdinaryGroup']);
});

test('absence of later verification retains the original workbench boundary', async () => {
  for (const options of [{ verified: false }, { supportsLateNotices: false }, { startPermission: 2 }]) {
    const example = fixture(options);
    await assert.rejects(example.quote(), { code: 'operation_not_available' });
    assert.ok(!example.reads.includes('previewOrdinaryGroup'));
  }
});

test('booking offers use the live funding check even though the original reserve record is retained', async () => {
  const coordinator = address('6'), customer = address('7'), formId = hash('6');
  const modules = {
    booking: { address: address('1'), abi: parseAbi([
      'function publishLesson()', 'function acceptForm(bytes32 formId, uint8 role)', 'function confirmPlace(bytes32 formId)',
    ]) },
    settlement: { address: address('2'), abi: [] },
    intake: { address: address('3'), abi: [] },
    funds: { address: address('4'), abi: [] },
    prefunding: { address: address('5'), abi: parseAbi(['function requireCommitmentFunding(bytes32, bytes32) view']) },
    coordinator: hash('7'), provider: hash('8'),
  };
  const snapshot = { point: { blockHash: block.hash, requireCanonical: true }, blockHash: block.hash,
    blockNumber: block.number, timestamp: block.timestamp };
  const form = { version: 1n, terms: { placeId: hash('9'), customer, student: customer, payer: customer,
    customerRepresentative: zeroAddress, payableFee: 20n }, confirmation: { confirmedAt: 0n } };
  const reads = {
    getLesson: { packageId: 1n, terms: { coordinator, provider: address('8'), tutor: address('9'), startsAt: 180n,
      endsAt: 200n, rosterLockAt: 0n, rosterRef: zeroHash, materialsTermsRef: zeroHash },
    prefunding: { evidenceId: 9n, reservedUnits: 58n } },
    getForm: form, getTeaching: { startedAt: 0n, endedAt: 0n, startPermission: 0 }, getRosterLock: { lockedAt: 0n },
    getTutorNotice: { evidenceId: 1n }, getPlannedForms: [formId], getGroupSettlement: { complete: false },
    termsProvisionEvidence: 1n, getStudentNotice: { evidenceId: 1n }, getAttendance: { reportedAt: 0n },
    getServiceFeedback: { evidenceId: 0n },
  };
  for (const [account, funded, usable] of [
    [customer, true, undefined],
    [customer, false, undefined],
    [coordinator, true, undefined],
    [coordinator, false, undefined],
    [customer, true, false],
    [coordinator, true, false],
    [coordinator, true, true],
  ]) {
    const usableTerms = usable === undefined ? undefined : { address: address('a'), abi: [] };
    const provisionReads = [];
    const client = {
      getContractEvents: async request => request.address === modules.booking.address ? [
        { eventName: 'LessonPublished', args: { lessonId }, transactionHash: hash('b') },
        { eventName: 'FormPublished', args: { lessonId, placeId: form.terms.placeId, formId } },
      ] : [],
      readContract: async ({ functionName, args, blockHash, requireCanonical }) => {
        assert.equal(blockHash, block.hash);
        assert.equal(requireCanonical, true);
        if (functionName === 'termsProvisionEvidence') provisionReads.push(args[1]);
        if (functionName === 'hasUsableCustomerTerms') return usable;
        if (functionName === 'hasUsableTermsProvision') return true;
        return functionName === 'acceptances'
          ? [account, account === coordinator ? 1n : 0n] : reads[functionName];
      },
    };
    const sdk = {
      deployment: { chainId: 31337 },
      actorContext: async (_client, { roleKey, actionKeys }) => ({ permissions: actionKeys.map((actionKey, index) =>
        ({ actionKey, allowed: account === coordinator && roleKey === modules.coordinator && index === 0 })) }),
      simulate: async (_client, _account, call, _abi, point) => {
        assert.equal(call.to, modules.prefunding.address);
        assert.equal(point.blockHash, block.hash);
        if (!funded) throw new AvaSigningError('simulate', 'contract_reverted');
      },
    };
    const course = createParticipantCourse({
      client, sdk, modules: { ...modules, usableTerms },
      genesisHash: hash('4'), installationHash: installation, packageId: 1n, previewLifetime: 60,
    });
    const [lesson] = (await course.workspace(account, snapshot)).lessons;
    assert.equal(lesson.prefunding.evidenceId, 9n);
    assert.equal(lesson.commitmentFundingAvailable, funded);
    const ids = lesson.seats[0].actions.map(action => action.operationId);
    assert.equal(ids.includes(account === customer ? 'acceptForm' : 'confirmPlace'), funded && usable !== false);
    const expectedHistoricalReads = account === coordinator ? [customer, reads.getLesson.terms.tutor]
      : funded && !usableTerms ? [customer] : [];
    assert.deepEqual(provisionReads.sort(), expectedHistoricalReads.sort());
  }
});

test('recharge offers share an issuer lookup within a block and check each offer’s authority', async () => {
  const customer = address('5'), issuer = address('6'), issuerRole = hash('7');
  const funds = { address: address('4'), abi: parseAbi(['function recharge(bytes32 offerId)']) };
  const modules = {
    booking: { address: address('1'), abi: [] },
    settlement: { address: address('2'), abi: [] },
    intake: { address: address('3'), abi: [] },
    funds,
    token: { address: address('8'), abi: [] },
    coordinator: hash('9'), provider: issuerRole,
  };
  const offerIds = [hash('a'), hash('b'), hash('c')];
  const earlierAuthority = hash('d'), currentAuthority = hash('e'), nextAuthority = hash('f');
  const nextBlock = { ...block, number: 5n, hash: hash('6') };
  const issuerReads = [];
  const client = {
    getContractEvents: async ({ eventName }) => eventName === 'RechargeOffered'
      ? offerIds.map(offerId => ({ args: { offerId } })) : [],
    readContract: async ({ functionName, args }) => {
      if (functionName === 'allowance') return 30n;
      assert.equal(functionName, 'getRechargeOffer');
      return { packageId: 1n, receiptId: 0n, provider: issuer,
        authorityId: args[0] === offerIds[2] ? earlierAuthority : currentAuthority,
        terms: { customer, amount: 10n, returnCap: 0n, returnThrough: 0n } };
    },
  };
  const sdk = {
    deployment: { chainId: 31337 },
    actorContext: async (_client, { account, roleKey, actionKeys }, point) => {
      const isIssuer = account === issuer && roleKey === issuerRole;
      assert.equal(point.requireCanonical, true);
      if (isIssuer) issuerReads.push(point.blockHash);
      return { authority: isIssuer ? { authorityId: point.blockHash === block.hash ? currentAuthority : nextAuthority } : undefined,
        permissions: actionKeys.map(actionKey => ({ actionKey, allowed: isIssuer })) };
    },
  };
  const course = createParticipantCourse({
    client, sdk, modules, genesisHash: hash('4'), installationHash: installation, packageId: 1n, previewLifetime: 60,
  });
  const workspace = ({ hash: blockHash, number: blockNumber, timestamp }) =>
    course.workspace(customer, { point: { blockHash, requireCanonical: true }, blockHash, blockNumber, timestamp });

  const first = await workspace(block);
  assert.deepEqual(first.recharges.map(offer => offer.actions.map(action => action.operationId)), [['recharge'], ['recharge'], []]);
  const second = await workspace(nextBlock);
  assert.deepEqual(second.recharges.map(offer => offer.actions), [[], [], []]);
  assert.deepEqual(issuerReads, [block.hash, nextBlock.hash]);
});
