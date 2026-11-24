import { BaseError, TransactionNotFoundError, decodeFunctionData, encodeFunctionData, isAddress, keccak256, parseAbi, toHex,
  zeroAddress, zeroHash, type Abi, type Address, type Hex, type Log, type PublicClient } from 'viem';
import { AvaReceiptError, AvaSigningError, readCanonicalEvent, withCanonicalSnapshot, type AvaSdk, type CanonicalSnapshot }
  from '@ava-protocol/sdk';
import { SparkBackendError } from '../case-store.ts';
import { sparkV15, type SparkV15PaymentInstallation } from './payments.ts';

const key = (value: string) => keccak256(toHex(value));
const same = (a: unknown, b: string) => typeof a === 'string' && a.toLowerCase() === b.toLowerCase();
const hasChainLocation = (log: Log) => log.blockNumber !== null && log.blockHash && log.transactionHash
  && log.logIndex !== null && !log.removed;
const paymentActions = {
  recordApproval: { event: 'PaymentApprovalRecorded', role: 'allocator', permission: 'ava.extension.allocation.record.v1' },
  recordReplacementArrangement: { event: 'ReplacementArranged', role: 'allocator', permission: 'ava.extension.allocation.record.v1' },
  imposeFormalHold: { event: 'FormalHoldImposed', role: 'verifier', permission: 'spark.action.formal-hold.v1.5' },
  liftFormalHold: { event: 'FormalHoldLifted', role: 'verifier', permission: 'spark.action.lift-hold.v1.5' },
  imposeTemporaryHold: { event: 'TemporaryHoldImposed', role: 'alternativeContact', permission: 'spark.action.temporary-hold.v1.5' },
  verifyPostLiftClock: { event: 'PostLiftClockVerified', role: 'verifier', permission: 'spark.action.verify-post-lift-clock.v1.5' },
  pay: { event: 'PaymentReceived', role: undefined, permission: undefined },
} as const;
type Action = keyof typeof paymentActions;
const roleKeys = { source: sparkV15.sourceRole, verifier: sparkV15.verifierRole, allocator: sparkV15.allocatorRole,
  alternativeContact: sparkV15.alternativeContactRole };
type Role = keyof typeof roleKeys;
const rolePermissions: Record<Role, readonly Hex[]> = {
  source: [key('ava.core.register-evidence.v1')],
  verifier: [key('ava.core.form-recognised-state.v1'), key(paymentActions.imposeFormalHold.permission),
    key(paymentActions.liftFormalHold.permission), key(paymentActions.verifyPostLiftClock.permission)],
  allocator: [key(paymentActions.recordApproval.permission)],
  alternativeContact: [key(paymentActions.imposeTemporaryHold.permission)],
};

export const participantHash = (value: unknown): value is Hex =>
  typeof value === 'string' && /^0x[0-9a-f]{64}$/i.test(value);
export function participantAddress(value: unknown): Address {
  if (typeof value !== 'string' || !isAddress(value) || same(value, zeroAddress)) throw new SparkBackendError('invalid_account');
  return value as Address;
}
export function participantObject(value: unknown): Record<string, unknown> {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new SparkBackendError('invalid_fields');
  return value as Record<string, unknown>;
}
function uint(value: unknown, bits = 256): bigint {
  if (typeof value !== 'string' || !/^(0|[1-9][0-9]{0,77})$/.test(value) || BigInt(value) >= (1n << BigInt(bits))) {
    throw new SparkBackendError('invalid_integer');
  }
  return BigInt(value);
}
function hash(value: unknown): Hex {
  if (!participantHash(value) || same(value, zeroHash)) throw new SparkBackendError('invalid_reference');
  return value;
}
function actionId(value: unknown): Action {
  if (typeof value !== 'string' || !Object.hasOwn(paymentActions, value)) throw new SparkBackendError('unknown_operation');
  return value as Action;
}
function snapshotInfo({ blockNumber, blockHash, timestamp }: CanonicalSnapshot) {
  return { blockNumber, blockHash, timestamp };
}

type Payments = Awaited<ReturnType<typeof import('./payments.ts').connectSparkV15Payments>>;
type OperationOffer = { operationId: Action; input?: Record<string, string | bigint> };
const min = (a: bigint, b: bigint) => a < b ? a : b;
const paymentReserveAbi = parseAbi(['function paymentReserved(bytes32 obligationId) view returns (uint128)']);
type CurrentObligation = Awaited<ReturnType<Payments['obligation']>> & {
  correctAmount: bigint; beneficiary: Address; destination: Address; eligibleFrom: bigint; eligibilityExact: boolean;
};
const outstandingFor = ({ correctAmount, paid }: CurrentObligation) => correctAmount > paid ? correctAmount - paid : 0n;

/** Match the wallet transaction to the original Spark action and check its receipt on the current chain. */
export async function observeParticipantOperation(options: { client: PublicClient; chainId: number; hash: Hex;
  contract: { address: Address; abi: Abi }; account: Address; data: Hex; operationId: string; eventName: string }) {
  const { client, chainId, hash, contract, account, data, operationId, eventName } = options;
  const status = <T extends string>(result: T) => ({ hash, status: result });
  try {
    if (decodeFunctionData({ abi: contract.abi, data }).functionName !== operationId) return status('mismatch');
  } catch { return status('mismatch'); }
  let minedAt: bigint | null;
  try {
    const tx = await client.getTransaction({ hash });
    if (!same(tx.hash, hash) || !same(tx.from, account) || !same(tx.to, contract.address)
      || !same(tx.input, data) || tx.value !== 0n || (tx.chainId !== undefined && tx.chainId !== chainId)) return status('mismatch');
    minedAt = tx.blockNumber;
  } catch (error) {
    if (error instanceof TransactionNotFoundError || (error instanceof BaseError
      && error.walk(error => error instanceof TransactionNotFoundError) instanceof TransactionNotFoundError)) return status('unknown');
    throw error;
  }
  try {
    return { ...status('confirmed'), events: [await readCanonicalEvent(client, hash,
      { chainId, emitter: contract.address, abi: contract.abi, eventName })] };
  } catch (error) {
    if (!(error instanceof AvaReceiptError)) throw error;
    if (error.code === 'not_mined') return status(minedAt === null ? 'pending' : 'unavailable');
    if (error.code === 'not_confirmed') return status('pending');
    if (error.code === 'reverted') {
      const receipt = await client.getTransactionReceipt({ hash });
      const block = await client.getBlock({ blockNumber: receipt.blockNumber });
      return status(same(block.hash, receipt.blockHash) && receipt.status === 'reverted' ? 'reverted' : 'orphaned');
    }
    if (error.code === 'orphaned') return status('orphaned');
    if (error.code === 'rpc_unavailable') return status('unavailable');
    return status('mismatch');
  }
}

export function createParticipantPayments(options: {
  client: PublicClient;
  sdk: AvaSdk;
  payment: Payments;
  installation: SparkV15PaymentInstallation;
  installationHash: Hex;
  returns: { address: Address; abi: Abi };
  genesisHash: Hex;
  previewLifetime: number;
}) {
  const { client, sdk, payment, installation, installationHash, genesisHash, previewLifetime, returns } = options;
  const { payments } = installation;
  const funds = { address: payment.fundsAddress, abi: paymentReserveAbi };
  const { appId, workflowKey } = sparkV15;
  const chain = { chainId: sdk.deployment.chainId, genesisHash };
  function requireMatchingInstallation(value: unknown) {
    if (!same(value, installationHash)) throw new SparkBackendError('installation_mismatch', 409);
  }

  async function authorities(account: Address, { point }: CanonicalSnapshot) {
    return Object.fromEntries(await Promise.all((Object.entries(roleKeys) as [Role, Hex][]).map(async ([name, roleKey]) => {
      const result = await sdk.actorContext(client, { appId, account, roleKey, actionKeys: rolePermissions[name] }, point);
      return [name, { roleKey, authority: result.authority,
        allowed: result.permissions.filter(permission => permission.allowed).map(permission => permission.actionKey) }] as const;
    }))) as Record<Role, { roleKey: Hex; authority: { authorityId: Hex } | null; allowed: Hex[] }>;
  }

  async function history(block: CanonicalSnapshot) {
    const point = { fromBlock: 0n, toBlock: block.blockNumber, strict: true } as const;
    const logs = (await Promise.all([client.getContractEvents({ ...payments, ...point }),
      client.getContractEvents({ ...returns, ...point })])).flat();
    return logs.filter(hasChainLocation).map(log => ({ name: log.eventName,
      args: log.args as Record<string, unknown>, hash: log.transactionHash!, blockHash: log.blockHash!,
      blockNumber: log.blockNumber!, logIndex: log.logIndex!, emitter: log.address }))
      .sort((a, b) => a.blockNumber === b.blockNumber ? a.logIndex - b.logIndex : a.blockNumber < b.blockNumber ? -1 : 1);
  }
  type Occurrence = Awaited<ReturnType<typeof history>>[number];

  async function workspace(account: Address, snapshot: CanonicalSnapshot) {
    const { point, timestamp } = snapshot;
    const [roles, logs] = await Promise.all([authorities(account, snapshot), history(snapshot)]);
    const activeRoles = (Object.keys(roles) as Role[]).filter(role => roles[role].authority && roles[role].allowed.length);
    const eventsByObligation = new Map<unknown, Occurrence[]>();
    for (const event of logs) {
      const id = event.args.obligationId;
      const occurrences = eventsByObligation.get(id);
      if (occurrences) occurrences.push(event);
      else eventsByObligation.set(id, [event]);
    }
    const creditBalances = new Map<string, Promise<bigint>>();
    function creditBalanceFor(debitAccount: Hex) {
      const accountKey = debitAccount.toLowerCase();
      if (accountKey === zeroHash) return;
      const pending = creditBalances.get(accountKey);
      if (pending) return pending;
      const balance = payment.creditBalance(debitAccount, point);
      creditBalances.set(accountKey, balance);
      return balance;
    }

    const records = await Promise.all(logs.filter(event => event.name === 'PaymentEstablished').map(async event => {
      const id = hash(event.args.obligationId);
      const timeline = eventsByObligation.get(id) ?? [];
      const approvals = timeline.filter(event => event.name === 'PaymentApprovalRecorded');
      const [obligation, approvalHistory] = await Promise.all([
        payment.obligation(id, point) as Promise<CurrentObligation>,
        Promise.all(approvals.map(async event => ({ ...await payment.approval(event.args.requestId as bigint, point),
          requestId: event.args.requestId as bigint, occurrence: event }))),
      ]);
      const ownApprovals = approvalHistory.filter(record => same(record.terms.executor, account));
      const isRecipient = same(obligation.beneficiary, account) || same(obligation.terms.recipient, account);
      if (!activeRoles.length && !isRecipient && !ownApprovals.length) return;
      const [formalHolds, temporaryHolds, receipts, creditBalance, reserved] = await Promise.all([
        Promise.all(timeline.filter(event => event.name === 'FormalHoldImposed').map(async event => {
          const holdId = hash(event.args.holdId);
          return { id: holdId, ...await payment.formalHold(holdId, point), occurrence: event,
            lift: timeline.find(item => item.name === 'FormalHoldLifted' && same(item.args.holdId, holdId)) };
        })),
        Promise.all(timeline.filter(event => event.name === 'TemporaryHoldImposed').map(async event => {
          const holdId = hash(event.args.holdId);
          const record = await payment.temporaryHold(holdId, point);
          return { id: holdId, ...record, occurrence: event,
            active: same(record.replacedBy, zeroHash) && record.terms.expiresAt > timestamp };
        })),
        Promise.all(timeline.filter(event => event.name === 'PaymentReceived').map(async event => ({
          id: event.args.receiptId as bigint, ...await payment.receipt(event.args.receiptId as bigint, point), occurrence: event,
        }))),
        creditBalanceFor(obligation.terms.originalDebitAccount),
        client.readContract({ ...funds, ...point, functionName: 'paymentReserved', args: [id] }),
      ]);
      const outstanding = outstandingFor(obligation);
      const held = formalHolds.some(hold => hold.liftedAt === 0n) || temporaryHolds.some(hold => hold.active);
      const interested = same(obligation.terms.settlementProposer, account) || same(obligation.terms.settlementApprover, account)
        || approvalHistory.some(approval => same(approval.approver, account));
      const offers: OperationOffer[] = [];
      for (const operationId of ['recordApproval', 'recordReplacementArrangement', 'imposeFormalHold',
        'imposeTemporaryHold', 'verifyPostLiftClock'] as const) {
        const { role, permission } = paymentActions[operationId];
        if (roles[role].authority && roles[role].allowed.includes(key(permission))
          && (operationId !== 'verifyPostLiftClock' || (obligation.firstFullReleaseAt !== 0n
            && obligation.terms.postLiftPeriod !== 0n && obligation.postLiftClockEvidenceId === 0n))
          && (operationId !== 'recordReplacementArrangement' || obligation.firstFullReleaseAt !== 0n)
          && (operationId !== 'imposeFormalHold' || !interested)
          && outstanding > 0n) offers.push({ operationId });
      }
      if (roles.verifier.authority && roles.verifier.allowed.includes(key(paymentActions.liftFormalHold.permission)) && !interested) {
        for (const hold of formalHolds.filter(hold => hold.liftedAt === 0n)) {
          offers.push({ operationId: 'liftFormalHold', input: { holdId: hold.id } });
        }
      }
      if (!held && outstanding > 0n) {
        for (const approval of ownApprovals) {
          const ceilingRemaining = approval.terms.ceiling > obligation.paid ? approval.terms.ceiling - obligation.paid : 0n;
          const amount = min(min(outstanding, ceilingRemaining), reserved);
          if (amount === 0n || approval.stoppedAt !== 0n) continue;
          const call = { to: payments.address,
            data: encodeFunctionData({ abi: payments.abi, functionName: 'pay', args: [approval.requestId, amount] }) };
          try {
            await sdk.simulate(client, account, call, payments.abi, point);
            offers.push({ operationId: 'pay', input: { requestId: approval.requestId, amount } });
          } catch (error) {
            if (!(error instanceof AvaSigningError) || error.code !== 'contract_reverted') throw error;
          }
        }
      }
      const role = [...(isRecipient ? ['recipient'] : []), ...(ownApprovals.length ? ['executor'] : [])];
      return { id, role, obligation, outstanding, held, reserved, offers, approvals: approvalHistory, formalHolds, temporaryHolds, creditBalance,
        receipts, timeline: timeline.filter(record => ['ReplacementArranged', 'PaymentApprovalStopped',
          'PostLiftClockVerified', 'PaymentReturned', 'PaymentRevised'].includes(record.name)) };
    }));
    return { account, activeRoles, asOf: snapshotInfo(snapshot), obligations: records.filter(record => record !== undefined) };
  }

  async function prepare(value: unknown) {
    const request = participantObject(value), account = participantAddress(request.account);
    if (!same(request.appId, appId) || !same(request.workflowKey, workflowKey)) throw new SparkBackendError('installation_mismatch', 409);
    const operationId = actionId(request.operationId), input = participantObject(request.input);
    requireMatchingInstallation(input.installation);
    const now = Math.floor(Date.now() / 1000), issued = input.requestedAt;
    if (typeof issued !== 'number' || !Number.isSafeInteger(issued) || issued > now + 5
      || issued + previewLifetime <= now) throw new SparkBackendError('preview_expired', 409);
    const obligationId = hash(input.obligationId), expectedVersion = uint(input.expectedVersion);
    return withCanonicalSnapshot(client, async snapshot => {
      const obligation = await payment.obligation(obligationId, snapshot.point) as CurrentObligation;
      if (obligation.packageId === 0n) throw new SparkBackendError('obligation_not_found', 404);
      if (obligation.version !== expectedVersion) throw new SparkBackendError('preview_changed', 409);
      const { role, permission } = paymentActions[operationId];
      let authority: { roleKey: Hex; authorityId: Hex } | undefined;
      if (role) {
        const roleKey = roleKeys[role];
        const context = await sdk.actorContext(client, { appId, account, roleKey, actionKeys: [key(permission)] }, snapshot.point);
        if (!context.authority || !context.permissions[0]?.allowed) throw new SparkBackendError('role_not_authorised', 403);
        authority = { roleKey, authorityId: context.authority.authorityId };
      }
      const terms = { obligationId, expectedVersion };
      const wanted = { installation: installationHash, requestedAt: issued, obligationId, expectedVersion };
      let fields: Record<string, string | bigint>;
      let args: readonly unknown[];
      switch (operationId) {
        case 'recordApproval':
        case 'recordReplacementArrangement': {
          const approval = { obligationId, executor: participantAddress(input.executor), ceiling: uint(input.ceiling, 128),
            validThrough: uint(input.validThrough, 64), replacesRequestId: uint(input.replacesRequestId) };
          const requestId = uint(input.requestId);
          fields = { requestId, executor: approval.executor, ceiling: approval.ceiling, validThrough: approval.validThrough,
            replacesRequestId: approval.replacesRequestId };
          args = [requestId, approval];
          break;
        }
        case 'imposeFormalHold':
        case 'imposeTemporaryHold': {
          const caseId = hash(input.caseId), noticeHash = hash(input.noticeHash), evidenceId = uint(input.evidenceId);
          const clock: Record<string, bigint> = operationId === 'imposeFormalHold' ? { reviewAt: uint(input.reviewAt, 64) }
            : { authorisedAt: uint(input.authorisedAt, 64), expiresAt: uint(input.expiresAt, 64) };
          fields = { caseId, noticeHash, ...clock, evidenceId };
          args = [{ ...terms, caseId, noticeHash, ...clock }, evidenceId, authority!.authorityId];
          break;
        }
        case 'liftFormalHold': {
          const holdId = hash(input.holdId), disposition = hash(input.disposition), evidenceId = uint(input.evidenceId);
          const hold = await payment.formalHold(holdId, snapshot.point);
          if (!same(hold.terms.obligationId, obligationId)) throw new SparkBackendError('obligation_mismatch', 409);
          fields = { holdId, disposition, evidenceId };
          args = [holdId, disposition, expectedVersion, evidenceId, authority!.authorityId];
          break;
        }
        case 'verifyPostLiftClock': {
          const evidenceId = uint(input.evidenceId);
          fields = { evidenceId };
          args = [obligationId, evidenceId, authority!.authorityId];
          break;
        }
        case 'pay': {
          const requestId = uint(input.requestId), amount = uint(input.amount, 128);
          const approval = await payment.approval(requestId, snapshot.point);
          if (!same(approval.terms.obligationId, obligationId)) throw new SparkBackendError('obligation_mismatch', 409);
          if (!same(approval.terms.executor, account)) throw new SparkBackendError('role_not_authorised', 403);
          fields = { requestId, amount };
          args = [requestId, amount];
          break;
        }
      }
      const call = { to: payments.address, data: encodeFunctionData({ abi: payments.abi, functionName: operationId, args }) };
      try { await sdk.simulate(client, account, call, payments.abi, snapshot.point); }
      catch (error) {
        if (error instanceof AvaSigningError && error.code === 'contract_reverted') {
          throw new SparkBackendError('operation_not_available', 409);
        }
        throw error;
      }
      const { lessonId, originalDebitAccount } = obligation.terms;
      return { version: 1, operationVersion: 1, appId, workflowKey, operationId, account, chain, authority,
        roleKey: authority?.roleKey, asOf: snapshotInfo(snapshot), input: { ...wanted, ...fields, packageId: obligation.packageId },
        call: { ...call, value: '0' }, expiresAt: issued + previewLifetime,
        payment: { lessonId, recipient: obligation.destination, creditAccount: originalDebitAccount,
          confirmedAmount: obligation.correctAmount, outstanding: outstandingFor(obligation) } };
    });
  }

  async function observe(value: unknown) {
    const body = participantObject(value), locator = participantObject(body.locator), hashValue = hash(body.hash);
    const input = participantObject(locator.input), chainIdentity = participantObject(locator.chain), call = participantObject(locator.call);
    const account = participantAddress(locator.account), operationId = actionId(locator.operationId);
    const obligationId = hash(input.obligationId);
    requireMatchingInstallation(input.installation);
    if (!same(locator.appId, appId) || !same(locator.workflowKey, workflowKey)
      || chainIdentity.chainId !== chain.chainId || !same(chainIdentity.genesisHash, genesisHash)
      || !same(call.to, payments.address)) throw new SparkBackendError('installation_mismatch', 409);
    if (locator.operationVersion !== 1 || call.value !== '0' || typeof call.data !== 'string'
      || !/^0x(?:[0-9a-f]{2}){4,1024}$/i.test(call.data)) throw new SparkBackendError('invalid_transaction');
    const observation = await observeParticipantOperation({ client, chainId: chain.chainId, hash: hashValue, contract: payments,
      account, data: call.data as Hex, operationId, eventName: paymentActions[operationId].event });
    if (!('events' in observation)) return observation;
    const [event] = observation.events;
    const args = participantObject(event.args);
    if (!same(args.obligationId, obligationId)) return { hash: hashValue, status: 'mismatch' };
    const readback = operationId === 'pay' ? await payment.receipt(args.receiptId as bigint,
      { blockHash: event.blockHash, requireCanonical: true }) : undefined;
    return { ...observation, readback };
  }

  async function noticeLinked({ obligationId, caseId, noticeHash }: { obligationId: Hex; caseId: Hex; noticeHash: Hex }) {
    return withCanonicalSnapshot(client, async ({ blockNumber, point }) => {
      const range = { ...payments, fromBlock: 0n, toBlock: blockNumber,
        args: { obligationId: obligationId.toLowerCase() as Hex }, strict: true } as const;
      const [formal, temporary] = await Promise.all([
        client.getContractEvents({ ...range, eventName: 'FormalHoldImposed' }),
        client.getContractEvents({ ...range, eventName: 'TemporaryHoldImposed' }),
      ]);
      const holds = await Promise.all([
        ...formal.filter(hasChainLocation).map(log => payment.formalHold(hash((log.args as { holdId: Hex }).holdId), point)),
        ...temporary.filter(hasChainLocation).map(log => payment.temporaryHold(hash((log.args as { holdId: Hex }).holdId), point)),
      ]);
      return holds.some(hold => same(hold.terms.caseId, caseId) && same(hold.terms.noticeHash, noticeHash));
    });
  }

  return { workspace, prepare, observe, noticeLinked };
}
