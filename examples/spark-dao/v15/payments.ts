import { encodeFunctionData, isAddress, keccak256, parseAbi, toHex, type Abi, type Address, type Hex,
  type PublicClient } from 'viem';
import { AvaExtensions, AvaRuntimeError, readCanonicalEvent, readRuntimeContext, resolveReadPoint,
  verifySignedIntent, withCanonicalSnapshot, type AvaCall, type AvaSdk, type AvaServiceClient, type AvaWallet,
  type ReadPoint, type ServiceRequestOptions, type TransactionObservationOptions, type TransactionRecord } from '@ava-protocol/sdk';

const key = (text: string) => keccak256(toHex(text));
const same = (actual: unknown, expected: string) => typeof actual === 'string' && actual.toLowerCase() === expected.toLowerCase();
const fundsIdentityAbi = parseAbi([
  'function PAYMENTS() view returns (address)',
  'function TOKEN() view returns (address)',
  'function REQUEST_ALLOCATION() view returns (address)',
  'function WORKFLOW() view returns (bytes32)',
  'function creditBalance(bytes32 account) view returns (uint256)',
]);
const holdsReadAbi = parseAbi([
  'struct HoldTerms { bytes32 obligationId; bytes32 caseId; bytes32 noticeHash; uint64 reviewAt; uint256 expectedVersion; }',
  'struct TemporaryTerms { bytes32 obligationId; bytes32 caseId; bytes32 noticeHash; uint64 authorisedAt; uint64 expiresAt; uint256 expectedVersion; }',
  'struct FormalHold { HoldTerms terms; address reviewer; bytes32 authorityId; uint256 evidenceId; uint128 amount; uint64 imposedAt; uint64 liftedAt; address liftedBy; bytes32 liftAuthorityId; uint256 liftEvidenceId; bytes32 liftDisposition; bool completelyReleased; }',
  'struct TemporaryHold { TemporaryTerms terms; address setter; bytes32 authorityId; uint256 evidenceId; uint128 amount; uint64 imposedAt; bytes32 replacedBy; }',
  'struct HoldStatus { uint64 formalCoverageStartedAt; uint64 firstFullReleaseAt; uint64 postLiftCutoff; uint64 lastFullReleaseAt; uint256 postLiftClockEvidenceId; uint256 activeFormalHolds; bool active; }',
  'function PAYMENTS() view returns (address)',
  'function REQUEST_ALLOCATION() view returns (address)',
  'function WORKFLOW() view returns (bytes32)',
  'function VERIFIER_ROLE() view returns (bytes32)',
  'function formalHoldCommitment(HoldTerms terms, address reviewer) view returns (bytes32)',
  'function temporaryHoldCommitment(TemporaryTerms terms, address contact) view returns (bytes32)',
  'function formalLiftCommitment(bytes32 holdId, bytes32 disposition, uint256 expectedVersion, address reviewer) view returns (bytes32)',
  'function postLiftClockCommitment(bytes32 obligationId) view returns (bytes32)',
  'function getFormalHold(bytes32 id) view returns (FormalHold)',
  'function getTemporaryHold(bytes32 id) view returns (TemporaryHold)',
  'function getStatus(bytes32 obligationId) view returns (HoldStatus)',
]);

export const sparkV15 = Object.freeze({
  appId: key('ava.application.spark-dao.v1.5'),
  workflowKey: key('ava.spark.workflow.teaching.v1.5'),
  approvalObject: key('spark.object.payment-approval.v1.5'),
  approvalResponse: key('spark.response.approve-payment.v1.5'),
  approvalBurden: key('spark.burden.payment-approval.v1.5'),
  sourceRole: key('ava.spark.role.source.v1.5'),
  verifierRole: key('ava.spark.role.verifier.v1.5'),
  allocatorRole: key('ava.spark.role.allocator.v1.5'),
  alternativeContactRole: key('ava.spark.role.alternative-contact.v1.5'),
  eventSource: 'SparkV15Payments',
});

interface Contract { address: Address; abi: Abi }
export interface SparkV15PaymentInstallation {
  payments: Contract;
  requestPolicy: Contract;
  applicationModule: Address;
  token: Address;
  packageId: bigint;
  disclosurePolicyId: bigint;
}

export interface SparkV15PaymentTerms {
  lessonId: Hex;
  paymentPart: Hex;
  recipient: Address;
  originalDebitAccount: Hex;
  originalDebitAmount: bigint;
  amount: bigint;
  agreedStart: bigint;
  dueAt: bigint;
  executionDeadline: bigint;
  legalDeadline: bigint;
  postLiftDeadline: bigint;
  postLiftPeriod: bigint;
  dueAtExact: boolean;
  executionDeadlineExact: boolean;
  legalDeadlineExact: boolean;
  postLiftDeadlineExact: boolean;
  settlementProposer: Address;
  settlementApprover: Address;
}

export interface SparkV15ApprovalTerms {
  obligationId: Hex;
  executor: Address;
  ceiling: bigint;
  validThrough: bigint;
  replacesRequestId: bigint;
}

export interface SparkV15HoldTerms {
  obligationId: Hex;
  caseId: Hex;
  noticeHash: Hex;
  reviewAt: bigint;
  expectedVersion: bigint;
}

export interface SparkV15TemporaryHoldTerms {
  obligationId: Hex;
  caseId: Hex;
  noticeHash: Hex;
  authorisedAt: bigint;
  expiresAt: bigint;
  expectedVersion: bigint;
}

interface LiftTerms { holdId: Hex; disposition: Hex; expectedVersion: bigint }
interface EvidenceAuthority { evidenceId: bigint; authorityId: Hex }
export type SparkV15PaymentCommand =
  | ({ kind: 'establishPayment'; terms: SparkV15PaymentTerms; basis: Hex } & EvidenceAuthority)
  | { kind: 'recordApproval' | 'recordReplacementArrangement'; requestId: bigint; terms: SparkV15ApprovalTerms }
  | ({ kind: 'imposeTemporaryHold'; terms: SparkV15TemporaryHoldTerms } & EvidenceAuthority)
  | ({ kind: 'imposeFormalHold'; terms: SparkV15HoldTerms } & EvidenceAuthority)
  | ({ kind: 'liftFormalHold' } & LiftTerms & EvidenceAuthority)
  | ({ kind: 'verifyPostLiftClock'; obligationId: Hex } & EvidenceAuthority)
  | { kind: 'pay'; requestId: bigint; amount: bigint };

interface PaymentObligation {
  terms: SparkV15PaymentTerms;
  packageId: bigint;
  evidenceId: bigint;
  commitment: Hex;
  paid: bigint;
  formalCoverageStartedAt: bigint;
  firstFullReleaseAt: bigint;
  postLiftCutoff: bigint;
  lastFullReleaseAt: bigint;
  postLiftClockEvidenceId: bigint;
  activeFormalHolds: bigint;
  version: bigint;
  firstApprovalRequestId: bigint;
}
type HoldStatus = Pick<PaymentObligation, 'formalCoverageStartedAt' | 'firstFullReleaseAt' | 'postLiftCutoff'
  | 'lastFullReleaseAt' | 'postLiftClockEvidenceId' | 'activeFormalHolds'> & { active: boolean };
type StoredObligation = Omit<PaymentObligation, keyof HoldStatus>;

interface PaymentApproval {
  terms: SparkV15ApprovalTerms;
  approver: Address;
  authorityId: Hex;
  grantedAt: bigint;
  paid: bigint;
  stoppedAt: bigint;
  stoppedByCase: Hex;
}

interface PaymentReceipt {
  obligationId: Hex;
  approvalRequestId: bigint;
  executor: Address;
  recipient: Address;
  creditAccount: Hex;
  amount: bigint;
  approvedOutstandingBefore: bigint;
  paidAt: bigint;
  promptCutoff: bigint;
  promptCutoffMet: boolean;
}

interface FormalHold {
  terms: SparkV15HoldTerms;
  reviewer: Address;
  authorityId: Hex;
  evidenceId: bigint;
  amount: bigint;
  imposedAt: bigint;
  liftedAt: bigint;
  liftedBy: Address;
  liftAuthorityId: Hex;
  liftEvidenceId: bigint;
  liftDisposition: Hex;
  completelyReleased: boolean;
}

interface TemporaryHold {
  terms: SparkV15TemporaryHoldTerms;
  setter: Address;
  authorityId: Hex;
  evidenceId: bigint;
  amount: bigint;
  imposedAt: bigint;
  replacedBy: Hex;
}

export interface SparkV15SignedPayment {
  key: string;
  hash: Hex;
  account: Address;
  call: AvaCall;
  serializedTransaction: Hex;
}

type PaymentEvent = 'PaymentEstablished' | 'PaymentApprovalRecorded' | 'ReplacementArranged'
  | 'TemporaryHoldImposed' | 'FormalHoldImposed' | 'FormalHoldLifted' | 'PostLiftClockVerified' | 'PaymentReceived';

/** Local signed payment commands use the configured AVA relay and the installation's exact request policy. */
export async function connectSparkV15Payments(options: {
  client: PublicClient; sdk: AvaSdk; relay: AvaServiceClient; installation: SparkV15PaymentInstallation;
}) {
  const { client, sdk, relay } = options;
  const { payments, requestPolicy, applicationModule, token, packageId, disclosurePolicyId } =
    structuredClone(options.installation);
  const { appId, workflowKey, verifierRole, approvalObject, approvalResponse, approvalBurden, eventSource } = sparkV15;
  const { chainId, addresses } = sdk.deployment;
  const runtime = await readRuntimeContext(client, relay, { chainId });
  const at = { blockHash: runtime.checkpoint.blockHash, requireCanonical: true as const };
  let fundsAddress: Address;
  let holds: Contract;
  try {
    const readiness = await new AvaExtensions(sdk, {}).verifyInstallation(client, {
      appId, workflowKey, activePackageId: packageId, modules: [
        { capabilityKey: key('ava.capability.application.v1'), module: applicationModule },
        { capabilityKey: key('ava.capability.allocation.v1'), module: requestPolicy.address },
      ],
    }, at);
    if (!readiness.ready) throw new AvaRuntimeError('runtime_mismatch');
    const address = await client.readContract({ ...payments, functionName: 'FUNDS', ...at });
    if (typeof address !== 'string' || !isAddress(address) || same(address, payments.address)) {
      throw new AvaRuntimeError('runtime_mismatch');
    }
    fundsAddress = address;
    const funds = { address: fundsAddress, abi: fundsIdentityAbi };
    const holdsAddress = await client.readContract({ ...payments, functionName: 'HOLDS', ...at });
    if (typeof holdsAddress !== 'string' || !isAddress(holdsAddress) || same(holdsAddress, payments.address)) {
      throw new AvaRuntimeError('runtime_mismatch');
    }
    holds = { address: holdsAddress, abi: holdsReadAbi };
    const expected: readonly [Contract, string, Hex][] = [
      [payments, 'REQUEST_ALLOCATION', addresses.requests], [payments, 'WORKFLOW', workflowKey],
      [payments, 'TOKEN', token], [payments, 'VERIFIER_ROLE', verifierRole],
      [funds, 'PAYMENTS', payments.address], [funds, 'TOKEN', token],
      [funds, 'REQUEST_ALLOCATION', addresses.requests], [funds, 'WORKFLOW', workflowKey],
      [holds, 'PAYMENTS', payments.address], [holds, 'REQUEST_ALLOCATION', addresses.requests],
      [holds, 'WORKFLOW', workflowKey], [holds, 'VERIFIER_ROLE', verifierRole],
      [requestPolicy, 'REQUEST_ALLOCATION', addresses.requests], [requestPolicy, 'APP_ID', appId],
      [requestPolicy, 'WORKFLOW_KEY', workflowKey], [requestPolicy, 'EXECUTOR', payments.address],
      [requestPolicy, 'RESPONSE_CLASS', approvalResponse], [requestPolicy, 'BURDEN_HASH', approvalBurden],
    ];
    await Promise.all([
      ...expected.map(async ([contract, functionName, value]) => {
        if (!same(await client.readContract({ ...contract, functionName, ...at }), value)) {
          throw new AvaRuntimeError('runtime_mismatch');
        }
      }),
      sdk.contracts(client).disclosure.read.getPolicy([disclosurePolicyId], at).then(policy => {
        if (!same(policy.appId, appId)) throw new AvaRuntimeError('runtime_mismatch');
      }),
    ]);
  } catch (cause) {
    throw new Error('Spark v1.5 payment installation could not be verified', { cause });
  }

  function call(command: SparkV15PaymentCommand): AvaCall {
    let args: readonly unknown[];
    switch (command.kind) {
      case 'establishPayment': args = [command.terms, command.basis, command.evidenceId, command.authorityId]; break;
      case 'recordApproval':
      case 'recordReplacementArrangement': args = [command.requestId, command.terms]; break;
      case 'imposeTemporaryHold':
      case 'imposeFormalHold': args = [command.terms, command.evidenceId, command.authorityId]; break;
      case 'liftFormalHold': args = [command.holdId, command.disposition, command.expectedVersion, command.evidenceId, command.authorityId]; break;
      case 'verifyPostLiftClock': args = [command.obligationId, command.evidenceId, command.authorityId]; break;
      case 'pay': args = [command.requestId, command.amount]; break;
    }
    return { to: payments.address, data: encodeFunctionData({ abi: payments.abi, functionName: command.kind, args }) };
  }

  async function read<T>(functionName: string, args: readonly unknown[], point?: ReadPoint,
    contract: Contract = payments): Promise<T> {
    const snapshot = await resolveReadPoint(client, point);
    return await client.readContract({ ...contract, functionName, args,
      ...(typeof snapshot === 'bigint' ? { blockNumber: snapshot } : snapshot) }) as T;
  }

  const transactionKey = (hash: Hex) => `spark-v15:${hash.slice(2).toLowerCase()}`;
  async function forward(operation: SparkV15SignedPayment, recovering: boolean, options?: ServiceRequestOptions) {
    const { serializedTransaction, account, call, key, hash } = structuredClone(operation);
    if (!same(call.to, payments.address)) throw new Error('Spark v1.5 signed payment intent mismatch');
    const intent = await verifySignedIntent(serializedTransaction, { chainId, account, call });
    if (!same(intent.hash, hash) || transactionKey(intent.hash) !== key) {
      throw new Error('Spark v1.5 signed payment intent mismatch');
    }
    await readRuntimeContext(client, relay, runtime, { synchronize: false, signal: options?.signal });
    return recovering ? relay.recoverSubmit(key, serializedTransaction, options) : relay.submit(key, serializedTransaction, options);
  }

  return {
    get fundsAddress() { return fundsAddress; },
    paymentEvidenceCommitment: (terms: SparkV15PaymentTerms, basis: Hex) => read<Hex>('paymentEvidenceCommitment', [terms, basis]),
    temporaryHoldCommitment: (terms: SparkV15TemporaryHoldTerms, contact: Address) =>
      read<Hex>('temporaryHoldCommitment', [terms, contact], undefined, holds),
    formalHoldCommitment: (terms: SparkV15HoldTerms, reviewer: Address) =>
      read<Hex>('formalHoldCommitment', [terms, reviewer], undefined, holds),
    formalLiftCommitment: ({ holdId, disposition, expectedVersion }: LiftTerms, reviewer: Address) =>
      read<Hex>('formalLiftCommitment', [holdId, disposition, expectedVersion, reviewer], undefined, holds),
    postLiftClockCommitment: (obligationId: Hex) => read<Hex>('postLiftClockCommitment', [obligationId], undefined, holds),
    approvalRequest: (terms: SparkV15ApprovalTerms, validUntil: bigint) => withCanonicalSnapshot(client, async ({ point }) => {
      const parametersHash = await read<Hex>('approvalParameters', [terms], point);
      const input = { executor: payments.address, responseClass: approvalResponse, parametersHash,
        burdenHash: approvalBurden, validUntil };
      return { input, commitment: await sdk.requestCommitment(client, { appId, ...input }, point) };
    }),
    registerEvidence: (input: { roleKey: Hex; authorityId: Hex; commitment: Hex; evidenceTypeHash: Hex; uri: string }) =>
      sdk.registerEvidence({ ...input, appId, workflowKey, packageId, disclosurePolicyId, subjectId: input.authorityId }),
    registerApprovalObject: ({ evidenceId, commitment, ...input }: {
      roleKey: Hex; authorityId: Hex; evidenceId: bigint; commitment: Hex; uri: string;
    }) => sdk.registerObject({ ...input, appId, workflowKey, packageId, disclosurePolicyId, subjectId: input.authorityId,
      objectTypeKey: approvalObject, objectCommitment: commitment, metadataHash: commitment,
      parentObjectId: 0n, evidenceReceiptId: evidenceId }),
    async prepare(wallet: AvaWallet, command: SparkV15PaymentCommand): Promise<SparkV15SignedPayment> {
      const actor = wallet.account.address;
      const intent = call(command);
      const signed = await sdk.sign(client, wallet, intent, payments.abi);
      return { ...signed, account: actor, call: intent, key: transactionKey(signed.hash) };
    },
    submit: (operation: SparkV15SignedPayment, options?: ServiceRequestOptions) => forward(operation, false, options),
    recover: (operation: SparkV15SignedPayment, options?: ServiceRequestOptions) => forward(operation, true, options),
    observe: (identity: Pick<TransactionRecord, 'key' | 'hash'>, options?: TransactionObservationOptions) =>
      relay.observeTransaction(identity, options),
    event: (hash: Hex, eventName: PaymentEvent, options?: { logIndex?: number; confirmations?: number }) =>
      readCanonicalEvent(client, hash, { ...options, chainId, emitter: payments.address, abi: payments.abi, eventName }),
    events: (options?: { event?: PaymentEvent; after?: string; limit?: number } & ServiceRequestOptions) =>
      relay.events({ source: eventSource, expectedSourceAddress: payments.address,
        event: options?.event ?? 'PaymentReceived', after: options?.after, limit: options?.limit, order: 'asc' }, options),
    obligation: async (id: Hex, point?: ReadPoint) => {
      const joined = async (at: ReadPoint) => {
        const [obligation, hold] = await Promise.all([
          read<StoredObligation>('getObligation', [id], at),
          read<HoldStatus>('getStatus', [id], at, holds),
        ]);
        return { ...obligation, ...hold };
      };
      return point === undefined ? withCanonicalSnapshot(client, ({ point }) => joined(point)) : joined(point);
    },
    approval: (requestId: bigint, point?: ReadPoint) => read<PaymentApproval>('getApproval', [requestId], point),
    temporaryHold: (id: Hex, point?: ReadPoint) => read<TemporaryHold>('getTemporaryHold', [id], point, holds),
    formalHold: (id: Hex, point?: ReadPoint) => read<FormalHold>('getFormalHold', [id], point, holds),
    receipt: (receiptId: bigint, point?: ReadPoint) => read<PaymentReceipt>('getReceipt', [receiptId], point),
    creditBalance: (account: Hex, point?: ReadPoint) =>
      read<bigint>('creditBalance', [account], point, { address: fundsAddress, abi: fundsIdentityAbi }),
  };
}
