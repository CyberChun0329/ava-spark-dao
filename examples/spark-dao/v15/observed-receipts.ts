import { encodeFunctionData, isAddress, parseAbi, zeroAddress, zeroHash, type Abi, type Address, type Hex,
  type PublicClient } from 'viem';
import { AvaReceiptError, AvaRuntimeError, readCanonicalEvent, resolveReadPoint, withCanonicalSnapshot,
  type AvaSdk, type AvaWallet, type ReadPoint } from '@ava-protocol/sdk';
import { sparkV15 } from './payments.js';

const transferAbi = parseAbi(['event Transfer(address indexed from, address indexed to, uint256 value)']);
const paymentIdentityAbi = parseAbi([
  'function paymentObservations() view returns (address)',
  'function TOKEN() view returns (address)',
]);
const observationIdentityAbi = parseAbi([
  'function PAYMENTS() view returns (address)',
  'function REQUEST_ALLOCATION() view returns (address)',
  'function TOKEN() view returns (address)',
  'function WORKFLOW() view returns (bytes32)',
  'function VERIFIER_ROLE() view returns (bytes32)',
]);
const same = (left: unknown, right: unknown) => typeof left === 'string' && typeof right === 'string'
  && left.toLowerCase() === right.toLowerCase();
const maxUint64 = (1n << 64n) - 1n;
const maxUint128 = (1n << 128n) - 1n;

export interface SparkV15ObservedTransfer {
  transactionHash: Hex;
  blockHash: Hex;
  blockNumber: bigint;
  logIndex: bigint;
  occurredAt: bigint;
  sender: Address;
  destination: Address;
  amount: bigint;
}

export interface SparkV15ObservedTransferRequest {
  transactionHash: Hex;
  logIndex: number;
  confirmations?: number;
  expected?: Pick<SparkV15ObservedTransfer, 'sender' | 'destination' | 'amount'>;
}

export interface SparkV15ObservedPayment {
  obligationId: Hex;
  beneficiary: Address;
  transfer: SparkV15ObservedTransfer;
  evidenceAvailableAt: bigint;
  attributionRef: Hex;
  returnDestination: Address;
}

export interface SparkV15ObservedReturn {
  paymentReceiptId: Hex;
  transfer: SparkV15ObservedTransfer;
  evidenceAvailableAt: bigint;
  recoveryRef: Hex;
}

export interface SparkV15ObservedAttribution {
  paymentReceiptId: Hex;
  beneficiary: Address;
  attributionRef: Hex;
  returnDestination: Address;
}

interface ObservedReturnProof { terms: SparkV15ObservedReturn; evidenceId: bigint }

export interface SparkV15ObservedAgreedRecipient {
  paymentReceiptId: Hex;
  payee: Address;
  agreedAt: bigint;
  ceasedAt: bigint;
  agreedByTransferWithinSecond: boolean;
  ceasedAfterTransferWithinSecond: boolean;
  agreementRef: Hex;
}

export const SparkV15ObservationFinding = { Unknown: 0, No: 1, Yes: 2 } as const;
type Finding = typeof SparkV15ObservationFinding[keyof typeof SparkV15ObservationFinding];

export interface SparkV15ObservedExecution {
  paymentReceiptId: Hex;
  actualExecutor: Address;
  namedExecutor: Address;
  approvalRequestId: bigint;
  applicableDeadline: bigint;
  approvalCoverage: Finding;
  heldAtExecution: Finding;
  paidByDeadline: Finding;
  fullyPaidByDeadline: Finding;
  executorEvidenceRef: Hex;
  approvalEvidenceRef: Hex;
  holdEvidenceRef: Hex;
  deadlineEvidenceRef: Hex;
}

interface Verification {
  evidenceId: bigint;
  evidencePackageId: bigint;
  verifier: Address;
  authorityId: Hex;
  verifiedAt: bigint;
}
interface VerifiedPayment {
  terms: SparkV15ObservedPayment;
  verification: Verification;
  obligationPackageId: bigint;
  qualifies: boolean;
  afterOriginalExecutionDeadline: boolean;
  afterLegalDeadline: boolean;
}
interface VerifiedReturn { terms: SparkV15ObservedReturn; verification: Verification }
interface VerifiedAttribution { terms: SparkV15ObservedAttribution; verification: Verification }
interface VerifiedAgreedRecipient { terms: SparkV15ObservedAgreedRecipient; verification: Verification }
interface VerifiedExecution { findings: SparkV15ObservedExecution; verification: Verification }

type ObservationCommand = { authorityId: Hex } & (
  | { kind: 'verifyPayment'; terms: SparkV15ObservedPayment; evidenceId: bigint }
  | { kind: 'verifyPaymentAttribution'; terms: SparkV15ObservedAttribution; evidenceId: bigint;
      priorReturns?: ObservedReturnProof[] }
  | { kind: 'verifyReturn'; terms: SparkV15ObservedReturn; evidenceId: bigint }
  | { kind: 'verifyAgreedRecipient'; terms: SparkV15ObservedAgreedRecipient; evidenceId: bigint }
  | { kind: 'verifyExecutionAssessment'; terms: SparkV15ObservedExecution; evidenceId: bigint }
  | { kind: 'archiveObservation'; observationId: Hex }
);

/** Select an exact canonical log from the installed token and read its block time. */
export async function readSparkV15ObservedTransfer(client: PublicClient,
  { chainId, token, transactionHash, logIndex, confirmations, expected }: SparkV15ObservedTransferRequest & {
    chainId: number; token: Address;
  }): Promise<SparkV15ObservedTransfer> {
  if (!Number.isSafeInteger(logIndex) || logIndex < 0) throw new AvaReceiptError('invalid_request');
  const receipt = await readCanonicalEvent(client, transactionHash, {
    chainId, emitter: token, abi: transferAbi, eventName: 'Transfer', logIndex, confirmations,
  });
  const { from, to, value } = (receipt.args ?? {}) as { from?: unknown; to?: unknown; value?: unknown };
  if (typeof from !== 'string' || !isAddress(from) || typeof to !== 'string' || !isAddress(to)
      || same(from, zeroAddress) || same(to, zeroAddress) || same(from, to)
      || typeof value !== 'bigint' || value <= 0n || value > maxUint128) {
    throw new AvaReceiptError('invalid_receipt');
  }
  if (expected && (!same(expected.sender, from) || !same(expected.destination, to) || expected.amount !== value)) {
    throw new AvaReceiptError('receipt_mismatch');
  }
  const block = await client.getBlock({ blockNumber: receipt.blockNumber }).catch(() => {
    throw new AvaReceiptError('rpc_unavailable');
  });
  if (!block.hash || !same(block.hash, receipt.blockHash)) throw new AvaReceiptError('orphaned');
  if (block.number !== receipt.blockNumber || receipt.blockNumber > maxUint64
      || typeof block.timestamp !== 'bigint' || block.timestamp <= 0n || block.timestamp > maxUint64) {
    throw new AvaReceiptError('receipt_mismatch');
  }
  return { transactionHash: receipt.transactionHash, blockHash: receipt.blockHash, blockNumber: receipt.blockNumber,
    logIndex: BigInt(receipt.logIndex), occurredAt: block.timestamp, sender: from, destination: to, amount: value };
}

/** Connect the verifier's wallet to the observation module bound to one Spark v1.5 payment installation. */
export async function connectSparkV15PaymentObservations({ client, sdk, installation }: {
  client: PublicClient;
  sdk: AvaSdk;
  installation: { payments: Address; observations: { address: Address; abi: Abi }; token: Address };
}) {
  const { payments, observations, token } = structuredClone(installation);
  const recordsAssessmentEvents = observations.abi.some(item =>
    item.type === 'function' && item.name === 'executionAssessmentBlock');
  const { chainId, addresses } = sdk.deployment;
  if (await client.getChainId() !== chainId) throw new AvaRuntimeError('runtime_mismatch');
  await withCanonicalSnapshot(client, async ({ point }) => {
    const payment = { address: payments, abi: paymentIdentityAbi, ...point };
    const observer = { address: observations.address, abi: observationIdentityAbi, ...point };
    const [boundObserver, paymentToken, boundPayments, observationToken, requests, workflow, verifierRole] = await Promise.all([
      client.readContract({ ...payment, functionName: 'paymentObservations' }),
      client.readContract({ ...payment, functionName: 'TOKEN' }),
      client.readContract({ ...observer, functionName: 'PAYMENTS' }),
      client.readContract({ ...observer, functionName: 'TOKEN' }),
      client.readContract({ ...observer, functionName: 'REQUEST_ALLOCATION' }),
      client.readContract({ ...observer, functionName: 'WORKFLOW' }),
      client.readContract({ ...observer, functionName: 'VERIFIER_ROLE' }),
    ]);
    if (!same(boundObserver, observations.address) || !same(boundPayments, payments) || !same(observationToken, token)
        || !same(paymentToken, token) || !same(requests, addresses.requests) || !same(workflow, sparkV15.workflowKey)
        || !same(verifierRole, sparkV15.verifierRole)) throw new AvaRuntimeError('runtime_mismatch');
  });

  async function read<T>(functionName: string, args: readonly unknown[], point?: ReadPoint): Promise<T> {
    const at = await resolveReadPoint(client, point);
    return await client.readContract({ ...observations, functionName, args,
      ...(typeof at === 'bigint' ? { blockNumber: at } : at) }) as T;
  }

  async function execution(id: Hex, point?: ReadPoint): Promise<VerifiedExecution> {
    if (!recordsAssessmentEvents) return read<VerifiedExecution>('executionAssessment', [id], point);

    const snapshot = await client.getBlock(point === undefined ? { blockTag: 'latest' }
      : typeof point === 'bigint' ? { blockNumber: point } : { blockHash: point.blockHash });
    if (!snapshot.hash || snapshot.number === null
      || (typeof point === 'bigint' && snapshot.number !== point)
      || (typeof point === 'object' && !same(snapshot.hash, point.blockHash))) {
      throw new AvaReceiptError('receipt_mismatch');
    }
    const adoptedAt = await read<bigint>('executionAssessmentBlock', [id],
      { blockHash: snapshot.hash, requireCanonical: true });
    if (adoptedAt === 0n) {
      // Keep the same empty read as an installation using the legacy getter.
      return { findings: { paymentReceiptId: zeroHash, actualExecutor: zeroAddress, namedExecutor: zeroAddress,
        approvalRequestId: 0n, applicableDeadline: 0n, approvalCoverage: 0, heldAtExecution: 0,
        paidByDeadline: 0, fullyPaidByDeadline: 0, executorEvidenceRef: zeroHash, approvalEvidenceRef: zeroHash,
        holdEvidenceRef: zeroHash, deadlineEvidenceRef: zeroHash },
      verification: { evidenceId: 0n, evidencePackageId: 0n, verifier: zeroAddress, authorityId: zeroHash, verifiedAt: 0n } };
    }
    if (adoptedAt > snapshot.number) throw new AvaReceiptError('receipt_mismatch');
    const adoption = adoptedAt === snapshot.number ? snapshot : await client.getBlock({ blockNumber: adoptedAt });
    if (!adoption.hash || adoption.number !== adoptedAt) throw new AvaReceiptError('receipt_mismatch');
    const logs = await client.getContractEvents({ ...observations, blockHash: adoption.hash,
      eventName: 'PaymentExecutionAssessed', args: { paymentReceiptId: id }, strict: true });
    if (!same((await client.getBlock({ blockNumber: snapshot.number })).hash, snapshot.hash)) {
      throw new AvaReceiptError('orphaned');
    }
    if (logs.length === 0) throw new AvaReceiptError('event_missing');
    if (logs.length !== 1) throw new AvaReceiptError('event_ambiguous');
    const [log] = logs;
    const { paymentReceiptId, findings, verification } =
      log.args as Partial<VerifiedExecution & { paymentReceiptId: Hex }>;
    if (!findings || !verification || log.removed || !same(log.address, observations.address) || !same(log.blockHash, adoption.hash)
      || log.blockNumber !== adoptedAt || !same(paymentReceiptId, id) || !same(findings.paymentReceiptId, id)
      || verification.evidenceId === 0n || verification.verifiedAt !== adoption.timestamp) {
      throw new AvaReceiptError('receipt_mismatch');
    }
    return { findings, verification };
  }

  return {
    transfer: (request: SparkV15ObservedTransferRequest) => readSparkV15ObservedTransfer(client, { ...request, token, chainId }),
    sourceId: (hash: Hex, logIndex: bigint, point?: ReadPoint) => read<Hex>('sourceId', [hash, logIndex], point),
    paymentEvidenceCommitment: (terms: SparkV15ObservedPayment) => read<Hex>('paymentEvidenceCommitment', [terms]),
    attributionEvidenceCommitment: (terms: SparkV15ObservedAttribution, priorReturns: ObservedReturnProof[] = []) =>
      read<Hex>('attributionEvidenceCommitment', [terms, priorReturns]),
    returnEvidenceCommitment: (terms: SparkV15ObservedReturn) => read<Hex>('returnEvidenceCommitment', [terms]),
    agreedRecipientEvidenceCommitment: (terms: SparkV15ObservedAgreedRecipient) =>
      read<Hex>('agreedRecipientEvidenceCommitment', [terms]),
    executionEvidenceCommitment: (terms: SparkV15ObservedExecution) => read<Hex>('executionEvidenceCommitment', [terms]),
    payment: (id: Hex, point?: ReadPoint) => read<VerifiedPayment>('getPaymentObservation', [id], point),
    attribution: (id: Hex, point?: ReadPoint) => read<VerifiedAttribution>('getPaymentAttribution', [id], point),
    returned: (id: Hex, point?: ReadPoint) => read<VerifiedReturn>('getReturnObservation', [id], point),
    agreedRecipient: (id: Hex, point?: ReadPoint) => read<VerifiedAgreedRecipient>('getAgreedRecipient', [id], point),
    execution,
    returnIds: (id: Hex, point?: ReadPoint) => read<Hex[]>('getReturnIds', [id], point),
    returnedForReceipt: (id: Hex, point?: ReadPoint) => read<bigint>('returnedForReceipt', [id], point),
    archivedAt: (id: Hex, point?: ReadPoint) => read<bigint>('archivedAt', [id], point),
    async prepare(wallet: AvaWallet, command: ObservationCommand) {
      if (command.kind === 'archiveObservation'
        && !observations.abi.some(item => item.type === 'function' && item.name === 'archiveObservation')) {
        throw new Error('This installation files payment observations with the local archive CLI');
      }
      const args = command.kind === 'archiveObservation' ? [command.observationId, command.authorityId]
        : command.kind === 'verifyPaymentAttribution'
          ? [command.terms, command.evidenceId, command.priorReturns ?? [], command.authorityId]
          : [command.terms, command.evidenceId, command.authorityId];
      const call = { to: observations.address,
        data: encodeFunctionData({ abi: observations.abi, functionName: command.kind, args }) };
      const signed = await sdk.sign(client, wallet, call, observations.abi);
      return { ...signed, account: wallet.account.address, call };
    },
  };
}
