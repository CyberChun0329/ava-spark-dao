import { readFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { AvaExtensions, AvaSdk, RecognitionStatus, Stage, avaAbis, jsonValue, localClient, withCanonicalSnapshot,
  type AvaCall, type CanonicalSnapshot } from '@ava-protocol/sdk';
import type { PublicDeployment } from '@ava-protocol/sdk/deployment';
import { keccak256, parseAbi, toHex, zeroHash, type Address, type Hex, type PublicClient } from 'viem';
import { observeParticipantOperation, participantAddress, participantHash, participantObject } from './participant-payments.ts';
import { sparkV15, type SparkV15ApprovalTerms } from './payments.ts';

const { appId, workflowKey, sourceRole, verifierRole, allocatorRole, approvalObject, approvalResponse, approvalBurden } = sparkV15;
const key = (value: string) => keccak256(toHex(value));
const same = (actual: unknown, expected: string) => typeof actual === 'string' && actual.toLowerCase() === expected.toLowerCase();
const registerEvidence = { role: sourceRole, permission: 'ava.core.register-evidence.v1', target: 'evidence',
  method: 'registerEvidence', event: 'EvidenceRegistered', id: 'evidenceId' } as const;
const actions = {
  evidence: { ...registerEvidence, next: null },
  'completion-evidence': { ...registerEvidence, next: 'recordOneToOneCompletion' },
  object: { role: sourceRole, permission: 'ava.core.register-governed-object.v1', target: 'kernel',
    method: 'registerGovernedObject', event: 'GovernedObjectRegistered', id: 'id', next: 'form' },
  form: { role: verifierRole, permission: 'ava.core.form-recognised-state.v1', target: 'kernel',
    method: 'formRecognisedState', event: 'RecognisedStateFormed', id: 'id', next: 'challengeable' },
  challengeable: { role: verifierRole, permission: 'ava.core.transition-recognised-state.v1', target: 'kernel',
    method: 'transitionRecognisedState', event: 'RecognisedStateTransitioned', id: 'recognisedStateId', next: 'vest' },
  vest: { role: verifierRole, permission: 'ava.core.vest-recognised-state.v1', target: 'kernel',
    method: 'vestRecognisedState', event: 'RecognisedStateTransitioned', id: 'recognisedStateId', next: 'request' },
  request: { role: sourceRole, permission: 'ava.extension.request.create.v1', target: 'requests',
    method: 'createRequest', event: 'RequestCreated', id: 'requestId', next: 'allocate' },
  allocate: { role: allocatorRole, permission: 'ava.extension.allocation.record.v1', target: 'requests',
    method: 'approve', event: 'RequestApproved', id: 'requestId', next: 'recordApproval' },
} as const;
type Action = keyof typeof actions;
type Fields = Record<string, unknown>;
const settlementAbi = parseAbi([
  'function ALTERNATIVES() view returns (address)',
  'function hasAdoptedOneToOneCompletion(bytes32 lessonId, bytes32 formId) view returns (bool)',
]);
const alternativesAbi = parseAbi([
  'function completionCommitment(bytes32 formId, bytes32 reportRef, address actor) view returns (bytes32)',
  'function SETTLEMENT() view returns (address)', 'function BOOKING() view returns (address)',
  'function PAYMENTS() view returns (address)', 'function studentCompletion(bytes32 formId) view returns (uint256)',
  'function coordinatorCompletion(bytes32 formId) view returns (uint256)',
]);

const readJson = async (path: string): Promise<unknown> => JSON.parse(await readFile(path, 'utf8'));
function nonempty(value: unknown, field: string): string {
  if (typeof value !== 'string' || !value.trim()) throw new Error(`Missing ${field}`);
  return value;
}
function actionName(value: unknown): Action {
  if (typeof value !== 'string' || !Object.hasOwn(actions, value)) throw new Error('Unknown participant action');
  return value as Action;
}
function hash(value: unknown, field: string): Hex {
  if (!participantHash(value) || same(value, zeroHash)) throw new Error(`${field} must be a nonzero bytes32`);
  return value;
}
function uint(value: unknown, field: string, bits = 256, allowZero = false): bigint {
  if (typeof value === 'string' && /^(0|[1-9][0-9]{0,77})$/.test(value)) {
    const parsed = BigInt(value);
    if ((allowZero || parsed > 0n) && parsed < 1n << BigInt(bits)) return parsed;
  }
  throw new Error(`${field} must be a ${allowZero ? 'nonnegative' : 'positive'} decimal uint${bits} string`);
}

async function loadInstallation(configPath: string) {
  const config = participantObject(await readJson(configPath));
  const rpc = new URL(nonempty(config.rpcUrl, 'rpcUrl'));
  if (rpc.protocol !== 'http:' || rpc.hostname !== '127.0.0.1' || rpc.username || rpc.password
    || rpc.pathname !== '/' || rpc.search || rpc.hash) throw new Error('Use an HTTP loopback origin');

  const contents = await readFile(resolve(dirname(configPath), nonempty(config.deploymentPath, 'deploymentPath')));
  const declaration = JSON.parse(contents.toString('utf8')) as PublicDeployment;
  const profile = declaration.workflows?.[appId]?.[workflowKey] ?? declaration.apps?.[appId];
  if (declaration.schemaVersion !== 1 || declaration.deployment?.chainId !== 31337
    || !profile || !same(profile.appId, appId) || !same(profile.workflowKey, workflowKey)) {
    throw new Error('Expected the exported local Spark v1.5 deployment');
  }
  const { SparkV15Payments: payments, AVABoundRequestPolicy: requestPolicy,
    SparkV15ApplicationModule: application } = profile.contracts;
  for (const contract of [payments, requestPolicy, application]) {
    if (!contract || !Array.isArray(contract.abi)) throw new Error('Incomplete Spark v1.5 deployment export');
    participantAddress(contract.address);
  }

  const sdk = new AvaSdk(declaration.deployment);
  const client = localClient(rpc.origin);
  return { client, sdk, profile, payments, requestPolicy, application, token: participantAddress(config.token),
    packageId: uint(profile.packageId, 'packageId'), disclosurePolicyId: uint(profile.disclosurePolicyId, 'disclosurePolicyId'),
    deploymentHash: keccak256(contents) };
}

type Installation = Awaited<ReturnType<typeof loadInstallation>>;
async function verifyInstallation(installation: Installation, { point }: CanonicalSnapshot) {
  const { client, sdk, packageId, disclosurePolicyId, application, payments, requestPolicy, token } = installation;
  const requests = sdk.deployment.addresses.requests;
  const [readiness, policy, ...checks] = await Promise.all([
    new AvaExtensions(sdk, {}).verifyInstallation(client, { appId, workflowKey, activePackageId: packageId, modules: [
      { capabilityKey: key('ava.capability.application.v1'), module: application.address },
      { capabilityKey: key('ava.capability.allocation.v1'), module: requestPolicy.address },
    ] }, point),
    sdk.contracts(client).disclosure.read.getPolicy([disclosurePolicyId], point),
    ...([
      [payments, 'REQUEST_ALLOCATION', requests], [payments, 'WORKFLOW', workflowKey], [payments, 'TOKEN', token],
      [requestPolicy, 'REQUEST_ALLOCATION', requests], [requestPolicy, 'APP_ID', appId],
      [requestPolicy, 'WORKFLOW_KEY', workflowKey], [requestPolicy, 'EXECUTOR', payments.address],
      [requestPolicy, 'RESPONSE_CLASS', approvalResponse], [requestPolicy, 'BURDEN_HASH', approvalBurden],
    ] as const).map(async ([contract, functionName, expected]) =>
      same(await client.readContract({ ...contract, functionName, ...point }), expected)),
  ]);
  if (!readiness.ready || !same(policy.appId, appId) || !checks.every(Boolean)) {
    throw new Error('Current chain does not match the recorded Spark payment installation');
  }
}

async function requireAuthority({ client, sdk }: Installation, account: Address, roleKey: Hex, permission: string,
  { point }: CanonicalSnapshot) {
  const context = await sdk.actorContext(client, { appId, account, roleKey, actionKeys: [key(permission)] }, point);
  if (!context.authority || !context.permissions[0]?.allowed) throw new Error(`Account lacks ${permission} in this installation`);
  return context.authority;
}

async function completionEvidence(installation: Installation, input: Fields, snapshot: CanonicalSnapshot) {
  const { client, profile, payments, packageId } = installation;
  const { point } = snapshot;
  const formId = hash(input.formId, 'formId'), reportRef = hash(input.reportRef, 'reportRef');
  const confirmingAccount = participantAddress(input.confirmingAccount);
  const booking = profile.contracts.SparkV15Booking, settlement = profile.contracts.SparkV15Settlement;
  if (!booking || !settlement) throw new Error('Course settlement is not installed');
  const host = { address: participantAddress(settlement.address), abi: settlementAbi, ...point };
  const alternatives = { address: participantAddress(await client.readContract({ ...host, functionName: 'ALTERNATIVES' })),
    abi: alternativesAbi, ...point };
  const [alternativesHost, alternativesBooking, alternativesPayments] = await Promise.all([
    client.readContract({ ...alternatives, functionName: 'SETTLEMENT' }),
    client.readContract({ ...alternatives, functionName: 'BOOKING' }),
    client.readContract({ ...alternatives, functionName: 'PAYMENTS' }),
  ]);
  if (!same(alternativesHost, host.address) || !same(alternativesBooking, booking.address)
    || !same(alternativesPayments, payments.address)) throw new Error('Settlement alternatives do not match the deployment export');

  const form = await client.readContract({ ...booking, functionName: 'getForm', args: [formId], ...point }) as {
    lessonId: Hex; terms: { student: Address }; confirmation: { confirmedAt: bigint };
  };
  const [lesson, teaching] = await Promise.all([
    client.readContract({ ...booking, functionName: 'getLesson', args: [form.lessonId], ...point }) as Promise<{
      packageId: bigint; terms: { rosterRef: Hex; coordinator: Address };
    }>,
    client.readContract({ ...booking, functionName: 'getTeaching', args: [form.lessonId], ...point }) as Promise<{ endEvidenceId: bigint }>,
  ]);
  if (lesson.packageId !== packageId || !same(lesson.terms.rosterRef, zeroHash)
    || form.confirmation.confirmedAt === 0n || teaching.endEvidenceId === 0n) {
    throw new Error('Expected an ended one-to-one lesson and a confirmed seat in this installation');
  }
  const student = same(confirmingAccount, form.terms.student);
  if (!student) {
    if (!same(confirmingAccount, lesson.terms.coordinator)) throw new Error('Expected the recorded student or coordinator');
    const role = hash(await client.readContract({ ...booking, functionName: 'COORDINATOR_ROLE', ...point }), 'coordinator role');
    await requireAuthority(installation, confirmingAccount, role, 'spark.action.confirm-one-to-one-completion.v1.5', snapshot);
  }
  if (settlement.abi.some(entry => entry.type === 'function' && entry.name === 'hasAdoptedOneToOneCompletion')
    && await client.readContract({ ...host, functionName: 'hasAdoptedOneToOneCompletion', args: [form.lessonId, formId] })) {
    throw new Error('This participant already confirmed completion in the settlement');
  }
  const [recorded, commitment] = await Promise.all([
    client.readContract({ ...alternatives, functionName: student ? 'studentCompletion' : 'coordinatorCompletion', args: [formId] }),
    client.readContract({ ...alternatives, functionName: 'completionCommitment', args: [formId, reportRef, confirmingAccount] }),
  ]);
  if (recorded !== 0n) throw new Error('This participant already recorded completion');
  return { commitment, formId, reportRef, confirmingAccount, endEvidenceId: teaching.endEvidenceId };
}

async function approvalContext({ client, sdk, payments, packageId }: Installation, input: Fields, snapshot: CanonicalSnapshot) {
  const { point, timestamp } = snapshot;
  const supplied = participantObject(input.terms);
  const terms: SparkV15ApprovalTerms = { obligationId: hash(supplied.obligationId, 'obligationId'),
    executor: participantAddress(supplied.executor), ceiling: uint(supplied.ceiling, 'ceiling', 128),
    validThrough: uint(supplied.validThrough, 'validThrough', 64), replacesRequestId: uint(supplied.replacesRequestId, 'replacesRequestId', 256, true) };
  const validUntil = uint(input.validUntil, 'validUntil', 64);
  if (validUntil <= timestamp || terms.validThrough < timestamp) throw new Error('Core request or Spark approval validity has expired');
  const obligation = await client.readContract({ ...payments, functionName: 'getObligation', args: [terms.obligationId], ...point }) as {
    packageId: bigint; version: bigint; beneficiaryVersion: bigint; beneficiary: Address; destination: Address; paid: bigint; correctAmount: bigint;
  };
  if (obligation.packageId !== packageId || terms.ceiling <= obligation.paid || terms.ceiling > obligation.correctAmount) {
    throw new Error('Obligation or ceiling does not match the current installation and outstanding amount');
  }
  const parametersHash = hash(await client.readContract({ ...payments, functionName: 'approvalParameters', args: [terms], ...point }), 'approval parameters');
  const request = { executor: payments.address, responseClass: approvalResponse, parametersHash, burdenHash: approvalBurden, validUntil };
  const commitment = await sdk.requestCommitment(client, { appId, ...request }, point);
  return { terms, obligation, request, commitment };
}

async function prepare(installation: Installation, input: Fields) {
  const { client, sdk, packageId, disclosurePolicyId, deploymentHash } = installation;
  const chainId = sdk.deployment.chainId;
  const action = actionName(input.action), operation = actions[action], account = participantAddress(input.account);
  return withCanonicalSnapshot(client, async snapshot => {
    await verifyInstallation(installation, snapshot);
    const { point, blockNumber, blockHash, timestamp } = snapshot;
    const [authority, genesis] = await Promise.all([
      requireAuthority(installation, account, operation.role, operation.permission, snapshot),
      client.getBlock({ blockNumber: 0n }),
    ]);
    const scope = { appId, workflowKey, packageId, disclosurePolicyId, ...authority };
    const core = sdk.contracts(client);
    let call: AvaCall;
    let details: Fields;
    if (action === 'evidence' || action === 'completion-evidence') {
      const evidence = action === 'evidence' ? { commitment: hash(input.commitment, 'commitment') }
        : await completionEvidence(installation, input, snapshot);
      const evidenceTypeHash = hash(input.evidenceTypeHash, 'evidenceTypeHash');
      details = { ...evidence, evidenceTypeHash };
      call = sdk.registerEvidence({ ...scope, subjectId: authority.authorityId,
        commitment: evidence.commitment, evidenceTypeHash, uri: '' });
    } else {
      const approval = await approvalContext(installation, input, snapshot);
      const { commitment, request } = approval;
      details = { ...approval };
      if (action === 'object') {
        const evidenceId = uint(input.evidenceId, 'evidenceId');
        details.evidenceId = evidenceId;
        call = sdk.registerObject({ ...scope, subjectId: authority.authorityId, objectTypeKey: approvalObject,
          objectCommitment: commitment, metadataHash: commitment, parentObjectId: 0n, evidenceReceiptId: evidenceId, uri: '' });
      } else if (action === 'allocate') {
        const requestId = uint(input.requestId, 'requestId');
        const [record, scoped] = await Promise.all([
          core.requests.read.getRequest([requestId], point), core.requests.read.scopedSupportByRequest([requestId], point),
        ]);
        if (scoped || record.packageId !== packageId || !same(record.appId, appId) || !same(record.workflowKey, workflowKey)
          || !same(record.input.executor, request.executor) || !same(record.input.responseClass, request.responseClass)
          || !same(record.input.burdenHash, request.burdenHash) || !same(record.input.parametersHash, request.parametersHash)
          || record.input.validUntil !== request.validUntil) throw new Error('Request does not match these Spark approval terms');
        details.requestId = requestId;
        details.stateId = record.input.recognisedStateId;
        call = sdk.allocate(requestId, authority);
      } else {
        const stateId = action === 'form' ? undefined : uint(input.stateId, 'stateId');
        const recognition = stateId === undefined ? undefined : await sdk.recognition(client, stateId, point);
        const object = recognition?.object ?? await core.kernel.read.getGovernedObject([uint(input.objectId, 'objectId')], point);
        if (object.packageId !== packageId || !same(object.appId, appId) || !same(object.workflowKey, workflowKey)
          || !same(object.objectTypeKey, approvalObject) || !same(object.objectCommitment, commitment)) {
          throw new Error('Governed object does not match these Spark approval terms');
        }
        details.objectId = object.id;
        details.evidenceId = object.evidenceReceiptId;
        if (action === 'form') {
          call = sdk.formRecognition({ ...authority, governedObjectId: object.id, stage: Stage.Verification,
            status: RecognitionStatus.Provisional, reasonHash: hash(input.reasonHash, 'reasonHash'), reasonURI: '' });
        } else {
          const state = recognition!.state;
          const required = { challengeable: RecognitionStatus.Provisional, vest: RecognitionStatus.Challengeable,
            request: RecognitionStatus.Vested }[action];
          if (state.stage !== Stage.Verification || state.status !== required) throw new Error('Unexpected recognition stage or status');
          details.stateId = state.id;
          details.transitionId = state.lastTransitionId;
          if (action === 'request') call = sdk.createRequest({ ...request, recognisedStateId: state.id }, authority);
          else {
            const transition = { ...authority, recognisedStateId: state.id, reasonHash: hash(input.reasonHash, 'reasonHash'),
              reasonURI: '', toStatus: action === 'vest' ? RecognitionStatus.Vested : RecognitionStatus.Challengeable };
            call = action === 'vest' ? sdk.vest(transition) : sdk.transition(transition);
          }
        }
      }
    }
    await sdk.simulate(client, account, call, avaAbis[operation.target], point);
    return { action, account, chainId, deploymentHash, genesisHash: hash(genesis.hash, 'genesis hash'),
      asOf: { blockNumber, blockHash, timestamp }, scope, details, call: { ...call, value: 0n } };
  });
}

async function observe(installation: Installation, intent: Fields, transactionHash: Hex) {
  const { client, sdk, deploymentHash } = installation, { chainId, addresses } = sdk.deployment;
  const action = actionName(intent.action), operation = actions[action], account = participantAddress(intent.account);
  const call = participantObject(intent.call), asOf = participantObject(intent.asOf);
  const address = addresses[operation.target], abi = avaAbis[operation.target];
  const blockNumber = uint(asOf.blockNumber, 'prepared block number', 256, true);
  const [actualChainId, genesis, preparedAt] = await Promise.all([
    client.getChainId(), client.getBlock({ blockNumber: 0n }), client.getBlock({ blockNumber }),
  ]);
  if (intent.chainId !== chainId || actualChainId !== chainId || !same(intent.deploymentHash, deploymentHash)
    || !genesis.hash || !same(intent.genesisHash, genesis.hash) || !preparedAt.hash || !same(asOf.blockHash, preparedAt.hash)
    || !same(call.to, address) || call.value !== '0' || typeof call.data !== 'string' || !/^0x(?:[0-9a-f]{2})+$/i.test(call.data)) {
    throw new Error('Prepared intent does not match the local installation or its canonical block');
  }
  const result = await observeParticipantOperation({ client, chainId, hash: transactionHash,
    contract: { address, abi }, account, data: call.data as Hex, operationId: operation.method, eventName: operation.event });
  if (result.status === 'confirmed' && 'events' in result && result.events) {
    const [event] = result.events;
    const id = participantObject(event.args)[operation.id];
    if (event.blockNumber <= blockNumber || typeof id !== 'bigint' || id <= 0n) return { action, status: 'mismatch', hash: transactionHash };
    return { action, ...result, id, idField: operation.id, nextAction: operation.next };
  }
  return { action, ...result };
}

if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try {
    const [configPath, command, inputPath, transactionHash, ...extra] = process.argv.slice(2);
    if (!configPath || !inputPath || extra.length || !((command === 'prepare' && !transactionHash)
      || (command === 'observe' && transactionHash))) {
      throw new Error('Usage: participant-approval-cli.ts <participant.json> prepare <action.json>\n'
        + '       participant-approval-cli.ts <participant.json> observe <intent.json> <transaction-hash>');
    }
    const input = participantObject(await readJson(inputPath));
    const installation = await loadInstallation(resolve(configPath));
    const result = command === 'prepare' ? await prepare(installation, input)
      : await observe(installation, input, hash(transactionHash, 'transaction hash'));
    console.log(JSON.stringify(jsonValue(result), null, 2));
  } catch (error) {
    console.error(error instanceof Error ? error.message : 'Spark participant operation failed');
    process.exitCode = 1;
  }
}
