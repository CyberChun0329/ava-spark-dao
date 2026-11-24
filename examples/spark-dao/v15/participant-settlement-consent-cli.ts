import { readFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { AvaExtensions, AvaSdk, jsonValue, localClient, withCanonicalSnapshot, type CanonicalSnapshot } from '@ava-protocol/sdk';
import type { PublicDeployment } from '@ava-protocol/sdk/deployment';
import { encodeFunctionData, isAddress, keccak256, parseSignature, recoverTypedDataAddress, toHex, zeroHash,
  type Abi, type AbiFunction, type AbiParameter, type Address, type Hex, type PublicClient, zeroAddress } from 'viem';
import { participantAddress, participantHash, participantObject } from './participant-payments.ts';
import { sparkV15 } from './payments.ts';

const { appId, workflowKey, sourceRole } = sparkV15;
const key = (s: string) => keccak256(toHex(s));
const same = (a: unknown, b: string) => typeof a === 'string' && a.toLowerCase() === b.toLowerCase();
const readJson = async (p: string): Promise<unknown> => JSON.parse(await readFile(p, 'utf8'));
const types = { OrdinarySettlementConsent: [
  { name: 'packageId', type: 'uint256' }, { name: 'lessonId', type: 'bytes32' },
  { name: 'basis', type: 'bytes32' }, { name: 'approver', type: 'address' },
  { name: 'sourceRole', type: 'bytes32' }, { name: 'sourceAuthorityId', type: 'bytes32' },
  { name: 'disclosurePolicyId', type: 'uint256' },
] } as const;
const wageTypes = { OrdinaryWageEvidence: [
  { name: 'commitment', type: 'bytes32' }, { name: 'packageId', type: 'uint256' },
  { name: 'sourceRole', type: 'bytes32' }, { name: 'sourceAuthorityId', type: 'bytes32' },
  { name: 'disclosurePolicyId', type: 'uint256' }, { name: 'validThrough', type: 'uint64' },
] } as const;

function compactSignature(value: unknown, label: string) {
  if (typeof value !== 'string' || !/^0x[0-9a-f]{130}$/i.test(value)) {
    throw new Error(`A 65-byte ${label} signature is required`);
  }
  const signature = value as Hex;
  const parsed = parseSignature(signature);
  if (parsed.yParity !== 0 && parsed.yParity !== 1) throw new Error('Invalid signature parity');
  const vs = toHex(BigInt(parsed.s) | (BigInt(parsed.yParity) << 255n), { size: 32 });
  return { signature, r: parsed.r, vs };
}

function hash(value: unknown, label: string): Hex {
  if (!participantHash(value) || same(value, zeroHash)) throw new Error(`${label} must be a nonzero bytes32`);
  return value;
}
function uint(value: unknown, label: string, bits = 256): bigint {
  if (typeof value === 'string' && /^[1-9][0-9]{0,77}$/.test(value)) {
    const n = BigInt(value);
    if (n < 1n << BigInt(bits)) return n;
  }
  throw new Error(`${label} must be a positive decimal uint${bits} string`);
}
function argument(param: AbiParameter, value: unknown): unknown {
  if (param.type.endsWith('[]')) {
    if (!Array.isArray(value) || value.length > 100) throw new Error('Invalid assessment array');
    return value.map(item => argument({ ...param, type: param.type.slice(0, -2) } as AbiParameter, item));
  }
  if (param.type === 'tuple' && 'components' in param) {
    const object = participantObject(value);
    return Object.fromEntries(param.components.map(item => [item.name, argument(item, object[item.name!])]));
  }
  if (param.type === 'address' && typeof value === 'string' && isAddress(value)) return value;
  if (param.type === 'bytes32' && participantHash(value)) return value;
  if (param.type === 'bool' && typeof value === 'boolean') return value;
  if (param.type.startsWith('uint') && (typeof value === 'string' || (typeof value === 'number' && Number.isSafeInteger(value)))
    && /^(0|[1-9][0-9]{0,77})$/.test(String(value))) {
    const parsed = BigInt(value), bits = Number(param.type.slice(4)) || 256;
    if (parsed < 1n << BigInt(bits)) return parsed;
  }
  throw new Error(`Invalid assessment field ${param.name ?? ''}`);
}
const completionFields = [
  { name: 'lessonId', type: 'bytes32' }, { name: 'formId', type: 'bytes32' },
  { name: 'endedAt', type: 'uint64' }, { name: 'endEvidenceId', type: 'uint256' },
  { name: 'reportRef', type: 'bytes32' }, { name: 'validThrough', type: 'uint64' },
] as const;
const attendanceFields = [
  ...completionFields.slice(0, 4), { name: 'attended', type: 'bool' }, ...completionFields.slice(4),
] as const;
type Contract = { address: Address; abi: Abi };

const settlementEntries = {
  registered: { approvalEntry: 'approveOrdinaryOneToOneWithConsent', previewEntry: 'previewOrdinaryGroup', recordsCount: 0 },
  local: { approvalEntry: 'approveOrdinaryOneToOneWithLocalRecords', previewEntry: 'previewOrdinaryOneToOneWithLocalRecords', recordsCount: 1 },
  attendance: { approvalEntry: 'approveOrdinaryOneToOneWithLocalAttendance', previewEntry: 'previewOrdinaryOneToOneWithLocalAttendance', recordsCount: 2 },
} as const;

async function prepareCompletionSignature(
  client: PublicClient, sdk: AvaSdk, booking: Contract, settlement: Contract, snapshot: CanonicalSnapshot,
  scope: { chainId: number; lessonId: Hex; formId: Hex; student: Address; coordinator: Address; assessment: unknown },
  action: 'student' | 'coordinator' | 'attendance', input: Record<string, unknown>,
) {
  const { point, timestamp } = snapshot;
  const { chainId, lessonId, formId, student, coordinator, assessment } = scope;
  const account = participantAddress(input.account);
  if (!same(account, action === 'coordinator' ? coordinator : student)) throw new Error('Account is not the recorded participant');
  const reportRef = hash(input.reportRef, 'reportRef'), validThrough = uint(input.validThrough, 'validThrough', 64);
  const teaching = await client.readContract({ ...booking, functionName: 'getTeaching', args: [lessonId], ...point }) as
    { endedAt: bigint; endEvidenceId: bigint };
  const { endedAt, endEvidenceId } = teaching;
  if (!endedAt || !endEvidenceId || timestamp > validThrough) throw new Error('Lesson end evidence or consent window is unavailable');
  const domain = { name: 'Spark DAO One-to-One Settlement Records', version: '1', chainId, verifyingContract: settlement.address };
  const message = { lessonId, formId, endedAt, endEvidenceId, reportRef, validThrough };
  if (action === 'attendance') {
    if (input.attended !== true) throw new Error('Attendance preparation requires an affirmative attendance statement');
    return { account, typedData: { domain, primaryType: 'StudentAttendance',
      types: { StudentAttendance: attendanceFields }, message: { ...message, attended: true } } };
  }
  if (action === 'student') {
    return { account, typedData: { domain, primaryType: 'StudentCompletion',
      types: { StudentCompletion: completionFields }, message } };
  }
  const [coordinatorRole, proposal] = await Promise.all([
    client.readContract({ ...booking, functionName: 'COORDINATOR_ROLE', ...point }),
    client.readContract({ ...settlement, functionName: 'proposalCommitment', args: [lessonId, assessment], ...point }),
  ]);
  const actor = await sdk.actorContext(client, { appId, account, roleKey: hash(coordinatorRole, 'coordinator role'),
    actionKeys: [key('spark.action.confirm-one-to-one-completion.v1.5'), key('spark.action.propose-group-settlement.v1.5')] }, point);
  if (!actor.authority || actor.permissions.length !== 2 || !actor.permissions.every(permission => permission.allowed)) {
    throw new Error('Coordinator lacks current completion or proposal authority');
  }
  const proposalCommitment = hash(proposal, 'proposal commitment');
  return { account, typedData: { domain, primaryType: 'CoordinatorCompletionAndProposal',
    types: { CoordinatorCompletionAndProposal: [...completionFields,
      { name: 'proposalCommitment', type: 'bytes32' }, { name: 'authorityId', type: 'bytes32' }] },
    message: { ...message, proposalCommitment, authorityId: actor.authority.authorityId } } };
}
async function prepare(configPath: string, input: Record<string, unknown>) {
  const action = input.action;
  const signing = action === 'student' || action === 'coordinator' || action === 'attendance';
  if (!signing && action !== 'source' && action !== 'approver') throw new Error('Unknown participant action');
  const local = signing || Object.hasOwn(input, 'localRecords');
  const attendance = action === 'attendance' || (!signing && Object.hasOwn(input, 'signedAttendance'));
  if (attendance && !local) throw new Error('Attendance adoption also requires localRecords');
  const wageInput = Object.hasOwn(input, 'wageEvidence') ? participantObject(input.wageEvidence) : undefined;
  if (wageInput && (signing || !attendance || Object.hasOwn(input, 'paymentEvidenceIds'))) {
    throw new Error('First-use wage evidence requires signed attendance and replaces the payment evidence ID');
  }
  const config = participantObject(await readJson(configPath));
  if (typeof config.rpcUrl !== 'string' || typeof config.deploymentPath !== 'string' || !config.deploymentPath.trim()) throw new Error('Missing participant installation');
  const rpc = new URL(config.rpcUrl);
  if (rpc.protocol !== 'http:' || rpc.hostname !== '127.0.0.1' || rpc.username || rpc.password || rpc.pathname !== '/' || rpc.search || rpc.hash) throw new Error('Use an HTTP loopback origin');
  const contents = await readFile(resolve(dirname(configPath), config.deploymentPath));
  const declaration = JSON.parse(contents.toString('utf8')) as PublicDeployment;
  const profile = declaration.workflows?.[appId]?.[workflowKey] ?? declaration.apps?.[appId];
  if (declaration.schemaVersion !== 1 || declaration.deployment?.chainId !== 31337 || !profile || !same(profile.appId, appId) || !same(profile.workflowKey, workflowKey)) throw new Error('Expected the exported local Spark v1.5 deployment');
  const { SparkV15Booking: booking, SparkV15Funds: funds, SparkV15Payments: payments, SparkV15Settlement: settlement, SparkV15ApplicationModule: application } = profile.contracts;
  for (const contract of [booking, funds, payments, settlement, application]) {
    if (!contract || !Array.isArray(contract.abi)) throw new Error('Incomplete Spark deployment');
    participantAddress(contract.address);
  }
  const abi = settlement.abi as Abi;
  const route = settlementEntries[attendance ? 'attendance' : local ? 'local' : 'registered'];
  const { previewEntry, recordsCount } = route;
  const approvalEntry = wageInput ? 'approveOrdinaryOneToOneWithAdoptedWage' : route.approvalEntry;
  const entry = abi.find((item): item is AbiFunction => item.type === 'function' && item.name === approvalEntry);
  if (!entry || entry.inputs.length !== 4 + recordsCount
    || !abi.some(item => item.type === 'function' && item.name === previewEntry && item.inputs.length === 3 + recordsCount)) {
    throw new Error('Requested settlement entry is unavailable in this installation');
  }
  const assessment = argument(entry.inputs[1], input.assessment);
  const localRecords = local && !signing ? argument(entry.inputs[4], input.localRecords) : undefined;
  const signedAttendance = attendance && !signing ? argument(entry.inputs[5], input.signedAttendance) : undefined;
  const rawAssessment = participantObject(input.assessment);
  if (String(rawAssessment.route) !== '2' || !Array.isArray(rawAssessment.seats) || rawAssessment.seats.length !== 1) throw new Error('Pilot supports ordinary one-to-one only');
  const seat = participantObject(rawAssessment.seats[0]);
  const formId = hash(seat.formId, 'formId'), lessonId = hash(input.lessonId, 'lessonId');
  if (localRecords && !same(participantObject(localRecords).formId, formId)) throw new Error('Local records do not match the assessment form');
  const packageId = uint(profile.packageId, 'packageId'), disclosurePolicyId = uint(profile.disclosurePolicyId, 'disclosurePolicyId');
  const client = localClient(rpc.origin), sdk = new AvaSdk(declaration.deployment);
  return withCanonicalSnapshot(client, async snapshot => {
    const { point, blockNumber, blockHash, timestamp } = snapshot;
    const core = sdk.contracts(client);
    const [chainId, genesis, readiness, policy, bookingFunds, bookingRequests, workflow, settlementBooking, settlementPayments, token, verifierRole, lesson, proposal] = await Promise.all([
      client.getChainId(), client.getBlock({ blockNumber: 0n }),
      new AvaExtensions(sdk, {}).verifyInstallation(client, { appId, workflowKey, activePackageId: packageId, modules: [{ capabilityKey: key('ava.capability.application.v1'), module: application.address }] }, point),
      core.disclosure.read.getPolicy([disclosurePolicyId], point),
      client.readContract({ ...booking, functionName: 'FUNDS', ...point }), client.readContract({ ...booking, functionName: 'REQUEST_ALLOCATION', ...point }),
      client.readContract({ ...booking, functionName: 'WORKFLOW', ...point }), client.readContract({ ...settlement, functionName: 'BOOKING', ...point }),
      client.readContract({ ...settlement, functionName: 'PAYMENTS', ...point }), client.readContract({ ...funds, functionName: 'TOKEN', ...point }),
      client.readContract({ ...payments, functionName: 'VERIFIER_ROLE', ...point }),
      client.readContract({ ...booking, functionName: 'getLesson', args: [lessonId], ...point }) as Promise<{ packageId: bigint; terms: { rosterRef: Hex; materialsTermsRef: Hex; coordinator: Address } }>,
      client.readContract({ ...settlement, functionName: 'proposals', args: [lessonId], ...point }) as Promise<readonly [Hex, Address, Hex, bigint]>,
    ]);
    if (chainId !== 31337 || !readiness.ready || !same(policy.appId, appId) || !same(bookingFunds, funds.address) || !same(bookingRequests, sdk.deployment.addresses.requests)
      || !same(workflow, workflowKey) || !same(settlementBooking, booking.address) || !same(settlementPayments, payments.address) || !same(token, participantAddress(config.token))) throw new Error('Current chain does not match the recorded installation');
    const proposer = lesson.terms.coordinator;
    if (lesson.packageId !== packageId || !same(lesson.terms.rosterRef, zeroHash) || !same(lesson.terms.materialsTermsRef, zeroHash)
      || !same(proposal[1], local ? zeroAddress : proposer)) throw new Error('Lesson or existing proposal is outside the requested pilot');
    const form = await client.readContract({ ...booking, functionName: 'getForm', args: [formId], ...point }) as
      { lessonId: Hex; confirmation: { confirmedAt: bigint }; terms: { materialsBundleRef: Hex; student: Address } };
    if (!same(form.terms.materialsBundleRef, zeroHash)) throw new Error('Materials are outside the pilot');
    const context = { action, chainId, genesisHash: hash(genesis.hash, 'genesis hash'), deploymentHash: keccak256(contents),
      asOf: { blockNumber, blockHash, timestamp }, lessonId, assessment };
    if (signing) {
      if (!same(form.lessonId, lessonId) || !form.confirmation.confirmedAt) throw new Error('Expected the confirmed form for this lesson');
      const details = await prepareCompletionSignature(client, sdk, booking, settlement, snapshot,
        { chainId, lessonId, formId, student: form.terms.student, coordinator: proposer, assessment }, action, input);
      return { ...context, ...details };
    }

    const source = participantAddress(input.source), approver = participantAddress(input.approver);
    if (same(source, proposer) || same(source, approver) || same(approver, proposer)) throw new Error('Settlement actors must be independent');
    const records = local ? [localRecords] : [];
    if (attendance) records.push(signedAttendance);
    const [sourceActor, approverActor, preview] = await Promise.all([
      sdk.actorContext(client, { appId, account: source, roleKey: sourceRole, actionKeys: [key('ava.core.register-evidence.v1')] }, point),
      sdk.actorContext(client, { appId, account: approver, roleKey: hash(verifierRole, 'verifier role'), actionKeys: [key('spark.action.approve-group-settlement.v1.5')] }, point),
      client.readContract({ ...settlement, functionName: previewEntry,
        args: [lessonId, assessment, approver, ...records], ...point }) as
        Promise<{ basis: Hex; payments: readonly unknown[] }>,
    ]);
    if (!sourceActor.authority || !sourceActor.permissions[0]?.allowed || !approverActor.authority || !approverActor.permissions[0]?.allowed) throw new Error('Source or approver lacks current authority');
    const basis = hash(preview.basis, 'settlement basis'), sourceAuthorityId = sourceActor.authority.authorityId;
    const typedData = { domain: { name: 'Spark DAO Ordinary Settlement', version: '1', chainId, verifyingContract: settlement.address as Address }, types,
      primaryType: 'OrdinarySettlementConsent' as const, message: { packageId, lessonId, basis, approver, sourceRole, sourceAuthorityId, disclosurePolicyId } };
    let wageDetails;
    if (wageInput) {
      const wageSource = participantAddress(wageInput.source);
      const validThrough = uint(wageInput.validThrough, 'wage evidence validThrough', 64);
      if (same(wageSource, proposer) || same(wageSource, approver) || timestamp > validThrough || preview.payments.length !== 1) {
        throw new Error('First-use proof requires one new wage, an independent Source and a current adoption window');
      }
      const [wageActor, commitment] = await Promise.all([
        same(wageSource, source) ? sourceActor :
          sdk.actorContext(client, { appId, account: wageSource, roleKey: sourceRole, actionKeys: [key('ava.core.register-evidence.v1')] }, point),
        client.readContract({ ...payments, functionName: 'paymentEvidenceCommitment', args: [preview.payments[0], basis], ...point }),
      ]);
      if (!wageActor.authority || !wageActor.permissions[0]?.allowed) throw new Error('Wage Source lacks current authority');
      wageDetails = { wageSource, wageTypedData: {
        domain: { name: 'Spark DAO Ordinary Wage Evidence', version: '1', chainId, verifyingContract: settlement.address as Address },
        types: wageTypes,
        primaryType: 'OrdinaryWageEvidence' as const,
        message: { commitment: hash(commitment, 'wage commitment'), packageId, sourceRole,
          sourceAuthorityId: wageActor.authority.authorityId, disclosurePolicyId, validThrough },
      } };
    }
    let call;
    if (action === 'approver') {
      const { signature, r, vs } = compactSignature(input.signature, 'settlement Source');
      if (!same(await recoverTypedDataAddress({ ...typedData, signature }), source)) throw new Error('Signature does not match the current Source and settlement');
      let paymentEvidence;
      if (wageInput && wageDetails) {
        const wageSignature = compactSignature(wageInput.signature, 'wage Source');
        const { wageSource, wageTypedData } = wageDetails;
        if (!same(await recoverTypedDataAddress({ ...wageTypedData, signature: wageSignature.signature }), wageSource)) {
          throw new Error('Signature does not match the current Wage Source and exact obligation');
        }
        paymentEvidence = { sourceRole, sourceAuthorityId: wageTypedData.message.sourceAuthorityId, disclosurePolicyId,
          validThrough: wageTypedData.message.validThrough, r: wageSignature.r, vs: wageSignature.vs };
      } else {
        if (!Array.isArray(input.paymentEvidenceIds) || input.paymentEvidenceIds.length !== preview.payments.length) {
          throw new Error('Provide one independent payment evidence ID per obligation');
        }
        paymentEvidence = input.paymentEvidenceIds.map((id, index) => uint(id, `paymentEvidenceIds[${index}]`));
      }
      const args = [lessonId, assessment, { sourceRole, sourceAuthorityId, disclosurePolicyId, r, vs }, paymentEvidence, ...records];
      const data = encodeFunctionData({ abi, functionName: approvalEntry, args });
      await client.call({ account: approver, to: settlement.address as Address, data, ...point });
      call = { to: settlement.address, data, value: '0' };
    }
    const proposalContext = local ? { proposer, adopted: false } : proposal;
    return { ...context, source, approver, proposal: proposalContext, preview, basis, typedData,
      ...(local ? { localRecords } : {}), ...(attendance ? { signedAttendance } : {}), ...wageDetails, ...(call ? { call } : {}) };
  });
}
if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try {
    const [configPath, command, inputPath, ...extra] = process.argv.slice(2);
    if (!configPath || command !== 'prepare' || !inputPath || extra.length) throw new Error('Usage: participant-settlement-consent-cli.ts <participant.json> prepare <input.json>');
    console.log(JSON.stringify(jsonValue(await prepare(resolve(configPath), participantObject(await readJson(inputPath)))), null, 2));
  } catch (error) {
    console.error(error instanceof Error ? error.message : 'Spark settlement preparation failed');
    process.exitCode = 1;
  }
}
