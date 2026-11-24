import { readFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { AvaExtensions, AvaSdk, jsonValue, localClient, withCanonicalSnapshot, type CanonicalSnapshot } from '@ava-protocol/sdk';
import type { PublicDeployment } from '@ava-protocol/sdk/deployment';
import { concatHex, encodeAbiParameters, encodeFunctionData, getAddress, hashStruct, keccak256, parseAbi, parseAbiParameters, parseSignature,
  recoverTypedDataAddress, toHex, zeroAddress, zeroHash, type Abi, type AbiFunction, type Address, type Hex } from 'viem';
import { participantAddress, participantHash, participantObject } from './participant-payments.ts';
import { sparkV15, type SparkV15ApprovalTerms } from './payments.ts';

const { appId, workflowKey, sourceRole } = sparkV15;
const key = (name: string) => keccak256(toHex(name));
const same = (actual: unknown, expected: string) => typeof actual === 'string' && actual.toLowerCase() === expected.toLowerCase();
const readJson = async (path: string): Promise<unknown> => JSON.parse(await readFile(path, 'utf8'));
const commands = ['prepare-grant', 'prepare-booking-signature', 'prepare-booking-adoption',
  'prepare-occurrence', 'prepare-prefunding', 'prepare-notice'] as const;
const usage = `Usage: participant-ordinary-cli.ts <participant.json> <${commands.join('|')}> <input.json>`;

function hash(value: unknown, label: string): Hex {
  if (!participantHash(value) || same(value, zeroHash)) throw new Error(`${label} must be a nonzero bytes32`);
  return value;
}

function uint(value: unknown, label: string, bits = 256): bigint {
  if (typeof value === 'string' && /^[1-9][0-9]{0,77}$/.test(value)) {
    const parsed = BigInt(value);
    if (parsed < 1n << BigInt(bits)) return parsed;
  }
  throw new Error(`${label} must be a positive decimal uint${bits} string`);
}

async function loadInstallation(configPath: string) {
  const config = participantObject(await readJson(configPath));
  if (typeof config.rpcUrl !== 'string' || typeof config.deploymentPath !== 'string' || !config.deploymentPath.trim()) {
    throw new Error('The participant configuration needs rpcUrl and deploymentPath');
  }
  const rpc = new URL(config.rpcUrl);
  if (rpc.protocol !== 'http:' || rpc.hostname !== '127.0.0.1' || rpc.username || rpc.password
    || rpc.pathname !== '/' || rpc.search || rpc.hash) throw new Error('Use an HTTP loopback origin');

  const contents = await readFile(resolve(dirname(configPath), config.deploymentPath));
  const declaration = JSON.parse(contents.toString('utf8')) as PublicDeployment;
  const profile = declaration.workflows?.[appId]?.[workflowKey] ?? declaration.apps?.[appId];
  if (declaration.schemaVersion !== 1 || declaration.deployment?.chainId !== 31337
    || !profile || !same(profile.appId, appId) || !same(profile.workflowKey, workflowKey)) {
    throw new Error('Expected the exported local Spark v1.5 deployment');
  }
  const { contracts } = profile;
  function contract(name: string) {
    const item = contracts[name];
    if (!item || !Array.isArray(item.abi)) throw new Error(`Missing installation ABI for ${name}`);
    return { address: participantAddress(item.address), abi: item.abi as Abi };
  }
  return { client: localClient(rpc.origin), sdk: new AvaSdk(declaration.deployment), contract,
    application: contract('SparkV15ApplicationModule'), token: participantAddress(config.token),
    packageId: uint(profile.packageId, 'packageId'), disclosurePolicyId: profile.disclosurePolicyId,
    deploymentHash: keccak256(contents) };
}

type Installation = Awaited<ReturnType<typeof loadInstallation>>;

async function verifyInstallation(installation: Installation, { point }: CanonicalSnapshot) {
  const { client, sdk, application, packageId } = installation;
  const [chainId, genesis, readiness] = await Promise.all([
    client.getChainId(), client.getBlock({ blockNumber: 0n }),
    new AvaExtensions(sdk, {}).verifyInstallation(client, { appId, workflowKey, activePackageId: packageId,
      modules: [{ capabilityKey: key('ava.capability.application.v1'), module: application.address }] }, point),
  ]);
  if (chainId !== sdk.deployment.chainId || !readiness.ready) {
    throw new Error('Current chain does not match the recorded Spark installation');
  }
  return { chainId, genesisHash: hash(genesis.hash, 'genesis hash') };
}

async function requireAuthority({ client, sdk }: Installation, account: Address, roleKey: Hex,
  actionKey: string, { point }: CanonicalSnapshot) {
  const actor = await sdk.actorContext(client, { appId, account, roleKey, actionKeys: [key(actionKey)] }, point);
  if (!actor.authority || !actor.permissions[0]?.allowed) throw new Error(`Account lacks current authority for ${actionKey}`);
  return actor.authority;
}

const occurrenceAbi = parseAbi([
  'function TEACHING_END() view returns (address)',
  'function SERVICE_REPORTS() view returns (address)',
  'function COURSE_NOTICES() view returns (address)',
  'struct SourceProof { bytes32 sourceRole; bytes32 sourceAuthorityId; uint256 disclosurePolicyId; uint64 validThrough; bytes32 r; bytes32 vs; }',
  'struct StartObservation { uint64 occurredAt; bool providerWentAhead; address[] studentsTakingLesson; bytes32 occurrenceRef; bytes32 unmetConditionRef; }',
  'function recordOrdinaryTeachingStarted(bytes32 lessonId, StartObservation observation, SourceProof proof)',
  'function recordOrdinaryTeachingEnded(bytes32 lessonId, uint64 occurredAt, bytes32 occurrenceRef, SourceProof proof)',
  'function recordFullServiceFeedback(bytes32 formId, bytes32 receivedRef, SourceProof proof)',
  'function recordCompletedTutorDelivery(bytes32 lessonId, bytes32 detailsRef, SourceProof proof)',
  'function recordStudentNoticeWithConsent(bytes32 formId, uint64 deliveredAt, bytes32 deliveryRef, SourceProof proof)',
  'function recordTutorNoticeWithConsent(bytes32 lessonId, bytes32 channelRef, uint64 deliveredAt, bytes32 deliveryRef, SourceProof proof)',
]);
const occurrenceSourceFields = [
  { name: 'sourceRole', type: 'bytes32' }, { name: 'sourceAuthorityId', type: 'bytes32' },
  { name: 'disclosurePolicyId', type: 'uint256' }, { name: 'validThrough', type: 'uint64' },
] as const;

async function preparePrefunding(installation: Installation, input: Record<string, unknown>,
  snapshot: CanonicalSnapshot, chainId: number) {
  const { client, contract, packageId } = installation;
  const { point, timestamp } = snapshot;
  const booking = contract('SparkV15Booking');
  const opening = contract('SparkV15BookingOpening');
  const prefunding = contract('SparkV15BookingPrefunding');
  const lesson = participantObject(input.lesson), place = participantObject(input.place);
  const verifier = participantAddress(input.account), source = participantAddress(input.source);
  const coordinator = participantAddress(lesson.coordinator), lessonId = hash(lesson.lessonId, 'lessonId');
  const requiredUnits = uint(input.requiredUnits, 'requiredUnits', 128), fundingRef = hash(input.fundingRef, 'fundingRef');
  const validThrough = uint(input.validThrough, 'validThrough', 64);
  const draftValidThrough = uint(input.draftValidThrough, 'draftValidThrough', 64);
  const disclosurePolicyId = uint(installation.disclosurePolicyId, 'disclosurePolicyId');
  if (same(source, verifier) || same(source, coordinator) || same(coordinator, verifier)) {
    throw new Error('The Source, coordinator and verifier use separate accounts');
  }
  if (validThrough < timestamp || draftValidThrough < timestamp) throw new Error('A signature window has already expired');
  const [openingAddress, fundingAddress, role, lessonScope, sourceAuthority, policy] = await Promise.all([
    client.readContract({ ...booking, functionName: 'OPENING', ...point }),
    client.readContract({ ...booking, functionName: 'PREFUNDING', ...point }),
    client.readContract({ ...booking, functionName: 'VERIFIER_ROLE', ...point }),
    client.readContract({ ...opening, functionName: 'prepareLesson', args: [lesson], ...point }) as Promise<readonly [bigint, Hex]>,
    requireAuthority(installation, source, sourceRole, 'ava.core.register-evidence.v1', snapshot),
    installation.sdk.contracts(client).disclosure.read.getPolicy([disclosurePolicyId], point),
  ]);
  if (!same(openingAddress, opening.address) || !same(fundingAddress, prefunding.address)
    || !same(policy.appId, appId) || lessonScope[0] !== packageId) {
    throw new Error('The draft or evidence policy is outside this installed Spark package');
  }
  await requireAuthority(installation, verifier, hash(role, 'verifierRole'), 'spark.action.verify-booking-funding.v1.5', snapshot);
  const publishForm = booking.abi.find((item): item is AbiFunction => item.type === 'function' && item.name === 'publishForm');
  if (!publishForm) throw new Error('The installation does not expose the confirmed-form format');
  const formId = keccak256(encodeAbiParameters(
    [{ type: 'bytes32' }, { type: 'uint64' }, publishForm.inputs[1]], [lessonScope[1], 1n, place]
  ));
  const commitment = keccak256(encodeAbiParameters(parseAbiParameters('bytes32, bytes32, bytes32[], uint128, bytes32'),
    [key('spark.v1.5.booking.verified-prefunding'), lessonScope[1], [formId], requiredUnits, fundingRef]));
  const sourceTypedData = {
    domain: { name: 'Spark DAO Prefunding Evidence', version: '1', chainId, verifyingContract: getAddress(prefunding.address) },
    primaryType: 'PrefundingEvidence' as const,
    types: { PrefundingEvidence: [
      { name: 'packageId', type: 'uint256' }, { name: 'lessonId', type: 'bytes32' },
      { name: 'commitment', type: 'bytes32' }, { name: 'verifier', type: 'address' }, ...occurrenceSourceFields,
    ] as const },
    message: { packageId, lessonId, commitment, verifier, sourceRole,
      sourceAuthorityId: sourceAuthority.authorityId, disclosurePolicyId, validThrough },
  };
  const evidenceId = BigInt(hashStruct({
    data: sourceTypedData.message, primaryType: sourceTypedData.primaryType, types: sourceTypedData.types,
  }));
  const draftTypedData = {
    domain: { name: 'Spark DAO Booking Draft', version: '1', chainId, verifyingContract: getAddress(booking.address) },
    primaryType: 'AdoptOrdinaryBookingDraft' as const,
    types: { AdoptOrdinaryBookingDraft: [
      { name: 'formId', type: 'bytes32' }, { name: 'requiredUnits', type: 'uint128' },
      { name: 'fundingRef', type: 'bytes32' }, { name: 'fundingEvidenceId', type: 'uint256' },
      { name: 'verifier', type: 'address' }, { name: 'validThrough', type: 'uint64' },
    ] as const },
    message: { formId, requiredUnits, fundingRef, fundingEvidenceId: evidenceId, verifier, validThrough: draftValidThrough },
  };
  const preparation = { source, coordinator, verifier, lessonId, formId, commitment, evidenceId, sourceTypedData, draftTypedData };
  if (input.sourceSignature === undefined && input.draftSignature === undefined) return preparation;
  const sourceSignature = occurrenceSignature(input.sourceSignature, 'Source signature');
  if (!same(await recoverTypedDataAddress({ ...sourceTypedData, signature: sourceSignature }), source)) {
    throw new Error('Signature does not match the current Source and this funding proof');
  }
  if (input.draftSignature === undefined) return preparation;
  const draftSignature = occurrenceSignature(input.draftSignature, 'coordinator signature');
  if (!same(await recoverTypedDataAddress({ ...draftTypedData, signature: draftSignature }), coordinator)) {
    throw new Error('Signature does not match the coordinator and this draft');
  }
  const { r, vs } = compactOccurrenceSignature(sourceSignature);
  const draft = compactOccurrenceSignature(draftSignature);
  const proof = { sourceRole, sourceAuthorityId: sourceAuthority.authorityId, disclosurePolicyId, validThrough, r, vs };
  const data = encodeFunctionData({ abi: prefunding.abi, functionName: 'adoptOrdinaryBookingDraftWithPrefundingProof',
    args: [lesson, place, requiredUnits, fundingRef, draftValidThrough, draft.r, draft.vs, proof] });
  await client.call({ account: verifier, to: prefunding.address, data, ...point });
  return { ...preparation, call: { from: verifier, to: prefunding.address, data, value: 0n } };
}

function occurrenceSignature(value: unknown, label: string): Hex {
  if (typeof value !== 'string' || !/^0x[0-9a-f]{130}$/i.test(value)) {
    throw new Error(`A 65-byte ${label} is required`);
  }
  return value as Hex;
}

function compactOccurrenceSignature(signature: Hex) {
  const { r, s, yParity } = parseSignature(signature);
  if (yParity !== 0 && yParity !== 1) throw new Error('Invalid signature parity');
  return { r, vs: toHex(BigInt(s) | (BigInt(yParity) << 255n), { size: 32 }) };
}

async function prepareNotice(installation: Installation, input: Record<string, unknown>,
  snapshot: CanonicalSnapshot, chainId: number) {
  const { client, contract, sdk, packageId } = installation;
  const { point, timestamp } = snapshot;
  const booking = contract('SparkV15Booking');
  const source = participantAddress(input.source), actor = participantAddress(input.account);
  const deliveredAt = uint(input.deliveredAt, 'deliveredAt', 64), deliveryRef = hash(input.deliveryRef, 'deliveryRef');
  const validThrough = uint(input.validThrough, 'validThrough', 64);
  const disclosurePolicyId = uint(installation.disclosurePolicyId, 'disclosurePolicyId');
  if (input.kind !== 'student' && input.kind !== 'tutor') throw new Error('Expected a student or tutor notice');
  if (same(source, actor) || validThrough < timestamp || deliveredAt > timestamp) {
    throw new Error('The notice requires a separate Source, an unexpired adoption window and a past delivery');
  }
  const target = input.kind === 'student' ? { kind: 'student' as const, formId: hash(input.formId, 'formId') }
    : { kind: 'tutor' as const, lessonId: hash(input.lessonId, 'lessonId'), channelRef: hash(input.channelRef, 'channelRef') };
  const lessonId = target.kind === 'student' ? (await client.readContract({
    ...booking, functionName: 'getForm', args: [target.formId], ...point,
  }) as { lessonId: Hex }).lessonId : target.lessonId;
  const [opening, lesson, commitment, policy, sourceAuthority] = await Promise.all([
    client.readContract({ ...booking, functionName: 'OPENING', ...point }),
    client.readContract({ ...booking, functionName: 'getLesson', args: [lessonId], ...point }) as Promise<{
      packageId: bigint; terms: { provider: Address; coordinator: Address };
    }>,
    target.kind === 'student' ? client.readContract({ ...booking, functionName: 'studentNoticeCommitment',
      args: [target.formId, deliveredAt, deliveryRef], ...point })
      : client.readContract({ ...booking, functionName: 'tutorNoticeCommitment',
        args: [lessonId, target.channelRef, deliveredAt, deliveryRef], ...point }),
    sdk.contracts(client).disclosure.read.getPolicy([disclosurePolicyId], point),
    requireAuthority(installation, source, sourceRole, 'ava.core.register-evidence.v1', snapshot),
  ]);
  if (lesson.packageId !== packageId || !same(policy.appId, appId)) throw new Error('The notice uses a different package');
  const providerNotice = target.kind === 'tutor' && same(actor, lesson.terms.provider);
  if (!providerNotice) {
    if (!same(actor, lesson.terms.coordinator)) throw new Error('The account must be the coordinator or the provider for a tutor notice');
    const role = await client.readContract({ ...booking, functionName: 'COORDINATOR_ROLE', ...point });
    await requireAuthority(installation, actor, hash(role, 'coordinator role'), 'spark.action.coordinate-booking.v1.5', snapshot);
  }
  const to = await client.readContract({ address: participantAddress(opening), abi: occurrenceAbi, functionName: 'COURSE_NOTICES', ...point });
  const primaryType = target.kind === 'student' ? 'StudentNoticeEvidence' : 'TutorNoticeEvidence';
  const typedData = {
    domain: { name: 'Spark DAO Course Notice Evidence', version: '1', chainId, verifyingContract: getAddress(to) },
    primaryType,
    types: { [primaryType]: [
      { name: 'commitment', type: 'bytes32' }, { name: 'packageId', type: 'uint256' },
      { name: 'actor', type: 'address' }, ...occurrenceSourceFields,
    ] as const },
    message: { commitment: hash(commitment, 'commitment'), packageId, actor, sourceRole,
      sourceAuthorityId: sourceAuthority.authorityId, disclosurePolicyId, validThrough },
  };
  const preparation = { kind: target.kind, lessonId, source, actor, deliveredAt, deliveryRef, typedData };
  if (input.signature === undefined) return preparation;
  const signature = occurrenceSignature(input.signature, 'Source signature');
  if (!same(await recoverTypedDataAddress({ ...typedData, signature }), source)) {
    throw new Error('Signature does not match the current Source and this notice');
  }
  const proof = { sourceRole, sourceAuthorityId: sourceAuthority.authorityId, disclosurePolicyId, validThrough,
    ...compactOccurrenceSignature(signature) };
  const data = target.kind === 'student'
    ? encodeFunctionData({ abi: occurrenceAbi, functionName: 'recordStudentNoticeWithConsent',
      args: [target.formId, deliveredAt, deliveryRef, proof] })
    : encodeFunctionData({ abi: occurrenceAbi, functionName: 'recordTutorNoticeWithConsent',
      args: [lessonId, target.channelRef, deliveredAt, deliveryRef, proof] });
  await client.call({ account: actor, to, data, ...point });
  return { ...preparation, call: { from: actor, to, data, value: 0n } };
}

async function prepareOccurrence(installation: Installation, input: Record<string, unknown>,
  snapshot: CanonicalSnapshot, chainId: number) {
  const { client, contract, sdk, packageId } = installation;
  const { point, timestamp } = snapshot;
  const booking = contract('SparkV15Booking');
  const source = participantAddress(input.source);
  const account = participantAddress(input.account);
  const validThrough = uint(input.validThrough, 'validThrough', 64);
  const disclosurePolicyId = uint(installation.disclosurePolicyId, 'disclosurePolicyId');
  if (input.kind !== 'teaching-start' && input.kind !== 'teaching-end'
    && input.kind !== 'full-service-feedback' && input.kind !== 'tutor-completion') {
    throw new Error('Expected teaching-start, teaching-end, full-service-feedback or tutor-completion');
  }
  if (same(source, account) || validThrough < timestamp) {
    throw new Error('The proof requires a separate Source and an unexpired adoption window');
  }
  const sourceAuthority = await requireAuthority(installation, source, sourceRole, 'ava.core.register-evidence.v1', snapshot);
  const [opening, policy] = await Promise.all([
    client.readContract({ ...booking, functionName: 'OPENING', ...point }),
    sdk.contracts(client).disclosure.read.getPolicy([disclosurePolicyId], point),
  ]);
  if (!same(policy.appId, appId)) throw new Error('Disclosure policy is outside this Spark installation');
  const isStart = input.kind === 'teaching-start';
  const isEnd = input.kind === 'teaching-end';
  const isTutor = input.kind === 'tutor-completion';
  const primaryType = isStart ? 'TeachingStartEvidence' : isEnd ? 'TeachingEndEvidence'
    : isTutor ? 'CompletedTutorDelivery' : 'FullServiceFeedback';
  const to = await client.readContract({ address: participantAddress(opening), abi: occurrenceAbi,
    functionName: isStart || isEnd ? 'TEACHING_END' : 'SERVICE_REPORTS', ...point });
  const domain = { name: isStart ? 'Spark DAO Teaching Start Evidence' : isEnd ? 'Spark DAO Teaching End Evidence'
    : isTutor ? 'Spark DAO Completed Tutor Delivery' : 'Spark DAO Full Service Feedback',
    version: '1', chainId, verifyingContract: to };
  const common = { packageId, sourceRole, sourceAuthorityId: sourceAuthority.authorityId, disclosurePolicyId, validThrough };
  const scope = await (async () => {
    if (isStart || isEnd) {
      const lessonId = hash(input.lessonId, 'lessonId');
      const occurrence = isStart ? { kind: 'start' as const, lessonId, observation: startObservation(input.observation) }
        : { kind: 'end' as const, lessonId, occurredAt: uint(input.occurredAt, 'occurredAt', 64),
          occurrenceRef: hash(input.occurrenceRef, 'occurrenceRef') };
      const [lesson, commitment, role] = await Promise.all([
        client.readContract({ ...booking, functionName: 'getLesson', args: [lessonId], ...point }) as Promise<{ packageId: bigint }>,
        occurrence.kind === 'start'
          ? client.readContract({ ...booking, functionName: 'teachingStartCommitment', args: [lessonId, occurrence.observation], ...point })
          : client.readContract({ ...booking, functionName: 'teachingEndCommitment',
            args: [lessonId, occurrence.occurredAt, occurrence.occurrenceRef], ...point }),
        client.readContract({ ...booking, functionName: 'VERIFIER_ROLE', ...point }),
      ]);
      if (lesson.packageId !== packageId) throw new Error('The lesson uses a different package');
      await requireAuthority(installation, account, hash(role, 'verifierRole'), 'spark.action.verify-teaching-occurrence.v1.5', snapshot);
      return { ...occurrence, message: { ...common, lessonId,
        commitment: hash(commitment, 'commitment'), verifier: account }, fields: [
        { name: 'packageId', type: 'uint256' }, { name: 'lessonId', type: 'bytes32' },
        { name: 'commitment', type: 'bytes32' }, { name: 'verifier', type: 'address' },
      ] };
    }
    if (isTutor) {
      const lessonId = hash(input.lessonId, 'lessonId'), detailsRef = hash(input.detailsRef, 'detailsRef');
      const [lesson, teaching, commitment] = await Promise.all([
        client.readContract({ ...booking, functionName: 'getLesson', args: [lessonId], ...point }) as Promise<{ packageId: bigint }>,
        client.readContract({ ...booking, functionName: 'getTeaching', args: [lessonId], ...point }) as Promise<{ startedAt: bigint; endedAt: bigint }>,
        client.readContract({ ...booking, functionName: 'tutorDeliveryCommitment', args: [lessonId, true, detailsRef], ...point }),
      ]);
      if (lesson.packageId !== packageId || teaching.endedAt === 0n) {
        throw new Error('The lesson must have ended under the installed package');
      }
      const arrangement = await client.readContract({ ...booking, functionName: 'getEffectiveArrangement',
        args: [lessonId, teaching.startedAt], ...point }) as { tutor: Address };
      if (!same(arrangement.tutor, account)) throw new Error('The acting account must be the effective tutor');
      return { kind: 'tutor' as const, lessonId, detailsRef, message: { ...common, commitment: hash(commitment, 'commitment'), tutor: account },
        fields: [{ name: 'commitment', type: 'bytes32' }, { name: 'packageId', type: 'uint256' }, { name: 'tutor', type: 'address' }] };
    }
    const formId = hash(input.formId, 'formId'), receivedRef = hash(input.receivedRef, 'receivedRef');
    const [form, commitment] = await Promise.all([
      client.readContract({ ...booking, functionName: 'getForm', args: [formId], ...point }) as Promise<{
        lessonId: Hex; terms: { student: Address };
      }>,
      client.readContract({ ...booking, functionName: 'serviceFeedbackCommitment', args: [formId, 3, receivedRef, zeroHash], ...point }),
    ]);
    const lesson = await client.readContract({ ...booking, functionName: 'getLesson', args: [form.lessonId], ...point }) as { packageId: bigint };
    if (!same(form.terms.student, account) || lesson.packageId !== packageId) {
      throw new Error('The form requires its student and the installed package');
    }
    return { kind: 'feedback' as const, formId, receivedRef, message: { ...common, commitment: hash(commitment, 'commitment'), student: account },
      fields: [{ name: 'commitment', type: 'bytes32' }, { name: 'packageId', type: 'uint256' }, { name: 'student', type: 'address' }] };
  })();
  const typedData = { domain, primaryType, types: { [primaryType]: [...scope.fields, ...occurrenceSourceFields] }, message: scope.message };
  const result = { kind: input.kind, source, account, typedData };
  if (input.signature === undefined) return result;
  const signature = occurrenceSignature(input.signature, 'Source signature');
  if (!same(await recoverTypedDataAddress({ ...typedData, signature }), source)) {
    throw new Error('Signature does not match the current Source and this occurrence');
  }
  const proof = { sourceRole, sourceAuthorityId: sourceAuthority.authorityId, disclosurePolicyId, validThrough,
    ...compactOccurrenceSignature(signature) };
  let data;
  if (scope.kind === 'start') {
    data = encodeFunctionData({ abi: occurrenceAbi, functionName: 'recordOrdinaryTeachingStarted',
      args: [scope.lessonId, scope.observation, proof] });
  } else if (scope.kind === 'end') {
    data = encodeFunctionData({ abi: occurrenceAbi, functionName: 'recordOrdinaryTeachingEnded',
      args: [scope.lessonId, scope.occurredAt, scope.occurrenceRef, proof] });
  } else if (scope.kind === 'tutor') {
    data = encodeFunctionData({ abi: occurrenceAbi, functionName: 'recordCompletedTutorDelivery',
      args: [scope.lessonId, scope.detailsRef, proof] });
  } else {
    data = encodeFunctionData({ abi: occurrenceAbi, functionName: 'recordFullServiceFeedback',
      args: [scope.formId, scope.receivedRef, proof] });
  }
  await client.call({ account, to, data, ...point });
  return { ...result, call: { from: account, to, data, value: 0n } };
}

function startObservation(input: unknown) {
  const observation = participantObject(input);
  if (typeof observation.providerWentAhead !== 'boolean' || !Array.isArray(observation.studentsTakingLesson)
    || !participantHash(observation.unmetConditionRef)) throw new Error('Supply the complete teaching-start observation');
  return { occurredAt: uint(observation.occurredAt, 'occurredAt', 64),
    providerWentAhead: observation.providerWentAhead,
    studentsTakingLesson: observation.studentsTakingLesson.map(participantAddress),
    occurrenceRef: hash(observation.occurrenceRef, 'occurrenceRef'), unmetConditionRef: observation.unmetConditionRef };
}

async function prepareGrant(installation: Installation, input: Record<string, unknown>, snapshot: CanonicalSnapshot) {
  const { client, sdk, contract, application, token } = installation;
  const { point } = snapshot;
  const payments = contract('SparkV15Payments');
  const functionName = 'grantOrdinaryWageApproval';
  if (!payments.abi.some(item => item.type === 'function' && item.name === functionName)) {
    throw new Error('Ordinary wage grant is unavailable in this installation');
  }
  const account = participantAddress(input.account);
  const supplied = participantObject(input.terms);
  if (supplied.replacesRequestId !== undefined && supplied.replacesRequestId !== '0') {
    throw new Error('Ordinary wage grant is a first approval');
  }
  const terms: SparkV15ApprovalTerms = { obligationId: hash(supplied.obligationId, 'obligationId'),
    executor: participantAddress(supplied.executor), ceiling: uint(supplied.ceiling, 'ceiling', 128),
    validThrough: uint(supplied.validThrough, 'validThrough', 64), replacesRequestId: 0n };

  const [requests, paymentWorkflow, paymentToken, role] = await Promise.all([
    client.readContract({ ...payments, functionName: 'REQUEST_ALLOCATION', ...point }),
    client.readContract({ ...payments, functionName: 'WORKFLOW', ...point }),
    client.readContract({ ...payments, functionName: 'TOKEN', ...point }),
    client.readContract({ ...application, functionName: 'ALLOCATOR_ROLE', ...point }),
  ]);
  if (!same(requests, sdk.deployment.addresses.requests) || !same(paymentWorkflow, workflowKey)
    || !same(paymentToken, token)) throw new Error('Current payments contract does not match the recorded Spark installation');
  const authority = await requireAuthority(installation, account, hash(role, 'allocator role'),
    'ava.extension.allocation.record.v1', snapshot);
  const [obligation, { result: approvalId }] = await Promise.all([
    client.readContract({ ...payments, functionName: 'getObligation', args: [terms.obligationId], ...point }),
    client.simulateContract({ ...payments, account, functionName, args: [terms], ...point }),
  ]);
  return { account, authority, terms, obligation, approvalId,
    call: { from: account, to: payments.address, data: encodeFunctionData({ abi: payments.abi, functionName, args: [terms] }), value: 0n } };
}

const bookingEntry = 'confirmOrdinaryPlaceWithAcceptances';
const roleNames = ['provider', 'tutor', 'customer', 'payer'] as const;
const bookingFields = [
  { name: 'formId', type: 'bytes32' },
  { name: 'fundingEvidenceId', type: 'uint256' },
  { name: 'role', type: 'uint8' },
] as const;
const withdrawalAbi = parseAbi(['function ordinaryAcceptanceWithdrawn(bytes32 formId) view returns (bool)']);
const deliveryEntry = 'confirmOrdinaryPlaceWithDeliveries';
const deliveryAbi = parseAbi([
  'struct RechargeDebit { uint256 receiptId; uint128 amount; }',
  'struct TermsProvisionConsent { bytes32 sourceRole; bytes32 sourceAuthorityId; uint256 disclosurePolicyId; bytes32 r; bytes32 vs; }',
  'struct DeliveredTerms { bytes32 deliveryRef; TermsProvisionConsent consent; }',
  'function confirmOrdinaryPlaceWithDeliveries(bytes32 formId, RechargeDebit[] rechargeDebits, bytes signatures, bytes teachingSignatures, DeliveredTerms customerDelivery, DeliveredTerms tutorDelivery)',
]);

type BookingConsentKind = 'AdoptBookingAcceptance' | 'AdoptTeachingAgreement';

type BookingForm = { lessonId: Hex; version: bigint; hasAcceptance: boolean; confirmation: { confirmedAt: bigint };
  terms: { placeId: Hex; customer: Address; customerRepresentative: Address; payer: Address; creditAccount: Hex;
    normalFee: bigint; payableFee: bigint; materialsBundleRef: Hex; rechargeDebitsHash: Hex } };
type BookingLesson = { packageId: bigint; prefunding: { evidenceId: bigint; reservedUnits: bigint };
  terms: { provider: Address; tutor: Address; coordinator: Address; startsAt: bigint; rosterLockAt: bigint;
    rosterRef: Hex; materialsTermsRef: Hex } };

function bookingConsent<Kind extends BookingConsentKind>(chainId: number, bookingAddress: Address, formId: Hex,
  fundingEvidenceId: bigint, role: number, primaryType: Kind) {
  return {
    domain: { name: 'Spark DAO Booking Acceptance', version: '1', chainId, verifyingContract: bookingAddress },
    types: { [primaryType]: bookingFields } as Record<Kind, typeof bookingFields>,
    primaryType,
    message: { formId, fundingEvidenceId, role },
  };
}

async function bookingContext(installation: Installation, input: Record<string, unknown>, { point, timestamp }: CanonicalSnapshot,
  localDelivery: boolean) {
  const { client, sdk, contract, token, packageId } = installation;
  const booking = contract('SparkV15Booking'), funds = contract('SparkV15Funds');
  const entry = booking.abi.find((item): item is AbiFunction => item.type === 'function' && item.name === bookingEntry);
  const signature = entry?.inputs.map(field => field.type).join(',');
  if (signature !== 'bytes32,tuple[],bytes' && signature !== 'bytes32,tuple[],bytes,bytes') {
    throw new Error('Ordinary booking adoption is unavailable in this installation');
  }
  const firstTeachingSignatures = signature === 'bytes32,tuple[],bytes,bytes';
  if (localDelivery && !firstTeachingSignatures) throw new Error('This installation needs recorded terms delivery');
  const formId = hash(input.formId, 'formId');
  const [form, workflow, requests, fundingModule, fundToken, opening] = await Promise.all([
    client.readContract({ ...booking, functionName: 'getForm', args: [formId], ...point }) as Promise<BookingForm>,
    client.readContract({ ...booking, functionName: 'WORKFLOW', ...point }),
    client.readContract({ ...booking, functionName: 'REQUEST_ALLOCATION', ...point }),
    client.readContract({ ...booking, functionName: 'FUNDS', ...point }),
    client.readContract({ ...funds, functionName: 'TOKEN', ...point }),
    client.readContract({ ...booking, functionName: 'OPENING', ...point }),
  ]);
  if (!form.version || !same(workflow, workflowKey) || !same(requests, sdk.deployment.addresses.requests)
    || !same(fundingModule, funds.address) || !same(fundToken, token)) throw new Error('Form or booking installation could not be verified');
  const place = form.terms;
  const [lesson, current, planned, reserve, withdrawn, customerTermsProvided] = await Promise.all([
    client.readContract({ ...booking, functionName: 'getLesson', args: [form.lessonId], ...point }) as Promise<BookingLesson>,
    client.readContract({ ...booking, functionName: 'currentForm', args: [form.lessonId, place.placeId], ...point }),
    client.readContract({ ...booking, functionName: 'getPlannedForms', args: [form.lessonId], ...point }) as Promise<Hex[]>,
    client.readContract({ ...funds, functionName: 'lessonReserved', args: [form.lessonId], ...point }) as Promise<bigint>,
    client.readContract({ address: participantAddress(opening), abi: withdrawalAbi,
      functionName: 'ordinaryAcceptanceWithdrawn', args: [formId], ...point }),
    client.readContract({ ...booking, functionName: 'hasTermsProvision', args: [formId, place.customer], ...point }),
  ]);
  const { provider, tutor, coordinator, startsAt, rosterLockAt, rosterRef, materialsTermsRef } = lesson.terms;
  const fundingEvidenceId = lesson.prefunding.evidenceId;
  if (lesson.packageId !== packageId || !same(current, formId) || planned.length !== 1 || !same(planned[0], formId)
    || form.hasAcceptance || form.confirmation.confirmedAt !== 0n || withdrawn || timestamp >= (rosterLockAt || startsAt)
    || !fundingEvidenceId || reserve < lesson.prefunding.reservedUnits || (!localDelivery && !customerTermsProvided)
    || !same(rosterRef, zeroHash) || !same(materialsTermsRef, zeroHash) || !same(place.materialsBundleRef, zeroHash)
    || !same(place.customerRepresentative, zeroAddress) || place.payableFee === 0n || place.payableFee !== place.normalFee) {
    throw new Error('Expected the current uncommitted and prefunded form of a paid ordinary one-to-one lesson');
  }

  const [tutorTermsProvided, providerSignedAt, tutorSignedAt] = await Promise.all([
    client.readContract({ ...booking, functionName: 'hasTermsProvision', args: [formId, tutor], ...point }),
    client.readContract({ ...booking, functionName: 'teachingAgreementSignedAt', args: [form.lessonId, provider], ...point }),
    client.readContract({ ...booking, functionName: 'teachingAgreementSignedAt', args: [form.lessonId, tutor], ...point }),
    verifyBookingFunding(installation, form.lessonId, formId, fundingEvidenceId, point),
  ]);
  if ((!localDelivery && !tutorTermsProvided) || (firstTeachingSignatures
    ? providerSignedAt !== 0n || tutorSignedAt !== 0n : providerSignedAt === 0n || tutorSignedAt === 0n)) {
    throw new Error('Teaching agreement or terms delivery does not match this booking entry');
  }

  const governingTerms = { lesson: lesson.terms, place, formVersion: form.version, lessonId: form.lessonId,
    formId, fundingEvidenceId, reservedUnits: reserve, providerSignedAt, tutorSignedAt,
    customerTermsProvided, tutorTermsProvided };
  const actors = same(place.customer, place.payer) ? [provider, tutor, place.customer] : [provider, tutor, place.customer, place.payer];
  return { booking, opening: participantAddress(opening), formId, fundingEvidenceId, firstTeachingSignatures, actors,
    coordinator, governingTerms, rechargeDebitsHash: place.rechargeDebitsHash };
}

async function verifyBookingFunding(installation: Installation, lessonId: Hex, formId: Hex, evidenceId: bigint,
  point: CanonicalSnapshot['point']) {
  const { client, sdk, contract, packageId } = installation;
  const booking = contract('SparkV15Booking');
  if (booking.abi.some(item => item.type === 'function' && item.name === 'PREFUNDING')) {
    const prefunding = contract('SparkV15BookingPrefunding');
    const installed = await client.readContract({ ...booking, functionName: 'PREFUNDING', ...point });
    if (!same(installed, prefunding.address)) throw new Error('Booking prefunding does not match the installation');
    await Promise.all([
      client.readContract({ ...prefunding, functionName: 'requireAvailable', args: [lessonId, evidenceId, packageId], ...point }),
      client.readContract({ ...prefunding, functionName: 'requireCommitmentFunding', args: [lessonId, formId], ...point }),
    ]);
    return;
  }
  await Promise.all([
    sdk.contracts(client).evidence.read.requireUsableEvidenceReferenceForPackage([evidenceId, packageId], point),
    client.readContract({ ...contract('SparkV15Funds'), functionName: 'requireCommitmentFunding', args: [lessonId, formId], ...point }),
  ]);
}

async function compactConsents(values: unknown, expected: readonly Address[], context: Awaited<ReturnType<typeof bookingContext>>,
  chainId: number, kind: BookingConsentKind) {
  if (!Array.isArray(values) || values.length !== expected.length) throw new Error(`Provide ${expected.length} ${kind} signatures in role order`);
  return concatHex(await Promise.all(expected.map(async (account, role) => {
    const signature = values[role];
    if (typeof signature !== 'string' || !/^0x[0-9a-f]{130}$/i.test(signature)) throw new Error('Expected a 65-byte wallet signature');
    const typedData = bookingConsent(chainId, context.booking.address, context.formId, context.fundingEvidenceId, role, kind);
    const signed = signature as Hex;
    if (!same(await recoverTypedDataAddress({ ...typedData, signature: signed }), account)) {
      throw new Error(`${kind} signature does not match ${roleNames[role]} for the current form and funding evidence`);
    }
    const parsed = parseSignature(signed);
    if (parsed.yParity !== 0 && parsed.yParity !== 1) throw new Error('Invalid signature parity');
    return concatHex([parsed.r, toHex(BigInt(parsed.s) | (BigInt(parsed.yParity) << 255n), { size: 32 })]);
  })));
}

async function prepareBooking(installation: Installation, input: Record<string, unknown>, snapshot: CanonicalSnapshot,
  chainId: number, forSignature: boolean) {
  const account = participantAddress(input.account);
  const deliveryInput = forSignature ? input.deliveredTermsRefs : input.deliveries;
  if (deliveryInput !== undefined && (!Array.isArray(deliveryInput) || deliveryInput.length !== 2)) {
    throw new Error('Supply the customer and tutor terms deliveries in recipient order');
  }
  const context = await bookingContext(installation, input, snapshot, deliveryInput !== undefined);
  const { booking, formId, fundingEvidenceId, firstTeachingSignatures, actors, coordinator, governingTerms } = context;
  if (forSignature) {
    const kind = input.kind;
    if (kind !== 'AdoptBookingAcceptance' && kind !== 'AdoptTeachingAgreement') throw new Error('Unknown signature kind');
    const role = roleNames.findIndex(name => name === input.role);
    if (role < 0 || !same(actors[role], account)
      || (kind === 'AdoptTeachingAgreement' && (!firstTeachingSignatures || role > 1))) {
      throw new Error('Account is not the recorded participant for this consent');
    }
    const deliveredTermsRefs = Array.isArray(deliveryInput) ? deliveryInput.map(ref => hash(ref, 'delivery reference')) : undefined;
    return { account, governingTerms, deliveredTermsRefs,
      typedData: bookingConsent(chainId, booking.address, formId, fundingEvidenceId, role, kind) };
  }

  if (!same(account, coordinator)) throw new Error('Only the recorded coordinator prepares adoption');
  const { client } = installation, { point } = snapshot;
  const role = await client.readContract({ ...booking, functionName: 'COORDINATOR_ROLE', ...point });
  const authority = await requireAuthority(installation, account, hash(role, 'coordinator role'),
    'spark.action.coordinate-booking.v1.5', snapshot);
  if (!Array.isArray(input.rechargeDebits)) throw new Error('Provide the form’s rechargeDebits array');
  const rechargeDebits = input.rechargeDebits.map((debit: unknown) => {
    const item = participantObject(debit);
    return { receiptId: uint(item.receiptId, 'recharge debit receiptId'), amount: uint(item.amount, 'recharge debit amount', 128) };
  });
  const debitHash = rechargeDebits.length === 0 ? zeroHash : keccak256(encodeAbiParameters(
    [{ type: 'tuple[]', components: [{ name: 'receiptId', type: 'uint256' }, { name: 'amount', type: 'uint128' }] }], [rechargeDebits],
  ));
  if (!same(debitHash, context.rechargeDebitsHash)) throw new Error('Recharge debits do not match the signed form');
  const acceptances = await compactConsents(input.bookingSignatures, actors, context, chainId, 'AdoptBookingAcceptance');
  const args: unknown[] = [formId, rechargeDebits, acceptances];
  if (firstTeachingSignatures) {
    args.push(await compactConsents(input.teachingSignatures, actors.slice(0, 2), context, chainId, 'AdoptTeachingAgreement'));
  } else if (input.teachingSignatures !== undefined) {
    throw new Error('This entry uses teaching agreement signatures already effective on the contract');
  }
  if (Array.isArray(deliveryInput)) {
    args.push(...deliveryInput.map(delivery => {
      const { deliveryRef, consent } = participantObject(delivery);
      const packet = participantObject(consent);
      return { deliveryRef: hash(deliveryRef, 'delivery reference'), consent: {
        sourceRole: hash(packet.sourceRole, 'source role'), sourceAuthorityId: hash(packet.sourceAuthorityId, 'source authority'),
        disclosurePolicyId: uint(packet.disclosurePolicyId, 'disclosure policy'),
        r: hash(packet.r, 'signature r'), vs: hash(packet.vs, 'compact signature'),
      } };
    }));
  }
  const { address: to, abi }: { address: Address; abi: Abi } = deliveryInput === undefined ? booking
    : { address: context.opening, abi: deliveryAbi };
  const data = encodeFunctionData({ abi, functionName: deliveryInput === undefined ? bookingEntry : deliveryEntry, args });
  await client.call({ account, to, data, ...point });
  return { account, coordinator, authority, governingTerms, rechargeDebits,
    call: { from: account, to, data, value: 0n } };
}

if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try {
    const [configPath, command, inputPath, ...extra] = process.argv.slice(2);
    if (!configPath || !commands.some(action => action === command) || !inputPath || extra.length) throw new Error(usage);
    const input = participantObject(await readJson(inputPath));
    const installation = await loadInstallation(resolve(configPath));
    const result = await withCanonicalSnapshot(installation.client, async snapshot => {
      const { chainId, genesisHash } = await verifyInstallation(installation, snapshot);
      const { blockNumber, blockHash, timestamp } = snapshot;
      let details;
      if (command === 'prepare-grant') details = await prepareGrant(installation, input, snapshot);
      else if (command === 'prepare-occurrence') details = await prepareOccurrence(installation, input, snapshot, chainId);
      else if (command === 'prepare-prefunding') details = await preparePrefunding(installation, input, snapshot, chainId);
      else if (command === 'prepare-notice') details = await prepareNotice(installation, input, snapshot, chainId);
      else details = await prepareBooking(installation, input, snapshot, chainId, command === 'prepare-booking-signature');
      return { action: command, chainId, genesisHash, deploymentHash: installation.deploymentHash,
        packageId: installation.packageId, asOf: { blockNumber, blockHash, timestamp }, ...details };
    });
    console.log(JSON.stringify(jsonValue(result), null, 2));
  } catch (error) {
    console.error(error instanceof Error ? error.message : 'Spark ordinary operation preparation failed');
    process.exitCode = 1;
  }
}
