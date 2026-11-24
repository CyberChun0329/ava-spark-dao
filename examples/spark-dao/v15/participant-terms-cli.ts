import { readFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { AvaExtensions, AvaSdk, jsonValue, localClient, withCanonicalSnapshot } from '@ava-protocol/sdk';
import type { PublicDeployment } from '@ava-protocol/sdk/deployment';
import { encodeFunctionData, keccak256, parseAbi, parseSignature, recoverTypedDataAddress, toHex, zeroHash,
  type Address, type Hex } from 'viem';
import { participantAddress, participantHash, participantObject } from './participant-payments.ts';
import { sparkV15 } from './payments.ts';

const { appId, workflowKey, sourceRole } = sparkV15;
const key = (s: string) => keccak256(toHex(s));
const same = (a: unknown, b: string) => typeof a === 'string' && a.toLowerCase() === b.toLowerCase();
const readJson = async (p: string): Promise<unknown> => JSON.parse(await readFile(p, 'utf8'));
const pilotAbi = parseAbi([
  'function hasTermsProvision(bytes32 formId, address recipient) view returns (bool)',
  'function recordTermsProvisionWithConsent(bytes32 formId, address recipient, bytes32 deliveryRef, (bytes32 sourceRole, bytes32 sourceAuthorityId, uint256 disclosurePolicyId, bytes32 r, bytes32 vs) consent)',
]);
const types = { TermsProvisionConsent: [
  { name: 'packageId', type: 'uint256' }, { name: 'formId', type: 'bytes32' },
  { name: 'recipient', type: 'address' }, { name: 'deliveryRef', type: 'bytes32' },
  { name: 'coordinator', type: 'address' }, { name: 'sourceRole', type: 'bytes32' },
  { name: 'sourceAuthorityId', type: 'bytes32' }, { name: 'disclosurePolicyId', type: 'uint256' },
] } as const;
function hash(value: unknown, label: string): Hex {
  if (!participantHash(value) || same(value, zeroHash)) throw new Error(`${label} must be a nonzero bytes32`);
  return value;
}
function uint(value: unknown, label: string): bigint {
  if (typeof value === 'string' && /^[1-9][0-9]{0,77}$/.test(value)) {
    const n = BigInt(value);
    if (n < 1n << 256n) return n;
  }
  throw new Error(`${label} must be a positive decimal uint256 string`);
}
async function prepare(configPath: string, input: Record<string, unknown>) {
  if (input.action !== 'source' && input.action !== 'coordinator') throw new Error('Unknown participant action');
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
  const { SparkV15Booking: booking, SparkV15Funds: funds, SparkV15ApplicationModule: application } = profile.contracts;
  for (const contract of [booking, funds, application]) {
    if (!contract || !Array.isArray(contract.abi)) throw new Error('Incomplete Spark v1.5 deployment export');
    participantAddress(contract.address);
  }
  const token = participantAddress(config.token);
  const packageId = uint(profile.packageId, 'packageId'), disclosurePolicyId = uint(profile.disclosurePolicyId, 'disclosurePolicyId');
  const source = participantAddress(input.source), coordinator = participantAddress(input.coordinator);
  const recipient = participantAddress(input.recipient), formId = hash(input.formId, 'formId'), deliveryRef = hash(input.deliveryRef, 'deliveryRef');
  if (same(source, coordinator)) throw new Error('Source and coordinator must be independent');
  const client = localClient(rpc.origin), sdk = new AvaSdk(declaration.deployment);
  return withCanonicalSnapshot(client, async snapshot => {
    const { point, blockNumber, blockHash, timestamp } = snapshot;
    const core = sdk.contracts(client);
    const [chainId, genesis, readiness, policy, requests, workflow, bookingFunds, fundToken, coordinatorRole] = await Promise.all([
      client.getChainId(), client.getBlock({ blockNumber: 0n }),
      new AvaExtensions(sdk, {}).verifyInstallation(client, { appId, workflowKey, activePackageId: packageId, modules: [
        { capabilityKey: key('ava.capability.application.v1'), module: application.address },
      ] }, point),
      core.disclosure.read.getPolicy([disclosurePolicyId], point),
      client.readContract({ ...booking, functionName: 'REQUEST_ALLOCATION', ...point }),
      client.readContract({ ...booking, functionName: 'WORKFLOW', ...point }),
      client.readContract({ ...booking, functionName: 'FUNDS', ...point }),
      client.readContract({ ...funds, functionName: 'TOKEN', ...point }),
      client.readContract({ ...booking, functionName: 'COORDINATOR_ROLE', ...point }),
    ]);
    if (chainId !== 31337 || !readiness.ready || !same(policy.appId, appId)
      || !same(requests, sdk.deployment.addresses.requests) || !same(workflow, workflowKey)
      || !same(bookingFunds, funds.address) || !same(fundToken, token)) throw new Error('Current chain does not match the recorded Spark installation');
    const form = await client.readContract({ ...booking, functionName: 'getForm', args: [formId], ...point }) as {
      lessonId: Hex; version: bigint; hasAcceptance: boolean;
      terms: { placeId: Hex; customer: Address; customerRepresentative: Address; materialsBundleRef: Hex };
    };
    const [lesson, current, representativeAuthorised, already, sourceActor, coordinatorActor] = await Promise.all([
      client.readContract({ ...booking, functionName: 'getLesson', args: [form.lessonId], ...point }) as Promise<{
        packageId: bigint; terms: { coordinator: Address; provider: Address; tutor: Address; serviceTermsRef: Hex;
          rosterRef: Hex; materialsTermsRef: Hex; startsAt: bigint };
      }>,
      client.readContract({ ...booking, functionName: 'currentForm', args: [form.lessonId, form.terms.placeId], ...point }),
      client.readContract({ ...booking, functionName: 'representativeAuthorised', args: [formId], ...point }),
      client.readContract({ address: booking.address, abi: pilotAbi, functionName: 'hasTermsProvision', args: [formId, recipient], ...point }),
      sdk.actorContext(client, { appId, account: source, roleKey: sourceRole, actionKeys: [key('ava.core.register-evidence.v1')] }, point),
      sdk.actorContext(client, { appId, account: coordinator, roleKey: hash(coordinatorRole, 'coordinator role'),
        actionKeys: [key('spark.action.coordinate-booking.v1.5')] }, point),
    ]);
    if (!form.version || !same(current, formId) || lesson.packageId !== packageId || !same(lesson.terms.coordinator, coordinator)) {
      throw new Error('Form, package or recorded coordinator is not current');
    }
    if (!same(recipient, form.terms.customer) && !same(recipient, lesson.terms.tutor)
      && !(representativeAuthorised && same(recipient, form.terms.customerRepresentative))) throw new Error('Recipient is not eligible for this form');
    if (form.hasAcceptance || !same(lesson.terms.rosterRef, zeroHash) || !same(lesson.terms.materialsTermsRef, zeroHash)
      || !same(form.terms.materialsBundleRef, zeroHash) || timestamp >= lesson.terms.startsAt) {
      throw new Error('This delivery already has a commitment or falls outside the ordinary-course pilot');
    }
    const signatures = await Promise.all([lesson.terms.provider, lesson.terms.tutor].map(signer =>
      client.readContract({ ...booking, functionName: 'teachingAgreementSignedAt', args: [form.lessonId, signer], ...point })));
    if (signatures.some(value => value !== 0n)) throw new Error('A teaching agreement has already been signed');
    if (already) throw new Error('Terms provision already exists for this recipient');
    if (!sourceActor.authority || !sourceActor.permissions[0]?.allowed || !coordinatorActor.authority || !coordinatorActor.permissions[0]?.allowed) {
      throw new Error('Source or coordinator lacks current authority for this action');
    }
    const scope = { packageId, sourceRole, sourceAuthorityId: sourceActor.authority.authorityId, disclosurePolicyId };
    const typedData = { domain: { name: 'Spark DAO Terms Delivery', version: '1', chainId, verifyingContract: booking.address as Address },
      types, primaryType: 'TermsProvisionConsent' as const,
      message: { packageId, formId, recipient, deliveryRef, coordinator, sourceRole,
        sourceAuthorityId: sourceActor.authority.authorityId, disclosurePolicyId } };
    let call;
    if (input.action === 'coordinator') {
      if (typeof input.signature !== 'string' || !/^0x[0-9a-f]{130}$/i.test(input.signature)) throw new Error('A 65-byte Source signature is required');
      const signature = input.signature as Hex;
      if (!same(await recoverTypedDataAddress({ ...typedData, signature }), source)) throw new Error('Signature does not match the current Source and exact delivery');
      const parsed = parseSignature(signature);
      if (parsed.yParity !== 0 && parsed.yParity !== 1) throw new Error('Invalid signature parity');
      const vs = toHex(BigInt(parsed.s) | (BigInt(parsed.yParity) << 255n), { size: 32 });
      const data = encodeFunctionData({ abi: pilotAbi, functionName: 'recordTermsProvisionWithConsent',
        args: [formId, recipient, deliveryRef, { sourceRole, sourceAuthorityId: sourceActor.authority.authorityId,
          disclosurePolicyId, r: parsed.r, vs }] });
      await client.call({ account: coordinator, to: booking.address as Address, data, ...point });
      call = { to: booking.address, data, value: 0n };
    }
    return { action: input.action, chainId, deploymentHash: keccak256(contents), genesisHash: hash(genesis.hash, 'genesis hash'),
      asOf: { blockNumber, blockHash, timestamp }, source, coordinator, formId, recipient, deliveryRef,
      lessonId: form.lessonId, formVersion: form.version, serviceTermsRef: lesson.terms.serviceTermsRef, scope, typedData, ...(call ? { call } : {}) };
  });
}
if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try {
    const [configPath, command, inputPath, ...extra] = process.argv.slice(2);
    if (!configPath || command !== 'prepare' || !inputPath || extra.length) {
      throw new Error('Usage: participant-terms-cli.ts <participant.json> prepare <input.json>');
    }
    console.log(JSON.stringify(jsonValue(await prepare(resolve(configPath), participantObject(await readJson(inputPath)))), null, 2));
  } catch (error) {
    console.error(error instanceof Error ? error.message : 'Spark terms preparation failed');
    process.exitCode = 1;
  }
}
