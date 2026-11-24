import { randomBytes } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import Fastify, { type FastifyRequest } from 'fastify';
import { concatHex, keccak256, parseAbi, toHex, zeroHash, type Address, type Hex, type PublicClient } from 'viem';
import { AvaRuntimeError, AvaSdk, jsonValue, readRuntimeContext, withCanonicalSnapshot, type AvaServiceClient } from '@ava-protocol/sdk';
import type { PublicDeployment } from '@ava-protocol/sdk/deployment';
import type { MaterialCustody, MaterialReceipt } from '@ava-protocol/local-service/custody';
import { SparkBackendError, SparkCaseStore } from '../case-store.ts';
import { authenticateSparkRequest, sparkRequestMessage } from '../request-auth.ts';
import { createParticipantCases } from './participant-cases.ts';
import { courseOperationIds, createParticipantCourse, verifyParticipantCourse, type CourseOperation } from './participant-course.ts';
import { createParticipantPayments, participantAddress, participantHash, participantObject } from './participant-payments.ts';
import { connectSparkV15Payments, sparkV15 } from './payments.ts';

const key = (input: string) => keccak256(toHex(input));
const same = (a: unknown, b: string) => typeof a === 'string' && a.toLowerCase() === b.toLowerCase();
const noticeClass = key('spark.v1.5.hold-notice');
const caseNoticeClass = key('spark.v1.5.case-notice');
const privatePath = '/api/private/notice';
const casePath = '/api/private/cases';
const previewLifetime = 120;
const web = new URL('../../../web/spark-dao/', import.meta.url);
const returnsAbi = parseAbi([
  'function PAYMENTS() view returns (address)',
  'function REQUEST_ALLOCATION() view returns (address)',
  'function VERIFIER_ROLE() view returns (bytes32)',
  'event PaymentReturned(bytes32 indexed obligationId, uint256 indexed receiptId, uint256 indexed returnId, address returnedBy, bytes32 creditAccount, uint128 amount)',
]);

interface NoticeReference { receipt: MaterialReceipt; noticeHash: Hex }
export interface SparkV15ParticipantOptions {
  publicDeployment: PublicDeployment;
  client: PublicClient;
  relay: AvaServiceClient;
  token: Address;
  custody: MaterialCustody;
  databasePath: string;
  requestAudience: Hex;
  /** Links public notice references to private records in the Vault. The Vault stores who can read each notice. */
  notices?: readonly NoticeReference[];
}

function noticeInput(value: unknown) {
  const { obligationId, caseId, noticeHash } = participantObject(value);
  if (!participantHash(obligationId) || ![caseId, noticeHash].every(item => participantHash(item) && !same(item, zeroHash))) {
    throw new SparkBackendError('invalid_reference');
  }
  return { obligationId: obligationId as Hex, caseId: caseId as Hex, noticeHash: noticeHash as Hex };
}

/** Serve the local Spark workbench. Participants submit transactions from their own wallets. */
export async function buildSparkV15ParticipantApp(options: SparkV15ParticipantOptions) {
  const { publicDeployment, client, relay, custody, databasePath } = options;
  const { appId, workflowKey } = sparkV15;
  if (publicDeployment.schemaVersion !== 1 || publicDeployment.deployment.chainId !== 31337) {
    throw new SparkBackendError('invalid_deployment');
  }
  if (!participantHash(options.requestAudience) || same(options.requestAudience, zeroHash)) throw new SparkBackendError('invalid_audience');
  const profile = publicDeployment.workflows?.[appId]?.[workflowKey] ?? publicDeployment.apps[appId];
  if (!profile || !same(profile.appId, appId) || !same(profile.workflowKey, workflowKey)) {
    throw new SparkBackendError('installation_mismatch', 409);
  }
  const { SparkV15Payments: payments, AVABoundRequestPolicy: requestPolicy, SparkV15ApplicationModule: application } =
    profile.contracts;
  for (const contract of [payments, requestPolicy, application]) {
    if (!contract || !Array.isArray(contract.abi)) throw new SparkBackendError('invalid_deployment');
    participantAddress(contract.address);
  }
  const token = participantAddress(options.token);
  const installation = { payments, requestPolicy, applicationModule: application.address, token,
    packageId: BigInt(profile.packageId), disclosurePolicyId: BigInt(profile.disclosurePolicyId) };
  const sdk = new AvaSdk(publicDeployment.deployment);
  await sdk.verify(client);
  const payment = await connectSparkV15Payments({ client, sdk, relay, installation });
  const saved = SparkCaseStore.runtimeState(databasePath);
  if (saved.legacyData) throw new SparkBackendError('legacy_runtime_binding_required', 409);
  const chainId = sdk.deployment.chainId;
  const runtime = await readRuntimeContext(client, relay, saved.binding ?? { chainId }, { signal: AbortSignal.timeout(5_000) });
  const point = { blockHash: runtime.checkpoint.blockHash, requireCanonical: true } as const;
  const returns = { address: participantAddress(await client.readContract({ ...payments, functionName: 'RETURNS', ...point })),
    abi: returnsAbi };
  const [returnHost, returnRequests, returnVerifier] = await Promise.all([
    client.readContract({ ...returns, functionName: 'PAYMENTS', ...point }),
    client.readContract({ ...returns, functionName: 'REQUEST_ALLOCATION', ...point }),
    client.readContract({ ...returns, functionName: 'VERIFIER_ROLE', ...point }),
  ]);
  if (!same(returnHost, payments.address) || !same(returnRequests, sdk.deployment.addresses.requests)
    || !same(returnVerifier, sparkV15.verifierRole)
    || (profile.contracts.SparkV15Returns && !same(profile.contracts.SparkV15Returns.address, returns.address))) {
    throw new AvaRuntimeError('runtime_mismatch');
  }
  const courseInstallation = await verifyParticipantCourse({ profile, client, sdk, payments, tokenAddress: token,
    fundsAddress: payment.fundsAddress, point });
  const targets = [...new Set([...Object.values(sdk.deployment.addresses), ...Object.values(profile.contracts)
    .map(contract => participantAddress(contract.address)), token, payment.fundsAddress, returns.address]
    .map(address => address.toLowerCase()))].sort();
  const codes = await Promise.all(targets.map(async value => {
    const address = participantAddress(value);
    const code = await client.getCode({ address, blockNumber: runtime.checkpoint.blockNumber });
    if (!code || code === '0x') throw new AvaRuntimeError('runtime_mismatch');
    return [address, keccak256(code)];
  }));
  const installationHash = key(JSON.stringify(jsonValue({ appId, workflowKey, payments: payments.address.toLowerCase(),
    packageId: installation.packageId, disclosurePolicyId: installation.disclosurePolicyId, codes })));
  const requestScope = { chainId, teaching: payments.address, audience: options.requestAudience,
    genesisHash: runtime.genesisHash, installationHash };
  const requestProfile = { version: 2 as const, audience: requestScope.audience };
  const notices = new Map<string, MaterialReceipt>();
  for (const { receipt, noticeHash } of options.notices ?? []) {
    if (!receipt || !same(receipt.appId, appId) || ![noticeClass, caseNoticeClass].some(kind => same(receipt.materialClass, kind))
      || !participantHash(receipt.caseId) || !participantHash(noticeHash) || notices.has(noticeHash.toLowerCase())) {
      throw new SparkBackendError('invalid_notice_index');
    }
    notices.set(noticeHash.toLowerCase(), structuredClone(receipt));
  }
  const store = new SparkCaseStore(databasePath, requestScope);
  try {
    store.bindRequestProfile(requestProfile);
    if (!store.bindRuntime({ ...runtime, installationHash }, saved.binding)) throw new AvaRuntimeError('runtime_mismatch');
  } catch (error) {
    store.close();
    throw error;
  }
  const domain = createParticipantPayments({ client, sdk, payment, installation, installationHash, returns,
    genesisHash: runtime.genesisHash, previewLifetime });
  const course = courseInstallation && createParticipantCourse({ client, sdk, modules: courseInstallation,
    genesisHash: runtime.genesisHash, installationHash, packageId: installation.packageId, previewLifetime });
  const cases = course && createParticipantCases({ client, modules: courseInstallation!, course });
  const isCourseOperation = (value: unknown) => typeof value === 'string' && courseOperationIds.includes(value as CourseOperation);
  const app = Fastify({ logger: false, bodyLimit: 64_000 });
  app.addHook('onClose', async () => store.close());
  app.addHook('onRequest', async (_request, reply) => {
    reply.header('cache-control', 'no-store').header('x-content-type-options', 'nosniff').header('referrer-policy', 'no-referrer')
      .header('content-security-policy', "default-src 'none'; script-src 'self'; style-src 'self'; connect-src 'self'; "
        + "base-uri 'none'; frame-ancestors 'none'; form-action 'self'");
  });
  app.setErrorHandler((error, _request, reply) => {
    if (error instanceof SparkBackendError) return reply.code(error.status).send({ error: error.code });
    if (error instanceof AvaRuntimeError) return reply.code(error.code === 'runtime_mismatch' ? 409 : 503).send({ error: error.code });
    if ((error as { statusCode?: number }).statusCode === 400) return reply.code(400).send({ error: 'invalid_fields' });
    if ((error as { statusCode?: number }).statusCode === 413) return reply.code(413).send({ error: 'request_too_large' });
    return reply.code(503).send({ error: 'read_unavailable' });
  });
  const assets = [
    ['/', new URL('index.html', web), 'text/html'],
    ['/app.js', new URL('app.js', web), 'text/javascript'],
    ['/course.js', new URL('course.js', web), 'text/javascript'],
    ['/i18n.js', new URL('i18n.js', web), 'text/javascript'],
    ['/styles.css', new URL('styles.css', web), 'text/css'],
    ['/wallet.js', new URL(import.meta.resolve('@ava-protocol/workbench')), 'text/javascript'],
  ] as const;
  for (const [path, file, type] of assets) {
    app.get(path, async (_request, reply) => reply.type(type).send(await readFile(file)));
  }
  async function checkInstallation() {
    const [network, start, checkpoint] = await Promise.all([client.getChainId(), client.getBlock({ blockNumber: 0n }),
      client.getBlock({ blockNumber: runtime.checkpoint.blockNumber })]);
    if (network !== chainId || !same(start.hash, runtime.genesisHash) || !same(checkpoint.hash, runtime.checkpoint.blockHash)) {
      throw new AvaRuntimeError('runtime_mismatch');
    }
  }
  app.get('/api/installation', async () => {
    await checkInstallation();
    return jsonValue({ appId, workflowKey, payments: payments.address, token, packageId: installation.packageId, requestScope,
      checkpoint: runtime.checkpoint, operationTargets: [payments.address, ...(course?.targets ?? [])], cases: !!cases });
  });
  app.get('/api/workspace', async request => {
    const { account } = participantObject(request.query);
    await checkInstallation();
    const actor = participantAddress(account);
    return withCanonicalSnapshot(client, async snapshot => {
      const [payments, courses] = await Promise.all([domain.workspace(actor, snapshot), course?.workspace(actor, snapshot)]);
      return jsonValue({ ...payments, courses });
    });
  });
  app.post('/api/prepare', async request => {
    await checkInstallation();
    const body = participantObject(request.body);
    return jsonValue(await (course && isCourseOperation(body.operationId) ? course.prepare(body) : domain.prepare(body)));
  });
  app.post('/api/observe', async request => {
    await checkInstallation();
    const body = participantObject(request.body);
    const { operationId } = participantObject(body.locator);
    return jsonValue(await (course && isCourseOperation(operationId) ? course.observe(body) : domain.observe(body)));
  });
  app.post('/api/course/quote', async request => {
    await checkInstallation();
    if (!course) throw new SparkBackendError('installation_mismatch', 409);
    return jsonValue(await course.quote(request.body));
  });
  app.post('/api/private/challenge', async request => {
    const { account, input, path = privatePath } = participantObject(request.body);
    if (path !== privatePath && path !== casePath) throw new SparkBackendError('invalid_reference');
    if (path === casePath && !cases) throw new SparkBackendError('installation_mismatch', 409);
    const payload = path === privatePath ? noticeInput(input) : {};
    await checkInstallation();
    const auth = { account: participantAddress(account), nonce: randomBytes(24).toString('base64url'),
      expiresAt: Math.floor(Date.now() / 1000) + previewLifetime };
    return { ...auth, message: sparkRequestMessage(requestScope, 'POST', path, payload, auth) };
  });
  async function privateActor(request: FastifyRequest) {
    store.assertRequestProfile(requestProfile);
    await checkInstallation();
    return (await authenticateSparkRequest(requestScope, store, request.headers['x-spark-auth'], request.method,
      request.raw.url!, request.body)).account;
  }
  app.post(casePath, async request => {
    const actor = await privateActor(request);
    if (!cases) throw new SparkBackendError('installation_mismatch', 409);
    return jsonValue(await cases.inbox(actor));
  });
  app.post(privatePath, async request => {
    const actor = await privateActor(request);
    const scope = noticeInput(request.body), receipt = notices.get(scope.noticeHash.toLowerCase());
    const denied = () => new SparkBackendError('notice_forbidden', 403);
    if (!receipt || !same(receipt.caseId, scope.caseId)) throw denied();
    let material;
    try { material = await custody.read(receipt); }
    catch { throw new SparkBackendError('notice_unavailable', 503); }
    const { readers, salt, source, payments: target, obligationId } = material.metadata;
    if (!Array.isArray(readers) || !readers.some(reader => same(reader, actor)) || !same(target, payments.address)
      || !same(obligationId, scope.obligationId) || !participantHash(salt)
      || !same(keccak256(concatHex([salt, keccak256(material.payload)])), scope.noticeHash)
      || typeof source !== 'string' || !['participant-statement', 'verified-record', 'ai-suggestion'].includes(source)) throw denied();
    const linked = same(receipt.materialClass, caseNoticeClass) ? await cases?.noticeLinked(scope)
      : !same(scope.obligationId, zeroHash) && await domain.noticeLinked(scope);
    if (!linked) throw denied();
    return { text: material.payload.toString('utf8'), source, caseId: scope.caseId, obligationId: scope.obligationId };
  });
  return app;
}
