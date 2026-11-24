import { decodeFunctionData, encodeAbiParameters, encodeFunctionData, isAddress, keccak256, parseAbi, toHex, zeroAddress, zeroHash,
  type Abi, type AbiFunction, type AbiParameter, type Address, type Hex, type PublicClient } from 'viem';
import { AvaRuntimeError, AvaSigningError, withCanonicalSnapshot, type AvaSdk, type CanonicalSnapshot, type ReadPoint }
  from '@ava-protocol/sdk';
import type { PublicDeploymentApp } from '@ava-protocol/sdk/deployment';
import { SparkBackendError } from '../case-store.ts';
import { sparkV15 } from './payments.ts';
import { observeParticipantOperation, participantAddress, participantHash, participantObject } from './participant-payments.ts';

const key = (value: string) => keccak256(toHex(value));
const same = (a: unknown, b: string) => typeof a === 'string' && a.toLowerCase() === b.toLowerCase();
export type ParticipantContract = { address: Address; abi: Abi };
const methods = {
  publishLesson: ['booking', 'LessonPublished', '公布课次'],
  publishForm: ['booking', 'FormPublished', '公布名额确认单'],
  authoriseRepresentative: ['booking', 'RepresentativeAuthorised', '授权确认代理人'],
  recordTermsProvision: ['booking', 'TermsProvisionRecorded', '登记条款交付'],
  verifyPrefunding: ['booking', 'PrefundingVerified', '核验备付'],
  retainInventory: ['fundingCases', 'FundingInventoryRetained', '留存已核验费用清单'],
  signTeachingAgreement: ['booking', 'TeachingAgreementSigned', '签署授课协议'],
  acceptForm: ['booking', 'FormAccepted', '接受确认单'],
  confirmPlace: ['booking', 'PlaceConfirmed', '确认名额并扣款'],
  recordStudentNotice: ['booking', 'StudentNoticeRecorded', '登记学生通知'],
  recordTutorNotice: ['booking', 'TutorNoticeRecorded', '登记教师通知'],
  lockRoster: ['booking', 'GroupRosterLocked', '锁定团课名册'],
  recordTeachingStarted: ['booking', 'TeachingStarted', '登记实际开课'],
  recordTeachingEnded: ['booking', 'TeachingEnded', '登记实际下课'],
  recordAttendance: ['booking', 'AttendanceReported', '报告出勤'],
  recordServiceFeedback: ['booking', 'ServiceFeedbackReported', '报告服务交付'],
  recordOneToOneCompletion: ['alternatives', 'OneToOneCompletionRecorded', '确认单人课完成'],
  recordTutorDelivery: ['booking', 'TutorDeliveryReported', '报告教师履约'],
  proposeOrdinaryGroup: ['settlement', 'GroupSettlementProposed', '提出逐席结算'],
  approveOrdinaryGroup: ['settlement', 'GroupSettlementApproved', '批准逐席结算'],
  proposeProviderStartedEarly: ['settlement', 'GroupSettlementProposed', '提出未满足开课条件的专门结算'],
  approveProviderStartedEarly: ['settlement', 'GroupSettlementApproved', '批准未满足开课条件的专门结算'],
  offerRecharge: ['funds', 'RechargeOffered', '公布充值条款', 'offer-recharge'],
  approveRechargeToken: ['token', 'Approval', '授权资金库扣取本次充值'],
  recharge: ['funds', 'RechargeReceived', '确认并充值'],
  publishContacts: ['intake', 'ContactsPublished', '公布案件联系人'],
  receiveConcern: ['intake', 'ConcernReceived', '提交案件'],
  receiveConcernAt: ['intake', 'ConcernReceived', '登记此前已收到的异议'],
  acknowledge: ['intake', 'ConcernAcknowledged', '登记案件受理', 'acknowledge-concern'],
  reply: ['intake', 'ConcernReplyRecorded', '登记案件答复', 'reply-to-concern'],
  requestReview: ['intake', 'ReviewRequested', '申请独立复核'],
  escalate: ['intake', 'CaseEscalated', '登记案件接办', 'escalate-review-case'],
  appoint: ['cases', 'CaseActorAppointed', '指定案件承办人', 'appoint-case-actor'],
  decideInitial: ['cases', 'InitialFindingRecorded', '登记初判', 'decide-initial-finding'],
  retainOriginal: ['cases', 'OriginalOutcomeRetained', '留存教师过错初判', 'retain-original-outcome'],
  recordFault: ['remedies', 'LessonFaultRecorded', '登记教师过错'],
  publishRedressTerms: ['redress', 'RedressTermsPublished', '公布补偿条款'],
  acceptStandardCompensation: ['redress', 'StandardCompensationAccepted', '接受标准补偿'],
  assessRefund: ['redress', 'RefundAssessed', '核定退款', 'assess-fault-refund'],
  establishRefundPayment: ['redress', 'RefundPaymentEstablished', '登记应退金额'],
  issueCourseCredit: ['redress', 'CompensationCreditIssued', '发放可用课程余额'],
  releaseBudget: ['serviceReserve', 'FundingReserveReleased', '释放多余备付', 'verify-reserve-release'],
  decideReview: ['cases', 'IndependentReviewRecorded', '登记独立复核', 'decide-independent-review'],
  decidePaymentRevision: ['cases', 'IndependentReviewRecorded', '复核并核定款项更正', 'decide-independent-review'],
  adoptCorrection: ['cases', 'CorrectionAdopted', '采纳更正', 'adopt-review-correction'],
  adoptApprovalStop: ['cases', 'CorrectionAdopted', '采纳并停止未执行的批准', 'adopt-review-correction'],
  adoptPaymentRevision: ['cases', 'CorrectionAdopted', '采纳款项更正', 'adopt-review-correction'],
} as const;
export type CourseOperation = keyof typeof methods;
export const courseOperationIds = Object.keys(methods) as CourseOperation[];
const labels: Record<string, string> = {
  terms: '已核对的条款', assessment: '逐席结算单', observation: '实际开课记录', evidenceId: '经核实的证据编号',
  formId: '确认单标识', lessonId: '课次标识', formIds: '备付覆盖的确认单标识列表', requiredUnits: '备付金额（最小单位）',
  fundingRef: '备付核对依据', registerRef: '名册承诺', input: '案件记录', caseId: '案件标识', role: '签署角色',
  discountRef: '全免依据', discountEvidenceId: '全免证据编号', rechargeDebits: '扣款对应的实际充值收据',
  deliveryRef: '交付或通知承诺', recipient: '交付对象地址', deliveredAt: '实际送达时间（UTC 秒）',
  channelRef: '约定通知渠道承诺', occurredAt: '实际发生时间（UTC 秒）', occurrenceRef: '实际发生依据',
  completed: '已经完成授课', detailsRef: '教师报告承诺', attended: '学生实际出勤', reportRef: '报告承诺',
  status: '服务交付状态（1 未交付 · 2 部分 · 3 全部）', receivedRef: '已交付内容承诺',
  notReceivedRef: '未交付内容承诺', paymentEvidenceIds: '逐项款项证据编号列表', grounds: '复核申请依据',
  notice: '已发通知记录',
  receivedAt: '异议实际收到时间（UTC 秒）', receiptRef: '原收件凭据引用',
  offerId: '充值条款标识', revision: '已核实的款项更正', finding: '已认定的教师过错',
  paymentEvidenceId: '退款款项的证据编号', releaseRef: '备付释放依据',
  scenarios: '已核验的费用情形清单',
  serviceValue: '已独立核实的实际教学价值（最小单位）',
  tutorAmount: '按有效教师协议核实的教师应收（最小单位）',
  originalPayer: '确认单付款人地址', originalDebitAccount: '原扣款账户',
};

export interface CourseOffer {
  operationId: CourseOperation;
  label: string;
  arguments: Record<string, unknown>;
  fields: { name: string; label: string; type: 'json' | 'bool' | 'uint' | 'address' | 'hash' }[];
}

function parameters(contract: ParticipantContract, functionName: string) {
  const items = contract.abi.filter((entry): entry is AbiFunction => entry.type === 'function' && entry.name === functionName);
  if (items.length !== 1) throw new AvaRuntimeError('runtime_mismatch');
  return items[0].inputs;
}

function argument(param: AbiParameter, value: unknown): unknown {
  if (param.type.endsWith('[]')) {
    if (!Array.isArray(value) || value.length > 100) throw new SparkBackendError('invalid_fields');
    const element = { ...param, type: param.type.slice(0, -2) } as AbiParameter;
    return value.map(item => argument(element, item));
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
    const bits = Number(param.type.slice(4)) || 256;
    const parsed = BigInt(value);
    if (parsed < 1n << BigInt(bits)) return parsed;
  }
  throw new SparkBackendError('invalid_fields');
}
function fieldType(param: AbiParameter): CourseOffer['fields'][number]['type'] {
  if (param.type === 'bool' || param.type === 'address') return param.type;
  if (param.type === 'bytes32') return 'hash';
  if (/^uint\d*$/.test(param.type)) return 'uint';
  return 'json';
}

export async function verifyParticipantCourse(options: {
  profile: PublicDeploymentApp; client: PublicClient; sdk: AvaSdk;
  payments: ParticipantContract; fundsAddress: Address; tokenAddress: Address; point: ReadPoint;
}) {
  const { client, sdk, profile, payments, fundsAddress, tokenAddress, point } = options;
  const { SparkV15Booking: booking, SparkV15Settlement: settlement, SparkV15ReviewCases: cases,
    SparkV15ConcernIntake: intake, SparkV15Funds: funds, SparkV15LessonRemedies: remedies,
    SparkV15CustomerRedress: redress, SparkV15ServiceReserve: serviceReserve,
    SparkV15BookingOpening: opening,
    SparkV15MaterialProvisions: provisions, SparkV15SettlementAlternatives: alternatives,
    SparkV15SettlementOccurrences: occurrences } = profile.contracts;
  if (!booking && !settlement && !cases && !intake) return;
  if (!booking || !settlement || !cases || !intake || !funds || !same(funds.address, fundsAddress)) {
    throw new AvaRuntimeError('runtime_mismatch');
  }
  const at = typeof point === 'bigint' ? { blockNumber: point } : point;
  const expected: [ParticipantContract, string, Hex][] = [
    [booking, 'FUNDS', fundsAddress], [booking, 'REQUEST_ALLOCATION', sdk.deployment.addresses.requests],
    [booking, 'WORKFLOW', sparkV15.workflowKey], [booking, 'VERIFIER_ROLE', sparkV15.verifierRole],
    [settlement, 'PAYMENTS', payments.address], [settlement, 'BOOKING', booking.address],
    [payments, 'reviewCases', cases.address], [cases, 'INTAKE', intake.address],
  ];
  if (alternatives) {
    expected.push([settlement, 'ALTERNATIVES', alternatives.address], [alternatives, 'BOOKING', booking.address],
      [alternatives, 'SETTLEMENT', settlement.address], [alternatives, 'PAYMENTS', payments.address]);
  }
  const earlyStart = occurrences?.abi.some(entry => entry.type === 'function' && entry.name === 'encodeProviderStartedEarlyAmounts')
    && occurrences.abi.some(entry => entry.type === 'function' && entry.name === 'readProviderStartBasis') ? occurrences : undefined;
  if (earlyStart) {
    if (!alternatives) throw new AvaRuntimeError('runtime_mismatch');
    expected.push([alternatives, 'OCCURRENCES', earlyStart.address]);
  }
  if (remedies || redress) {
    if (!remedies || !redress) throw new AvaRuntimeError('runtime_mismatch');
    expected.push(
      [settlement, 'remedyPolicy', remedies.address], [remedies, 'BOOKING', booking.address],
      [remedies, 'PAYMENTS', payments.address], [remedies, 'CASES', cases.address],
      [remedies, 'customerRedress', redress.address], [redress, 'REMEDIES', remedies.address],
    );
  }
  if (serviceReserve) {
    if (!redress || !provisions) throw new AvaRuntimeError('runtime_mismatch');
    expected.push(
      [funds, 'materialProvisions', provisions.address], [provisions, 'SERVICE_RESERVE', serviceReserve.address],
      [serviceReserve, 'FUNDS', funds.address], [serviceReserve, 'redress', redress.address],
    );
  }
  const usableTerms = opening?.abi.some(entry => entry.type === 'function' && entry.name === 'hasUsableTermsProvision')
    ? opening : undefined;
  if (usableTerms) expected.push([booking, 'OPENING', usableTerms.address], [usableTerms, 'BOOKING', booking.address]);
  let prefunding: ParticipantContract | undefined;
  if (booking.abi.some(entry => entry.type === 'function' && entry.name === 'PREFUNDING')) {
    const address = await client.readContract({ ...booking, functionName: 'PREFUNDING', ...at }) as Address;
    if (!same(address, zeroAddress)) {
      prefunding = { address, abi: parseAbi([
        'function BOOKING() view returns (address)',
        'function requireCommitmentFunding(bytes32 lessonId, bytes32 formId) view',
      ]) };
      expected.push([prefunding, 'BOOKING', booking.address]);
    }
  }
  let fundingCases: ParticipantContract | undefined;
  if (funds.abi.some(entry => entry.type === 'function' && entry.name === 'materialBookingCoverage')) {
    const materialCoverage = await client.readContract({ ...funds, functionName: 'materialBookingCoverage', ...at }) as Address;
    const hasMaterialCoverage = !same(materialCoverage, zeroAddress);
    if (Boolean(provisions) !== hasMaterialCoverage) throw new AvaRuntimeError('runtime_mismatch');
    const coverage = !hasMaterialCoverage
      && funds.abi.some(entry => entry.type === 'function' && entry.name === 'ordinaryBookingCoverage')
      ? await client.readContract({ ...funds, functionName: 'ordinaryBookingCoverage', ...at }) as Address
      : materialCoverage;
    if (!same(coverage, zeroAddress)) {
      fundingCases = { address: coverage, abi: parseAbi([
        'struct MaterialPortion { bytes32 formId; uint128 units; }',
        'struct Expense { bytes32 referenceId; bytes32 obligationId; bytes32 material; bytes32 termsRef; uint128 units; MaterialPortion[] portions; }',
        'struct FundingScenario { bool teachingBegan; bytes32[] forms; bytes32[] outcomes; Expense[] expenses; }',
        'function BOOKING() view returns (address)', 'function PAYMENTS() view returns (address)',
        'function FUNDS() view returns (address)', 'function hasInventory(bytes32 lessonId) view returns (bool)',
        'function retainInventory(bytes32 lessonId, FundingScenario[] scenarios)',
        'event FundingInventoryRetained(bytes32 indexed lessonId, bytes32 indexed inventoryRef, uint256 evidenceId)',
      ]) };
      if (provisions) expected.push([provisions, 'FUNDING_CASES', coverage]);
      expected.push([fundingCases, 'BOOKING', booking.address],
        [fundingCases, 'PAYMENTS', payments.address], [fundingCases, 'FUNDS', funds.address]);
    }
  }
  await Promise.all(expected.map(async ([contract, functionName, value]) => {
    if (!same(await client.readContract({ ...contract, functionName, ...at }), value)) throw new AvaRuntimeError('runtime_mismatch');
  }));
  const [coordinator, provider] = await Promise.all([
    client.readContract({ ...booking, functionName: 'COORDINATOR_ROLE', ...at }) as Promise<Hex>,
    client.readContract({ ...funds, functionName: 'CREDIT_PROVIDER_ROLE', ...at }) as Promise<Hex>,
  ]);
  const token = { address: tokenAddress, abi: parseAbi([
    'function allowance(address owner, address spender) view returns (uint256)',
    'function approve(address spender, uint256 amount) returns (bool)',
    'event Approval(address indexed owner, address indexed spender, uint256 value)',
  ]) };
  return { booking, settlement, alternatives, cases, intake, funds, token, coordinator, provider, remedies, redress,
    payments, serviceReserve, fundingCases, prefunding, usableTerms, earlyStart };
}

export type CourseInstallation = NonNullable<Awaited<ReturnType<typeof verifyParticipantCourse>>>;
type Lesson = { packageId: bigint; terms: { lessonId: Hex; provider: Address; coordinator: Address; tutor: Address;
  startsAt: bigint; endsAt: bigint; rosterLockAt: bigint; rosterRef: Hex; tutorNoticeChannelRef: Hex; materialsTermsRef: Hex }; prefunding: { evidenceId: bigint; reservedUnits: bigint } };
type Form = { version: bigint; lessonId: Hex; terms: { placeId: Hex; payer: Address; customer: Address; customerRepresentative: Address;
  student: Address; creditAccount: Hex; normalFee: bigint; payableFee: bigint }; confirmation: { confirmedAt: bigint; debitedUnits: bigint } };
type Teaching = { startedAt: bigint; endedAt: bigint; startEvidenceId: bigint; endEvidenceId: bigint; startPermission: number;
  providerWentAhead: boolean; unmetConditionRef: Hex };
type GroupSettlement = { basis: Hex; complete: boolean; totalTutorPay: bigint; attendanceConfirmations: bigint; route: number };
type EarlySeatSettlement = { formId: Hex; debitAccount: Hex; debited: bigint; disposition: number; feeDue: bigint; tutorPay: bigint; tutorNetPay: bigint;
  refundDue: bigint; refundAlreadyReceived: bigint };
type AssessmentRoute = { route: bigint; verificationRef: Hex; seats: { disposition: bigint }[] };
type InitialDecision = { input: { issue: number; outcome: Hex }; decider: Address; evidenceId: bigint; decidedAt: bigint };
type CaseDecision = { initial: InitialDecision; original: { evidenceId: bigint }; review: { decidedAt: bigint } };
type FaultMatter = { termsId: Hex; lessonId: Hex; obligationId: Hex; partiesHash: Hex };
type OriginalFinding = { termsId: Hex; concernRef: Hex; obligationId: Hex; paymentCommitment: Hex; decider: Address;
  decidedAt: bigint; outcome: Hex; parties: Address[] };
type RefundAssessment = { cause: number; caseId: Hex; faultRevision: bigint; principal: bigint; obligationId: Hex };
type RechargeOffer = { terms: { customer: Address; amount: bigint; returnCap: bigint; returnThrough: bigint }; provider: Address;
  authorityId: Hex; packageId: bigint; receiptId: bigint };
const coordAction = 'coordinate-booking', verifyFunding = 'verify-booking-funding', verifyTeaching = 'verify-teaching-occurrence';
const proposes = 'propose-group-settlement', approves = 'approve-group-settlement', publishesContacts = 'publish-review-contacts';
const confirmOneToOne = 'confirm-one-to-one-completion';
const offersRecharge = 'offer-recharge';
const isTutorFault = (kind: number) => kind === 1 || kind === 2;
const faultIssue = 1;
const originalRelief = 0;
const assessRefundPermission = 'assess-fault-refund';
const releaseBudgetPermission = 'verify-reserve-release';
const permittedTeachingStart = 1;
const teachingRequirementsNotMet = 2;
const unverifiedTeachingStart = 3;
const providerStartedEarlyRoute = 6;
const providerStartedEarlySeat = 6;
const verifiedEarlyAmounts: readonly AbiParameter[] = [{ name: 'serviceValue', type: 'uint128' }, { name: 'tutorAmount', type: 'uint128' }];
const isEarlySettlement = (id: CourseOperation) => id === 'proposeProviderStartedEarly' || id === 'approveProviderStartedEarly';
const isSettlementProposal = (id: CourseOperation) => id === 'proposeOrdinaryGroup' || id === 'proposeProviderStartedEarly';
const settlementMethod = (id: CourseOperation) => id === 'proposeProviderStartedEarly' ? 'proposeOrdinaryGroup'
  : id === 'approveProviderStartedEarly' ? 'approveOrdinaryGroup' : id;

function hasEarlySettlementRoute(assessment: AssessmentRoute) {
  return assessment.route === BigInt(providerStartedEarlyRoute)
    || assessment.seats.some(seat => seat.disposition === BigInt(providerStartedEarlySeat));
}

export function createParticipantCourse(options: {
  client: PublicClient; sdk: AvaSdk; modules: CourseInstallation; genesisHash: Hex;
  installationHash: Hex; packageId: bigint; previewLifetime: number;
}) {
  const { client, sdk, modules, genesisHash, packageId, installationHash, previewLifetime } = options;
  const { appId, workflowKey } = sparkV15;
  const chain = { chainId: sdk.deployment.chainId, genesisHash };
  const authorityRoles = [modules.coordinator, sparkV15.verifierRole, modules.provider, sparkV15.alternativeContactRole,
    key('ava.spark.role.core-partner.v1.5')];
  const targets = new Set([modules.booking, modules.settlement, modules.alternatives, modules.intake, modules.cases, modules.funds, modules.token,
    modules.remedies, modules.redress, modules.serviceReserve, modules.fundingCases].flatMap(contract => contract ? [contract.address.toLowerCase()] : []));
  const bookingIndex = { address: modules.booking.address, abi: modules.booking.abi.filter(entry =>
    entry.type === 'event' && (entry.name === 'LessonPublished' || entry.name === 'FormPublished')) };
  const readsAdoptedCompletion = modules.settlement.abi.some(entry =>
    entry.type === 'function' && entry.name === 'hasAdoptedOneToOneCompletion');
  const readsTermsProvision = modules.booking.abi.some(entry =>
    entry.type === 'function' && entry.name === 'hasTermsProvision');
  const { usableTerms } = modules;
  async function read<T>(contract: ParticipantContract, functionName: string, point: ReadPoint, args: readonly unknown[] = []) {
    return await client.readContract({ ...contract, functionName, args, ...(typeof point === 'bigint' ? { blockNumber: point } : point) }) as T;
  }
  async function authority(account: Address, roleKey: Hex, actions: string[], point: ReadPoint) {
    const actionKeys = actions.map(action => key(`spark.action.${action}.v1.5`));
    const actor = await sdk.actorContext(client, { appId, account, roleKey, actionKeys }, point);
    const allowed = new Set(actor.permissions.flatMap((permission, index) => permission.allowed ? [actions[index]] : []));
    return { authority: actor.authority, allowed };
  }
  function rechargeIssuer(provider: Address, point: ReadPoint) {
    return authority(provider, modules.provider, [offersRecharge], point);
  }
  async function mayRecharge(
    offer: RechargeOffer, account: Address, readIssuer: (provider: Address) => ReturnType<typeof rechargeIssuer>,
  ) {
    if (offer.receiptId !== 0n || offer.packageId === 0n || !same(offer.terms.customer, account)) return false;
    const issuer = await readIssuer(offer.provider);
    return issuer.allowed.has(offersRecharge) && same(issuer.authority?.authorityId, offer.authorityId);
  }

  const lookup = (id: unknown) => {
    if (typeof id !== 'string' || !Object.hasOwn(methods, id)) throw new SparkBackendError('unknown_operation');
    return id as CourseOperation;
  };
  function contractFor(id: CourseOperation) {
    const contract = modules[methods[id][0]];
    if (!contract) throw new SparkBackendError('operation_not_available', 409);
    if (id === 'receiveConcernAt' && !supportsEarlierConcernReceipt) {
      throw new SparkBackendError('operation_not_available', 409);
    }
    return contract;
  }
  function inputParameters(id: CourseOperation): readonly AbiParameter[] {
    const contract = contractFor(id);
    if (id === 'approveRechargeToken') return parameters(modules.funds, 'recharge');
    const params = isSettlementProposal(id) ? parameters(contract, 'previewOrdinaryGroup').slice(0, 2)
      : parameters(contract, settlementMethod(id));
    return isEarlySettlement(id) ? [...params, ...verifiedEarlyAmounts] : params;
  }
  function offer(operationId: CourseOperation, fixed: Record<string, unknown> = {}): CourseOffer {
    const [, , label] = methods[operationId];
    const fields = inputParameters(operationId).filter(param => param.name !== 'authorityId' && !(param.name! in fixed))
      .map(param => ({ name: param.name!, label: labels[param.name!] ?? param.name!, type: fieldType(param) }));
    return { operationId, label, fields, arguments: fixed };
  }
  async function canPrepare(account: Address, call: { to: Address; data: Hex }, abi: Abi, point: ReadPoint) {
    try {
      await sdk.simulate(client, account, call, abi, point);
      return true;
    } catch (error) {
      if (error instanceof AvaSigningError && error.code === 'contract_reverted') return false;
      throw error;
    }
  }

  const supportsUnconfirmedEarlyStart = modules.earlyStart?.abi.some(entry =>
    entry.type === 'function' && entry.name === 'requireUnconfirmedProviderStartForm');
  const supportsLateOpeningNotices = modules.earlyStart?.abi.some(entry =>
    entry.type === 'function' && entry.name === 'hasUsableLateOpeningNotices');
  const supportsEarlierConcernReceipt = modules.intake.abi.some(entry =>
    entry.type === 'function' && entry.name === 'receiveConcernAt');

  function mayUseOrdinarySettlement(lessonId: Hex, teaching: Teaching, point: ReadPoint) {
    // No actual start can still support the separately verified absence routes.
    if (teaching.startedAt === 0n || teaching.startPermission === permittedTeachingStart) return true;
    if (teaching.startPermission !== unverifiedTeachingStart || !supportsLateOpeningNotices) return false;
    return read<boolean>(modules.earlyStart!, 'hasUsableLateOpeningNotices', point, [lessonId]);
  }

  async function earlyStartSeat(lessonId: Hex, lesson: Lesson, teaching: Teaching, point: ReadPoint) {
    if (!modules.earlyStart || teaching.startPermission !== teachingRequirementsNotMet || !teaching.providerWentAhead
      || teaching.startedAt === 0n || teaching.endedAt === 0n || teaching.startEvidenceId === 0n || teaching.endEvidenceId === 0n
      || same(teaching.unmetConditionRef, zeroHash) || !same(lesson.terms.rosterRef, zeroHash)
      || !same(lesson.terms.materialsTermsRef, zeroHash)) return;
    const forms = await read<Hex[]>(modules.booking, 'getPlannedForms', point, [lessonId]);
    if (forms.length !== 1) return;
    const formId = forms[0];
    const form = await read<Form>(modules.booking, 'getForm', point, [formId]);
    const { confirmedAt, debitedUnits } = form.confirmation;
    const unconfirmed = confirmedAt === 0n;
    if (unconfirmed ? debitedUnits !== 0n : confirmedAt >= teaching.startedAt || debitedUnits === 0n) return;
    return { formId, form, unconfirmed };
  }

  async function usableEarlyStart(
    account: Address, lessonId: Hex, seat: { formId: Hex; unconfirmed: boolean }, timestamp: bigint, point: ReadPoint,
  ) {
    const { formId, unconfirmed } = seat;
    if (unconfirmed && !supportsUnconfirmedEarlyStart) return false;
    const occurrences = modules.earlyStart!;
    const [cancelled, usable] = await Promise.all([
      read<boolean>(modules.booking, 'isCancelledAt', point, [formId, timestamp]),
      canPrepare(account, { to: occurrences.address,
        data: encodeFunctionData({ abi: occurrences.abi, functionName: 'readProviderStartBasis', args: [lessonId] }) },
      occurrences.abi, point),
    ]);
    return !cancelled && usable;
  }

  async function earlyAssessment(account: Address, id: CourseOperation, fields: Record<string, unknown>, snapshot: CanonicalSnapshot) {
    if (!modules.earlyStart) throw new SparkBackendError('operation_not_available', 409);
    if (!participantHash(fields.lessonId)) throw new SparkBackendError('invalid_fields');
    const lessonId = fields.lessonId;
    const { point, timestamp } = snapshot;
    const [lesson, teaching, settled] = await Promise.all([
      read<Lesson>(modules.booking, 'getLesson', point, [lessonId]), read<Teaching>(modules.booking, 'getTeaching', point, [lessonId]),
      read<GroupSettlement>(modules.settlement, 'getGroupSettlement', point, [lessonId]),
    ]);
    const proposal = isSettlementProposal(id);
    const role = proposal ? modules.coordinator : sparkV15.verifierRole;
    const action = proposal ? proposes : approves;
    if ((proposal && !same(lesson.terms.coordinator, account)) || !(await authority(account, role, [action], point)).allowed.has(action)) {
      throw new SparkBackendError('role_not_authorised', 403);
    }
    const seat = await earlyStartSeat(lessonId, lesson, teaching, point);
    if (!seat || settled.complete || timestamp < lesson.terms.startsAt
      || !await usableEarlyStart(account, lessonId, seat, timestamp, point)) {
      throw new SparkBackendError('operation_not_available', 409);
    }
    const assessment = participantObject(fields.assessment);
    const { seats } = assessment;
    if (!Array.isArray(seats) || seats.length !== 1) throw new SparkBackendError('invalid_fields');
    const finding = participantObject(seats[0]);
    if (!same(finding.formId, seat.formId) || !same(assessment.effectiveChangeId, zeroHash)) {
      throw new SparkBackendError('invalid_fields');
    }
    const [serviceValue, tutorAmount] = verifiedEarlyAmounts.map(param => argument(param, fields[param.name!]) as bigint);
    const { debitedUnits } = seat.form.confirmation;
    if (!seat.unconfirmed && serviceValue > debitedUnits) throw new SparkBackendError('invalid_fields');
    const verificationRef = await read<Hex>(modules.earlyStart, 'encodeProviderStartedEarlyAmounts', point, [serviceValue, tutorAmount]);
    if ((assessment.route !== undefined && String(assessment.route) !== String(providerStartedEarlyRoute))
      || (finding.disposition !== undefined && String(finding.disposition) !== String(providerStartedEarlySeat))
      || (assessment.verificationRef !== undefined && !same(assessment.verificationRef, verificationRef))) {
      throw new SparkBackendError('invalid_fields');
    }
    const debitDetails = { originalPayer: seat.form.terms.payer,
      ...(seat.unconfirmed ? { debitedUnits, refundDue: 0n } : { originalDebitAccount: seat.form.terms.creditAccount }) };
    return { assessment: { ...assessment, route: providerStartedEarlyRoute, verificationRef,
      seats: [{ ...finding, disposition: providerStartedEarlySeat }] }, debitDetails };
  }
  async function fundingReady(account: Address, lessonId: Hex, point: ReadPoint) {
    const contract = modules.prefunding ?? modules.funds;
    const call = { to: contract.address, data: encodeFunctionData({ abi: contract.abi,
      functionName: 'requireCommitmentFunding', args: [lessonId, zeroHash] }) };
    return canPrepare(account, call, contract.abi, point);
  }
  async function findOriginalRefund(redress: ParticipantContract, formId: Hex, caseId: Hex, revision: bigint, point: ReadPoint) {
    const [count] = await read<readonly [bigint, bigint, bigint]>(redress, 'refundStatus', point, [formId]);
    for (let index = count; index > 0n;) {
      --index;
      const assessment = await read<RefundAssessment>(redress, 'getRefund', point, [formId, index]);
      if (assessment.cause === originalRelief && assessment.faultRevision === revision && same(assessment.caseId, caseId)) {
        return { index, assessment };
      }
    }
  }
  async function compensationStatus(formId: Hex, form: Form, account: Address, access: {
    isProvider: boolean; canAcceptAsCustomer: boolean; canAssessRefund: boolean;
  }, point: ReadPoint) {
    const { remedies, redress } = modules;
    if (!remedies || !redress) return;

    const [termsEvidence, decision, caseId] = await Promise.all([
      read<bigint>(redress, 'redressTermsEvidence', point, [formId]),
      read<{ acceptedAt: bigint; directRefundAt: bigint; creditIssuedAt: bigint }>(redress, 'getRedress', point, [formId]),
      read<Hex>(remedies, 'placeFaultCase', point, [formId]),
    ]);
    const termsPublished = termsEvidence !== 0n;
    const accepted = decision.acceptedAt !== 0n;
    const creditIssued = decision.creditIssuedAt !== 0n;
    const revision = same(caseId, zeroHash) ? 0n : await read<bigint>(remedies, 'latestFaultRevision', point, [caseId]);
    const faultRecorded = revision > 0n && isTutorFault((await read<{ kind: number }>(
      remedies, 'getFault', point, [caseId, revision])).kind);
    const operative = termsPublished && faultRecorded && await read<boolean>(remedies, 'isOperative', point, [caseId, revision]);
    const [refund, creditRemaining] = await Promise.all([
      operative ? findOriginalRefund(redress, formId, caseId, revision, point) : undefined,
      creditIssued ? read<bigint>(modules.funds, 'compensationCreditRemaining', point, [form.lessonId, form.terms.placeId]) : 0n,
    ]);
    let refundDue: bigint | undefined;
    if (refund && !same(refund.assessment.obligationId, zeroHash)) {
      const payment = await read<{ correctAmount: bigint; paid: bigint }>(modules.payments, 'getObligation', point,
        [refund.assessment.obligationId]);
      refundDue = payment.correctAmount > payment.paid ? payment.correctAmount - payment.paid : 0n;
    }
    const actions: CourseOffer[] = [];
    if (access.isProvider && !termsPublished) actions.push(offer('publishRedressTerms', { formId }));
    if (access.canAssessRefund && operative) {
      if (!refund) actions.push(offer('assessRefund', { formId, cause: originalRelief }));
      else if (refund.assessment.principal > 0n && refundDue === undefined) {
        actions.push(offer('establishRefundPayment', { formId, index: refund.index }));
      }
    }
    if (access.canAcceptAsCustomer && operative && !accepted && decision.directRefundAt === 0n) {
      const call = { to: redress.address,
        data: encodeFunctionData({ abi: redress.abi, functionName: 'acceptStandardCompensation', args: [formId] }) };
      if (await canPrepare(account, call, redress.abi, point)) actions.push(offer('acceptStandardCompensation', { formId }));
    }
    if (access.isProvider && accepted && !creditIssued) {
      const call = { to: redress.address,
        data: encodeFunctionData({ abi: redress.abi, functionName: 'issueCourseCredit', args: [formId] }) };
      if (await canPrepare(account, call, redress.abi, point)) actions.push(offer('issueCourseCredit', { formId }));
    }
    return { actions, view: { termsPublished, faultRecorded, accepted, creditIssued, creditRemaining,
      refundAssessed: refund?.assessment.principal, refundDue } };
  }
  async function workspace(account: Address, snapshot: CanonicalSnapshot) {
    const { point, timestamp } = snapshot;
    const [coordinator, verifier, provider, logs, publications, rechargeEvents] = await Promise.all([
      authority(account, modules.coordinator, [coordAction, proposes, confirmOneToOne], point),
      authority(account, sparkV15.verifierRole, [verifyFunding, verifyTeaching, approves,
        assessRefundPermission, releaseBudgetPermission], point),
      authority(account, modules.provider, [publishesContacts, offersRecharge], point),
      client.getContractEvents({ ...bookingIndex, fromBlock: 0n, toBlock: snapshot.blockNumber, strict: true }),
      client.getContractEvents({ ...modules.intake, eventName: 'ContactsPublished', fromBlock: 0n,
        toBlock: snapshot.blockNumber, strict: true }),
      client.getContractEvents({ ...modules.funds, eventName: 'RechargeOffered', args: { customer: account },
        fromBlock: 0n, toBlock: snapshot.blockNumber, strict: true }),
    ]);
    const global = coordinator.allowed.has(coordAction) ? [offer('publishLesson')] : [];
    if (provider.allowed.has(offersRecharge)) global.push(offer('offerRecharge'));
    const canAssessRefund = verifier.allowed.has(assessRefundPermission);
    const serviceReserve = verifier.allowed.has(releaseBudgetPermission) ? modules.serviceReserve : undefined;
    const releasedByLesson = new Map<string, bigint>();
    if (serviceReserve) {
      const events = await client.getContractEvents({ ...serviceReserve, eventName: 'FundingReserveReleased',
        fromBlock: 0n, toBlock: snapshot.blockNumber, strict: true });
      for (const event of events) {
        const { lessonId, amount } = event.args as { lessonId: Hex; amount: bigint };
        const id = lessonId.toLowerCase();
        releasedByLesson.set(id, (releasedByLesson.get(id) ?? 0n) + amount);
      }
    }
    let allowance: Promise<bigint> | undefined;
    const rechargeIssuers = new Map<string, ReturnType<typeof rechargeIssuer>>();
    function readIssuer(provider: Address) {
      const key = provider.toLowerCase();
      let issuer = rechargeIssuers.get(key);
      if (!issuer) {
        issuer = rechargeIssuer(provider, point);
        rechargeIssuers.set(key, issuer);
      }
      return issuer;
    }
    const rechargeReads = rechargeEvents.map(async event => {
      const offerId = (event.args as { offerId: Hex }).offerId;
      const terms = await read<RechargeOffer>(modules.funds, 'getRechargeOffer', point, [offerId]);
      const actions: CourseOffer[] = [];
      if (await mayRecharge(terms, account, readIssuer)) {
        allowance ??= read<bigint>(modules.token, 'allowance', point, [account, modules.funds.address]);
        actions.push(offer(await allowance < terms.terms.amount ? 'approveRechargeToken' : 'recharge', { offerId }));
      }
      return { offerId, amount: terms.terms.amount, returnCap: terms.terms.returnCap, returnThrough: terms.terms.returnThrough,
        provider: terms.provider, receiptId: terms.receiptId, actions };
    });
    const formsByLesson = new Map<string, Map<Hex, Hex>>();
    for (const event of logs) {
      if (event.eventName !== 'FormPublished') continue;
      const { lessonId, placeId, formId } = event.args as { lessonId: Hex; placeId: Hex; formId: Hex };
      const lessonKey = lessonId.toLowerCase();
      let current = formsByLesson.get(lessonKey);
      if (!current) {
        current = new Map();
        formsByLesson.set(lessonKey, current);
      }
      current.set(placeId, formId);
    }
    const lessonReads = logs.filter(event => event.eventName === 'LessonPublished').map(async event => {
      const lessonId = (event.args as { lessonId: Hex }).lessonId;
      const lesson = await read<Lesson>(modules.booking, 'getLesson', point, [lessonId]);
      const { terms, prefunding } = lesson;
      const isCoordinator = same(account, terms.coordinator) && coordinator.allowed.has(coordAction);
      const isProvider = same(account, terms.provider);
      const isTutor = same(account, terms.tutor);
      const current = formsByLesson.get(lessonId.toLowerCase());
      const forms = await Promise.all(Array.from(current?.values() ?? [], async formId => ({
        formId, ...await read<Form>(modules.booking, 'getForm', point, [formId]),
      })));
      const formMember = (form: Form) => [form.terms.payer, form.terms.customer, form.terms.customerRepresentative,
        form.terms.student].some(actor => same(account, actor));
      const canConfirmAsCoordinator = same(account, terms.coordinator) && coordinator.allowed.has(confirmOneToOne);
      const staff = isCoordinator || canConfirmAsCoordinator || isProvider || isTutor || verifier.allowed.size > 0;
      const own = forms.some(formMember);
      if (!staff && !own) return;
      const cutoff = terms.rosterLockAt || terms.startsAt;
      const beforeCutoff = timestamp < cutoff;
      const ready = prefunding.evidenceId !== 0n;
      const [teaching, roster, tutorNotice, tutorDelivery, providerSigned, tutorSigned, funded, settled, proposal] = await Promise.all([
        read<Teaching>(modules.booking, 'getTeaching', point, [lessonId]),
        read<{ evidenceId: bigint; lockedAt: bigint }>(modules.booking, 'getRosterLock', point, [lessonId]),
        isCoordinator && ready ? read<{ evidenceId: bigint }>(modules.booking, 'getTutorNotice', point, [lessonId]) : undefined,
        isTutor ? read<{ evidenceId: bigint }>(modules.booking, 'getTutorDelivery', point, [lessonId]) : undefined,
        beforeCutoff && (isTutor || (isProvider && ready))
          ? read<bigint>(modules.booking, 'teachingAgreementSignedAt', point, [lessonId, terms.provider]) : 0n,
        beforeCutoff && isTutor ? read<bigint>(modules.booking, 'teachingAgreementSignedAt', point, [lessonId, terms.tutor]) : 0n,
        ready && beforeCutoff && forms.some(form => form.confirmation.confirmedAt === 0n)
          ? read<Hex[]>(modules.booking, 'getPlannedForms', point, [lessonId]) : undefined,
        read<GroupSettlement>(modules.settlement, 'getGroupSettlement', point, [lessonId]),
        verifier.allowed.has(approves) ? read<readonly [Hex, Address, Hex, bigint]>(modules.settlement, 'proposals', point, [lessonId])
          : undefined,
      ]);
      const offers: CourseOffer[] = [];
      const lessonAction = (id: CourseOperation, fixed?: Record<string, unknown>) => offers.push(offer(id, { lessonId, ...fixed }));
      if (isCoordinator && !ready && beforeCutoff) lessonAction('publishForm');
      if (verifier.allowed.has(verifyFunding) && forms.length > 0 && !ready && beforeCutoff) lessonAction('verifyPrefunding');
      const material = modules.fundingCases && !same(terms.materialsTermsRef, zeroHash);
      if (modules.fundingCases && ready && (isProvider || verifier.allowed.has(verifyFunding))
        && !await read<boolean>(modules.fundingCases!, 'hasInventory', point, [lessonId])) lessonAction('retainInventory');
      const pendingFunding = ready && beforeCutoff && Boolean(funded?.length);
      const lessonFundingReady = pendingFunding && (!(modules.prefunding || material) || await fundingReady(account, lessonId, point));
      if (ready && beforeCutoff && (lessonFundingReady || modules.usableTerms)
        && ((isProvider && providerSigned === 0n) || (isTutor && tutorSigned === 0n))) {
        if (!modules.usableTerms || await canPrepare(account, { to: modules.booking.address,
          data: encodeFunctionData({ abi: modules.booking.abi, functionName: 'signTeachingAgreement', args: [lessonId] }),
        }, modules.booking.abi, point)) lessonAction('signTeachingAgreement');
      }
      if (tutorNotice?.evidenceId === 0n) lessonAction('recordTutorNotice', { channelRef: terms.tutorNoticeChannelRef });
      const confirmed = forms.some(form => form.confirmation.confirmedAt !== 0n);
      if (isCoordinator && confirmed && terms.rosterLockAt !== 0n && roster.evidenceId === 0n && timestamp >= cutoff) lessonAction('lockRoster');
      // An observed start can precede its scheduled time even when the start conditions were unmet.
      if (verifier.allowed.has(verifyTeaching) && teaching.startedAt === 0n) {
        lessonAction('recordTeachingStarted');
      }
      if (verifier.allowed.has(verifyTeaching) && teaching.startedAt > 0n && teaching.endedAt === 0n) lessonAction('recordTeachingEnded');
      if (teaching.endedAt > 0n && tutorDelivery?.evidenceId === 0n) lessonAction('recordTutorDelivery');
      const ordinarySettlementAvailable = await mayUseOrdinarySettlement(lessonId, teaching, point);
      if (!settled.complete && ordinarySettlementAvailable) {
        if (isCoordinator && coordinator.allowed.has(proposes) && teaching.endedAt > 0n) lessonAction('proposeOrdinaryGroup');
        if (proposal && !same(proposal[0], zeroHash)) lessonAction('approveOrdinaryGroup');
      }
      let earlySettlement;
      const canPropose = isCoordinator && coordinator.allowed.has(proposes);
      const hasProposal = proposal && !same(proposal[0], zeroHash);
      if ((settled.complete && settled.route === providerStartedEarlyRoute) || canPropose || hasProposal) {
        const early = await earlyStartSeat(lessonId, lesson, teaching, point);
        if (early && settled.complete && settled.route === providerStartedEarlyRoute) {
          const row = await read<EarlySeatSettlement>(modules.settlement, 'getSeatSettlement', point, [lessonId, early.formId]);
          const { formId, debitAccount, debited, disposition, feeDue, tutorPay, tutorNetPay, refundDue, refundAlreadyReceived } = row;
          if (disposition === providerStartedEarlySeat && same(formId, early.formId)) {
            earlySettlement = { formId, payer: early.form.terms.payer, feeDue, tutorPay, tutorNetPay, refundDue, refundAlreadyReceived,
              ...(early.unconfirmed ? { debitedUnits: debited } : { debitAccount }) };
          }
        } else if (early && !settled.complete && timestamp >= terms.startsAt
          && await usableEarlyStart(account, lessonId, early, timestamp, point)) {
          if (canPropose) lessonAction('proposeProviderStartedEarly');
          if (hasProposal) lessonAction('approveProviderStartedEarly');
        }
      }
      const contactEntries = publications.filter(entry => same((entry.args as { lessonId: Hex }).lessonId, lessonId));
      if (isProvider && provider.allowed.has(publishesContacts)) offers.push(offer('publishContacts'));
      if (own && contactEntries.length) {
        offers.push(offer('receiveConcern'));
        if (supportsEarlierConcernReceipt) offers.push(offer('receiveConcernAt'));
      }
      const termsProvided = (formId: Hex, recipient: Address) => readsTermsProvision
        ? read<boolean>(modules.booking, 'hasTermsProvision', point, [formId, recipient])
        : read<bigint>(modules.booking, 'termsProvisionEvidence', point, [formId, recipient]).then(id => id !== 0n);
      const seats = await Promise.all(forms.filter(form => staff || formMember(form)).map(async form => {
        const { formId, terms: seat, confirmation } = form;
        const paid = confirmation.confirmedAt !== 0n;
        const accepting = !paid && lessonFundingReady && funded?.includes(formId) === true;
        const customer = same(account, seat.customer);
        const isRepresentative = same(account, seat.customerRepresentative);
        const isPayer = same(account, seat.payer);
        const separatePayer = !same(seat.payer, seat.customer);
        const signingRoles = [isProvider, isTutor, customer || isRepresentative, isPayer && separatePayer];
        const signaturesForConfirmation = isCoordinator ? (separatePayer ? 4 : 3) : 0;
        const canAppoint = customer && !paid && !same(seat.customerRepresentative, zeroAddress);
        const showRecordedDelivery = isCoordinator && !paid;
        const checkTutorDelivery = accepting && (isCoordinator || isTutor);
        const recordedCustomerDelivery = showRecordedDelivery || (accepting && !usableTerms)
          ? termsProvided(formId, seat.customer) : false;
        const recordedTutorDelivery = showRecordedDelivery || (checkTutorDelivery && !usableTerms)
          ? termsProvided(formId, terms.tutor) : false;
        const [customerTerms, tutorProvision, recordedProvision, recordedTutorProvision, notice, attendance, feedback, signatures, representative] = await Promise.all([
          accepting && (usableTerms
            ? read<boolean>(usableTerms, 'hasUsableCustomerTerms', point,
                [formId, seat.customer, seat.customerRepresentative, lesson.packageId])
            : recordedCustomerDelivery),
          checkTutorDelivery && (usableTerms
            ? read<boolean>(usableTerms, 'hasUsableTermsProvision', point, [formId, terms.tutor, lesson.packageId])
            : recordedTutorDelivery),
          recordedCustomerDelivery,
          recordedTutorDelivery,
          read<{ evidenceId: bigint }>(modules.booking, 'getStudentNotice', point, [formId]),
          read<{ reportedAt: bigint; attended: boolean }>(modules.booking, 'getAttendance', point, [formId]),
          read<{ evidenceId: bigint; status: number }>(modules.booking, 'getServiceFeedback', point, [formId]),
          accepting ? Promise.all(signingRoles.map((canSign, role) => canSign || role < signaturesForConfirmation
            ? read<readonly [Address, bigint]>(modules.booking, 'acceptances', point, [formId, role]) : undefined)) : undefined,
          isRepresentative || canAppoint ? read<boolean>(modules.booking, 'representativeAuthorised', point, [formId]) : false,
        ]);
        const actions: CourseOffer[] = [];
        const formAction = (id: CourseOperation, fixed?: Record<string, unknown>) => actions.push(offer(id, { formId, ...fixed }));
        if (canAppoint && !representative) formAction('authoriseRepresentative');
        if (showRecordedDelivery && (!recordedProvision || !recordedTutorProvision)) formAction('recordTermsProvision');
        if (signatures && customerTerms) {
          const outstandingSigning = [
            signingRoles[0], signingRoles[1] && tutorProvision && providerSigned > 0n && tutorSigned > 0n,
            customer || (representative && isRepresentative), signingRoles[3],
          ];
          for (const [role, needed] of outstandingSigning.entries()) {
            if (needed && signatures[role]?.[1] === 0n) formAction('acceptForm', { role });
          }
          if (signaturesForConfirmation && (!usableTerms || tutorProvision)
            && signatures.slice(0, signaturesForConfirmation).every(signature => signature && signature[1] > 0n)) {
            formAction('confirmPlace', seat.payableFee === 0n ? {} : { discountRef: zeroHash, discountEvidenceId: '0' });
          }
        }
        let localCompletionAdopted = false;
        if (modules.alternatives && paid && same(terms.rosterRef, zeroHash) && teaching.endEvidenceId > 0n
          && ordinarySettlementAvailable) {
          localCompletionAdopted = readsAdoptedCompletion && settled.complete
            && await read<boolean>(modules.settlement, 'hasAdoptedOneToOneCompletion', point, [lessonId, formId]);
          const isStudent = same(account, seat.student);
          if (!localCompletionAdopted && (isStudent || canConfirmAsCoordinator)) {
            const field = isStudent ? 'studentCompletion' : 'coordinatorCompletion';
            if (await read<bigint>(modules.alternatives, field, point, [formId]) === 0n) formAction('recordOneToOneCompletion');
          }
        }
        if (isCoordinator && paid && notice.evidenceId === 0n) formAction('recordStudentNotice');
        if (paid && same(account, seat.student) && teaching.endedAt > 0n) {
          if (attendance.reportedAt === 0n) formAction('recordAttendance');
          if (feedback.evidenceId === 0n) formAction('recordServiceFeedback');
        }
        const canAcceptAsCustomer = customer || (isRepresentative && representative);
        const compensation = isProvider || (paid && (canAcceptAsCustomer || canAssessRefund || serviceReserve))
          ? await compensationStatus(formId, form, account, { isProvider, canAcceptAsCustomer: paid && canAcceptAsCustomer,
            canAssessRefund: paid && canAssessRefund }, point) : undefined;
        if (compensation) actions.push(...compensation.actions);
        const roles = [...(same(account, seat.student) ? ['student'] : []), ...(isPayer ? ['payer'] : []),
          ...(customer ? ['customer'] : []), ...(representative && isRepresentative ? ['representative'] : [])];
        return { formId, version: form.version, placeId: seat.placeId, normalFee: seat.normalFee, payableFee: seat.payableFee, confirmation,
          notice: notice.evidenceId > 0n, attendance: attendance.reportedAt > 0n ? attendance.attended : undefined,
          feedback: feedback.evidenceId > 0n ? feedback.status : undefined, localCompletionAdopted,
          compensation: compensation?.view, actions, roles };
      }));
      let fundingReview;
      if (serviceReserve && seats.some(seat => seat.compensation?.creditIssued && seat.compensation.refundDue !== undefined)) {
        const [lessonHeld, earnedFees, releasable] = await Promise.all([
          read<bigint>(modules.funds, 'lessonReserved', point, [lessonId]),
          read<bigint>(modules.funds, 'lessonFeeBalance', point, [lessonId]),
          read<bigint>(serviceReserve, 'releasableProviderHold', point, [lessonId]),
        ]);
        fundingReview = { lessonHeld, earnedFees, releasable, released: releasedByLesson.get(lessonId.toLowerCase()) ?? 0n };
        if (releasable > 0n) lessonAction('releaseBudget');
      }
      const roles = [...(isProvider ? ['courseProvider'] : []), ...(isTutor ? ['tutor'] : []), ...seats.flatMap(seat => seat.roles)];
      const openingNoticesVerifiedLater = teaching.startedAt !== 0n
        && teaching.startPermission === unverifiedTeachingStart && ordinarySettlementAvailable;
      return { lessonId, packageId: lesson.packageId, startsAt: terms.startsAt, endsAt: terms.endsAt, roster, teaching,
        openingNoticesVerifiedLater, commitmentFundingAvailable: pendingFunding ? lessonFundingReady : undefined,
        prefunding, settled, earlySettlement, fundingReview, recorded: event.transactionHash, offers, seats, roles,
        contacts: contactEntries.map(entry => (entry.args as { termsId: Hex }).termsId) };
    });
    const [recharges, lessons] = await Promise.all([Promise.all(rechargeReads), Promise.all(lessonReads)]);
    return { asOf: { blockNumber: snapshot.blockNumber, blockHash: snapshot.blockHash, timestamp }, global,
      recharges,
      roles: [...(coordinator.allowed.size ? ['bookingCoordinator'] : []), ...(verifier.allowed.size ? ['verifier'] : []),
        ...(provider.allowed.size ? ['courseProvider'] : []), ...lessons.flatMap(lesson => lesson?.roles ?? [])],
      lessons: lessons.filter(value => value !== undefined) };
  }

  function scoped(value: unknown) {
    const request = participantObject(value);
    const account = participantAddress(request.account), input = participantObject(request.input);
    if (!same(request.appId, appId) || !same(request.workflowKey, workflowKey) || !same(input.installation, installationHash)) {
      throw new SparkBackendError('installation_mismatch', 409);
    }
    const now = Math.floor(Date.now() / 1000), issued = input.requestedAt;
    if (typeof issued !== 'number' || !Number.isSafeInteger(issued) || issued > now + 5 || issued + previewLifetime <= now) {
      throw new SparkBackendError('preview_expired', 409);
    }
    return { account, input, issued, operationId: lookup(request.operationId) };
  }
  async function prepare(value: unknown) {
    const { account, input, issued, operationId } = scoped(value);
    const descriptor = methods[operationId], [, , label] = descriptor;
    const contract = contractFor(operationId);
    const fields = participantObject(input.arguments);
    return withCanonicalSnapshot(client, async snapshot => {
      const { point, blockNumber, blockHash, timestamp } = snapshot;
      const early = isEarlySettlement(operationId) ? await earlyAssessment(account, operationId, fields, snapshot) : undefined;
      const args: Record<string, unknown> = {};
      const params = inputParameters(operationId);
      let signer: { roleKey: Hex; authorityId: Hex } | undefined;
      for (const param of params) {
        if (param.name === 'authorityId') {
          const permission = operationId === 'publishContacts' ? publishesContacts : descriptor[3];
          if (!permission) throw new AvaRuntimeError('runtime_mismatch');
          const authorities = await Promise.all(authorityRoles.map(roleKey => authority(account, roleKey, [permission], point)));
          signer = authorities.find(actor => actor.allowed.has(permission))?.authority ?? undefined;
          if (!signer) throw new SparkBackendError('role_not_authorised', 403);
        } else {
          const value = early && param.name === 'assessment' ? early.assessment : fields[param.name!];
          args[param.name!] = argument(param, value);
        }
      }
      if (operationId === 'proposeOrdinaryGroup' || operationId === 'approveOrdinaryGroup') {
        const teaching = await read<Teaching>(modules.booking, 'getTeaching', point, [args.lessonId]);
        if (!await mayUseOrdinarySettlement(args.lessonId as Hex, teaching, point)
          || hasEarlySettlementRoute(args.assessment as AssessmentRoute)) {
          throw new SparkBackendError('operation_not_available', 409);
        }
      }
      let proofPackage: bigint | undefined;
      let functionName: string = settlementMethod(operationId);
      const callParams = early ? params.slice(0, -verifiedEarlyAmounts.length) : params;
      let encoded = isSettlementProposal(operationId)
        ? [args.lessonId, await read<Hex>(contract, 'proposalCommitment', point, [args.lessonId, args.assessment])]
        : callParams.map(param => param.name === 'authorityId' ? signer!.authorityId : args[param.name!]);
      if (early) Object.assign(args, early.debitDetails);
      if (operationId === 'approveRechargeToken' || operationId === 'recharge') {
        const rechargeOffer = await read<RechargeOffer>(modules.funds, 'getRechargeOffer', point, [args.offerId]);
        if (!await mayRecharge(rechargeOffer, account, provider => rechargeIssuer(provider, point))) {
          throw new SparkBackendError('role_not_authorised', 403);
        }
        proofPackage = rechargeOffer.packageId;
        args.amount = rechargeOffer.terms.amount;
        if (operationId === 'approveRechargeToken') {
          functionName = 'approve';
          args.spender = modules.funds.address;
          encoded = [args.spender, args.amount];
        }
      }
      if (operationId === 'retainOriginal') {
        const original = args.input as OriginalFinding;
        const { terms } = await read<{ terms: { lessonId: Hex } }>(modules.intake, 'getPublishedContacts', point, [original.termsId]);
        const caseId = await read<Hex>(modules.cases, 'caseIdFor', point, [terms.lessonId, original.concernRef]);
        const [matter, decision] = await Promise.all([
          read<FaultMatter>(modules.intake, 'caseContext', point, [caseId]),
          read<CaseDecision>(modules.cases, 'getCase', point, [caseId]),
        ]);
        const { initial } = decision;
        if (!modules.remedies || !same(original.termsId, matter.termsId) || !same(matter.obligationId, zeroHash)
          || !same(original.obligationId, matter.obligationId)
          || !same(keccak256(encodeAbiParameters([{ type: 'address[]' }], [original.parties])), matter.partiesHash)
          || initial.evidenceId === 0n || initial.input.issue !== faultIssue
          || !same(original.decider, initial.decider) || original.decidedAt !== initial.decidedAt
          || !same(original.outcome, initial.input.outcome)) {
          throw new SparkBackendError('operation_not_available', 409);
        }
        args.caseId = caseId;
      }
      if (operationId === 'recordFault') {
        const [decision, revision] = await Promise.all([
          read<CaseDecision>(modules.cases, 'getCase', point, [args.caseId]),
          read<bigint>(contract, 'latestFaultRevision', point, [args.caseId]),
        ]);
        if (!same(decision.initial.decider, account)) throw new SparkBackendError('role_not_authorised', 403);
        if (decision.initial.input.issue !== faultIssue || revision !== 0n
          || decision.original.evidenceId === 0n || decision.review.decidedAt !== 0n
          || !isTutorFault(Number((args.finding as { kind: bigint }).kind))) {
          throw new SparkBackendError('operation_not_available', 409);
        }
      }
      if (operationId === 'establishRefundPayment') {
        const verifier = await authority(account, sparkV15.verifierRole, [assessRefundPermission], point);
        if (!verifier.allowed.has(assessRefundPermission)) throw new SparkBackendError('role_not_authorised', 403);
        signer = verifier.authority ?? undefined;
      }
      if (operationId === 'issueCourseCredit') {
        const form = await read<Form>(modules.booking, 'getForm', point, [args.formId]);
        const lesson = await read<Lesson>(modules.booking, 'getLesson', point, [form.lessonId]);
        if (!same(account, lesson.terms.provider)) throw new SparkBackendError('role_not_authorised', 403);
        proofPackage = lesson.packageId;
      }
      if (operationId === 'retainInventory') {
        const lesson = await read<Lesson>(modules.booking, 'getLesson', point, [args.lessonId]);
        const verifier = await authority(account, sparkV15.verifierRole, [verifyFunding], point);
        if (!same(account, lesson.terms.provider) && !verifier.allowed.has(verifyFunding)) {
          throw new SparkBackendError('role_not_authorised', 403);
        }
      }
      const call = { to: contract.address, data: encodeFunctionData({ abi: contract.abi, functionName, args: encoded }) };
      if (!await canPrepare(account, call, contract.abi, point)) throw new SparkBackendError('operation_not_available', 409);
      const terms = args.terms as { lessonId?: Hex } | undefined;
      const lessonId = proofPackage ? undefined : participantHash(args.lessonId) ? args.lessonId : terms?.lessonId
        ?? (participantHash(args.formId) ? (await read<Form>(modules.booking, 'getForm', point, [args.formId])).lessonId
          : participantHash(args.caseId) ? (await read<{ lessonId: Hex }>(modules.intake, 'getConcern', point, [args.caseId])).lessonId
            : undefined);
      if (lessonId !== undefined) proofPackage = (await read<Lesson>(modules.booking, 'getLesson', point, [lessonId])).packageId;
      return { version: 1, operationVersion: 1, appId, workflowKey, operationId, account, chain, authority: signer,
        asOf: { blockNumber, blockHash, timestamp }, input: { installation: installationHash, requestedAt: issued,
          arguments: args, packageId: proofPackage || packageId, label },
        call: { ...call, value: '0' }, expiresAt: issued + previewLifetime, courseOperation: label };
    });
  }
  async function quote(value: unknown) {
    const { account, operationId, input } = scoped(value);
    if (operationId !== 'approveOrdinaryGroup' && operationId !== 'approveProviderStartedEarly') {
      throw new SparkBackendError('unknown_operation');
    }
    const [lesson, assessment] = inputParameters(operationId);
    const fields = participantObject(input.arguments);
    return withCanonicalSnapshot(client, async snapshot => {
      const { point } = snapshot;
      const lessonId = argument(lesson, fields.lessonId);
      if (operationId === 'approveProviderStartedEarly') {
        const { assessment: early, debitDetails } = await earlyAssessment(account, operationId, fields, snapshot);
        const preview = await read<Record<string, unknown>>(modules.settlement, 'previewOrdinaryGroup', point,
          [lessonId, argument(assessment, early), account]);
        return { ...preview, ...debitDetails };
      }
      const teaching = await read<Teaching>(modules.booking, 'getTeaching', point, [lessonId]);
      if (!await mayUseOrdinarySettlement(lessonId as Hex, teaching, point)) {
        throw new SparkBackendError('operation_not_available', 409);
      }
      const draft = argument(assessment, fields.assessment) as AssessmentRoute;
      if (hasEarlySettlementRoute(draft)) throw new SparkBackendError('operation_not_available', 409);
      return read(modules.settlement, 'previewOrdinaryGroup', point, [lessonId, draft, account]);
    });
  }
  async function observe(value: unknown) {
    const body = participantObject(value), locator = participantObject(body.locator), requested = participantObject(locator.input);
    const identity = participantObject(locator.chain), call = participantObject(locator.call);
    const operationId = lookup(locator.operationId);
    const [, event] = methods[operationId];
    const contract = contractFor(operationId);
    if (!same(locator.appId, appId) || !same(locator.workflowKey, workflowKey) || identity.chainId !== chain.chainId
      || !same(identity.genesisHash, genesisHash) || !same(requested.installation, installationHash)
      || !same(call.to, contract.address)) throw new SparkBackendError('installation_mismatch', 409);
    if (!participantHash(body.hash) || locator.operationVersion !== 1 || call.value !== '0' || typeof call.data !== 'string'
      || !/^0x(?:[0-9a-f]{2}){4,16384}$/i.test(call.data)) throw new SparkBackendError('invalid_transaction');
    const account = participantAddress(locator.account);
    let functionName: string = settlementMethod(operationId);
    if (isEarlySettlement(operationId)) {
      const occurrences = modules.earlyStart;
      if (!occurrences) return { hash: body.hash, status: 'mismatch' };
      const fields = participantObject(requested.arguments);
      const params = inputParameters(operationId);
      const value = params.map(param => argument(param, fields[param.name!]));
      const [lessonId, assessment] = value as [Hex, AssessmentRoute];
      if (assessment.route !== BigInt(providerStartedEarlyRoute) || assessment.seats.length !== 1
        || assessment.seats[0].disposition !== BigInt(providerStartedEarlySeat)) return { hash: body.hash, status: 'mismatch' };
      const matches = await withCanonicalSnapshot(client, async ({ point }) => {
        const amounts = value.slice(-verifiedEarlyAmounts.length);
        const ref = await read<Hex>(occurrences, 'encodeProviderStartedEarlyAmounts', point, amounts);
        if (!same(ref, assessment.verificationRef)) return false;
        const args = isSettlementProposal(operationId)
          ? [lessonId, await read<Hex>(contract, 'proposalCommitment', point, [lessonId, assessment])]
          : value.slice(0, -verifiedEarlyAmounts.length);
        return same(encodeFunctionData({ abi: contract.abi, functionName, args }), call.data as Hex);
      });
      if (!matches) return { hash: body.hash, status: 'mismatch' };
    }
    if (operationId === 'approveRechargeToken') {
      const parameters = participantObject(requested.arguments);
      const result = decodeFunctionData({ abi: modules.token.abi, data: call.data as Hex });
      if (!participantHash(parameters.offerId) || result.functionName !== 'approve'
        || !same(result.args[0], modules.funds.address)) return { hash: body.hash, status: 'mismatch' };
      const matchesOffer = await withCanonicalSnapshot(client, async ({ point }) => {
        const original = await read<RechargeOffer>(modules.funds, 'getRechargeOffer', point, [parameters.offerId]);
        return same(original.terms.customer, account) && original.terms.amount === result.args[1];
      });
      if (!matchesOffer) return { hash: body.hash, status: 'mismatch' };
      functionName = 'approve';
    }
    return observeParticipantOperation({ client, chainId: chain.chainId, hash: body.hash, contract,
      account, data: call.data as Hex, operationId: functionName, eventName: event });
  }
  return { workspace, prepare, quote, observe, offer, read, authority, targets };
}
