import { createPublicQueue, createWorkbenchController } from '/wallet.js';
import { createCourseView, operationFields as renderOperationFields, courseActionLabel, courseFieldLabel, courseArgumentValue, isCourseTimeField, RecordInputError } from '/course.js';
import { b, localized, inLanguage, setText, initLanguage } from './i18n.js';

initLanguage();

const el = id => document.getElementById(id);
const same = (a, b) => typeof a === 'string' && typeof b === 'string' && a.toLowerCase() === b.toLowerCase();
const hash = /^0x[0-9a-f]{64}$/i;
const address = /^0x[0-9a-f]{40}$/i;
const empty = '0x' + '0'.repeat(64);
const operationLabel = {
  recordApproval: b('登记付款批准', 'Record payment approval'),
  recordReplacementArrangement: b('登记新的付款安排', 'Record a replacement payment arrangement'),
  imposeFormalHold: b('正式暂缓付款', 'Place a formal payment hold'),
  liftFormalHold: b('解除这笔付款的暂缓', 'Lift this payment hold'),
  imposeTemporaryHold: b('临时暂缓付款', 'Place a temporary hold'),
  verifyPostLiftClock: b('核对解除暂缓后的付款期限', 'Verify the payment deadline after release'),
  pay: b('付款', 'Make payment'),
};
const roleLabel = { source: b('证据来源', 'Evidence source'), verifier: b('核验与复核', 'Verification and review'), allocator: b('付款批准', 'Payment approval'), alternativeContact: b('备用联系人', 'Alternative contact'),
  recipient: b('收款方', 'Recipient'), executor: b('指定执行人', 'Designated executor'), bookingCoordinator: b('课程协调员', 'Course coordinator'), courseProvider: b('课程方', 'Course provider'), tutor: b('教师', 'Tutor'),
  student: b('学生', 'Student'), payer: b('付款人', 'Payer'), customer: b('客户', 'Customer'), representative: b('确认代理人', 'Confirmation representative') };
const sourceLabel = { 'participant-statement': b('参与者陈述', 'Participant statement'), 'verified-record': b('已核实记录', 'Verified record'), 'ai-suggestion': b('AI 建议', 'AI suggestion') };
const walletHint = b('连接钱包后，可以查看与你相关的课程、款项和交易记录。', 'Connect your wallet to see your classes, payments and transaction history.');
const transactionLabel = { unknown: b('等待核验', 'Awaiting verification'), pending: b('等待链上确认', 'Awaiting on-chain confirmation'), confirmed: b('交易已确认', 'Transaction confirmed'), reverted: b('交易在链上执行失败', 'Transaction failed on-chain'),
  mismatch: b('交易与原操作不匹配', 'Transaction does not match the original operation'), orphaned: b('回执已不在当前链上', 'Receipt is no longer on the current chain'), rejected: b('钱包已拒绝', 'Wallet rejected'), unavailable: b('交易读取暂不可用', 'Transaction lookup temporarily unavailable') };
const errorLabel = {
  installation_mismatch: b('这条记录属于另一套 Spark DAO 服务。请刷新后重试。', 'This record belongs to a different Spark DAO service. Refresh and try again.'),
  runtime_mismatch: b('服务的区块链或配置验证失败。', 'The service blockchain or configuration could not be verified.'),
  role_not_authorised: b('当前钱包已无权办理此操作。', 'This wallet is no longer authorized for this operation.'),
  preview_expired: b('预览已过期，请重新生成。', 'The preview has expired. Generate it again.'),
  preview_changed: b('款项记录已变化，请刷新后重新预览。', 'The payment record has changed. Refresh and preview again.'),
  obligation_mismatch: b('原批准或暂缓记录属于另一款项。', 'The original approval or hold belongs to another payment.'),
  operation_not_available: b('这项操作现在无法办理。请核对记录和相关证据。', 'This action is unavailable. Check the records and supporting evidence.'),
  notice_forbidden: b('此钱包没有该通知的读取权限。', 'This wallet is not authorized to read this notice.'),
  notice_unavailable: b('暂时无法读取这条私密通知，请稍后再试。', 'This private notice is temporarily unavailable. Try again later.'),
  invalid_integer: b('请输入有效范围内的十进制整数。', 'Enter a decimal integer within the valid range.'),
  invalid_fields: b('填写内容与当前服务要求的字段不符，请核对记录格式和数值。', 'The supplied fields do not match this service. Check the record format and values.'),
  invalid_reference: b('请检查款项、案件或证据引用。', 'Check the payment, case, or evidence reference.'),
  wallet_mismatch: b('钱包网络与当前服务不匹配', 'The wallet network does not match this service'),
};
const field = (name, label, type = 'uint', options = {}) => ({ name, label, type, ...options });
const clock = (name, label) => field(name, label, 'uint', { utc: true });
const evidenceFields = [field('evidenceId', b('已核实证据编号', 'Verified evidence ID'))];
const privateNoticeHashLabel = b('私密通知校验值', 'Private notice verification hash');
const basicHoldFields = [field('caseId', b('案件标识', 'Case ID'), 'hash'), field('noticeHash', privateNoticeHashLabel, 'hash')];
const approvalFields = [field('requestId', b('AVA 请求编号', 'AVA request ID')), field('executor', b('指定执行人地址', 'Designated executor address'), 'address'),
  field('ceiling', b('批准上限（最小单位）', 'Approval ceiling (base units)')), clock('validThrough', b('批准截止时间', 'Approval expiry')),
  field('replacesRequestId', b('原批准请求编号', 'Original approval request ID'), 'uint', { default: '0', help: b('首次批准填 0。', 'Enter 0 for the first approval.') })];
const operationFields = {
  recordApproval: approvalFields,
  recordReplacementArrangement: approvalFields,
  imposeFormalHold: [...basicHoldFields, clock('reviewAt', b('复核时间', 'Review time')), ...evidenceFields],
  liftFormalHold: [field('disposition', b('解除决定的校验值', 'Hold release decision hash'), 'hash'), ...evidenceFields],
  imposeTemporaryHold: [...basicHoldFields, clock('authorisedAt', b('授权时间', 'Authorization time')), clock('expiresAt', b('临时暂缓到期时间', 'Temporary hold expires')), ...evidenceFields],
  verifyPostLiftClock: evidenceFields,
  pay: [field('requestId', b('批准请求编号', 'Approval request ID')), field('amount', b('实际付款金额（最小单位）', 'Actual payment amount (base units)'))],
};
const labels = { requestId: b('请求编号', 'Request ID'), executor: b('指定执行人', 'Designated executor'), ceiling: b('批准上限（最小单位）', 'Approval ceiling (base units)'), validThrough: b('批准截止', 'Approval expiry'),
  replacesRequestId: b('接替的批准', 'Approval replaced'), caseId: b('案件标识', 'Case ID'), noticeHash: privateNoticeHashLabel, reviewAt: b('复核时间', 'Review time'),
  authorisedAt: b('授权时间', 'Authorization time'), expiresAt: b('临时暂缓到期', 'Temporary hold expires'), evidenceId: b('已核实证据', 'Verified evidence'), holdId: b('暂缓记录', 'Hold record'),
  disposition: b('解除决定的校验值', 'Hold release decision hash'), amount: b('付款金额（最小单位）', 'Payment amount (base units)') };
const dates = Object.fromEntries(['zh', 'en'].map(lang => [lang, new Intl.DateTimeFormat(lang === 'zh' ? 'zh-CN' : 'en-US', { dateStyle: 'medium', timeStyle: 'medium', timeZone: 'UTC' })]));
function time(value) {
  const instant = Number(value) * 1000;
  return value && value !== '0' && !Number.isNaN(new Date(instant).valueOf())
    ? localized(lang => `${dates[lang].format(instant)} UTC`) : '—';
}
function previewTime(value) {
  const date = time(value);
  return localized(lang => `${date === '—' ? '' : `${inLanguage(date, lang)} · `}${value} ${lang === 'zh' ? 'UTC 秒' : 'UTC seconds'}`);
}
function boundary(value, exact) {
  return localized(lang => `${inLanguage(time(value), lang)} · ${exact ? (lang === 'zh' ? '该秒可办理' : 'inclusive of this second') : (lang === 'zh' ? '办理时不含该秒' : 'exclusive of this second')}`);
}

let config, controller, account, workspace, operation, rendered, currentPreview, noticeTrigger;
let connectionGeneration = 0, draftGeneration = 0, noticeGeneration = 0, readGeneration = 0;
let caseGeneration = 0;
let submitting = false;
const pendingTransactionChecks = new Set();
const confirmedTransactionReceipts = new Map();
const provider = () => window.ethereum;
const context = () => account && config ? { appId: config.appId, workflowKey: config.workflowKey,
  chainId: config.requestScope.chainId, genesisHash: config.requestScope.genesisHash, account } : undefined;

async function request(path, body, headers = {}, signal) {
  const response = await fetch(path, { method: body === undefined ? 'GET' : 'POST', credentials: 'same-origin',
    cache: 'no-store', redirect: 'error', signal,
    headers: body === undefined ? headers : { ...headers, 'content-type': 'application/json' },
    body: body === undefined ? undefined : JSON.stringify(body) });
  const data = await response.json();
  if (!response.ok) throw Object.assign(new Error('Spark request failed'), { code: data.error });
  return data;
}

function node(tag, text, className) {
  const item = document.createElement(tag);
  if (text != null) setText(item, text);
  if (className) item.className = className;
  return item;
}
function button(label, onClick, marker, value = '') {
  const item = node('button', label);
  item.type = 'button';
  if (marker) item.dataset[marker] = value;
  item.addEventListener('click', onClick);
  return item;
}
function facts(rows) {
  const list = node('dl', null, 'details-list');
  for (const [name, value] of rows) list.append(node('dt', name), node('dd', value ?? '—'));
  return list;
}
function details(label, content, open = false) {
  const result = node('details');
  result.append(node('summary', label));
  if (typeof content !== 'function') result.append(content);
  else if (open) result.append(content());
  else result.addEventListener('toggle', function showContent() {
    if (!result.open) return;
    result.append(content());
    result.removeEventListener('toggle', showContent);
  });
  result.open = open;
  return result;
}
function reference(label, value) {
  const reference = details(localized(lang => `${inLanguage(label, lang)} ${value.slice(0, 8)}…${value.slice(-6)}`), node('p', value, 'identifier'));
  reference.className = 'compact-reference';
  return reference;
}
function paymentTitle(item) {
  return item.terms.originalDebitAccount === empty ? b('代币付款', 'Token payment') : b('退回课程余额', 'Refund to course balance');
}
function status(text, error = false) {
  el('operation-result').hidden = true;
  const line = el('message');
  setText(line, text);
  setText(el('announcement'), text);
  line.hidden = !text;
  line.classList.toggle('error', error);
}
function failure(error) {
  return errorLabel[error?.code] ?? (error?.code === 4001 ? b('钱包已拒绝此请求。', 'The wallet rejected this request.') : b('暂时无法核验，请刷新记录后重试。', 'Unable to verify right now. Refresh the records and try again.'));
}

function clearNotice() {
  noticeGeneration++;
  noticeTrigger = undefined;
  setText(el('notice-status'), '');
  el('notice-content').replaceChildren();
  el('notices').hidden = true;
}
function clearCases() {
  caseGeneration++;
  el('case-records').replaceChildren();
  setText(el('case-status'), '');
  el('case-status').classList.remove('sr-only', 'error');
  el('case-intro').hidden = false;
  const trigger = el('load-cases');
  trigger.removeAttribute('aria-disabled');
  setText(trigger, b('用钱包授权查看', 'Unlock cases with wallet'));
}
function clearPreview() {
  draftGeneration++;
  currentPreview = undefined;
  controller?.contextChanged();
  el('preview-content').replaceChildren();
  el('preview-content').hidden = true;
  el('edit-operation').hidden = true;
  el('submit').hidden = true;
}
function clearOperation() {
  clearPreview();
  operation = undefined;
  rendered = undefined;
  const message = el('message');
  if (message.parentElement === el('operation')) el('workspace-content').before(message);
  el('operation-result').hidden = true;
  el('operation-context').replaceChildren();
  el('operation-fields').replaceChildren();
  el('operation').hidden = true;
  el('course-quote').hidden = true;
  el('quote-result').replaceChildren();
  el('quote-result').hidden = true;
}
async function checkWallet(actor, turn, point = config.checkpoint) {
  const wallet = provider();
  const [accounts, chainId, genesis, block] = await Promise.all([
    wallet.request({ method: 'eth_accounts' }),
    wallet.request({ method: 'eth_chainId' }),
    wallet.request({ method: 'eth_getBlockByNumber', params: ['0x0', false] }),
    wallet.request({ method: 'eth_getBlockByNumber', params: [`0x${BigInt(point.blockNumber).toString(16)}`, false] }),
  ]);
  if (turn !== connectionGeneration || !Array.isArray(accounts) || !same(accounts[0], actor)
    || Number(chainId) !== config.requestScope.chainId || !same(genesis?.hash, config.requestScope.genesisHash)
    || !same(block?.hash, point.blockHash)) throw Object.assign(new Error('Wallet context changed'), { code: 'wallet_mismatch' });
}
async function connect(prompt) {
  if (!config) return;
  const turn = ++connectionGeneration;
  account = undefined;
  workspace = undefined;
  el('payment-actions-only').checked = false;
  el('workspace-content').hidden = true;
  el('refresh').hidden = true;
  el('access-hint').hidden = false;
  setText(el('access-hint'), walletHint);
  clearOperation();
  clearNotice();
  clearCases();
  pendingTransactionChecks.clear();
  confirmedTransactionReceipts.clear();
  el('case-jump').hidden = el('case-inbox').hidden = true;
  el('connect').disabled = true;
  el('refresh').disabled = true;
  setText(el('connect'), b('连接钱包', 'Connect wallet'));
  setText(el('wallet-role'), '');
  setText(el('wallet-account'), b('正在核对钱包', 'Checking wallet'));
  renderWorkspace();
  renderTransactions();
  status('');
  try {
    if (!provider()) {
      setText(el('wallet-account'), b('未检测到浏览器钱包', 'No browser wallet detected'));
      setText(el('access-hint'), b('请在支持钱包的浏览器中打开本页，然后重试。', 'Open this page in a browser with a wallet, then try again.'));
      return;
    }
    const accounts = await provider().request({ method: prompt ? 'eth_requestAccounts' : 'eth_accounts' });
    if (turn !== connectionGeneration) return;
    const actor = Array.isArray(accounts) ? accounts[0] : undefined;
    if (!address.test(actor ?? '')) {
      setText(el('wallet-account'), b('钱包未连接', 'Wallet not connected'));
      return;
    }
    await checkWallet(actor, turn);
    if (turn !== connectionGeneration) return;
    account = actor;
    setText(el('wallet-account'), account);
    setText(el('connect'), b('核对钱包', 'Check wallet'));
    el('access-hint').hidden = true;
    el('refresh').hidden = false;
    el('workspace-content').hidden = false;
    el('case-jump').hidden = el('case-inbox').hidden = !config.cases;
    await refresh();
  } catch (error) {
    if (turn !== connectionGeneration) return;
    setText(el('wallet-account'), error?.code === 4001 ? b('已取消钱包连接', 'Wallet connection cancelled')
      : errorLabel[error?.code] ?? b('钱包连接不可用', 'Wallet connection unavailable'));
    if (error?.code === 'wallet_mismatch') {
      const chainId = config.requestScope.chainId;
      setText(el('access-hint'), b(`请在钱包中选择此工作台使用的网络（链 ID ${chainId}），再核对钱包。`, `Select this workspace’s network in your wallet (chain ID ${chainId}), then check your wallet again.`));
    }
  } finally {
    if (turn === connectionGeneration) {
      el('connect').disabled = false;
      el('refresh').disabled = !account;
      renderTransactions();
    }
  }
}
async function refresh() {
  if (!account) return;
  const turn = connectionGeneration, read = ++readGeneration, actor = account;
  clearOperation();
  el('refresh').disabled = true;
  setText(el('reading'), b('正在读取链上记录…', 'Loading blockchain records…'));
  if (!workspace) el('obligations').replaceChildren();
  try {
    const result = await request(`/api/workspace?${new URLSearchParams({ account: actor })}`);
    if (turn !== connectionGeneration || read !== readGeneration) return;
    workspace = result;
    const roles = new Set([...result.activeRoles, ...result.obligations.flatMap(item => item.role), ...result.courses?.roles ?? []]);
    setText(el('wallet-role'), roles.size ? localized(lang => [...roles].map(role => inLanguage(roleLabel[role] ?? role, lang)).join(' · ')) : b('此钱包没有登记角色', 'No Spark DAO roles for this wallet'));
    renderWorkspace();
  } catch (error) {
    if (turn === connectionGeneration && read === readGeneration) {
      workspace = undefined;
      renderWorkspace();
      status(failure(error), true);
    }
  } finally {
    if (turn === connectionGeneration && read === readGeneration) el('refresh').disabled = !account;
  }
}

function approvals(record) {
  const list = node('div');
  for (const approval of record.approvals) {
    const row = node('div', null, 'history-item');
    row.append(node('h4', b(`批准请求 ${approval.requestId}`, `Approval request ${approval.requestId}`)), facts([
      [b('批准人', 'Approver'), approval.approver], [b('指定执行人', 'Designated executor'), approval.terms.executor], [b('最多可付（最小单位）', 'Maximum approved amount (base units)'), approval.terms.ceiling],
      [b('生效', 'Effective from'), time(approval.grantedAt)], [b('有效至', 'Valid through'), time(approval.terms.validThrough)],
      [b('停止于', 'Stopped at'), time(approval.stoppedAt)], [b('交易', 'Transaction'), approval.occurrence.hash],
    ]));
    list.append(row);
  }
  return list;
}
function holds(record) {
  const list = node('div');
  for (const hold of [...record.formalHolds, ...record.temporaryHolds]) {
    const row = node('div', null, 'history-item');
    row.dataset.hold = hold.id;
    const formal = 'liftedAt' in hold, active = formal ? hold.liftedAt === '0' : hold.active;
    const title = formal ? (active ? b('正式暂缓中', 'Formal hold active') : b('正式暂缓已解除', 'Formal hold lifted'))
      : (active ? b('临时暂缓中', 'Temporary hold active') : hold.replacedBy === empty ? b('临时暂缓已到期', 'Temporary hold expired') : b('临时暂缓已替换', 'Temporary hold replaced'));
    const until = localized(lang => formal && !active ? `${lang === 'zh' ? '解除于' : 'Lifted at'} ${inLanguage(time(hold.liftedAt), lang)}`
      : `${formal ? (lang === 'zh' ? '复核' : 'Review') : (lang === 'zh' ? '临时暂缓到期' : 'Temporary hold expires')} ${inLanguage(time(formal ? hold.terms.reviewAt : hold.terms.expiresAt), lang)}`);
    row.append(node('h4', title), node('p', localized(lang => `${lang === 'zh' ? '范围' : 'Scope'} ${hold.amount} ${lang === 'zh' ? '最小单位' : 'base units'} · ${inLanguage(until, lang)}`), 'card-label'));
    const offer = record.offers.find(offer => offer.operationId === 'liftFormalHold' && same(offer.input.holdId, hold.id));
    const actions = node('div', null, 'action-row');
    if (offer) actions.append(actionButton(record, offer));
    actions.append(button(b('用钱包查看私密通知', 'Open private notice with wallet'), event => readNotice(record, hold, event.currentTarget), 'notice'));
    row.append(actions, details(b('案件与证据', 'Case and evidence'), facts([
      [b('案件标识', 'Case ID'), hold.terms.caseId], [b('设定时间', 'Imposed at'), time(hold.imposedAt)],
      [b('已核实的证据编号', 'Verified evidence ID'), hold.evidenceId], [privateNoticeHashLabel, hold.terms.noticeHash],
      [b('暂缓交易', 'Transaction placing the hold'), hold.occurrence.hash], ...(hold.lift ? [[b('解除交易', 'Lift transaction'), hold.lift.hash]] : []),
    ])));
    list.append(row);
  }
  return list;
}
function receipts(record) {
  const list = node('div');
  for (const receipt of record.receipts) {
    const row = node('div', null, 'history-item');
    row.append(node('h5', b(`收据 ${receipt.id} · ${receipt.amount} 最小单位`, `Receipt ${receipt.id} · ${receipt.amount} base units`)), facts([
      [b('支付时间', 'Paid at'), time(receipt.paidAt)], [b('批准请求编号', 'Approval request ID'), receipt.approvalRequestId],
      ...(receipt.promptCutoff === '0' ? [] : [[b('解除暂缓后及时付款的时限', 'Timely payment cutoff after release'), time(receipt.promptCutoff)],
        [b('这次付款在期限内到账', 'This payment arrived by the deadline'), receipt.promptCutoffMet ? b('是', 'Yes') : b('否', 'No')]]),
      [b('实际执行者', 'Actual executor'), receipt.executor], [receipt.creditAccount === empty ? b('收款地址', 'Recipient address') : b('退回到原课程余额账户', 'Refunded to the original course balance account'),
        receipt.creditAccount === empty ? receipt.recipient : receipt.creditAccount],
      [b('链上交易', 'On-chain transaction'), receipt.occurrence.hash], [b('区块 / 日志', 'Block / log'), `${receipt.occurrence.blockNumber} / ${receipt.occurrence.logIndex}`],
    ]));
    list.append(row);
  }
  return list;
}
function obligationCard(record) {
  const { obligation: item, id, outstanding, held } = record;
  const card = node('article', null, 'obligation');
  card.dataset.obligation = id;
  card.toggleAttribute('data-action-available', record.offers.length > 0);
  const isPaid = outstanding === '0' && item.paid !== '0';
  const state = outstanding === '0' ? (isPaid ? 'paid' : 'closed') : (held ? 'held' : 'due');
  card.dataset.state = state;
  const header = node('div', null, 'obligation-heading');
  const title = node('div');
  title.append(node('h4', paymentTitle(item), 'payment-title'));
  if (record.role.length) title.append(node('p', localized(lang => record.role.map(role => inLanguage(roleLabel[role] ?? role, lang)).join(' · ')), 'card-label'));
  header.append(title, node('span', { held: b('暂缓中', 'On hold'), paid: b('已付清', 'Paid in full'), closed: b('无待付金额', 'No amount due'), due: b('还有款项待付', 'Payment outstanding') }[state], `state ${state}`));
  card.append(header, reference(b('款项标识', 'Payment ID'), id));
  const summary = node('dl', null, 'summary-grid');
  const balances = isPaid ? [[b('实际到账', 'Net received'), item.paid], [b('还需支付', 'Still to pay'), outstanding]] : [[b('还需支付', 'Still to pay'), outstanding], [b('实际到账', 'Net received'), item.paid]];
  for (const [label, amount] of [...balances, [b('本笔款项金额', 'Payment total'), item.correctAmount]]) {
    const cell = node('div');
    const value = node('dd', `${amount} `);
    value.append(node('span', b('最小单位', 'base units'), 'money-unit'));
    cell.append(node('dt', label), value);
    summary.append(cell);
  }
  const context = node('div', null, 'payment-context');
  const latestReceipt = record.receipts.at(-1);
  const available = record.offers.find(offer => offer.operationId === 'pay');
  if (isPaid && latestReceipt) context.append(node('p', localized(lang => `${lang === 'zh' ? '最近到账' : 'Last received'} ${inLanguage(time(latestReceipt.paidAt), lang)}`), 'context-item'));
  else if (state === 'held') context.append(node('p', b('暂缓仅限此笔款项。', 'The hold applies only to this payment.'), 'context-item'));
  else if (state === 'due' && item.firstFullReleaseAt !== '0' && item.postLiftCutoff !== '0') {
    context.append(node('p', localized(lang => `${lang === 'zh' ? '解除暂缓后最晚付款时间' : 'Payment deadline after release'} ${inLanguage(boundary(item.postLiftCutoff, item.terms.postLiftDeadlineExact || item.postLiftClockEvidenceId !== '0'), lang)}`), 'context-item'));
  } else if (state === 'due') context.append(node('p', localized(lang => `${lang === 'zh' ? '到期' : 'Due'} ${inLanguage(time(item.terms.dueAt), lang)}`), 'context-item'));
  if (available) context.append(node('p', b('当前钱包可办理付款', 'This wallet can make the payment'), 'context-item'));
  card.append(summary);
  if (context.childElementCount) card.append(context);
  const deadline = () => facts([[b('款项到期', 'Payment due'), boundary(item.terms.dueAt, item.terms.dueAtExact)],
    ...(item.eligibleFrom !== item.terms.dueAt || item.eligibilityExact !== item.terms.dueAtExact
      ? [[b('最早可付款时间', 'Earliest payment time'), boundary(item.eligibleFrom, item.eligibilityExact)]] : []),
    [b('原付款截止时间', 'Original payment deadline'), boundary(item.terms.executionDeadline, item.terms.executionDeadlineExact)],
    ...(item.terms.legalDeadline !== '0' ? [[b('法定提前期限', 'Statutory early deadline'), boundary(item.terms.legalDeadline, item.terms.legalDeadlineExact)]] : []),
    ...(item.firstFullReleaseAt !== '0' ? [[b('第一次解除全部暂缓', 'First release of all holds'), time(item.firstFullReleaseAt)],
      [b('解除暂缓后最晚付款时间', 'Payment deadline after release'), boundary(item.postLiftCutoff, item.terms.postLiftDeadlineExact || item.postLiftClockEvidenceId !== '0')]] : []),
    [b('适用规则编号', 'Rules used'), item.packageId], [b('当前收款地址', 'Current recipient address'), item.destination], [b('为这笔付款预留的资金（最小单位）', 'Funds set aside for this payment (base units)'), record.reserved],
    ...(item.correctAmount !== item.terms.amount || !same(item.destination, item.terms.recipient)
      ? [[b('原定款项金额（最小单位）', 'Original payment amount (base units)'), item.terms.amount], [b('原收款地址', 'Original recipient address'), item.terms.recipient]] : []),
    ...(record.creditBalance === undefined ? [[b('代币合约', 'Token contract'), config.token]] : [
      [b('原课程余额账户', 'Original course balance account'), item.terms.originalDebitAccount], [b('该账户当前余额（最小单位）', 'Current account balance (base units)'), record.creditBalance],
    ])]);
  const actions = node('div', null, 'action-row');
  if (available) actions.append(actionButton(record, available));
  for (const offer of record.offers) {
    if (offer !== available && offer.operationId !== 'liftFormalHold') actions.append(actionButton(record, offer));
  }
  if (actions.childElementCount) card.append(actions);
  const history = node('div', null, 'payment-history');
  if (record.receipts.length) history.append(details(b(`链上收据 · ${record.receipts.length}`, `On-chain receipts · ${record.receipts.length}`), () => receipts(record)));
  const holdCount = record.formalHolds.length + record.temporaryHolds.length;
  if (holdCount) {
    const canLift = record.offers.some(offer => offer.operationId === 'liftFormalHold');
    const holdsHistory = details(b(`暂缓与解除 · ${holdCount}`, `Holds and releases · ${holdCount}`),
      () => holds(record), held || canLift || record.role.includes('recipient'));
    history.append(holdsHistory);
  }
  const paymentDetails = () => {
    const basis = node('div');
    if (record.approvals.length) basis.append(details(b(`批准记录 · ${record.approvals.length}`, `Approvals · ${record.approvals.length}`), () => approvals(record)));
    basis.append(details(b('期限、规则与收款方', 'Deadlines, rules and recipient'), deadline));
    if (record.timeline.length) {
      basis.append(details(b('后续变更', 'Later changes'), () => {
        const trail = node('div');
        for (const event of record.timeline) {
          const name = { ReplacementArranged: b('替换安排', 'Replacement arrangement'), PaymentApprovalStopped: b('已撤销付款批准', 'Payment approval revoked'),
            PostLiftClockVerified: b('解除暂缓后的付款期限已核实', 'Post-lift deadline verified'), PaymentReturned: b('款项退回', 'Payment returned'), PaymentRevised: b('采纳的款项更正', 'Adopted payment correction') }[event.name];
          trail.append(node('h4', name), facts([
            ...(event.name === 'PaymentReturned' ? [[b('原收讫编号', 'Original receipt ID'), event.args.receiptId], [b('退回金额（最小单位）', 'Returned amount (base units)'), event.args.amount]] : []),
            ...(event.name === 'PaymentRevised' ? [[b('更正后金额（最小单位）', 'Corrected amount (base units)'), event.args.amount], [b('采纳的决定', 'Adopted decision'), event.args.decisionRef]] : []),
            [b('链上交易', 'On-chain transaction'), event.hash], [b('区块 / 日志', 'Block / log'), `${event.blockNumber} / ${event.logIndex}`], [b('发出事件的合约', 'Emitting contract'), event.emitter],
          ]));
        }
        return trail;
      }));
    }
    return basis;
  };
  history.append(details(b('款项详情', 'Payment details'), paymentDetails));
  card.append(history);
  return card;
}
function applyPaymentFilter() {
  if (el('payment-filter').hidden) return;
  const actionsOnly = el('payment-actions-only').checked;
  let shown = 0, total = 0;
  for (const group of el('obligations').children) {
    const cards = group.querySelector('.payment-items').children;
    let visible = 0;
    for (const card of cards) {
      card.hidden = actionsOnly && !card.hasAttribute('data-action-available');
      if (!card.hidden) visible++;
    }
    group.hidden = visible === 0;
    setText(group.querySelector('.payment-count'), b(`${visible} 笔款项`, `${visible} ${visible === 1 ? 'payment' : 'payments'}`));
    shown += visible;
    total += cards.length;
  }
  setText(el('payment-filter-status'), b(`显示 ${shown} / ${total} 笔`, `Showing ${shown} of ${total}`));
  el('payment-filter-empty').hidden = shown > 0;
}
function renderWorkspace() {
  const host = el('obligations');
  host.replaceChildren();
  el('payment-filter').hidden = !workspace?.obligations.length;
  el('payment-filter-empty').hidden = true;
  if (el('payment-filter').hidden) setText(el('payment-filter-status'), '');
  const courseRecords = el('courses');
  courseView.render(courseRecords, workspace?.courses);
  el('course-jump').hidden = el('course-workspace').hidden = !courseRecords.childElementCount;
  setText(el('reading'), workspace ? localized(lang => `${lang === 'zh' ? '链上区块' : 'On-chain block'} ${workspace.asOf.blockNumber} · ${inLanguage(time(workspace.asOf.timestamp), lang)}`) : '');
  if (!workspace) {
    host.append(node('p', account ? b('款项记录未能载入，请刷新链上记录。', 'Payments could not load. Refresh blockchain records.') : b('连接钱包后查看相应款项与待办。', 'Connect a wallet to view its payments and actions.'), 'empty'));
    return;
  }
  if (!workspace.obligations.length) {
    host.append(node('p', b('当前钱包没有相关款项。', 'There are no payments related to this wallet.'), 'empty'));
    return;
  }
  const courses = new Map();
  for (const record of workspace.obligations) {
    const lessonId = record.obligation.terms.lessonId;
    if (!courses.has(lessonId)) courses.set(lessonId, []);
    courses.get(lessonId).push(record);
  }
  const lessons = new Map(workspace.courses?.lessons.map(lesson => [lesson.lessonId, lesson]));
  const paymentPriority = record => record.held && record.outstanding !== '0' ? 0
    : record.offers.some(offer => offer.operationId === 'pay') ? 1
      : record.approvals.length || record.receipts.length ? 2 : 3;
  for (const [lessonId, records] of courses) {
    const course = node('section', null, 'course');
    const header = node('header', null, 'course-header');
    const title = node('div');
    const lesson = lessons.get(lessonId);
    title.append(node('h3', lesson ? localized(lang => `${lang === 'zh' ? '计划开课' : 'Scheduled start'} ${inLanguage(time(lesson.startsAt), lang)}`) : b('课次', 'Class')), reference(b('课次标识', 'Lesson ID'), lessonId));
    header.append(title, node('span', null, 'payment-count'));
    const items = node('div', null, 'payment-items');
    items.append(...records.sort((a, b) => paymentPriority(a) - paymentPriority(b)).map(obligationCard));
    course.append(header, items);
    host.append(course);
  }
  applyPaymentFilter();
}

function actionButton(record, offer) {
  const item = button(operationLabel[offer.operationId], () => selectOperation(record, offer, item), 'operation', offer.operationId);
  if (offer.operationId === 'pay' || offer.operationId === 'liftFormalHold') item.classList.add('primary');
  return item;
}
function focusOperationField() {
  (el('operation-fields').querySelector('input, textarea') ?? el('preview')).focus();
}
function showOperation(title, summary = '', references = []) {
  setText(el('operation-title'), title);
  const description = el('operation-context');
  description.replaceChildren(node('p', summary, 'card-label'), ...references);
  description.hidden = !summary;
  el('operation-form').before(el('message'));
  el('operation').hidden = false;
  el('operation').scrollIntoView({ block: 'start' });
  focusOperationField();
}
function selectOperation(record, offer, trigger) {
  if (submitting) return;
  clearOperation();
  status('');
  operation = { record, offer, trigger };
  rendered = renderOperationFields(el('operation-fields'), operationFields[offer.operationId], offer.input);
  const { obligation: item } = record;
  const references = [reference(b('款项标识', 'Payment ID'), record.id), reference(b('课次标识', 'Lesson ID'), item.terms.lessonId)];
  if (offer.operationId === 'pay') {
    const refundAccount = item.terms.originalDebitAccount;
    references.push(refundAccount === empty ? reference(b('当前收款地址', 'Current recipient address'), item.destination)
      : reference(b('退款去向（原课程余额账户）', 'Refund destination (original course balance account)'), refundAccount));
  }
  showOperation(operationLabel[offer.operationId], localized(lang => `${inLanguage(paymentTitle(item), lang)} · ${lang === 'zh' ? '待付' : 'Due'} ${record.outstanding} ${lang === 'zh' ? '最小单位' : 'base units'}`), references);
}
const settlementQuoteOps = new Set(['approveOrdinaryGroup', 'approveProviderStartedEarly']);
function selectCourse(offer, trigger, { lessonId, formId, caseId } = {}) {
  if (submitting) return;
  clearOperation();
  status('');
  operation = { course: offer, trigger };
  rendered = renderOperationFields(el('operation-fields'), offer.fields.map(field => ({
    ...field,
    label: courseFieldLabel(field.name, field.label),
    utc: isCourseTimeField(offer.operationId, field.name),
  })));
  el('course-quote').hidden = !settlementQuoteOps.has(offer.operationId);
  if (offer.operationId === 'proposeProviderStartedEarly' || offer.operationId === 'approveProviderStartedEarly') {
    el('operation-fields').prepend(node('p', b(
      '分别填写两项已核实金额。结算记录须引用本名额及其依据，可省略结算路径、名额处理类型和 verificationRef，由工作台按本次办理填入。',
      'Enter the two independently verified amounts. The settlement record must refer to this seat and its evidence. You can omit the route, seat disposition and verificationRef; the workbench fills them in.'
    ), 'muted'));
  }
  const references = [[b('课次', 'Lesson'), lessonId], [b('名额确认单', 'Booking confirmation'), formId], [b('案件', 'Case'), caseId]];
  const summary = localized(lang => references.filter(([, id]) => id).map(([label, id]) => `${inLanguage(label, lang)} ${id}`).join(' · '));
  showOperation(courseActionLabel(offer.operationId, offer.label), summary);
}
function transactionDraft(only) {
  const common = { installation: config.requestScope.installationHash, requestedAt: Math.floor(Date.now() / 1000) };
  const actor = { appId: config.appId, workflowKey: config.workflowKey, account };
  if (operation.course) return { ...actor, operationId: operation.course.operationId,
    input: { ...common, arguments: { ...operation.course.arguments, ...rendered.read(only) } } };
  const { record, offer } = operation;
  return { ...actor, operationId: offer.operationId,
    input: { ...offer.input, ...rendered.read(), obligationId: record.id, expectedVersion: record.obligation.version, ...common } };
}
function previewContent(preview) {
  if (preview.courseOperation) {
    const { operationId } = operation.course;
    const fieldLabels = Object.fromEntries(operation.course.fields.map(field => [field.name, field.label]));
    const rows = [], complex = [], unknown = {};
    for (const [name, value] of Object.entries(preview.input.arguments)) {
      const fallback = fieldLabels[name] !== name ? fieldLabels[name] : undefined;
      const label = courseFieldLabel(name, fallback);
      if (!label) unknown[name] = value;
      else if (value !== null && typeof value === 'object') complex.push(details(label, () => node('pre', JSON.stringify(value, null, 2))));
      else rows.push([label, isCourseTimeField(operationId, name) ? previewTime(value) : courseArgumentValue(operationId, name, value)]);
    }
    if (Object.keys(unknown).length) complex.push(details(b('其他交易参数', 'Other transaction arguments'), () => node('pre', JSON.stringify(unknown, null, 2))));
    el('preview-content').replaceChildren(node('h3', courseActionLabel(operation.course.operationId, operation.course.label)), facts([
      [b('当前钱包', 'Current wallet'), preview.account], [b('适用规则编号', 'Rules used'), preview.input.packageId], ...rows,
      [b('预览有效至', 'Preview expires'), time(preview.expiresAt)], [b('目标合约', 'Target contract'), preview.call.to],
    ]), ...complex, details(b('交易数据（供核对）', 'Transaction data for verification'), node('p', preview.call.data, 'identifier')));
    el('preview-content').hidden = false;
    return;
  }
  const info = preview.payment, input = preview.input;
  const command = Object.entries(input).filter(([name]) => labels[name]).map(([name, value]) => [labels[name],
    operationFields[preview.operationId].some(field => field.name === name && field.utc) ? previewTime(value) : value]);
  const target = info.creditAccount === empty ? info.recipient : info.creditAccount;
  const list = [...command, [b('待付金额（最小单位）', 'Amount due (base units)'), info.outstanding],
    [info.creditAccount === empty ? b('收款地址', 'Recipient address') : b('退款去向（原课程余额账户）', 'Refund destination (original course balance account)'), target],
    [b('当前钱包', 'Current wallet'), preview.account], [b('预览有效至', 'Preview expires'), time(preview.expiresAt)],
    [b('课次', 'Class'), info.lessonId], [b('款项', 'Payment'), input.obligationId], [b('适用规则编号', 'Rules used'), input.packageId],
    [b('结算币种合约', 'Settlement token contract'), config.token], [b('目标合约', 'Target contract'), preview.call.to]];
  el('preview-content').replaceChildren(node('h3', operationLabel[preview.operationId]), facts(list),
    details(b('交易数据（供核对）', 'Transaction data for verification'), node('p', preview.call.data, 'identifier')));
  el('preview-content').hidden = false;
}
async function prepare(event) {
  event.preventDefault();
  if (!operation || !account || submitting) return;
  operation.submitted = false;
  const focusBefore = document.activeElement;
  const wasInForm = el('operation-form').contains(focusBefore);
  clearPreview();
  const turn = draftGeneration;
  el('preview').disabled = true;
  try {
    const preview = await controller.prepare(transactionDraft());
    if (turn !== draftGeneration) return;
    currentPreview = preview;
    previewContent(preview);
    el('edit-operation').hidden = false;
    el('submit').hidden = false;
    status(b('请核对本次操作，再请求钱包确认。', 'Review this operation before requesting wallet confirmation.'));
    if (wasInForm && (document.activeElement === focusBefore || document.activeElement === document.body)) el('preview-content').focus();
  } catch (error) {
    if (turn === draftGeneration) status(error instanceof RecordInputError ? b('请根据出错字段下方的提示修改记录。', 'Correct the record using the guidance under the field.') : failure(error), true);
  } finally {
    el('preview').disabled = false;
  }
}
async function showSettlementQuote() {
  const operationId = operation?.course?.operationId;
  if (!settlementQuoteOps.has(operationId)) return;
  const turn = draftGeneration;
  const target = el('quote-result');
  try {
    const quote = await request('/api/course/quote', transactionDraft(operationId === 'approveProviderStartedEarly'
      ? ['assessment', 'serviceValue', 'tutorAmount'] : ['assessment']));
    if (turn !== draftGeneration) return;
    target.replaceChildren(node('h3', b('每个名额的结算预览', 'Settlement preview by seat')), facts([
      ...(quote.originalPayer ? [[courseFieldLabel('originalPayer'), quote.originalPayer]] : []),
      ...(quote.originalDebitAccount ? [[courseFieldLabel('originalDebitAccount'), quote.originalDebitAccount]] : []),
      ...(quote.debitedUnits === undefined ? [] : [[courseFieldLabel('debitedUnits'), quote.debitedUnits],
        [courseFieldLabel('refundDue'), quote.refundDue]]),
      [b('出勤确认数', 'Attendance confirmations'), quote.attendanceConfirmations],
      [quote.debitedUnits === undefined ? b('课酬合计（最小单位）', 'Total tutor pay (base units)') : courseFieldLabel('tutorAmount'), quote.totalTutorPay],
      [b('结算记录校验值', 'Settlement verification hash'), quote.basis],
      ...quote.payments.map(payment => [payment.originalDebitAccount === empty ? b('代币付款', 'Token payment') : b('退回课程余额', 'Refund to course balance'),
        `${payment.amount} → ${payment.originalDebitAccount === empty ? payment.recipient : payment.originalDebitAccount}`]),
    ]));
    target.hidden = false;
  } catch (error) {
    if (turn === draftGeneration) status(error instanceof RecordInputError ? b('请根据结算记录下方的提示修改。', 'Correct the settlement record using the guidance under its field.') : failure(error), true);
  }
}
async function submit() {
  if (!currentPreview || submitting) return;
  const turn = draftGeneration;
  const focusResult = document.activeElement === el('submit');
  submitting = true;
  el('edit-operation').disabled = true;
  el('submit').disabled = true;
  status(b('正在重新核对这项操作，然后打开钱包确认。', 'Checking this action again before opening your wallet.'));
  try {
    if (Math.floor(Date.now() / 1000) >= currentPreview.expiresAt) throw Object.assign(new Error(), { code: 'preview_expired' });
    const record = await controller.submit();
    if (turn !== draftGeneration) return;
    status(record.hash ? b('钱包已返回交易哈希。点「核对交易结果」查看是否上链。', 'Your wallet returned a transaction hash. Check the transaction result to see whether it is on-chain.')
      : record.status === 'rejected' ? b('钱包已拒绝本次交易。', 'The wallet rejected this transaction.') : b('提交结果待核验，请使用钱包提供的原交易哈希。', 'Submission is awaiting verification. Use the original transaction hash from your wallet.'));
    if (record.status !== 'rejected') {
      operation.submitted = true;
      const result = el('operation-result');
      result.dataset.transactionId = record.locator.localId;
      result.hidden = false;
    }
  } catch (error) {
    if (turn === draftGeneration) status(failure(error), true);
  } finally {
    submitting = false;
    el('edit-operation').disabled = false;
    el('submit').disabled = false;
    if (turn === draftGeneration) {
      clearPreview();
      const result = el('operation-result');
      if (focusResult && !result.hidden && document.activeElement === document.body) result.focus();
    }
  }
}

async function observe(record, candidate) {
  const id = record.locator.localId;
  if (pendingTransactionChecks.has(id)) return;
  const turn = connectionGeneration;
  pendingTransactionChecks.add(id);
  confirmedTransactionReceipts.delete(id);
  renderTransactions();
  let transactionFeedback;
  try {
    const result = candidate ? await controller.recover(record, candidate) : await controller.observe(record);
    if (turn !== connectionGeneration) return;
    if (result.status === 'confirmed') {
      const event = result.observation?.events?.[0];
      if (event) confirmedTransactionReceipts.set(id, event);
      const payment = result.locator.operationId === 'pay'
        ? workspace?.obligations.find(item => same(item.id, result.locator.input.obligationId)) : undefined;
      const alreadyShown = event && payment?.receipts.some(({ occurrence }) =>
        same(occurrence.hash, event.transactionHash) && same(occurrence.blockHash, event.blockHash));
      if (!alreadyShown && operation && !operation.submitted) {
        transactionFeedback = b('交易已确认。完成当前表单后可刷新记录。', 'Transaction confirmed. Refresh records after finishing your current form.');
      } else if (!alreadyShown) await refresh();
    }
    if (candidate && !result.hash) transactionFeedback = result.status === 'unavailable' ? transactionLabel.unavailable
      : b('未能用这个哈希核对原交易。请检查钱包中的原交易哈希后重试。', 'This hash could not verify the original transaction. Check the original hash in your wallet and try again.');
    if (turn === connectionGeneration && !transactionFeedback) status(transactionLabel[result.status], !['confirmed', 'pending'].includes(result.status));
  } catch (error) {
    if (turn === connectionGeneration) status(failure(error), true);
  } finally {
    if (turn === connectionGeneration) {
      pendingTransactionChecks.delete(id);
      renderTransactions();
      if (transactionFeedback) {
        const row = transactionRow(id);
        const feedback = row?.querySelector('.transaction-feedback');
        if (feedback) {
          feedback.classList.toggle('error', row.dataset.status !== 'confirmed');
          setText(feedback, transactionFeedback);
        }
      }
    }
  }
}
function transactionRow(id) {
  return Array.from(el('transactions').children).find(row => row.dataset.transactionId === id);
}
function renderTransactions() {
  const target = el('transactions');
  const focused = document.activeElement;
  const focusedRow = target.contains(focused) ? focused.closest('[data-transaction-id]') : null;
  const previous = new Map(Array.from(target.children, row => [row.dataset.transactionId, row]));
  const current = context();
  const records = current && controller?.list().filter(record => same(record.locator.account, account)
    && same(record.locator.input.installation, config.requestScope.installationHash));
  if (!records?.length) {
    target.replaceChildren(node('p', current ? b('此钱包在此浏览器中还没有操作记录。', 'No activity for this wallet in this browser yet.') : b('连接钱包后查看操作记录。', 'Connect a wallet to see activity.'), 'muted'));
    return;
  }
  for (const [index, record] of records.reverse().entries()) {
    const id = record.locator.localId;
    const checking = pendingTransactionChecks.has(id);
    const event = confirmedTransactionReceipts.get(id);
    const presentation = [record.status, record.hash, checking, event?.blockHash, event?.logIndex].join('|');
    const oldRow = previous.get(id);
    if (oldRow?.dataset.presentation === presentation) {
      if (target.children[index] !== oldRow) target.insertBefore(oldRow, target.children[index] ?? null);
      if (focusedRow === oldRow && document.activeElement !== focused) focused.focus({ preventScroll: true });
      continue;
    }
    const row = node('div', null, 'transaction');
    row.tabIndex = -1;
    row.dataset.presentation = presentation;
    row.dataset.transactionId = id;
    row.dataset.transaction = record.hash ?? record.locator.localId;
    row.dataset.status = record.status;
    row.append(node('h3', operationLabel[record.locator.operationId] ?? courseActionLabel(record.locator.operationId, record.locator.input.label)));
    row.append(node('p', checking ? b('正在核对交易…', 'Checking transaction…') : transactionLabel[record.status], 'transaction-status'));
    const { obligationId, arguments: args } = record.locator.input;
    const subject = [[b('款项标识', 'Payment ID'), obligationId], [b('案件标识', 'Case ID'), args?.caseId],
      [b('确认单标识', 'Confirmation form ID'), args?.formId], [b('课次标识', 'Lesson ID'), args?.lessonId]].find(([, value]) => hash.test(value ?? ''));
    if (subject) row.append(reference(...subject));
    const feedback = node('p', null, 'transaction-feedback');
    feedback.id = `transaction-feedback-${id}`;
    feedback.setAttribute('role', 'status');
    if (record.hash) {
      const check = button(b('核对交易结果', 'Check transaction result'), () => observe(record), 'observe');
      check.dataset.transactionControl = 'check';
      if (checking) check.setAttribute('aria-disabled', 'true');
      row.append(check, reference(b('交易哈希', 'Transaction hash'), record.hash));
    } else if (record.status !== 'rejected') {
      const label = node('label', null, 'muted');
      label.append(node('span', b('钱包显示的原交易哈希', 'Original transaction hash from your wallet')));
      const input = node('input');
      input.pattern = '0[xX][0-9a-fA-F]{64}';
      input.maxLength = 66;
      input.autocomplete = 'off';
      input.spellcheck = false;
      input.setAttribute('aria-describedby', feedback.id);
      input.dataset.transactionControl = 'hash';
      input.value = oldRow?.querySelector('input')?.value ?? '';
      label.append(input);
      const verify = button(b('用原哈希核验', 'Verify with original hash'), () => {
        if (checking) return;
        if (hash.test(input.value)) { void observe(record, input.value); return; }
        feedback.classList.add('error');
        setText(feedback, b('请输入钱包显示的完整交易哈希。', 'Enter the full transaction hash from your wallet.'));
        input.setAttribute('aria-invalid', 'true');
        input.focus();
      });
      verify.dataset.transactionControl = 'check';
      if (checking) verify.setAttribute('aria-disabled', 'true');
      input.addEventListener('input', () => { input.removeAttribute('aria-invalid'); setText(feedback, ''); });
      row.append(label, verify);
    }
    row.append(feedback);
    if (event) row.append(details(b('链上回执', 'On-chain receipt'), facts([[b('事件', 'Event'), event.eventName], [b('区块哈希', 'Block hash'), event.blockHash],
      [b('区块 / 日志', 'Block / log'), `${event.blockNumber} / ${event.logIndex}`], ...('receiptId' in event.args ? [[b('收据编号', 'Receipt ID'), event.args.receiptId]] : [])])));
    oldRow?.remove();
    target.insertBefore(row, target.children[index] ?? null);
    if (focusedRow?.dataset.transactionId === id) {
      const control = focused.dataset.transactionControl;
      (Array.from(row.querySelectorAll('[data-transaction-control]')).find(item => item.dataset.transactionControl === control) ?? row).focus({ preventScroll: true });
    }
  }
  while (target.children.length > records.length) {
    confirmedTransactionReceipts.delete(target.lastElementChild.dataset.transactionId);
    target.lastElementChild.remove();
  }
}

async function signedPrivateRead(path, input, actor, connection, live) {
  const challenge = await request('/api/private/challenge', { account: actor, input, path });
  if (!live()) return;
  await checkWallet(actor, connection);
  if (!live()) return;
  const { message, nonce, expiresAt } = challenge;
  const bytes = Array.from(new TextEncoder().encode(message), byte => byte.toString(16).padStart(2, '0'));
  const signature = await provider().request({ method: 'personal_sign', params: [`0x${bytes.join('')}`, actor] });
  await checkWallet(actor, connection);
  if (!live()) return;
  const header = btoa(JSON.stringify({ account: actor, nonce, expiresAt, signature }))
    .replaceAll('+', '-').replaceAll('/', '_').replaceAll('=', '');
  return request(path, input, { 'x-spark-auth': header });
}
async function readVaultNotice(input, trigger) {
  clearNotice();
  if (!account) return;
  const turn = noticeGeneration, connection = connectionGeneration, actor = account;
  const output = el('notice-content');
  const pending = b('正在核对钱包授权…', 'Checking wallet authorization…');
  noticeTrigger = trigger;
  setText(el('notice-status'), pending);
  el('notices').hidden = false;
  output.replaceChildren(node('p', pending));
  el('close-notice').focus({ preventScroll: true });
  el('notices').scrollIntoView({ block: 'nearest' });
  try {
    const notice = await signedPrivateRead('/api/private/notice', input, actor, connection, () => turn === noticeGeneration);
    if (turn !== noticeGeneration || !notice) return;
    output.replaceChildren(node('h3', sourceLabel[notice.source]), node('p', notice.text));
    setText(el('notice-status'), b('私密通知已打开。', 'Private notice opened.'));
  } catch (error) {
    if (turn === noticeGeneration) {
      output.replaceChildren(node('p', failure(error)));
      setText(el('notice-status'), failure(error));
    }
  }
}
function readNotice(record, hold, trigger) {
  return readVaultNotice({ obligationId: record.id, caseId: hold.terms.caseId, noticeHash: hold.terms.noticeHash }, trigger);
}
async function loadCases() {
  const trigger = el('load-cases');
  if (!account || trigger.getAttribute('aria-disabled') === 'true') return;
  const turn = ++caseGeneration, connection = connectionGeneration, actor = account;
  const target = el('case-records');
  const live = () => turn === caseGeneration && connection === connectionGeneration;
  const pending = b('正在核对钱包授权…', 'Checking wallet authorization…');
  trigger.setAttribute('aria-disabled', 'true');
  target.replaceChildren();
  el('case-intro').hidden = true;
  el('case-status').classList.remove('sr-only', 'error');
  setText(el('case-status'), pending);
  try {
    const records = await signedPrivateRead('/api/private/cases', {}, actor, connection, live);
    if (live() && records) {
      courseView.inbox(target, records);
      const count = records.records.length;
      el('case-status').classList.toggle('sr-only', count === 0);
      setText(el('case-status'), b(`已读取 ${count} 个案件。`, `${count} ${count === 1 ? 'case' : 'cases'} loaded.`));
      setText(trigger, b('重新读取案件', 'Reload cases'));
    }
  } catch (error) {
    if (live()) {
      el('case-status').classList.add('error');
      setText(el('case-status'), failure(error));
    }
  } finally {
    if (live()) trigger.removeAttribute('aria-disabled');
  }
}
const courseView = createCourseView({ node, button, facts, time, details, reference, select: selectCourse, readNotice: readVaultNotice });

el('connect').addEventListener('click', () => connect(true));
el('reload').addEventListener('click', () => location.reload());
el('refresh').addEventListener('click', () => { status(''); void refresh(); });
el('payment-actions-only').addEventListener('change', applyPaymentFilter);
el('close-operation').addEventListener('click', () => {
  if (submitting) return;
  const trigger = operation?.trigger;
  clearOperation();
  status('');
  trigger?.focus();
});
el('operation-form').addEventListener('submit', prepare);
el('operation-form').addEventListener('input', event => {
  if (!event.target.name) return;
  if (operation) operation.submitted = false;
  clearPreview();
  if (event.target.name === 'assessment') {
    el('quote-result').replaceChildren();
    el('quote-result').hidden = true;
  }
  status('');
});
el('edit-operation').addEventListener('click', () => {
  clearPreview();
  status('');
  focusOperationField();
});
el('submit').addEventListener('click', submit);
el('operation-result').addEventListener('click', event => {
  const id = event.currentTarget.dataset.transactionId;
  (transactionRow(id) ?? el('wallet-transactions')).focus();
});
el('course-quote').addEventListener('click', showSettlementQuote);
el('load-cases').addEventListener('click', loadCases);
el('close-notice').addEventListener('click', () => {
  const trigger = noticeTrigger;
  clearNotice();
  (trigger?.isConnected ? trigger : el('wallet-transactions')).focus();
});
window.addEventListener('pagehide', () => {
  clearNotice();
  clearCases();
});

el('language-control').hidden = false;
setText(el('installation'), b('正在核对 Spark DAO 服务…', 'Checking the Spark DAO service…'));
setText(el('access-hint'), b('服务就绪后即可连接钱包。', 'You can connect your wallet when the service is ready.'));
try {
  config = await request('/api/installation');
  const queue = createPublicQueue({ key: `spark-v15:operations:${config.requestScope.installationHash}` });
  controller = createWorkbenchController({
    getContext: context, getProvider: provider, queue, onRecord: renderTransactions,
    postJson: (path, body, { signal } = {}) => request(path.endsWith('/prepare') ? '/api/prepare' : '/api/observe', body, {}, signal),
    async validatePrepared(preview) {
      if (!same(preview.input.installation, config.requestScope.installationHash)
        || !config.operationTargets.some(target => same(preview.call.to, target))) {
        throw Object.assign(new Error(), { code: 'installation_mismatch' });
      }
      await checkWallet(preview.account, connectionGeneration, preview.asOf);
    },
  });
  for (const event of ['accountsChanged', 'chainChanged', 'disconnect']) provider()?.on?.(event, () => connect(false));
  setText(el('installation'), b(`Spark v1.5 · 本机链 ${config.requestScope.chainId}`, `Spark v1.5 · Local chain ${config.requestScope.chainId}`));
  setText(el('access-hint'), walletHint);
  el('wallet-status').hidden = false;
  el('connect').hidden = false;
  el('connect').disabled = false;
} catch (error) {
  setText(el('installation'), b('服务不可用', 'Service unavailable'));
  setText(el('access-hint'), b('请检查 Spark DAO 服务是否已启动，再重新加载页面。', 'Check that the Spark DAO service is running, then reload this page.'));
  el('reload').hidden = false;
  status(failure(error), true);
}
