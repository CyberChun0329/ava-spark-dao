import { b, localized, inLanguage, setText } from './i18n.js';

const actions = {
  publishLesson: b('发布课程场次', 'Publish class'), publishForm: b('发布订课确认单', 'Publish booking confirmation'),
  authoriseRepresentative: b('授权确认代理人', 'Authorize a representative'), recordTermsProvision: b('登记条款交付', 'Record delivery of terms'),
  verifyPrefunding: b('核对预留资金', 'Verify funds set aside'), signTeachingAgreement: b('签署授课协议', 'Sign teaching agreement'),
  retainInventory: b('留存已核验费用清单', 'Retain verified expense inventory'),
  acceptForm: b('接受确认单', 'Accept confirmation form'), confirmPlace: b('确认名额并扣款', 'Confirm place and debit funds'),
  recordStudentNotice: b('登记学生通知', 'Record student notice'), recordTutorNotice: b('登记教师通知', 'Record tutor notice'),
  lockRoster: b('锁定团课名册', 'Lock group roster'), recordTeachingStarted: b('登记实际开课', 'Record actual teaching start'),
  recordTeachingEnded: b('登记实际下课', 'Record teaching end'), recordAttendance: b('报告出勤', 'Report attendance'),
  recordOneToOneCompletion: b('确认单人课完成', 'Confirm one-to-one completion'),
  recordServiceFeedback: b('反馈上课情况', 'Give feedback on the class'), recordTutorDelivery: b('报告授课情况', 'Report how the class went'),
  proposeOrdinaryGroup: b('提交按名额结算的方案', 'Propose settlement by seat'), approveOrdinaryGroup: b('批准按名额结算', 'Approve settlement by seat'),
  proposeProviderStartedEarly: b('提出未满足开课条件的专门结算', 'Propose settlement for teaching started without meeting requirements'),
  approveProviderStartedEarly: b('批准未满足开课条件的专门结算', 'Approve settlement for teaching started without meeting requirements'),
  offerRecharge: b('公布充值条款', 'Publish recharge terms'), approveRechargeToken: b('授权扣取本次充值', 'Authorize this top-up'),
  recharge: b('确认并充值', 'Confirm and recharge'), publishContacts: b('公布案件联系人', 'Publish case contacts'),
  receiveConcern: b('提交案件', 'Submit case'), acknowledge: b('登记案件受理', 'Record case acknowledgment'),
  receiveConcernAt: b('登记此前已收到的异议', 'Record a concern received earlier'),
  reply: b('登记案件答复', 'Record case reply'), requestReview: b('申请独立复核', 'Request independent review'),
  escalate: b('登记案件接办', 'Record case escalation'), appoint: b('指定案件承办人', 'Appoint case handler'),
  decideInitial: b('登记初判', 'Record initial finding'), retainOriginal: b('留存教师过错初判', 'Save the initial fault decision'),
  decideReview: b('登记独立复核', 'Record independent review'),
  decidePaymentRevision: b('复核并核定款项更正', 'Review and determine payment correction'),
  adoptCorrection: b('采纳更正', 'Adopt correction'), adoptApprovalStop: b('采纳并停止未执行的批准', 'Adopt and stop unexecuted approval'),
  adoptPaymentRevision: b('采纳款项更正', 'Adopt payment correction'),
  publishRedressTerms: b('公布补偿条款', 'Publish compensation terms'), recordFault: b('登记教师过错', 'Record tutor fault'),
  acceptStandardCompensation: b('接受标准补偿', 'Accept standard compensation'),
  assessRefund: b('核定应退金额', 'Assess refund'), establishRefundPayment: b('登记应退款项', 'Record refund due'),
  issueCourseCredit: b('发放课程抵用额', 'Issue course credit'), releaseBudget: b('解除未使用的课程方资金预留', 'Release unused provider reserve'),
};
const fields = {
  terms: b('已核对的条款', 'Verified terms'), assessment: b('按名额结算的记录', 'Settlement by seat'), observation: b('实际开课记录', 'Teaching start record'),
  evidenceId: b('经核实的证据编号', 'Verified evidence ID'), formId: b('确认单标识', 'Confirmation form ID'), lessonId: b('课次标识', 'Lesson ID'),
  formIds: b('预留资金对应的确认单编号', 'Booking confirmation IDs covered by these funds'), requiredUnits: b('需预留金额（最小单位）', 'Amount to set aside (base units)'),
  fundingRef: b('预留资金的核对依据', 'Evidence that funds were set aside'), registerRef: b('名册记录引用', 'Roster reference'), input: b('案件记录', 'Case record'),
  scenarios: b('已核验的费用情形清单', 'Verified expense scenarios'),
  serviceValue: b('已独立核实的实际教学价值（最小单位）', 'Independently verified value of teaching delivered (base units)'),
  tutorAmount: b('按有效教师协议核实的教师应收（最小单位）', 'Amount verified under the applicable tutor agreement (base units)'),
  originalPayer: b('确认单付款人地址', 'Payer named in the confirmation'), originalDebitAccount: b('原扣款账户', 'Original debit account'),
  debitedUnits: b('实际原扣款（最小单位）', 'Amount originally debited (base units)'),
  refundDue: b('原扣款对应退款（最小单位）', 'Refund from the original debit (base units)'),
  caseId: b('案件标识', 'Case ID'), role: b('签署角色', 'Signing role'), discountRef: b('全免依据', 'Full waiver reference'),
  discountEvidenceId: b('全免证据编号', 'Full waiver evidence ID'), rechargeDebits: b('扣款对应的实际充值收据', 'Recharge receipts used for the debit'),
  deliveryRef: b('送达或通知记录引用', 'Delivery or notice reference'), recipient: b('接收方地址', 'Recipient address'),
  receivedAt: b('异议实际收到时间（UTC 秒）', 'Time the concern was received (UTC seconds)'),
  receiptRef: b('原收件凭据引用', 'Original receipt reference'),
  deliveredAt: b('实际送达时间（UTC 秒）', 'Actual delivery time (UTC seconds)'), channelRef: b('约定通知渠道承诺', 'Agreed notice channel commitment'),
  occurredAt: b('实际发生时间（UTC 秒）', 'Actual occurrence time (UTC seconds)'), occurrenceRef: b('实际发生依据', 'Occurrence reference'),
  completed: b('已经完成授课', 'Teaching completed'), detailsRef: b('教师报告承诺', 'Tutor report commitment'), attended: b('学生实际出勤', 'Student attended'),
  reportRef: b('报告承诺', 'Report commitment'), status: b('服务交付状态（1 未交付 · 2 部分 · 3 全部）', 'Service delivery status (1 none · 2 partial · 3 complete)'),
  receivedRef: b('已交付内容承诺', 'Delivered content commitment'), notReceivedRef: b('未交付内容承诺', 'Undelivered content commitment'),
  paymentEvidenceIds: b('逐项款项证据编号列表', 'Payment evidence IDs'), grounds: b('复核申请依据', 'Grounds for review'),
  notice: b('已发通知记录', 'Sent notice record'), offerId: b('充值条款标识', 'Recharge offer ID'), revision: b('已核实的款项更正', 'Verified payment correction'),
  amount: b('金额（最小单位）', 'Amount (base units)'), spender: b('获准扣款的地址', 'Address authorized to debit funds'),
  finding: b('已核实的过错认定', 'Verified fault finding'),
  paymentEvidenceId: b('退款付款义务证据编号', 'Refund payment obligation evidence ID'), releaseRef: b('课程方资金预留解除记录引用', 'Provider reserve release reference'),
};
const acceptance = [b('课程方', 'Provider'), b('教师', 'Tutor'), b('客户', 'Customer'), b('付款人', 'Payer')];
const progress = [b('未触发', 'Not started'), b('办理中', 'In progress'), b('已逾期', 'Overdue'), b('按期完成', 'Completed on time'), b('逾期完成', 'Completed late'), b('完成时间与截止同秒，待核实', 'Completed in the deadline second; verification needed')];
const occurrence = [b('尚未发生', 'Not yet started'), b('获准开课', 'Teaching permitted'), b('开课要求未满足', 'Teaching requirements not met'), b('开课权限待核实', 'Teaching permission needs verification')];
const delivery = [b('未报告', 'Not reported'), b('未交付', 'Not delivered'), b('部分交付', 'Partially delivered'), b('全部交付', 'Fully delivered')];
const formats = {
  hash: ['0[xX][0-9a-fA-F]{64}', b('输入 0x 加 64 位十六进制字符。', 'Enter 0x followed by 64 hexadecimal characters.')],
  address: ['0x[0-9a-fA-F]{40}', b('输入 0x 加 40 位十六进制字符。', 'Enter 0x followed by 40 hexadecimal characters.')],
  uint: ['(?:0|[1-9][0-9]*)', b('输入十进制非负整数，省略前导零。', 'Enter a non-negative decimal integer without leading zeroes.')],
  json: [null, b('粘贴已核验的 JSON 记录或列表。较大的整数请写成带引号的十进制数字。', 'Paste a verified JSON record or list. Write large integers as quoted decimal digits.')],
};
const courseTimes = { recordStudentNotice: 'deliveredAt', recordTutorNotice: 'deliveredAt',
  recordTeachingEnded: 'occurredAt', receiveConcernAt: 'receivedAt' };
export const courseActionLabel = (operationId, fallback) => actions[operationId] ?? fallback;
export const courseFieldLabel = (name, fallback) => fields[name] ?? fallback;
export const isCourseTimeField = (operationId, name) => courseTimes[operationId] === name;
export function courseArgumentValue(operationId, name, value) {
  if (name === 'role') return acceptance[value] ?? value;
  if (operationId === 'recordServiceFeedback' && name === 'status') return delivery[value] ?? value;
  return typeof value === 'boolean' ? (value ? b('是', 'Yes') : b('否', 'No')) : value;
}

export class RecordInputError extends Error {
  constructor(hint) {
    super();
    this.hint = hint;
  }
}

function readRecord(source) {
  let value;
  try { value = JSON.parse(source); }
  catch {
    throw new RecordInputError(b('请输入有效的 JSON 格式。', 'Enter valid JSON.'));
  }
  const tokens = source.match(/"(?:[^"\\]|\\.)*"|[{}[\],:]|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?|true|false|null/g);
  for (const token of tokens) {
    if (!/^[-0-9]/.test(token)) continue;
    // Check the original token too. JSON.parse can round a fractional number to an integer.
    const [mantissa, exponent = '0'] = token.split(/[eE]/);
    const [whole, fraction = ''] = mantissa.replace(/^-/, '').split('.');
    const digits = whole + fraction;
    let end = digits.length;
    while (digits[end - 1] === '0') end--;
    const decimalPlaces = end - whole.length;
    if (!Number.isSafeInteger(Number(token)) || (end && Number(exponent) < decimalPlaces)) {
      throw new RecordInputError(b('请输入精确的整数。较大的整数请写成带引号的十进制数字。', 'Use exact integers. Write large integers as quoted decimal digits.'));
    }
  }
  return { value, tokens };
}

function formatRecord(tokens) {
  let depth = 0;
  let formatted = '';
  const line = () => '\n' + '  '.repeat(depth);
  for (const [index, token] of tokens.entries()) {
    if (token === '}' || token === ']') {
      depth--;
      if (tokens[index - 1] !== '{' && tokens[index - 1] !== '[') formatted += line();
    }
    formatted += token;
    if (token === '{' || token === '[') {
      depth++;
      if (tokens[index + 1] !== '}' && tokens[index + 1] !== ']') formatted += line();
    } else if (token === ',') formatted += line();
    else if (token === ':') formatted += ' ';
  }
  return formatted;
}

function fieldButton(label) {
  const button = document.createElement('button');
  button.type = 'button';
  button.className = 'field-tool';
  setText(button, label);
  return button;
}

function utcEntry(input) {
  const entry = document.createElement('details');
  entry.className = 'utc-entry';
  const heading = document.createElement('summary');
  setText(heading, b('按 UTC 日期和时间填写', 'Enter date and time in UTC'));
  const label = document.createElement('label');
  const caption = document.createElement('span');
  setText(caption, b('日期和时间（UTC）', 'Date and time (UTC)'));
  const picker = document.createElement('input');
  picker.type = 'datetime-local';
  picker.step = '1';
  // The optional picker must not participate in validation of the transaction form.
  picker.setAttribute('form', '');
  picker.dataset.utcFor = input.name;
  label.append(caption, picker);
  const apply = fieldButton(b('使用这个 UTC 时间', 'Use this UTC time'));
  apply.dataset.utcApply = input.name;
  const feedback = document.createElement('small');
  feedback.className = 'field-tool-feedback';
  feedback.id = `utc-help-${input.name}`;
  feedback.hidden = true;
  picker.setAttribute('aria-describedby', feedback.id);
  picker.addEventListener('input', () => {
    picker.removeAttribute('aria-invalid');
    feedback.hidden = true;
  });
  apply.addEventListener('click', () => {
    const seconds = picker.valueAsNumber / 1000;
    if (!Number.isSafeInteger(seconds) || seconds < 0) {
      setText(feedback, b('请输入完整的 UTC 日期和时间，且不早于 1970 年 1 月 1 日。', 'Enter a complete UTC date and time on or after January 1, 1970.'));
      feedback.hidden = false;
      picker.setAttribute('aria-invalid', 'true');
      picker.focus();
      return;
    }
    if (input.value !== String(seconds)) {
      input.value = String(seconds);
      input.dispatchEvent(new Event('input', { bubbles: true }));
    }
    entry.open = false;
    input.focus();
  });
  entry.append(heading, label, feedback, apply);
  return entry;
}

export function operationFields(target, fields, defaults = {}) {
  const controls = fields.map(field => {
    const container = document.createElement('div');
    container.className = 'operation-field';
    const label = document.createElement('label');
    const caption = document.createElement('span');
    setText(caption, field.label);
    const complex = field.type === 'json';
    const input = document.createElement(complex ? 'textarea' : 'input');
    input.name = field.name;
    input.required = field.type !== 'bool';
    const [pattern, hint] = formats[field.type] ?? [];
    const guidance = [field.help, field.utc ? b('直接输入 UTC 秒，或使用下方的日期和时间。', 'Enter UTC seconds directly or use the date and time control below.') : hint].filter(Boolean);
    const description = localized(language => guidance.map(value => inLanguage(value, language)).join(' '));
    if (complex) input.rows = 4;
    else input.type = field.type === 'bool' ? 'checkbox' : 'text';
    if (pattern) input.pattern = pattern;
    if (pattern || complex) input.spellcheck = false;
    if (field.type === 'uint') input.inputMode = 'numeric';
    if (defaults[field.name] != null) input.value = String(defaults[field.name]);
    else if (field.default != null) input.value = String(field.default);
    else if (field.name === 'notReceivedRef') input.value = `0x${'0'.repeat(64)}`;
    const help = document.createElement('small');
    help.id = `operation-help-${field.name}`;
    setText(help, description);
    help.hidden = !guidance.length;
    input.setAttribute('aria-describedby', help.id);
    const required = b('请填写此项。', 'Please fill out this field.');
    function showError(message) {
      setText(help, message);
      help.hidden = false;
      input.setAttribute('aria-invalid', 'true');
    }
    input.addEventListener('invalid', () => showError(input.validity.valueMissing ? required : hint ?? b('请检查填写格式。', 'Please check the format.')));
    input.addEventListener('input', () => {
      setText(help, description);
      help.hidden = !guidance.length;
      input.removeAttribute('aria-invalid');
    });
    label.append(caption, input, help);
    container.append(label);
    function record() {
      try {
        return readRecord(input.value);
      } catch (error) {
        if (error instanceof RecordInputError) {
          showError(input.validity.valueMissing ? required : error.hint);
          input.focus();
        }
        throw error;
      }
    }
    if (complex) {
      const format = fieldButton(b('整理 JSON', 'Format JSON'));
      format.dataset.jsonFormat = field.name;
      format.addEventListener('click', () => {
        let parsed;
        try { parsed = record(); }
        catch (error) {
          if (error instanceof RecordInputError) return;
          throw error;
        }
        const formatted = formatRecord(parsed.tokens);
        if (formatted !== input.value) {
          input.value = formatted;
          input.dispatchEvent(new Event('input', { bubbles: true }));
        }
        input.focus();
      });
      container.append(format);
    }
    if (field.utc) container.append(utcEntry(input));
    return { container, input, field, record };
  });
  target.replaceChildren(...controls.map(({ container }) => container));
  return {
    read(only) {
      const values = {};
      for (const { input, record, field: { name, type } } of controls) {
        if (only && !only.includes(name)) continue;
        if (type === 'json') values[name] = record().value;
        else values[name] = type === 'bool' ? input.checked : input.value.trim();
      }
      return values;
    },
  };
}

export function createCourseView({ node, button, facts, time, select, readNotice, details, reference }) {
  function action(offer, context) {
    const role = offer.operationId === 'acceptForm' ? offer.arguments.role : undefined;
    const label = courseActionLabel(offer.operationId, offer.label);
    const item = button(role === undefined ? label : localized(language => `${inLanguage(label, language)} · ${inLanguage(acceptance[role] ?? role, language)}`),
      () => select(offer, item, context), 'courseAction', offer.operationId);
    if (role !== undefined) item.dataset.acceptance = role;
    return item;
  }
  function actions(items, context) {
    const row = node('div', null, 'action-row');
    row.append(...items.map(offer => action(offer, context)));
    return row;
  }
  function render(target, courses) {
    target.hidden = !courses;
    target.replaceChildren();
    if (!courses) return;
    if (courses.global.length) target.append(actions(courses.global));
    for (const recharge of courses.recharges ?? []) {
      const item = node('article', null, 'panel');
      item.dataset.rechargeOffer = recharge.offerId;
      item.append(node('h2', recharge.receiptId === '0' ? b('充值条款', 'Recharge terms') : b('充值已入账', 'Recharge received')));
      if (recharge.actions.length) item.append(actions(recharge.actions));
      item.append(facts([[b('充值金额（最小单位）', 'Recharge amount (base units)'), recharge.amount],
          [b('可退上限（最小单位）', 'Refund cap (base units)'), recharge.returnCap], [b('未用余额可退至', 'Unused balance refundable through'), time(recharge.returnThrough)],
          [b('实收回执编号', 'Receipt ID'), recharge.receiptId === '0' ? '—' : recharge.receiptId]]),
        reference(b('充值条款标识', 'Recharge offer ID'), recharge.offerId),
        details(b('充值记录', 'Recharge record'), facts([[b('课程方地址', 'Provider address'), recharge.provider]])));
      target.append(item);
    }
    for (const lesson of courses.lessons) {
      const item = node('article', null, 'course');
      item.dataset.course = lesson.lessonId;
      const heading = node('header', null, 'course-header');
      const state = lesson.settled.complete ? b('已结算', 'Settled') : lesson.teaching.endedAt !== '0' ? b('已下课', 'Teaching ended')
        : lesson.teaching.startedAt !== '0' ? b('已开课', 'Teaching started') : b('订课中', 'Booking in progress');
      const title = node('div');
      title.append(node('h3', state), reference(b('课次标识', 'Lesson ID'), lesson.lessonId));
      heading.append(title);
      const body = node('div', null, 'obligation');
      if (lesson.offers.length) body.append(actions(lesson.offers, { lessonId: lesson.lessonId }));
      body.append(facts([
        [b('安排开课', 'Scheduled start'), time(lesson.startsAt)], [b('安排下课', 'Scheduled end'), time(lesson.endsAt)],
        [b('原核验的预留资金（最小单位）', 'Originally verified reserve (base units)'), lesson.prefunding.evidenceId === '0' ? b('待核验', 'Verification pending') : lesson.prefunding.reservedUnits],
        ...(lesson.commitmentFundingAvailable === false
          ? [[b('承诺前备付', 'Funding before commitment'), b('待重新核验', 'Verification needed')]] : []),
        [b('团课名册锁定', 'Group roster locked'), time(lesson.roster.lockedAt)], [b('实际开课', 'Actual start'), time(lesson.teaching.startedAt)],
        [b('开课登记时的判断', 'Decision when teaching start was recorded'), occurrence[lesson.teaching.startPermission]],
        ...(lesson.openingNoticesVerifiedLater
          ? [[b('后续核验', 'Later verification'), b('已核实按时通知', 'Timely notices verified')]] : []),
        [b('实际下课', 'Actual end'), time(lesson.teaching.endedAt)],
        ...(lesson.settled.complete ? [[b('课酬合计（最小单位）', 'Total tutor pay (base units)'), lesson.settled.totalTutorPay],
          [b('已确认出勤的人数', 'Confirmed attendance count'), lesson.settled.attendanceConfirmations]] : []),
      ]));
      if (lesson.earlySettlement) {
        const early = lesson.earlySettlement;
        body.append(details(b('未满足开课条件的专门结算', 'Settlement for teaching started without meeting requirements'),
          facts([
            [fields.originalPayer, early.payer],
            ...(early.debitAccount ? [[fields.originalDebitAccount, early.debitAccount]] : [[fields.debitedUnits, early.debitedUnits]]),
            [fields.serviceValue, early.feeDue], [fields.tutorAmount, early.tutorPay],
            [b('教师净应收（最小单位）', 'Net tutor amount due (base units)'), early.tutorNetPay],
            [b('本结算核定退款（最小单位）', 'Refund determined in this settlement (base units)'), early.refundDue],
            [b('结算时已认定收讫的退款（最小单位）', 'Refund already recognized as received at settlement (base units)'), early.refundAlreadyReceived],
          ])));
      }
      if (lesson.fundingReview) body.append(node('p', b('课次预留资金包含已赚取的课费，不包含单独的退款或已发放的课程抵用额。', 'Lesson funds held include earned fees and exclude separate refunds and issued course credit.')), facts([
        [b('课次预留资金（含已赚取的课费，最小单位）', 'Lesson funds held, including earned fees (base units)'), lesson.fundingReview.lessonHeld],
        [b('已赚取的课费（最小单位）', 'Earned fees (base units)'), lesson.fundingReview.earnedFees],
        [b('可解除预留的课程方资金（最小单位）', 'Provider reserve available to release (base units)'), lesson.fundingReview.releasable],
        [b('已解除预留的课程方资金（最小单位）', 'Provider reserve released (base units)'), lesson.fundingReview.released],
      ]));
      body.append(details(b('课程记录', 'Class record'), facts([
        [b('适用规则编号', 'Rules used'), lesson.packageId], [b('链上课次交易', 'On-chain lesson transaction'), lesson.recorded],
        ...(lesson.teaching.providerWentAhead ? [[b('课程方实际开课', 'Provider proceeded with teaching'), b('是', 'Yes')]] : []),
        ...(lesson.teaching.unmetConditionRef && !/^0x0{64}$/i.test(lesson.teaching.unmetConditionRef)
          ? [[b('未满足条件的依据', 'Unmet condition reference'), lesson.teaching.unmetConditionRef]] : []),
        ...(lesson.settled.complete ? [[b('结算证据校验值', 'Settlement evidence hash'), lesson.settled.basis]] : []),
        ...(lesson.contacts.length ? [[b('案件联系人条款标识', 'Case contact terms IDs'), lesson.contacts.join('\n')]] : []),
      ])));
      for (const seat of lesson.seats) {
        const place = node('article', null, 'course-place');
        place.dataset.courseForm = seat.formId;
        place.append(node('h3', seat.confirmation.confirmedAt !== '0' ? localized(language => language === 'zh' ? `已扣款 ${seat.confirmation.debitedUnits}` : `Debited ${seat.confirmation.debitedUnits}`) : b('待确认名额', 'Place awaiting confirmation')),
          reference(b('确认单标识', 'Confirmation form ID'), seat.formId));
        if (seat.actions.length) place.append(actions(seat.actions, { lessonId: lesson.lessonId, formId: seat.formId }));
        place.append(facts([
            [b('正常课费（最小单位）', 'Normal fee (base units)'), seat.normalFee], [b('应付课费（最小单位）', 'Payable fee (base units)'), seat.payableFee],
            [b('学生通知', 'Student notice'), seat.notice ? b('已登记送达', 'Delivery recorded') : b('待登记', 'Not yet recorded')], [b('学生出勤报告', 'Student attendance report'), seat.attendance === undefined
              ? b('未报告', 'Not reported') : seat.attendance ? b('出勤', 'Attended') : b('未出勤', 'Absent')], [b('学生上课反馈', 'Student feedback on the class'), delivery[seat.feedback] ?? b('未报告', 'Not reported')],
            ...(seat.compensation?.accepted ? [[b('补偿状态', 'Compensation status'), b('已接受标准补偿', 'Standard compensation accepted')]]
              : seat.compensation?.faultRecorded ? [[b('补偿状态', 'Compensation status'), b('已登记教师过错', 'Tutor fault recorded')]]
                : seat.compensation?.termsPublished ? [[b('补偿状态', 'Compensation status'), b('已公布补偿条款', 'Compensation terms published')]] : []),
            ...(seat.compensation?.refundAssessed !== undefined && seat.compensation.refundAssessed !== '0'
              ? [[b('已核定应退金额（最小单位）', 'Refund assessed (base units)'), seat.compensation.refundAssessed]] : []),
            ...(seat.compensation?.refundDue !== undefined
              ? [[b('尚未付清的退款（最小单位）', 'Refund outstanding (base units)'), seat.compensation.refundDue]] : []),
            ...(seat.compensation?.creditIssued
              ? [[b('剩余课程抵用额（最小单位）', 'Course credit remaining (base units)'), seat.compensation.creditRemaining]] : []),
          ]));
        place.append(details(b('确认单记录', 'Confirmation record'), facts([[b('确认单版本', 'Confirmation form version'), seat.version]])));
        body.append(place);
      }
      item.append(heading, body);
      target.append(item);
    }
  }
  function inbox(target, snapshot) {
    target.replaceChildren();
    if (!snapshot.records.length) {
      target.append(node('p', b('此钱包当前没有可查看的案件。', 'There are no cases this wallet can open.'), 'muted'));
      return;
    }
    target.append(node('p', localized(language => `${language === 'zh' ? '链上区块' : 'Block'} ${snapshot.asOf.blockNumber} · ${inLanguage(time(snapshot.asOf.timestamp), language)}`), 'reading'));
    for (const record of snapshot.records) {
      const item = node('article', null, 'course-place');
      item.dataset.case = record.caseId;
      item.append(node('h3', record.adopted ? b('已采纳更正', 'Correction adopted') : record.acknowledged ? b('已受理', 'Acknowledged') : b('待受理', 'Awaiting acknowledgment')),
        reference(b('案件标识', 'Case ID'), record.caseId));
      if (record.offers.length) item.append(actions(record.offers, { lessonId: record.lessonId, caseId: record.caseId }));
      for (const receipt of record.receipts) {
        const kinds = { '受理通知': b('受理通知', 'acknowledgment notice'), '更正通知': b('更正通知', 'correction notice'), '案件答复': b('案件答复', 'case reply') };
        item.append(button(localized(language => language === 'zh' ? `用钱包查看${inLanguage(kinds[receipt.kind] ?? receipt.kind, language)}` : `Open ${inLanguage(kinds[receipt.kind] ?? receipt.kind, language)} with wallet`), event => readNotice({
        obligationId: record.obligationId, caseId: record.caseId, noticeHash: receipt.referenceHash,
      }, event.currentTarget), 'caseNotice'));
      }
      item.append(facts([
        [b('收到时间', 'Received'), time(record.receivedAt)], [b('答复截止', 'Reply deadline'), time(record.replyCutoff)],
        [b('答复进度', 'Reply progress'), progress[record.progress[0]]], [b('复核截止', 'Review deadline'), time(record.reviewCutoff)], [b('复核进度', 'Review progress'), progress[record.progress[1]]],
      ]), reference(b('课次标识', 'Lesson ID'), record.lessonId), reference(b('提交交易', 'Submission transaction'), record.origin.hash));
      target.append(item);
    }
  }
  return { render, inbox };
}
