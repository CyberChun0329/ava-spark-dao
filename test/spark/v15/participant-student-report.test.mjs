import assert from 'node:assert/strict';
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { privateKeyToAccount } from 'viem/accounts';
import { fileStudentReport, prepareStudentReport, readStudentReport }
  from '../../../examples/spark-dao/v15/participant-student-report-cli.ts';

const h = d => `0x${d.repeat(64)}`;
const a = d => `0x${d.repeat(40)}`;
const formId = h('1');
const studentWallet = privateKeyToAccount(h('1'));
const otherWallet = privateKeyToAccount(h('2'));
const student = studentWallet.address.toLowerCase();
function fixture(t) {
  const folder = mkdtempSync(join(tmpdir(), 'spark-student-report-'));
  t.after(() => rmSync(folder, { recursive: true }));
  const genesis = { number: 0n, hash: h('d'), timestamp: 1n };
  const prepared = { number: 8n, hash: h('8'), timestamp: 100n };
  const filed = { number: 9n, hash: h('9'), timestamp: 101n };
  const state = { latest: prepared, current: formId, startedAt: 0n, changeId: h('0') };
  const installation = {
    archivePath: join(folder, 'configured.sqlite'), archiveScope: h('5'),
    booking: { address: a('a'), abi: [] }, sdk: { deployment: { chainId: 31337 } },
    client: {
      getChainId: async () => 31337,
      getBlock: async ({ blockNumber }) => blockNumber === 0n ? genesis : blockNumber === 8n ? prepared
        : blockNumber === 9n ? filed : state.latest,
      getCode: async () => '0x',
      readContract: async ({ functionName, blockHash }) => {
        const atFiling = blockHash === filed.hash;
        if (functionName === 'getForm') return { lessonId: h('2'), version: 1n, terms: { placeId: h('3'), student }, confirmation: { confirmedAt: 70n } };
        if (functionName === 'currentForm') return atFiling ? state.current : formId;
        if (functionName === 'getTeaching') return { startedAt: atFiling ? state.startedAt : 0n, endedAt: 0n };
        if (functionName === 'getEffectiveArrangement') return { startsAt: 100n, changeId: atFiling ? state.changeId : h('0') };
        throw Error(functionName);
      },
    },
  };
  return { installation, state, filed };
}
test('separate signed accounts are filed locally without an absence or payment finding', async t => {
  const { installation, state, filed } = fixture(t);
  const attendance = await prepareStudentReport(installation, formId, student, 'attendance', { attended: true, text: 'I waited in the room.' });
  const feedback = await prepareStudentReport(installation, formId, student, 'feedback', { text: 'Teaching did not begin.' });
  const signature = await studentWallet.signMessage({ message: attendance.message });
  state.latest = filed;
  const saved = await fileStudentReport(installation, attendance, signature);
  assert.equal(saved.intent.details.attended, true);
  assert.equal(saved.filingCheckpoint.blockNumber, '9');
  assert.ok(Number.isFinite(Date.parse(saved.localFiledAt)));
  assert.deepEqual(readStudentReport(installation, saved.id), saved);
  await assert.rejects(fileStudentReport(installation, attendance, signature), /already filed/);
  const second = await fileStudentReport(installation, feedback, await studentWallet.signMessage({ message: feedback.message }));
  assert.notEqual(saved.id, second.id);
  assert.equal(second.intent.kind, 'feedback');
});
test('filing refuses changed form, later teaching, changed arrangement and wrong signature', async t => {
  const { installation, state, filed } = fixture(t);
  const prepared = await prepareStudentReport(installation, formId, student, 'attendance', { attended: false, text: 'My account.' });
  const signature = await studentWallet.signMessage({ message: prepared.message });
  state.latest = filed;
  state.current = h('4');
  await assert.rejects(fileStudentReport(installation, prepared, signature), /active confirmed form/);
  state.current = formId; state.startedAt = 100n;
  await assert.rejects(fileStudentReport(installation, prepared, signature), /without recorded teaching/);
  state.startedAt = 0n; state.changeId = h('6');
  await assert.rejects(fileStudentReport(installation, prepared, signature), /arrangement changed/);
  state.changeId = h('0');
  await assert.rejects(fileStudentReport(installation, prepared, await otherWallet.signMessage({ message: prepared.message })), /student signature/);
  await assert.rejects(prepareStudentReport(installation, formId, a('2'), 'feedback', { text: 'wrong signer' }), /named student/);
});
