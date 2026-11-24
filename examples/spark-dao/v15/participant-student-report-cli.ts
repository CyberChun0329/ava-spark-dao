import { closeSync, existsSync, openSync } from 'node:fs';
import { resolve } from 'node:path';
import { DatabaseSync } from 'node:sqlite';
import { pathToFileURL } from 'node:url';
import { isDeepStrictEqual } from 'node:util';
import { jsonValue, withCanonicalSnapshot, type CanonicalSnapshot } from '@ava-protocol/sdk';
import { hashMessage, type Address, type Hex } from 'viem';
import { address, chainIdentity, checkpoint, hash, loadArchiveConfiguration, readJson,
  readPreparationCheckpoint, signedBy } from './participant-material-archive-cli.ts';
import { participantObject } from './participant-payments.ts';

const domain = 'ava.spark.local.student-no-start-report.v1';
type Kind = 'attendance' | 'feedback';
const same = (a: string, b: string) => a.toLowerCase() === b.toLowerCase();
function kindOf(value: unknown): Kind {
  if (value !== 'attendance' && value !== 'feedback') throw new Error('Expected attendance or feedback');
  return value;
}
function detailsOf(kind: Kind, details: unknown) {
  const value = participantObject(details);
  if (typeof value.text !== 'string' || !value.text.trim()) throw new Error('A student account is required');
  if (kind === 'attendance') {
    if (typeof value.attended !== 'boolean') throw new Error('Attendance account requires attended true or false');
    return { attended: value.attended, text: value.text };
  }
  return { text: value.text };
}
async function loadInstallation(configPath: string) {
  const installation = await loadArchiveConfiguration(configPath, domain);
  const booking = installation.profile.contracts.SparkV15Booking;
  if (!booking || !Array.isArray(booking.abi)) throw new Error('Booking is missing from the deployment export');
  address(booking.address);
  return { ...installation, booking };
}
type Installation = Awaited<ReturnType<typeof loadInstallation>>;
async function identity(installation: Installation) {
  return { ...await chainIdentity(installation), booking: address(installation.booking.address) };
}
async function basis(installation: Installation, formId: Hex, student: Address, snapshot: CanonicalSnapshot) {
  const { client, booking } = installation;
  const { point, timestamp } = snapshot;
  const form = await client.readContract({ ...booking, functionName: 'getForm', args: [formId], ...point }) as {
    lessonId: Hex; version: bigint; terms: { placeId: Hex; student: Address }; confirmation: { confirmedAt: bigint } };
  if (!form.version || !same(form.terms.student, student)) throw new Error('The signer is not the named student of this form');
  const [current, teaching, arrangement] = await Promise.all([
    client.readContract({ ...booking, functionName: 'currentForm', args: [form.lessonId, form.terms.placeId], ...point }) as Promise<Hex>,
    client.readContract({ ...booking, functionName: 'getTeaching', args: [form.lessonId], ...point }) as Promise<{ startedAt: bigint; endedAt: bigint }>,
    client.readContract({ ...booking, functionName: 'getEffectiveArrangement', args: [form.lessonId, timestamp], ...point }) as Promise<{ startsAt: bigint; changeId: Hex }>,
  ]);
  if (!same(current, formId) || !form.confirmation.confirmedAt || !arrangement.startsAt
    || form.confirmation.confirmedAt > arrangement.startsAt || timestamp < arrangement.startsAt
    || teaching.startedAt !== 0n || teaching.endedAt !== 0n) {
    throw new Error('Expected the active confirmed form and agreed start without recorded teaching');
  }
  return { formId, lessonId: form.lessonId, placeId: form.terms.placeId, formVersion: form.version,
    student, confirmedAt: form.confirmation.confirmedAt, agreedStart: arrangement.startsAt, changeId: arrangement.changeId };
}
export async function prepareStudentReport(installation: Installation, formId: Hex, student: Address, kind: Kind, details: unknown) {
  return withCanonicalSnapshot(installation.client, async snapshot => {
    const intent = jsonValue({ domain, installation: await identity(installation), archiveScope: installation.archiveScope,
      preparedAt: checkpoint(snapshot), ...(await basis(installation, formId, student, snapshot)),
      kind: kindOf(kind), details: detailsOf(kind, details) });
    return { intent, message: JSON.stringify(intent) };
  });
}
export async function fileStudentReport(installation: Installation, prepared: unknown, signature: Hex) {
  if (!/^0x(?:[0-9a-f]{2})+$/i.test(signature)) throw new Error('Expected a wallet message signature');
  const envelope = participantObject(prepared), intent = participantObject(envelope.intent);
  const formId = hash(intent.formId, 'Form ID'), student = address(intent.student), kind = kindOf(intent.kind);
  const details = detailsOf(kind, intent.details);
  const record = await withCanonicalSnapshot(installation.client, async snapshot => {
    const historical = await readPreparationCheckpoint(installation.client, participantObject(intent.preparedAt), snapshot);
    const [chain, initial, current] = await Promise.all([
      identity(installation), basis(installation, formId, student, historical), basis(installation, formId, student, snapshot),
    ]);
    const expected = jsonValue({ domain, installation: chain, archiveScope: installation.archiveScope,
      preparedAt: checkpoint(historical), ...initial, kind, details });
    const message = JSON.stringify(expected);
    if (!isDeepStrictEqual(intent, expected) || envelope.message !== message
      || !await signedBy(installation.client, student, message, signature, snapshot)) {
      throw new Error('The student signature must match the prepared account');
    }
    if (!isDeepStrictEqual(initial, current)) throw new Error('The confirmed form or arrangement changed after preparation');
    return participantObject(jsonValue({ intent: expected, signature, filingCheckpoint: checkpoint(snapshot), localFiledAt: new Date().toISOString() }));
  });
  closeSync(openSync(installation.archivePath, 'a', 0o600));
  const db = new DatabaseSync(installation.archivePath, { timeout: 5000 });
  try {
    db.exec('CREATE TABLE IF NOT EXISTS student_no_start_reports (message_hash TEXT PRIMARY KEY, record TEXT NOT NULL) STRICT');
    const id = hashMessage(JSON.stringify(record.intent));
    const inserted = db.prepare('INSERT INTO student_no_start_reports VALUES (?, ?) ON CONFLICT DO NOTHING').run(id, JSON.stringify(record));
    if (!inserted.changes) throw new Error('This signed student account is already filed');
    return { id, ...record };
  } finally { db.close(); }
}
export function readStudentReport(installation: Installation, id: Hex) {
  if (!existsSync(installation.archivePath)) return null;
  const db = new DatabaseSync(installation.archivePath, { readOnly: true });
  try {
    if (!db.prepare("SELECT name FROM sqlite_schema WHERE type='table' AND name='student_no_start_reports'").get()) return null;
    const row = db.prepare('SELECT record FROM student_no_start_reports WHERE message_hash = ?').get(id);
    return row ? { id, ...JSON.parse(row.record as string) } : null;
  } finally { db.close(); }
}
const usage = `Usage: node --import tsx examples/spark-dao/v15/participant-student-report-cli.ts <participant.json> prepare <form-id> <student> <attendance|feedback> <details.json>\n  ... file <prepared.json> <signature>\n  ... read <message-hash>\nStudent signs the exact prepared message; this is a local account, not an independent absence or delivery finding.`;
async function run(args: string[]) {
  if (args.length === 1 && args[0] === '--help') return console.log(usage);
  const [config, command, ...rest] = args;
  if (!config) throw new Error(usage);
  const installation = await loadInstallation(resolve(config));
  let result: unknown;
  if (command === 'prepare' && rest.length === 4) result = await prepareStudentReport(installation, hash(rest[0], 'Form ID'), address(rest[1]), kindOf(rest[2]), await readJson(rest[3]));
  else if (command === 'file' && rest.length === 2) result = await fileStudentReport(installation, await readJson(rest[0]), rest[1] as Hex);
  else if (command === 'read' && rest.length === 1) result = readStudentReport(installation, hash(rest[0], 'Message hash'));
  else throw new Error(usage);
  console.log(JSON.stringify(result, null, 2));
}
if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try { await run(process.argv.slice(2)); } catch (error) { console.error(error instanceof Error ? error.message : 'Student report failed'); process.exitCode = 1; }
}
