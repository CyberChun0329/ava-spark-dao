import { chmodSync, closeSync, existsSync, mkdirSync, openSync } from 'node:fs';
import { randomUUID } from 'node:crypto';
import { dirname } from 'node:path';
import { DatabaseSync } from 'node:sqlite';
import { deserialize, serialize } from 'node:v8';
import { isAddress, keccak256, toHex, type Address, type Hex } from 'viem';
import { jsonValue, type AvaCall, type TransactionRecord } from '@ava-protocol/sdk';
import type { MaterialReceipt } from '@ava-protocol/local-service/custody';
// Legacy case records share these serialized shapes with the v1.5 request store.
interface SparkSessionInput {
  courseTypeId: bigint; teacher: Address; students: readonly Address[]; scheduledAt: bigint;
  customerDiscountBps: number; linkedResearchAssetIds: readonly bigint[]; linkedResearchWeightBps: readonly number[];
}
interface SparkTask {
  action: 'schedule' | 'confirm-schedule' | 'complete' | 'cancel' | 'reschedule' | 'triage' | 'evidence-check' | 'pending-check';
}
interface SparkMaterialBinding {
  subject: { chainId: number; teaching: Address; sessionId?: bigint; proposalHash?: Hex;
    teacher: Address; students: readonly Address[]; scheduledAt: bigint };
}

export class SparkBackendError extends Error {
  constructor(readonly code: string, readonly status = 400) { super(code); this.name = 'SparkBackendError'; }
}
export interface SparkCase { id: string; sequence: number; revision: number; createdBy: Address; teacher: Address;
  students: Address[]; scheduledAt: bigint; sourceCommitment: Hex; proposal?: SparkSessionInput; sessionId?: bigint }
export interface SparkMaterialInput { owner: Address; kind: 'participant-statement' | 'unverified-upload';
  subject: SparkMaterialBinding['subject']; actions: SparkTask['action'][]; disclosures: { provider: string; model: string }[];
  contentHashes: Hex[]; signature: Hex; requestHash: Hex; receipt: unknown }
export type SparkMaterial = SparkMaterialInput & { id: string; caseId: string; revoked?: boolean };
export interface SparkComplaint { id: string; caseId: string; status: 'open' | 'resolved'; actor: Address;
  receipt: unknown; resolvedBy?: Address; resolutionReceipt?: unknown }
export interface SparkResearchSubject { kind: 'research'; assetId?: bigint; positionId?: bigint; revenueId?: bigint;
  claims?: readonly { sessionId: bigint; assetId: bigint; positionId: bigint }[] }
export interface SparkPreview { id: string; caseId?: string; actor: Address; action: string; call: AvaCall;
  subject?: SparkResearchSubject; createdId?: bigint;
  expiresAt: number; created?: { eventName: string; idField: string; source: 'teaching'|'evidence'|'kernel'|'requests'|'corrections'|'research'; referenceKind?: SparkReference['kind'] }; identity?: Pick<TransactionRecord, 'key' | 'hash'>;
  advice?: SparkAdviceLink; nonce?: number; nonceResolution?: SparkNonceProof; transactionStatus?: 'confirmed' | 'reverted' | 'nonce-consumed' }
export type SparkOperationSummary = Pick<SparkPreview, 'id' | 'caseId' | 'actor' | 'action' | 'expiresAt' | 'nonce' | 'identity' | 'transactionStatus' | 'subject' | 'createdId'>;
export interface SparkAdviceLink { id: string; hash: Hex; mode: 'ai'|'human'|'allocation'; sourceCommitment: Hex;
  reasonHash?: Hex; requestId?: bigint; receipt: unknown }
export interface SparkNonceProof { transactionHash: Hex; from: Address; nonce: number; blockNumber: bigint;
  blockHash: Hex; status: 'success'|'reverted' }
export interface SparkReference { kind: 'evidence' | 'object' | 'recognition' | 'request' | 'challenge' | 'finding';
  id: bigint; transactionHash: Hex }
export type SparkRequestProfile = { version: 1 } | { version: 2; audience: Hex };
export interface SparkRuntimeBinding { chainId: number; genesisHash: Hex; installationHash: Hex;
  checkpoint: { blockNumber: bigint; blockHash: Hex } }
export interface SparkCaseEvent { sequence: number; caseId: string; revision: number; event: string; data: unknown }
export interface SparkOperationEvent { sequence: number; previewId: string; event: string; data: unknown }
export interface SparkAdviceRecord { id: string; caseId: string; owner: Address; status: string;
  provider: string; model: string; receipt: unknown; hash?: Hex; sourceCommitment?: Hex }
type Page = { after?: number; limit?: number };
type BlobRow = { data: Uint8Array };
const unpack = <T>(value: Uint8Array): T => deserialize(value) as T;
const sourceDigest = (value: unknown): Hex => keccak256(toHex(JSON.stringify(jsonValue(value))));
const pageValues = (page: Page = {}) => {
  const after = page.after ?? 0, limit = page.limit ?? 50;
  if (!Number.isSafeInteger(after) || after < 0 || !Number.isSafeInteger(limit) || limit < 1 || limit > 100) {
    throw new SparkBackendError('invalid_page');
  }
  return { after, limit };
};

/** Trusted local metadata and opaque custody receipts; callers authenticate and protect receipt contents. */
export class SparkCaseStore {
  private readonly db: DatabaseSync;

  /** Enumerate immutable custody references in an existing stopped instance; never upgrades it. */
  static custodyInventory(path: string, context: { chainId: number; teaching: Address }): MaterialReceipt[] {
    if (path === ':memory:' || !existsSync(path) || !Number.isSafeInteger(context.chainId) || context.chainId < 1
      || !isAddress(context.teaching)) throw new SparkBackendError('custody_inventory_unavailable');
    let db: DatabaseSync | undefined;
    try {
      db = new DatabaseSync(path, { readOnly: true });
      db.exec('BEGIN');
      const row = db.prepare('SELECT data FROM spark_context WHERE id=1').get() as BlobRow | undefined;
      const saved = row && unpack<{ chainId: number; teaching: Address }>(row.data);
      if (!saved || saved.chainId !== context.chainId || typeof saved.teaching !== 'string'
        || saved.teaching.toLowerCase() !== context.teaching.toLowerCase()) throw new SparkBackendError('context_mismatch', 409);
      const receipts = new Map<string, MaterialReceipt>();
      const add = (value: unknown) => {
        if (!value || typeof value !== 'object' || Array.isArray(value)
          || Object.keys(value).sort().join(',') !== 'appId,caseId,ciphertextHash,materialClass,policyId,resourceId,uri') {
          throw new SparkBackendError('invalid_custody_receipt');
        }
        const item = value as MaterialReceipt;
        const hex = (part: unknown) => typeof part === 'string' && /^0x[0-9a-f]{64}$/.test(part) && part !== `0x${'0'.repeat(64)}`;
        if (![item.resourceId, item.appId, item.caseId, item.materialClass, item.ciphertextHash].every(hex)
          || item.policyId !== 1 || item.uri !== `ava-private:v1:${item.resourceId.slice(2)}`) {
          throw new SparkBackendError('invalid_custody_receipt');
        }
        const canonical: MaterialReceipt = { resourceId: item.resourceId, appId: item.appId, caseId: item.caseId,
          policyId: item.policyId, materialClass: item.materialClass, ciphertextHash: item.ciphertextHash, uri: item.uri };
        const previous = receipts.get(item.resourceId);
        if (previous && JSON.stringify(previous) !== JSON.stringify(canonical)) throw new SparkBackendError('conflicting_custody_receipt');
        receipts.set(item.resourceId, canonical);
      };
      for (const entry of db.prepare('SELECT data FROM spark_materials').iterate() as Iterable<BlobRow>) {
        add(unpack<SparkMaterial>(entry.data).receipt);
      }
      for (const entry of db.prepare('SELECT data FROM spark_complaints').iterate() as Iterable<BlobRow>) {
        const complaint = unpack<SparkComplaint>(entry.data);
        if (!complaint || (complaint.status !== 'open' && complaint.status !== 'resolved')) throw new SparkBackendError('invalid_custody_receipt');
        add(complaint.receipt);
        if (complaint.status === 'resolved' || complaint.resolutionReceipt !== undefined) add(complaint.resolutionReceipt);
      }
      for (const entry of db.prepare('SELECT data FROM spark_advice').iterate() as Iterable<BlobRow>) {
        add(unpack<SparkAdviceRecord>(entry.data).receipt);
      }
      for (const entry of db.prepare('SELECT data FROM spark_previews').iterate() as Iterable<BlobRow>) {
        const preview = unpack<SparkPreview>(entry.data);
        if (!preview || typeof preview !== 'object' || Array.isArray(preview)) throw new SparkBackendError('invalid_custody_receipt');
        if (preview.advice !== undefined) add(preview.advice?.receipt);
      }
      const events = db.prepare(`SELECT event,data FROM spark_case_events WHERE event IN
        ('material-added','complaint-opened','complaint-resolved','agent-advice','preview-created',
         'transaction-confirmed','transaction-reverted','transaction-nonce-recorded','transaction-bound','transaction-nonce-consumed')`);
      for (const entry of events.iterate() as Iterable<BlobRow & { event: string }>) {
        const data = unpack<Record<string, any>>(entry.data);
        if (!data || typeof data !== 'object' || Array.isArray(data)) throw new SparkBackendError('invalid_custody_receipt');
        if (['material-added', 'complaint-opened', 'complaint-resolved', 'agent-advice'].includes(entry.event)) {
          add(data.receipt);
          if (entry.event === 'complaint-resolved'
            || (entry.event === 'complaint-opened' && data.resolutionReceipt !== undefined)) add(data.resolutionReceipt);
        } else if (data.advice !== undefined) add(data.advice?.receipt);
      }
      db.exec('COMMIT');
      return [...receipts.values()];
    } catch (error) {
      if (error instanceof SparkBackendError) throw error;
      throw new SparkBackendError('custody_inventory_unavailable');
    } finally { db?.close(); }
  }

  static runtimeState(path: string): { binding?: SparkRuntimeBinding; legacyData: boolean } {
    if (path === ':memory:' || !existsSync(path)) return { legacyData: false };
    const db = new DatabaseSync(path, { readOnly: true });
    try {
      const table = (name: string) => !!db.prepare("SELECT 1 FROM sqlite_master WHERE type='table' AND name=?").get(name);
      const row = table('spark_runtime_binding')
        ? db.prepare('SELECT data FROM spark_runtime_binding WHERE id=1').get() as BlobRow | undefined : undefined;
      const binding = row && unpack<SparkRuntimeBinding>(row.data);
      const legacyData = !binding && (['spark_cases', 'spark_previews'].some(name =>
        table(name) && !!db.prepare(`SELECT 1 FROM ${name} LIMIT 1`).get()));
      return { ...(binding ? { binding } : {}), legacyData };
    } finally { db.close(); }
  }

  constructor(path: string, context: { chainId: number; teaching: Address }) {
    if (path !== ':memory:') {
      mkdirSync(dirname(path), { recursive: true, mode: 0o700 });
      closeSync(openSync(path, 'a', 0o600)); chmodSync(path, 0o600);
    }
    this.db = new DatabaseSync(path);
    try {
      // Initialization runs while the instance is stopped. Disable FK actions only for the atomic table rebuild.
      this.db.exec('PRAGMA busy_timeout = 5000; PRAGMA foreign_keys = OFF');
      this.transaction(() => {
        this.db.exec(`CREATE TABLE IF NOT EXISTS spark_context (id INTEGER PRIMARY KEY CHECK(id=1), data BLOB NOT NULL);
        CREATE TABLE IF NOT EXISTS spark_request_profile (id INTEGER PRIMARY KEY CHECK(id=1), data BLOB NOT NULL);
        CREATE TABLE IF NOT EXISTS spark_runtime_binding (id INTEGER PRIMARY KEY CHECK(id=1), data BLOB NOT NULL);
        CREATE TABLE IF NOT EXISTS spark_cases (sequence INTEGER PRIMARY KEY AUTOINCREMENT, id TEXT NOT NULL UNIQUE,
          revision INTEGER NOT NULL, data BLOB NOT NULL);
        CREATE TABLE IF NOT EXISTS spark_case_sessions (session_id TEXT PRIMARY KEY, case_id TEXT NOT NULL UNIQUE,
          FOREIGN KEY(case_id) REFERENCES spark_cases(id));
        CREATE TABLE IF NOT EXISTS spark_case_participants (case_id TEXT NOT NULL, account TEXT NOT NULL,
          PRIMARY KEY(case_id, account), FOREIGN KEY(case_id) REFERENCES spark_cases(id));
        CREATE TABLE IF NOT EXISTS spark_case_events (sequence INTEGER PRIMARY KEY AUTOINCREMENT, case_id TEXT NOT NULL,
          revision INTEGER NOT NULL, event TEXT NOT NULL, data BLOB NOT NULL, FOREIGN KEY(case_id) REFERENCES spark_cases(id));
        CREATE TABLE IF NOT EXISTS spark_materials (id TEXT PRIMARY KEY, case_id TEXT NOT NULL, data BLOB NOT NULL,
          FOREIGN KEY(case_id) REFERENCES spark_cases(id));
        CREATE TABLE IF NOT EXISTS spark_complaints (id TEXT PRIMARY KEY, case_id TEXT NOT NULL, status TEXT NOT NULL, data BLOB NOT NULL,
          FOREIGN KEY(case_id) REFERENCES spark_cases(id));
        CREATE TABLE IF NOT EXISTS spark_previews (id TEXT PRIMARY KEY, case_id TEXT, actor TEXT NOT NULL, data BLOB NOT NULL,
          FOREIGN KEY(case_id) REFERENCES spark_cases(id));
        CREATE TABLE IF NOT EXISTS spark_operation_events (sequence INTEGER PRIMARY KEY AUTOINCREMENT, preview_id TEXT NOT NULL,
          event TEXT NOT NULL, data BLOB NOT NULL, FOREIGN KEY(preview_id) REFERENCES spark_previews(id));
        CREATE INDEX IF NOT EXISTS spark_operation_events_preview ON spark_operation_events(preview_id);
        CREATE TABLE IF NOT EXISTS spark_schedule_claims (case_id TEXT PRIMARY KEY, preview_id TEXT NOT NULL,
          FOREIGN KEY(case_id) REFERENCES spark_cases(id), FOREIGN KEY(preview_id) REFERENCES spark_previews(id));
        CREATE TABLE IF NOT EXISTS spark_business_claims (preview_id TEXT PRIMARY KEY, case_id TEXT NOT NULL, action TEXT NOT NULL,
          FOREIGN KEY(case_id) REFERENCES spark_cases(id), FOREIGN KEY(preview_id) REFERENCES spark_previews(id));
        CREATE INDEX IF NOT EXISTS spark_business_claims_case_action ON spark_business_claims(case_id,action);
        CREATE TABLE IF NOT EXISTS spark_transaction_nonces (actor TEXT NOT NULL, nonce INTEGER NOT NULL, preview_id TEXT NOT NULL,
          PRIMARY KEY(actor,nonce), FOREIGN KEY(preview_id) REFERENCES spark_previews(id));
        CREATE TABLE IF NOT EXISTS spark_schedule_transactions (preview_id TEXT PRIMARY KEY, hash TEXT NOT NULL,
          FOREIGN KEY(preview_id) REFERENCES spark_previews(id));
        CREATE INDEX IF NOT EXISTS spark_schedule_transactions_hash ON spark_schedule_transactions(hash);
        CREATE TABLE IF NOT EXISTS spark_advice (id TEXT PRIMARY KEY, case_id TEXT NOT NULL, data BLOB NOT NULL,
          FOREIGN KEY(case_id) REFERENCES spark_cases(id));
        CREATE INDEX IF NOT EXISTS spark_advice_case ON spark_advice(case_id);
        CREATE TABLE IF NOT EXISTS spark_advice_previews (intent_key TEXT PRIMARY KEY, preview_id TEXT NOT NULL,
          FOREIGN KEY(preview_id) REFERENCES spark_previews(id));
        CREATE TABLE IF NOT EXISTS spark_references (case_id TEXT NOT NULL, kind TEXT NOT NULL, reference_id TEXT NOT NULL,
          data BLOB NOT NULL, PRIMARY KEY(case_id,kind,reference_id), FOREIGN KEY(case_id) REFERENCES spark_cases(id));
        CREATE TABLE IF NOT EXISTS spark_nonces (account TEXT NOT NULL, nonce TEXT NOT NULL, expires_at INTEGER NOT NULL,
          PRIMARY KEY(account, nonce));`);
        const row = this.db.prepare('SELECT data FROM spark_context WHERE id=1').get() as BlobRow | undefined;
        const stored = row && unpack<{ chainId: number; teaching: Address }>(row.data);
        if (stored && (stored.chainId !== context.chainId || stored.teaching.toLowerCase() !== context.teaching.toLowerCase())) {
          throw new SparkBackendError('context_mismatch', 409);
        }
        if (!stored) this.db.prepare('INSERT INTO spark_context(id,data) VALUES(1,?)').run(serialize(context));
        const columns = this.db.prepare('PRAGMA table_info(spark_complaints)').all() as { name: string }[];
        if (!columns.some(column => column.name === 'status')) {
          this.db.exec('ALTER TABLE spark_complaints ADD COLUMN status TEXT');
          const update = this.db.prepare('UPDATE spark_complaints SET status=? WHERE id=?');
          for (const row of this.db.prepare('SELECT id,data FROM spark_complaints').iterate() as Iterable<{ id: string; data: Uint8Array }>) {
            update.run(unpack<SparkComplaint>(row.data).status, row.id);
          }
        }
        this.db.exec(`CREATE INDEX IF NOT EXISTS spark_complaints_case_status ON spark_complaints(case_id,status);
          CREATE INDEX IF NOT EXISTS spark_complaints_case ON spark_complaints(case_id);
          CREATE INDEX IF NOT EXISTS spark_materials_case ON spark_materials(case_id);
          CREATE INDEX IF NOT EXISTS spark_references_case ON spark_references(case_id)`);
        // Backfill existing case databases and refuse ambiguous legacy session ownership.
        for (const row of this.db.prepare('SELECT data FROM spark_cases').iterate() as Iterable<BlobRow>) {
          const item = unpack<SparkCase>(row.data);
          if (item.sessionId !== undefined) this.registerSession(item.id, item.sessionId);
          if (item.sourceCommitment === undefined) {
            let commitment = sourceDigest(['spark-source-v1', 'legacy-case', item]);
            for (const material of this.db.prepare('SELECT data FROM spark_materials WHERE case_id=? ORDER BY rowid').iterate(item.id) as Iterable<BlobRow>) {
              commitment = sourceDigest(['spark-source-v1', commitment, 'legacy-material', unpack<SparkMaterial>(material.data)]);
            }
            for (const complaint of this.db.prepare('SELECT data FROM spark_complaints WHERE case_id=? ORDER BY rowid').iterate(item.id) as Iterable<BlobRow>) {
              commitment = sourceDigest(['spark-source-v1', commitment, 'legacy-complaint', unpack<SparkComplaint>(complaint.data)]);
            }
            item.sourceCommitment = commitment;
            this.db.prepare('UPDATE spark_cases SET data=? WHERE id=?').run(serialize(item), item.id);
          }
        }
        const previewColumns = this.db.prepare('PRAGMA table_info(spark_previews)').all() as { name: string; notnull: number }[];
        const backfillActors = !previewColumns.some(column => column.name === 'actor');
        if (backfillActors) this.db.exec('ALTER TABLE spark_previews ADD COLUMN actor TEXT');
        const updateActor = backfillActors ? this.db.prepare('UPDATE spark_previews SET actor=? WHERE id=?') : undefined;
        if (updateActor) {
          for (const row of this.db.prepare('SELECT id,data FROM spark_previews').iterate() as Iterable<BlobRow & { id: string }>) {
            updateActor.run(unpack<SparkPreview>(row.data).actor.toLowerCase(), row.id);
          }
        }
        if (previewColumns.find(column => column.name === 'case_id')?.notnull) {
          this.db.exec(`CREATE TABLE spark_previews_nullable (id TEXT PRIMARY KEY, case_id TEXT, actor TEXT NOT NULL, data BLOB NOT NULL,
              FOREIGN KEY(case_id) REFERENCES spark_cases(id));
            INSERT INTO spark_previews_nullable(rowid,id,case_id,actor,data) SELECT rowid,id,case_id,actor,data FROM spark_previews;
            DROP TABLE spark_previews;
            ALTER TABLE spark_previews_nullable RENAME TO spark_previews;`);
        }
        for (const row of this.db.prepare('SELECT data FROM spark_previews').iterate() as Iterable<BlobRow>) {
          const preview = unpack<SparkPreview>(row.data);
          if (preview.identity) {
            if (preview.nonce !== undefined && preview.transactionStatus !== 'nonce-consumed') this.claimNonce(preview, preview.nonce);
            if (preview.caseId !== undefined && preview.action === 'schedule') {
              this.db.prepare('INSERT OR IGNORE INTO spark_schedule_transactions(preview_id,hash) VALUES(?,?)').run(preview.id, preview.identity.hash.toLowerCase());
              if (preview.transactionStatus !== 'reverted' && preview.transactionStatus !== 'nonce-consumed') this.claimSchedule(preview);
            }
            if (preview.caseId !== undefined && ['close-valid', 'cancel-no-fault'].includes(preview.action)
              && preview.transactionStatus !== 'reverted' && preview.transactionStatus !== 'nonce-consumed') {
              this.db.prepare('INSERT OR IGNORE INTO spark_business_claims(preview_id,case_id,action) VALUES(?,?,?)')
                .run(preview.id, preview.caseId, preview.action);
            }
          }
        }
        this.db.exec('CREATE INDEX IF NOT EXISTS spark_previews_actor ON spark_previews(actor)');
        if (this.db.prepare('PRAGMA foreign_key_check').all().length) throw new SparkBackendError('invalid_store_foreign_keys', 409);
      });
      this.db.exec('PRAGMA foreign_keys = ON');
    } catch (error) { this.db.close(); throw error; }
  }

  private requestProfile(): SparkRequestProfile | undefined {
    const row = this.db.prepare('SELECT data FROM spark_request_profile WHERE id=1').get() as BlobRow | undefined;
    return row && unpack<SparkRequestProfile>(row.data);
  }

  private profileKey(profile: SparkRequestProfile): string {
    if (profile.version === 1 && Object.keys(profile).length === 1) return 'v1';
    if (profile.version === 2 && Object.keys(profile).length === 2 && /^0x[0-9a-fA-F]{64}$/.test(profile.audience)) {
      return `v2:${profile.audience.toLowerCase()}`;
    }
    throw new SparkBackendError('invalid_request_profile');
  }

  assertRequestProfile(profile: SparkRequestProfile): void {
    const expected = this.profileKey(profile), current = this.requestProfile();
    if (!current || this.profileKey(current) !== expected) throw new SparkBackendError('request_profile_mismatch', 409);
  }

  bindRequestProfile(profile: SparkRequestProfile): void {
    this.transaction(() => {
      this.profileKey(profile);
      if (this.requestProfile()) return this.assertRequestProfile(profile);
      const legacy = !!this.db.prepare('SELECT 1 FROM spark_cases LIMIT 1').get()
        || !!this.db.prepare('SELECT 1 FROM spark_nonces LIMIT 1').get();
      if (legacy && profile.version !== 1) throw new SparkBackendError('request_profile_migration_required', 409);
      this.db.prepare('INSERT INTO spark_request_profile(id,data) VALUES(1,?)').run(serialize(profile));
    });
  }

  /** Local stopped-operation only. Never exposed through HTTP. Keeps all nonces and histories. */
  migrateRequestProfile(expected: SparkRequestProfile, next: SparkRequestProfile): void {
    this.transaction(() => {
      this.profileKey(next);
      // Databases made before request-profile pinning used the local v1 domain.
      const current = this.requestProfile() ?? { version: 1 as const };
      if (this.profileKey(current) !== this.profileKey(expected)) throw new SparkBackendError('request_profile_mismatch', 409);
      this.db.prepare('INSERT INTO spark_request_profile(id,data) VALUES(1,?) ON CONFLICT(id) DO UPDATE SET data=excluded.data')
        .run(serialize(next));
    });
  }

  runtimeBinding(): SparkRuntimeBinding | undefined {
    const row = this.db.prepare('SELECT data FROM spark_runtime_binding WHERE id=1').get() as BlobRow | undefined;
    return row && unpack<SparkRuntimeBinding>(row.data);
  }

  recordSubmissionRecovery(previewId: string): boolean {
    return this.transaction(() => {
      const preview = this.preview(previewId);
      if (!preview?.identity) throw new SparkBackendError('operation_not_found', 404);
      if (preview.transactionStatus) return false;
      const item = preview.caseId === undefined ? undefined : this.requiredCase(preview.caseId);
      if (preview.advice && preview.advice.sourceCommitment !== item?.sourceCommitment) throw new SparkBackendError('source_changed', 409);
      this.appendPreview(preview, 'submission-recovery-requested',
        { previewId, actor: preview.actor, identity: preview.identity });
      return true;
    });
  }

  recordSubmissionFailure(previewId: string, outcome: { status: 'relay-rejected'|'submission-uncertain'; code: string }): void {
    this.transaction(() => {
      const preview = this.preview(previewId);
      if (!preview?.identity) throw new SparkBackendError('operation_not_found', 404);
      this.appendPreview(preview, 'submission-result',
        { previewId, identity: preview.identity, status: outcome.status, code: outcome.code });
    });
  }

  bindRuntime(value: SparkRuntimeBinding, expected?: SparkRuntimeBinding, allowLegacy = false): boolean {
    const valid = (item: SparkRuntimeBinding) => Number.isSafeInteger(item?.chainId) && item.chainId > 0
      && [item.genesisHash, item.installationHash, item.checkpoint?.blockHash].every(hash => typeof hash === 'string' && /^0x[0-9a-fA-F]{64}$/.test(hash))
      && typeof item.checkpoint?.blockNumber === 'bigint' && item.checkpoint.blockNumber >= 0n;
    if (!valid(value) || (expected !== undefined && !valid(expected))) throw new SparkBackendError('invalid_runtime_binding');
    const sameIdentity = (a: SparkRuntimeBinding, b: SparkRuntimeBinding) => a.chainId === b.chainId
      && a.genesisHash.toLowerCase() === b.genesisHash.toLowerCase() && a.installationHash.toLowerCase() === b.installationHash.toLowerCase();
    const sameCheckpoint = (a: SparkRuntimeBinding, b: SparkRuntimeBinding) => a.checkpoint.blockNumber === b.checkpoint.blockNumber
      && a.checkpoint.blockHash.toLowerCase() === b.checkpoint.blockHash.toLowerCase();
    return this.transaction(() => {
      const current = this.runtimeBinding();
      if (expected && (!current || !sameIdentity(current, expected) || !sameCheckpoint(current, expected))) return false;
      if (!current) {
        if (!allowLegacy && (this.db.prepare('SELECT 1 FROM spark_cases LIMIT 1').get()
          || this.db.prepare('SELECT 1 FROM spark_previews LIMIT 1').get())) return false;
        this.db.prepare('INSERT INTO spark_runtime_binding(id,data) VALUES(1,?)').run(serialize(value));
        return true;
      }
      if (!sameIdentity(current, value) || value.checkpoint.blockNumber < current.checkpoint.blockNumber) return false;
      if (value.checkpoint.blockNumber === current.checkpoint.blockNumber) return sameCheckpoint(current, value);
      if (!expected) return false;
      this.db.prepare('UPDATE spark_runtime_binding SET data=? WHERE id=1').run(serialize(value));
      return true;
    });
  }

  create(input: Omit<SparkCase, 'id' | 'sequence' | 'revision' | 'sourceCommitment'>): SparkCase {
    return this.transaction(() => {
      const id = randomUUID();
      const initial: Omit<SparkCase, 'sourceCommitment'> = { id, sequence: 0, revision: 1, createdBy: input.createdBy, teacher: input.teacher,
        students: [...input.students], scheduledAt: input.scheduledAt,
        ...(input.proposal === undefined ? {} : { proposal: structuredClone(input.proposal) }),
        ...(input.sessionId === undefined ? {} : { sessionId: input.sessionId }) };
      const result = this.db.prepare('INSERT INTO spark_cases(id,revision,data) VALUES(?,?,?)').run(id, initial.revision, serialize(initial));
      initial.sequence = Number(result.lastInsertRowid);
      const item: SparkCase = { ...initial, sourceCommitment: sourceDigest(['spark-source-v1', 'case-created', initial]) };
      this.db.prepare('UPDATE spark_cases SET data=? WHERE id=?').run(serialize(item), id);
      if (item.sessionId !== undefined) this.registerSession(id, item.sessionId);
      const add = this.db.prepare('INSERT INTO spark_case_participants(case_id,account) VALUES(?,?)');
      for (const account of new Set([item.createdBy, item.teacher, ...item.students].map(value => value.toLowerCase()))) add.run(id, account);
      this.append(item, 'created', item);
      return structuredClone(item);
    });
  }

  get(id: string): SparkCase | undefined {
    const row = this.db.prepare('SELECT data FROM spark_cases WHERE id=?').get(id) as BlobRow | undefined;
    return row && unpack<SparkCase>(row.data);
  }

  bySession(sessionId: bigint): SparkCase | undefined {
    const row = this.db.prepare('SELECT case_id FROM spark_case_sessions WHERE session_id=?').get(sessionId.toString()) as { case_id: string } | undefined;
    return row && this.get(row.case_id);
  }

  list(account: Address | undefined, page?: Page): { items: SparkCase[]; next?: number } {
    const { after, limit } = pageValues(page);
    const rows = (account === undefined
      ? this.db.prepare('SELECT c.data FROM spark_cases c WHERE c.sequence>? ORDER BY c.sequence LIMIT ?').all(after, limit + 1)
      : this.db.prepare('SELECT c.data FROM spark_cases c JOIN spark_case_participants p ON p.case_id=c.id WHERE p.account=? AND c.sequence>? ORDER BY c.sequence LIMIT ?')
        .all(account.toLowerCase(), after, limit + 1)) as BlobRow[];
    const items = rows.slice(0, limit).map(row => unpack<SparkCase>(row.data));
    return { items, ...(rows.length > limit ? { next: items[items.length - 1].sequence } : {}) };
  }

  operations(actor: Address, page?: Page): { items: SparkOperationSummary[]; next?: number } {
    const { after, limit } = pageValues(page);
    const rows = this.db.prepare('SELECT rowid AS cursor,data FROM spark_previews WHERE actor=? AND rowid>? ORDER BY rowid LIMIT ?')
      .all(actor.toLowerCase(), after, limit + 1) as { cursor: number; data: Uint8Array }[];
    const items = rows.slice(0, limit).map(row => {
      const { id, caseId, actor, action, expiresAt, identity, nonce, transactionStatus, subject, createdId } = unpack<SparkPreview>(row.data);
      return { id, ...(caseId === undefined ? { ...(subject === undefined ? {} : { subject }),
        ...(createdId === undefined ? {} : { createdId }) } : { caseId }), actor, action, expiresAt,
        ...(identity === undefined ? {} : { identity: { key: identity.key, hash: identity.hash } }),
        ...(nonce === undefined ? {} : { nonce }), ...(transactionStatus === undefined ? {} : { transactionStatus }) };
    });
    return { items, ...(rows.length > limit ? { next: rows[limit - 1].cursor } : {}) };
  }

  attachSession(id: string, sessionId: bigint, expectedRevision: number): SparkCase {
    this.validateRevision(expectedRevision);
    return this.transaction(() => {
      const item = this.requiredCase(id, expectedRevision);
      if (item.sessionId !== undefined) throw new SparkBackendError('session_already_attached', 409);
      this.registerSession(id, sessionId);
      item.sessionId = sessionId;
      this.change(item, 'session-attached', { sessionId });
      return structuredClone(item);
    });
  }

  addMaterial(caseId: string, input: SparkMaterialInput): SparkMaterial {
    return this.transaction(() => {
      const item = this.requiredCase(caseId);
      if (input.subject.sessionId !== item.sessionId
        || input.subject.proposalHash !== (item.sessionId === undefined && item.proposal ? sourceDigest(item.proposal) : undefined)) {
        throw new SparkBackendError('source_subject_mismatch', 409);
      }
      // Select the declared fields: material bodies and other caller extras are not stored.
      const material: SparkMaterial = { id: randomUUID(), caseId, owner: input.owner, kind: input.kind,
        subject: structuredClone(input.subject), actions: [...input.actions], disclosures: structuredClone(input.disclosures),
        contentHashes: [...input.contentHashes], signature: input.signature, requestHash: input.requestHash,
        receipt: structuredClone(input.receipt) };
      this.db.prepare('INSERT INTO spark_materials(id,case_id,data) VALUES(?,?,?)').run(material.id, caseId, serialize(material));
      this.change(item, 'material-added', material);
      return structuredClone(material);
    });
  }

  materials(caseId: string): SparkMaterial[] {
    this.requiredCase(caseId);
    const rows = this.db.prepare('SELECT data FROM spark_materials WHERE case_id=? ORDER BY rowid').all(caseId) as BlobRow[];
    return rows.map(row => unpack<SparkMaterial>(row.data));
  }

  getMaterial(caseId: string, id: string): SparkMaterial | undefined {
    this.requiredCase(caseId);
    const row = this.db.prepare('SELECT data FROM spark_materials WHERE id=? AND case_id=?').get(id, caseId) as BlobRow | undefined;
    return row && unpack<SparkMaterial>(row.data);
  }

  materialPage(caseId: string, page?: Page): { items: SparkMaterial[]; next?: number } {
    this.requiredCase(caseId);
    const { after, limit } = pageValues(page);
    const rows = this.db.prepare('SELECT rowid AS cursor,data FROM spark_materials WHERE case_id=? AND rowid>? ORDER BY rowid LIMIT ?')
      .all(caseId, after, limit + 1) as { cursor: number; data: Uint8Array }[];
    return { items: rows.slice(0, limit).map(row => unpack<SparkMaterial>(row.data)),
      ...(rows.length > limit ? { next: rows[limit - 1].cursor } : {}) };
  }

  revokeMaterial(caseId: string, materialId: string, actor: Address): void {
    this.transaction(() => {
      const item = this.requiredCase(caseId);
      const row = this.db.prepare('SELECT data FROM spark_materials WHERE id=? AND case_id=?').get(materialId, caseId) as BlobRow | undefined;
      if (!row) throw new SparkBackendError('material_not_found', 404);
      const material = unpack<SparkMaterial>(row.data);
      if (material.owner.toLowerCase() !== actor.toLowerCase()) throw new SparkBackendError('material_forbidden', 403);
      if (material.revoked) return;
      material.revoked = true;
      this.db.prepare('UPDATE spark_materials SET data=? WHERE id=? AND case_id=?').run(serialize(material), materialId, caseId);
      this.change(item, 'material-revoked', { materialId, actor });
    });
  }

  fileComplaint(caseId: string, actor: Address, receipt: unknown): SparkComplaint {
    return this.transaction(() => {
      const item = this.requiredCase(caseId);
      const complaint: SparkComplaint = { id: randomUUID(), caseId, status: 'open', actor, receipt: structuredClone(receipt) };
      this.db.prepare('INSERT INTO spark_complaints(id,case_id,status,data) VALUES(?,?,?,?)').run(complaint.id, caseId, complaint.status, serialize(complaint));
      this.change(item, 'complaint-opened', complaint);
      return structuredClone(complaint);
    });
  }

  resolveComplaint(caseId: string, complaintId: string, actor: Address, expectedRevision: number, receipt: unknown): void {
    this.validateRevision(expectedRevision);
    this.transaction(() => {
      const item = this.requiredCase(caseId, expectedRevision);
      const row = this.db.prepare('SELECT data FROM spark_complaints WHERE id=? AND case_id=?').get(complaintId, caseId) as BlobRow | undefined;
      if (!row) throw new SparkBackendError('complaint_not_found', 404);
      const complaint = unpack<SparkComplaint>(row.data);
      if (complaint.status !== 'open') throw new SparkBackendError('complaint_already_resolved', 409);
      complaint.status = 'resolved'; complaint.resolvedBy = actor; complaint.resolutionReceipt = structuredClone(receipt);
      this.db.prepare('UPDATE spark_complaints SET status=?,data=? WHERE id=?').run(complaint.status, serialize(complaint), complaintId);
      this.change(item, 'complaint-resolved', complaint);
    });
  }

  complaints(caseId: string): SparkComplaint[] {
    this.requiredCase(caseId);
    const rows = this.db.prepare('SELECT data FROM spark_complaints WHERE case_id=? ORDER BY rowid').all(caseId) as BlobRow[];
    return rows.map(row => unpack<SparkComplaint>(row.data));
  }

  getComplaint(caseId: string, id: string): SparkComplaint | undefined {
    this.requiredCase(caseId);
    const row = this.db.prepare('SELECT data FROM spark_complaints WHERE id=? AND case_id=?').get(id, caseId) as BlobRow | undefined;
    return row && unpack<SparkComplaint>(row.data);
  }

  hasOpenComplaint(caseId: string): boolean {
    this.requiredCase(caseId);
    return !!this.db.prepare("SELECT 1 FROM spark_complaints WHERE case_id=? AND status='open' LIMIT 1").get(caseId);
  }

  complaintPage(caseId: string, page?: Page & { status?: SparkComplaint['status'] }): { items: SparkComplaint[]; next?: number } {
    this.requiredCase(caseId);
    const { after, limit } = pageValues(page);
    if (page?.status !== undefined && page.status !== 'open' && page.status !== 'resolved') throw new SparkBackendError('invalid_page');
    const rows = (page?.status === undefined
      ? this.db.prepare('SELECT rowid AS cursor,data FROM spark_complaints WHERE case_id=? AND rowid>? ORDER BY rowid LIMIT ?').all(caseId, after, limit + 1)
      : this.db.prepare('SELECT rowid AS cursor,data FROM spark_complaints WHERE case_id=? AND status=? AND rowid>? ORDER BY rowid LIMIT ?').all(caseId, page.status, after, limit + 1)
    ) as { cursor: number; data: Uint8Array }[];
    return { items: rows.slice(0, limit).map(row => unpack<SparkComplaint>(row.data)),
      ...(rows.length > limit ? { next: rows[limit - 1].cursor } : {}) };
  }

  history(caseId: string, page?: Page): { items: SparkCaseEvent[]; next?: number } {
    this.requiredCase(caseId);
    const { after, limit } = pageValues(page);
    const rows = this.db.prepare('SELECT sequence,case_id,revision,event,data FROM spark_case_events WHERE case_id=? AND sequence>? ORDER BY sequence LIMIT ?')
      .all(caseId, after, limit + 1) as { sequence: number; case_id: string; revision: number; event: string; data: Uint8Array }[];
    const items = rows.slice(0, limit).map(row => ({ sequence: row.sequence, caseId: row.case_id,
      revision: row.revision, event: row.event, data: unpack<unknown>(row.data) }));
    return { items, ...(rows.length > limit ? { next: items[items.length - 1].sequence } : {}) };
  }

  /** Callers authenticate the preview owner before exposing this local history. */
  operationHistory(previewId: string, page?: Page): { items: SparkOperationEvent[]; next?: number } {
    if (!this.preview(previewId)) throw new SparkBackendError('preview_not_found', 404);
    const { after, limit } = pageValues(page);
    const rows = this.db.prepare('SELECT sequence,event,data FROM spark_operation_events WHERE preview_id=? AND sequence>? ORDER BY sequence LIMIT ?')
      .all(previewId, after, limit + 1) as { sequence: number; event: string; data: Uint8Array }[];
    const items = rows.slice(0, limit).map(row => ({ sequence: row.sequence, previewId, event: row.event, data: unpack<unknown>(row.data) }));
    return { items, ...(rows.length > limit ? { next: items[items.length - 1].sequence } : {}) };
  }

  createPreview(input: Omit<SparkPreview, 'id' | 'identity' | 'transactionStatus' | 'createdId'>): SparkPreview {
    return this.transaction(() => this.insertPreview(input));
  }

  private insertPreview(input: Omit<SparkPreview, 'id' | 'identity' | 'transactionStatus' | 'createdId'>): SparkPreview {
      if (input.caseId === undefined) {
        if (input.subject?.kind !== 'research' || input.advice) throw new SparkBackendError('invalid_preview_subject');
      } else {
        this.requiredCase(input.caseId);
        if (input.subject !== undefined) throw new SparkBackendError('invalid_preview_subject');
      }
      const preview: SparkPreview = { id: randomUUID(), ...(input.caseId === undefined
        ? { subject: structuredClone(input.subject) } : { caseId: input.caseId }), actor: input.actor,
        action: input.action, call: structuredClone(input.call), expiresAt: input.expiresAt,
        ...(input.advice ? { advice: structuredClone(input.advice) } : {}),
        ...(input.created ? { created: structuredClone(input.created) } : {}) };
      this.db.prepare('INSERT INTO spark_previews(id,case_id,actor,data) VALUES(?,?,?,?)').run(preview.id, preview.caseId ?? null, preview.actor.toLowerCase(), serialize(preview));
      this.appendPreview(preview, 'preview-created', preview);
      return structuredClone(preview);
  }

  advicePreview(intentKey: Hex): SparkPreview | undefined {
    const row = this.db.prepare('SELECT preview_id FROM spark_advice_previews WHERE intent_key=?').get(intentKey) as { preview_id: string } | undefined;
    return row && this.preview(row.preview_id);
  }

  createAdvicePreview(input: Omit<SparkPreview, 'id'|'identity'|'transactionStatus'|'createdId'> & { advice: SparkAdviceLink },
    intentKey: Hex, now: number): SparkPreview {
    const caseId = input.caseId;
    if (caseId === undefined) throw new SparkBackendError('invalid_preview_subject');
    return this.transaction(() => {
      const prior = this.advicePreview(intentKey);
      if (prior?.identity && prior.transactionStatus !== 'reverted' && prior.transactionStatus !== 'nonce-consumed') return prior;
      const current = this.requiredCase(caseId);
      if (current.sourceCommitment !== input.advice.sourceCommitment
        || (prior && !prior.transactionStatus && prior.expiresAt >= now
          && prior.advice?.sourceCommitment !== current.sourceCommitment)) throw new SparkBackendError('source_changed', 409);
      if (prior && !prior.transactionStatus && prior.expiresAt >= now) return prior;
      const preview = this.insertPreview(input);
      this.db.prepare(`INSERT INTO spark_advice_previews(intent_key,preview_id) VALUES(?,?)
        ON CONFLICT(intent_key) DO UPDATE SET preview_id=excluded.preview_id`).run(intentKey, preview.id);
      return preview;
    });
  }

  preview(id: string): SparkPreview | undefined {
    const row = this.db.prepare('SELECT data FROM spark_previews WHERE id=?').get(id) as BlobRow | undefined;
    return row && unpack<SparkPreview>(row.data);
  }

  /** Every outstanding legacy attempt is retained, including multiple pre-existing claims. */
  businessClaims(caseId: string, action: 'schedule'|'close-valid'|'cancel-no-fault'): SparkPreview[] {
    this.requiredCase(caseId);
    const rows = action === 'schedule'
      ? this.db.prepare('SELECT p.data FROM spark_schedule_claims c JOIN spark_previews p ON p.id=c.preview_id WHERE c.case_id=?').all(caseId) as BlobRow[]
      : this.db.prepare('SELECT p.data FROM spark_business_claims c JOIN spark_previews p ON p.id=c.preview_id WHERE c.case_id=? AND c.action=?').all(caseId, action) as BlobRow[];
    return rows.map(row => unpack<SparkPreview>(row.data));
  }

  pendingScheduleByTransaction(hash: Hex): SparkPreview | undefined {
    const rows = this.db.prepare(`SELECT p.data FROM spark_schedule_transactions t
      JOIN spark_previews p ON p.id=t.preview_id WHERE t.hash=? LIMIT 2`).all(hash.toLowerCase()) as BlobRow[];
    if (rows.length > 1) throw new SparkBackendError('ambiguous_schedule_transaction', 409);
    const preview = rows[0] && unpack<SparkPreview>(rows[0].data);
    return preview && preview.caseId !== undefined && (!preview.transactionStatus || preview.transactionStatus === 'confirmed')
      && this.requiredCase(preview.caseId).sessionId === undefined ? preview : undefined;
  }

  /** The caller has verified the exact creation receipt, not merely matching course text. */
  reconcileScheduledSession(previewId: string, sessionId: bigint, expectedRevision?: number): SparkCase {
    return this.transaction(() => {
      const preview = this.preview(previewId);
      if (!preview?.identity || preview.action !== 'schedule' || preview.caseId === undefined) throw new SparkBackendError('schedule_not_bound', 409);
      if (preview.transactionStatus && preview.transactionStatus !== 'confirmed') throw new SparkBackendError('transaction_status_conflict', 409);
      const item = this.requiredCase(preview.caseId);
      if (item.sessionId === undefined) {
        if (expectedRevision !== undefined) this.requiredCase(item.id, expectedRevision);
        this.registerSession(item.id, sessionId); item.sessionId = sessionId;
        this.change(item, 'session-attached', { sessionId });
      } else if (item.sessionId !== sessionId) throw new SparkBackendError('session_mismatch', 409);
      if (preview.transactionStatus !== 'confirmed') {
        preview.transactionStatus = 'confirmed';
        this.db.prepare('UPDATE spark_previews SET data=? WHERE id=?').run(serialize(preview), preview.id);
        this.append(item, 'transaction-confirmed', preview);
      }
      return structuredClone(item);
    });
  }

  addReference(caseId: string, reference: SparkReference): void {
    if (!['evidence', 'object', 'recognition', 'request', 'challenge', 'finding'].includes(reference?.kind)
      || typeof reference.id !== 'bigint' || reference.id < 0n || typeof reference.transactionHash !== 'string'
      || !/^0x[0-9a-fA-F]{64}$/.test(reference.transactionHash)) throw new SparkBackendError('invalid_reference');
    this.transaction(() => {
      const item = this.requiredCase(caseId);
      const row = this.db.prepare('SELECT data FROM spark_references WHERE case_id=? AND kind=? AND reference_id=?')
        .get(caseId, reference.kind, reference.id.toString()) as BlobRow | undefined;
      if (row) {
        const existing = unpack<SparkReference>(row.data);
        if (existing.transactionHash.toLowerCase() !== reference.transactionHash.toLowerCase()) {
          throw new SparkBackendError('reference_conflict', 409);
        }
        return;
      }
      const captured: SparkReference = { kind: reference.kind, id: reference.id, transactionHash: reference.transactionHash };
      this.db.prepare('INSERT INTO spark_references(case_id,kind,reference_id,data) VALUES(?,?,?,?)')
        .run(caseId, captured.kind, captured.id.toString(), serialize(captured));
      this.append(item, 'reference-added', captured);
    });
  }

  references(caseId: string): SparkReference[] {
    this.requiredCase(caseId);
    const rows = this.db.prepare('SELECT data FROM spark_references WHERE case_id=? ORDER BY rowid').all(caseId) as BlobRow[];
    return rows.map(row => unpack<SparkReference>(row.data));
  }

  referencePage(caseId: string, page?: Page): { items: SparkReference[]; total: number; next?: number } {
    this.requiredCase(caseId);
    const { after, limit } = pageValues(page);
    const total = (this.db.prepare('SELECT COUNT(*) AS total FROM spark_references WHERE case_id=?').get(caseId) as { total: number }).total;
    const rows = this.db.prepare('SELECT rowid AS cursor,data FROM spark_references WHERE case_id=? AND rowid>? ORDER BY rowid LIMIT ?')
      .all(caseId, after, limit + 1) as { cursor: number; data: Uint8Array }[];
    return { items: rows.slice(0, limit).map(row => unpack<SparkReference>(row.data)), total,
      ...(rows.length > limit ? { next: rows[limit - 1].cursor } : {}) };
  }

  recentReferences(caseId: string, limit = 100): { items: SparkReference[]; total: number; truncated: boolean } {
    this.requiredCase(caseId);
    pageValues({ limit });
    const total = (this.db.prepare('SELECT COUNT(*) AS total FROM spark_references WHERE case_id=?').get(caseId) as { total: number }).total;
    const rows = this.db.prepare('SELECT data FROM spark_references WHERE case_id=? ORDER BY rowid DESC LIMIT ?').all(caseId, limit) as BlobRow[];
    return { items: rows.reverse().map(row => unpack<SparkReference>(row.data)), total, truncated: total > limit };
  }

  hasReference(caseId: string, kind: SparkReference['kind'], id: bigint): boolean {
    this.requiredCase(caseId);
    return !!this.db.prepare('SELECT 1 FROM spark_references WHERE case_id=? AND kind=? AND reference_id=?')
      .get(caseId, kind, id.toString());
  }

  bindTransaction(previewId: string, identity: Pick<TransactionRecord, 'key' | 'hash'>, nonce?: number): SparkPreview {
    if (typeof identity?.key !== 'string' || !identity.key.trim() || typeof identity.hash !== 'string'
      || !/^0x[0-9a-fA-F]{64}$/.test(identity.hash)) throw new SparkBackendError('invalid_identity');
    return this.transaction(() => {
      const preview = this.preview(previewId);
      if (!preview) throw new SparkBackendError('preview_not_found', 404);
      if (nonce !== undefined && (!Number.isSafeInteger(nonce) || nonce < 0)) throw new SparkBackendError('invalid_nonce');
      if (preview.nonce !== undefined && nonce !== undefined && nonce !== preview.nonce) throw new SparkBackendError('identity_conflict', 409);
      if (preview.identity) {
        if (preview.identity.key !== identity.key || preview.identity.hash !== identity.hash) {
          throw new SparkBackendError('identity_conflict', 409);
        }
        if (nonce !== undefined && preview.nonce === undefined) {
          this.claimNonce(preview, nonce); preview.nonce = nonce;
          this.db.prepare('UPDATE spark_previews SET data=? WHERE id=?').run(serialize(preview), preview.id);
          this.appendPreview(preview, 'transaction-nonce-recorded', preview);
        }
        return preview;
      }
      const item = preview.caseId === undefined ? undefined : this.requiredCase(preview.caseId);
      if (preview.advice && preview.advice.sourceCommitment !== item?.sourceCommitment) throw new SparkBackendError('source_changed', 409);
      if (nonce !== undefined) { this.claimNonce(preview, nonce); preview.nonce = nonce; }
      if (item && preview.action === 'schedule') this.claimSchedule(preview);
      if (item && (preview.action === 'close-valid' || preview.action === 'cancel-no-fault')) {
        const row = this.db.prepare('SELECT preview_id FROM spark_business_claims WHERE case_id=? AND action=? LIMIT 1')
          .get(item.id, preview.action) as { preview_id: string } | undefined;
        if (row && row.preview_id !== preview.id) throw new SparkBackendError('operation_in_progress', 409);
        this.db.prepare('INSERT OR IGNORE INTO spark_business_claims(preview_id,case_id,action) VALUES(?,?,?)')
          .run(preview.id, item.id, preview.action);
      }
      preview.identity = { key: identity.key, hash: identity.hash };
      if (item && preview.action === 'schedule') this.db.prepare('INSERT INTO spark_schedule_transactions(preview_id,hash) VALUES(?,?)')
        .run(preview.id, identity.hash.toLowerCase());
      this.db.prepare('UPDATE spark_previews SET data=? WHERE id=?').run(serialize(preview), preview.id);
      this.appendPreview(preview, 'transaction-bound', preview);
      return structuredClone(preview);
    });
  }

  /** Caller verifies the canonical replacement receipt; this records its effect on the original local attempt only. */
  resolveNonce(previewId: string, proof: SparkNonceProof): SparkPreview {
    return this.transaction(() => {
      const preview = this.preview(previewId);
      if (!preview?.identity) throw new SparkBackendError('transaction_not_bound', 409);
      if (!proof || typeof proof.from !== 'string' || proof.from.toLowerCase() !== preview.actor.toLowerCase()
        || !Number.isSafeInteger(proof.nonce) || proof.nonce < 0 || (preview.nonce !== undefined && preview.nonce !== proof.nonce)
        || typeof proof.transactionHash !== 'string' || !/^0x[0-9a-fA-F]{64}$/.test(proof.transactionHash)
        || proof.transactionHash.toLowerCase() === preview.identity.hash.toLowerCase()
        || typeof proof.blockNumber !== 'bigint' || proof.blockNumber < 0n
        || typeof proof.blockHash !== 'string' || !/^0x[0-9a-fA-F]{64}$/.test(proof.blockHash)
        || !['success', 'reverted'].includes(proof.status)) throw new SparkBackendError('invalid_nonce_proof', 409);
      if (preview.transactionStatus === 'nonce-consumed' && sourceDigest(preview.nonceResolution) === sourceDigest(proof)) return preview;
      if (preview.transactionStatus) throw new SparkBackendError('transaction_status_conflict', 409);
      preview.nonce = proof.nonce; preview.nonceResolution = structuredClone(proof); preview.transactionStatus = 'nonce-consumed';
      this.db.prepare('UPDATE spark_previews SET data=? WHERE id=?').run(serialize(preview), preview.id);
      if (preview.caseId !== undefined) this.db.prepare('DELETE FROM spark_schedule_claims WHERE case_id=? AND preview_id=?').run(preview.caseId, preview.id);
      this.db.prepare('DELETE FROM spark_business_claims WHERE preview_id=?').run(preview.id);
      this.appendPreview(preview, 'transaction-nonce-consumed', preview);
      return structuredClone(preview);
    });
  }

  observeTransaction(previewId: string, status: 'confirmed' | 'reverted', createdId?: bigint): void {
    if (status !== 'confirmed' && status !== 'reverted') throw new SparkBackendError('invalid_transaction_status');
    if (createdId !== undefined && (typeof createdId !== 'bigint' || createdId < 0n || status !== 'confirmed')) {
      throw new SparkBackendError('invalid_created_id');
    }
    this.transaction(() => {
      const preview = this.preview(previewId);
      if (!preview) throw new SparkBackendError('preview_not_found', 404);
      if (!preview.identity) throw new SparkBackendError('transaction_not_bound', 409);
      if (createdId !== undefined && preview.caseId !== undefined) throw new SparkBackendError('invalid_created_id');
      if (preview.createdId !== undefined && createdId !== undefined && preview.createdId !== createdId) {
        throw new SparkBackendError('created_id_conflict', 409);
      }
      if (preview.transactionStatus === status) {
        if (createdId !== undefined && preview.createdId !== createdId) throw new SparkBackendError('created_id_conflict', 409);
        return;
      }
      if (preview.transactionStatus) throw new SparkBackendError('transaction_status_conflict', 409);
      preview.transactionStatus = status;
      if (createdId !== undefined) preview.createdId = createdId;
      this.db.prepare('UPDATE spark_previews SET data=? WHERE id=?').run(serialize(preview), preview.id);
      if (preview.caseId !== undefined && preview.action === 'schedule' && status === 'reverted') {
        this.db.prepare('DELETE FROM spark_schedule_claims WHERE case_id=? AND preview_id=?').run(preview.caseId, preview.id);
      }
      if (status === 'reverted') this.db.prepare('DELETE FROM spark_business_claims WHERE preview_id=?').run(preview.id);
      this.appendPreview(preview, `transaction-${status}`, preview);
    });
  }

  saveAdvice(caseId: string, input: Omit<SparkAdviceRecord, 'caseId'>): void {
    this.transaction(() => {
      const item = this.requiredCase(caseId);
      if (this.advice(input.id)) throw new SparkBackendError('advice_already_exists', 409);
      const record: SparkAdviceRecord = { id: input.id, caseId, owner: input.owner, status: input.status,
        provider: input.provider, model: input.model, receipt: structuredClone(input.receipt),
        ...(input.hash ? { hash: input.hash } : {}), ...(input.sourceCommitment ? { sourceCommitment: input.sourceCommitment } : {}) };
      this.db.prepare('INSERT INTO spark_advice(id,case_id,data) VALUES(?,?,?)').run(record.id, caseId, serialize(record));
      this.append(item, 'agent-advice', record);
    });
  }

  advice(id: string): SparkAdviceRecord | undefined {
    const row = this.db.prepare('SELECT data FROM spark_advice WHERE id=?').get(id) as BlobRow | undefined;
    return row && unpack<SparkAdviceRecord>(row.data);
  }

  advicePage(caseId: string, page?: Page): { items: SparkAdviceRecord[]; next?: number } {
    this.requiredCase(caseId); const { after, limit } = pageValues(page);
    const rows = this.db.prepare('SELECT rowid AS cursor,data FROM spark_advice WHERE case_id=? AND rowid>? ORDER BY rowid LIMIT ?')
      .all(caseId, after, limit + 1) as { cursor: number; data: Uint8Array }[];
    return { items: rows.slice(0, limit).map(row => unpack<SparkAdviceRecord>(row.data)),
      ...(rows.length > limit ? { next: rows[limit - 1].cursor } : {}) };
  }

  consumeNonce(account: Address, nonce: string, expiresAt: number, now: number): boolean {
    if (typeof nonce !== 'string' || !nonce.trim() || !Number.isSafeInteger(expiresAt)
      || !Number.isSafeInteger(now) || expiresAt <= now) throw new SparkBackendError('invalid_nonce');
    return this.transaction(() => {
      this.db.prepare('DELETE FROM spark_nonces WHERE expires_at<=?').run(now);
      return !!this.db.prepare('INSERT OR IGNORE INTO spark_nonces(account,nonce,expires_at) VALUES(?,?,?)')
        .run(account.toLowerCase(), nonce, expiresAt).changes;
    });
  }

  close(): void { this.db.close(); }
  private claimNonce(preview: SparkPreview, nonce: number): void {
    const actor = preview.actor.toLowerCase();
    const row = this.db.prepare('SELECT preview_id FROM spark_transaction_nonces WHERE actor=? AND nonce=?')
      .get(actor, nonce) as { preview_id: string } | undefined;
    if (row && row.preview_id !== preview.id) throw new SparkBackendError('nonce_in_progress', 409);
    if (!row) this.db.prepare('INSERT INTO spark_transaction_nonces(actor,nonce,preview_id) VALUES(?,?,?)').run(actor, nonce, preview.id);
  }
  private claimSchedule(preview: SparkPreview): void {
    if (preview.caseId === undefined) throw new SparkBackendError('case_not_found', 404);
    const row = this.db.prepare('SELECT preview_id FROM spark_schedule_claims WHERE case_id=?').get(preview.caseId) as { preview_id: string } | undefined;
    if (row && row.preview_id !== preview.id) throw new SparkBackendError('schedule_in_progress', 409);
    if (!row) this.db.prepare('INSERT INTO spark_schedule_claims(case_id,preview_id) VALUES(?,?)').run(preview.caseId, preview.id);
  }
  private registerSession(caseId: string, sessionId: bigint): void {
    if (typeof sessionId !== 'bigint' || sessionId < 0n) throw new SparkBackendError('invalid_session');
    const row = this.db.prepare('SELECT case_id FROM spark_case_sessions WHERE session_id=?').get(sessionId.toString()) as { case_id: string } | undefined;
    if (row && row.case_id !== caseId) throw new SparkBackendError('session_already_registered', 409);
    if (!row) this.db.prepare('INSERT INTO spark_case_sessions(session_id,case_id) VALUES(?,?)').run(sessionId.toString(), caseId);
  }
  private validateRevision(revision: number): void {
    if (!Number.isSafeInteger(revision) || revision < 1) throw new SparkBackendError('invalid_revision');
  }
  private requiredCase(id: string, expectedRevision?: number): SparkCase {
    const item = this.get(id);
    if (!item) throw new SparkBackendError('case_not_found', 404);
    if (expectedRevision !== undefined && (!Number.isSafeInteger(expectedRevision) || item.revision !== expectedRevision)) {
      throw new SparkBackendError('revision_conflict', 409);
    }
    return item;
  }
  private change(item: SparkCase, event: string, data: unknown): void {
    item.revision++;
    item.sourceCommitment = sourceDigest(['spark-source-v1', item.sourceCommitment, event, data]);
    this.db.prepare('UPDATE spark_cases SET revision=?,data=? WHERE id=?').run(item.revision, serialize(item), item.id);
    this.append(item, event, data);
  }
  private append(item: SparkCase, event: string, data: unknown): void {
    this.db.prepare('INSERT INTO spark_case_events(case_id,revision,event,data) VALUES(?,?,?,?)')
      .run(item.id, item.revision, event, serialize(data));
  }
  private appendPreview(preview: SparkPreview, event: string, data: unknown): void {
    if (preview.caseId !== undefined) this.append(this.requiredCase(preview.caseId), event, data);
    else this.db.prepare('INSERT INTO spark_operation_events(preview_id,event,data) VALUES(?,?,?)')
      .run(preview.id, event, serialize(data));
  }
  private transaction<T>(fn: () => T): T {
    this.db.exec('BEGIN IMMEDIATE');
    try { const result = fn(); this.db.exec('COMMIT'); return result; }
    catch (error) { this.db.exec('ROLLBACK'); throw error; }
  }
}
