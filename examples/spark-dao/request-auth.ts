import { randomBytes } from 'node:crypto';
import { isAddress, recoverMessageAddress, zeroAddress, type Address, type Hex, type LocalAccount } from 'viem';
import type { AvaWallet } from '@ava-protocol/sdk';
import { SparkBackendError, SparkCaseStore } from './case-store.ts';

export interface SparkRequestAuth { account: Address; nonce: string; expiresAt: number; signature: Hex }
export interface SparkRequestScope {
  chainId: number; teaching: Address;
  /** Trusted service identity; all three v2 fields are required together. */
  audience?: Hex; genesisHash?: Hex; installationHash?: Hex;
}
const canonical = (value: unknown): unknown => Array.isArray(value) ? value.map(canonical)
  : value && typeof value === 'object' ? Object.fromEntries(Object.entries(value).sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)
    .map(([key, item]) => [key, canonical(item)])) : value;
export function sparkRequestMessage(scope: SparkRequestScope, method: string, path: string, body: unknown,
  auth: Omit<SparkRequestAuth, 'signature'>): string {
  const remote = scope.audience !== undefined;
  if ([scope.audience, scope.genesisHash, scope.installationHash].some(value => value !== undefined)
    && (!remote || ![scope.audience, scope.genesisHash, scope.installationHash].every(value => typeof value === 'string' && /^0x[0-9a-fA-F]{64}$/.test(value)))) {
    throw new Error('invalid_request_scope');
  }
  return JSON.stringify(canonical({ domain: remote ? 'ava.spark.backend.request.v2' : 'ava.spark.backend.request.v1',
    chainId: scope.chainId, teaching: scope.teaching.toLowerCase(),
    ...(remote ? { audience: scope.audience!.toLowerCase(), genesisHash: scope.genesisHash!.toLowerCase(),
      installationHash: scope.installationHash!.toLowerCase() } : {}),
    method: method.toUpperCase(), path, body: body ?? null,
    account: auth.account.toLowerCase(), nonce: auth.nonce, expiresAt: auth.expiresAt }));
}
/** App request authentication only; transaction signing remains separate and owned by the actor. */
export async function signSparkRequest(wallet: AvaWallet | LocalAccount, scope: SparkRequestScope, method: string, path: string,
  body?: unknown, now = Math.floor(Date.now() / 1000)) {
  const signer = 'account' in wallet ? wallet.account : wallet;
  const auth = { account: signer.address, nonce: randomBytes(24).toString('base64url'), expiresAt: now + 120 };
  const message = sparkRequestMessage(scope, method, path, body, auth);
  const signature = 'account' in wallet ? await wallet.signMessage({ account: wallet.account, message })
    : await wallet.signMessage({ message });
  return { 'x-spark-auth': Buffer.from(JSON.stringify({ ...auth, signature })).toString('base64url') };
}
export async function authenticateSparkRequest(scope: SparkRequestScope, store: SparkCaseStore, header: unknown,
  method: string, path: string, body: unknown, now = Math.floor(Date.now() / 1000)): Promise<SparkRequestAuth> {
  let auth: SparkRequestAuth;
  try {
    if (typeof header !== 'string' || header.length > 2048 || !/^[A-Za-z0-9_-]+$/.test(header)) throw new Error();
    auth = JSON.parse(Buffer.from(header, 'base64url').toString('utf8'));
    if (!auth || Object.keys(auth).sort().join(',') !== 'account,expiresAt,nonce,signature' || !isAddress(auth.account) || auth.account === zeroAddress || !Number.isSafeInteger(auth.expiresAt)
      || auth.expiresAt <= now || auth.expiresAt > now + 300 || typeof auth.nonce !== 'string'
      || !/^[A-Za-z0-9_-]{16,100}$/.test(auth.nonce) || !/^0x[0-9a-fA-F]{130}$/.test(auth.signature)) throw new Error();
    const recovered = await recoverMessageAddress({ message: sparkRequestMessage(scope, method, path, body, auth), signature: auth.signature });
    if (recovered.toLowerCase() !== auth.account.toLowerCase()
      || !store.consumeNonce(auth.account, auth.nonce, auth.expiresAt, now)) throw new Error();
  } catch { throw new SparkBackendError('unauthorised', 401); }
  return auth;
}
