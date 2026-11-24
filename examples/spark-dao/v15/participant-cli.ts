import { readFile, realpath } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { AvaServiceClient, localClient } from '@ava-protocol/sdk';
import { LocalMaterialCustody } from '@ava-protocol/local-service/custody';
import type { PublicDeployment } from '@ava-protocol/sdk/deployment';
import { buildSparkV15ParticipantApp, type SparkV15ParticipantOptions } from './participant-http.ts';
import { participantAddress, participantHash, participantObject } from './participant-payments.ts';
import { sparkV15 } from './payments.ts';

function text(value: unknown): string {
  if (typeof value !== 'string' || !value.trim()) throw new Error('Missing participant configuration value');
  return value;
}
function loopback(value: unknown): string {
  const url = new URL(text(value));
  if (url.protocol !== 'http:' || url.hostname !== '127.0.0.1' || url.username || url.password
    || url.pathname !== '/' || url.search || url.hash) throw new Error('Use an HTTP loopback origin');
  return url.origin;
}

/** Start the Spark workbench on this machine. Relative paths use the folder containing the configuration file. */
export async function startSparkV15ParticipantApp(configPath: string) {
  const path = resolve(configPath), base = await realpath(dirname(path));
  const file = (value: unknown) => resolve(base, text(value));
  const readJson = async (path: string): Promise<unknown> => JSON.parse(await readFile(path, 'utf8'));
  const config = participantObject(await readJson(path));
  const storage = participantObject(config.storage), relay = participantObject(config.relay);
  const { requestAudience, port } = config;
  if (!participantHash(requestAudience) || typeof port !== 'number' || !Number.isInteger(port) || port < 0 || port > 65535) {
    throw new Error('Invalid participant audience or port');
  }
  if ((storage.masterKeyFile === undefined) === (storage.credentialProfileFile === undefined)) {
    throw new Error('Supply one Vault key file or credential profile');
  }
  const credentials = storage.masterKeyFile !== undefined ? { masterKeyFile: file(storage.masterKeyFile) }
    : { credentialProfileFile: file(storage.credentialProfileFile) };
  const custody = new LocalMaterialCustody({ ...credentials, appId: sparkV15.appId, rootDirectory: base,
    vaultPath: file(storage.vaultPath),
    ...(storage.pythonPath ? { pythonPath: file(storage.pythonPath) } : {}) });
  const publicDeployment = await readJson(file(config.deploymentPath)) as PublicDeployment;
  const notices = storage.noticeIndexPath === undefined ? undefined
    : await readJson(file(storage.noticeIndexPath)) as SparkV15ParticipantOptions['notices'];
  if (notices?.length) await custody.verifyConfiguration();
  const token = (await readFile(file(relay.tokenFile), 'utf8')).trim();
  const app = await buildSparkV15ParticipantApp({ client: localClient(loopback(config.rpcUrl)), publicDeployment,
    relay: new AvaServiceClient(loopback(relay.url), text(token)), custody, notices, token: participantAddress(config.token),
    databasePath: file(storage.databasePath), requestAudience });
  try {
    const origin = await app.listen({ host: '127.0.0.1', port });
    return { app, origin };
  } catch (error) {
    await app.close();
    throw error;
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try {
    if (process.argv.length !== 3) throw new Error('Usage: node --import tsx examples/spark-dao/v15/participant-cli.ts <config.json>');
    const { origin } = await startSparkV15ParticipantApp(process.argv[2]);
    console.log(`Spark v1.5 participant app listening on ${origin}`);
  } catch (error) {
    console.error(error instanceof Error ? error.message : 'Spark v1.5 participant app could not start');
    process.exitCode = 1;
  }
}
