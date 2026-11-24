import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { localClient } from '@ava-protocol/sdk';
import { exportPublicDeployment, foundryArtifactLoader } from '@ava-protocol/sdk/deployment';

const args = process.argv.slice(2);
const verification = args[0] === '--verify-local' && args[1] ? { client: localClient(args[1]) } : undefined;
const [output, ...inputs] = verification ? args.slice(2) : args;
if (!output || output.startsWith('--') || inputs.length === 0) {
  throw new Error('Usage: export:deployment -- [--verify-local http://localhost:8545] output.json broadcast.json [broadcast.json ...]');
}
const broadcasts = await Promise.all(inputs.map(async path => JSON.parse(await readFile(path, 'utf8'))));
const config = await exportPublicDeployment({ broadcasts, artifact: foundryArtifactLoader(resolve('.build/out')), verification });
await mkdir(dirname(output), { recursive: true });
await writeFile(output, JSON.stringify(config, null, 2) + '\n', { mode: 0o644 });
console.log(`Public deployment configuration: ${output}`);
