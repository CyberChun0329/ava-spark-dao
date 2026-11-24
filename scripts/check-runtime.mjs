import assert from 'node:assert/strict';
import { AvaSdk, AvaServiceClient } from '@ava-protocol/sdk';
import { exportPublicDeployment } from '@ava-protocol/sdk/deployment';
import { buildAvaService } from '@ava-protocol/local-service/server';
import { createWorkbenchController } from '@ava-protocol/workbench';
import { startSparkV15ParticipantApp } from '../examples/spark-dao/v15/participant-cli.ts';

const installed = new URL('../node_modules/@ava-protocol/', import.meta.url);
for (const specifier of [
  '@ava-protocol/sdk', '@ava-protocol/sdk/deployment', '@ava-protocol/local-service/server', '@ava-protocol/workbench',
]) {
  assert(import.meta.resolve(specifier).startsWith(installed.href), specifier);
}
for (const entry of [
  AvaSdk, AvaServiceClient, exportPublicDeployment, buildAvaService, createWorkbenchController, startSparkV15ParticipantApp,
]) {
  assert.equal(typeof entry, 'function');
}
console.log('Spark runtime and packaged AVA entry points loaded locally.');
