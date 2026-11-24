# Settle an ordinary one-to-one lesson

Use the local participant configuration and deployment export with the consent entry in its Settlement ABI. This route covers ordinary paid one-to-one lessons without materials. The Source and approver each use their own wallet.

Ask the coordinator for the settlement assessment for this lesson. If the proposal is already recorded, use the exact assessment from the coordinator's saved proposal input. The assessment must match the installed Settlement ABI's `previewOrdinaryGroup` input, with `route` set to `"2"` and one seat for the confirmed form. Set `action` to `"source"` and supply `source`, `approver`, `lessonId` and `assessment`. Then run the preparation command.

```sh
node --import tsx examples/spark-dao/v15/participant-settlement-consent-cli.ts participant.json prepare source-input.json
```

The Source reviews the assessment, proposal, obligations, amounts and payees, then signs the EIP-712 `typedData`. The signature lets the named approver use this proof in the approval transaction. Use previously registered Core evidence when approval depends on a proof that was already available. The proposal must be current. The proposer, Source and approver each act independently. The output identifies the chain and block used to prepare the approval.

For the approver, set `action` to `"approver"` and add the Source's 65-byte `signature`. For registered payment evidence, include `paymentEvidenceIds` as positive decimal strings in preview payment order. Run the same command to check the signature, recalculate the approval basis and simulate the transaction. Send the returned `call` with the approver's wallet. The contract checks the conditions again when it executes.

Each obligation has its own evidence. Later use of an existing obligation checks that its evidence is still usable. Keep the approval receipt with the signed records. Group, materials, exceptional and partial settlements use their existing routes.

## First adoption of local completion and proposal records

Use the same `prepare` command with these inputs on an installation that exposes the local-record settlement entry.

1. The student and coordinator each provide an input with `action` set to `"student"` or `"coordinator"`, their own `account`, the same `lessonId` and `assessment`, their respective `reportRef`, and the same `validThrough` as a positive decimal Unix second. Each reviews and signs the returned `typedData` in their own wallet. The coordinator's signature binds the exact proposal and current authority.
2. Both `"source"` and `"approver"` inputs add the same `localRecords` object. Its fields are `formId`, `studentReportRef`, `coordinatorReportRef`, `validThrough`, `studentR`, `studentVS`, `coordinatorR`, and `coordinatorVS`. Use the report references and form from the signed data. Each wallet signature contributes `r` and its compact `vs` word. With viem, use `parseSignature(signature)` and compute `vs` with `toHex(BigInt(s) | (BigInt(yParity) << 255n), { size: 32 })`.
3. The Source signs the settlement basis returned by the local-record preview. The approver adds that signature and `paymentEvidenceIds`, then sends the prepared call from their own wallet. The signed wage option below requires the student's separate attendance signature. Keep the receipt containing `OrdinaryOneToOneRecordsAdopted` with the local reports. The completion confirmations and proposal take effect in that approval transaction.

The registered workflow uses the same `"source"` and `"approver"` inputs with the `localRecords` field omitted.

## Positive student attendance

On an installation that exposes the local-attendance approval and preview, a student can also use `prepare` with `action: "attendance"`, `attended: true`, and the same fields as the student completion input. Use the attendance report's own `reportRef` and validity. The resulting `StudentAttendance` signature binds the confirmed form and recorded end evidence. The student signs attendance separately from completion.

For this route the Source and approver each supply `signedAttendance` with `reportRef`, `validThrough`, `r`, and `vs`, alongside the existing `localRecords` object. Prepare the Source consent from the resulting attendance-specific preview and use that signature when preparing the approver's transaction. For either earlier route, omit `signedAttendance`.

With both `localRecords` and `signedAttendance`, an installation that supports signed wage evidence can use a signature for exactly one new wage obligation. In the Source and approver inputs, set `wageEvidence.source` to the wage Source's address and `wageEvidence.validThrough` to the expiry as a decimal Unix second. The wage Source signs the returned `wageTypedData` for the exact obligation. Add that signature as `wageEvidence.signature` to the approver's input in place of `paymentEvidenceIds`.
