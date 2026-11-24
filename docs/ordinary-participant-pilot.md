# Participant commands for an ordinary one-to-one lesson

**Does this step update a state that multiple parties must rely on?** The shared vault, effective booking and payment choices, and facts that change later decisions are independently verifiable. Keep the signed source records with the participants and provide them when the relevant operation first uses them.

Use the official local `participant.json` and its exported deployment on chain 31337. The CLI reads and simulates at one canonical block. It prints typed data or an unsigned call for the participant's wallet. Each participant keeps custody of their wallet. A successful simulation describes the pinned block, and approval or booking takes effect only when the relevant transaction succeeds.

```sh
node --import tsx examples/spark-dao/v15/participant-ordinary-cli.ts participant.json prepare-grant grant.json
node --import tsx examples/spark-dao/v15/participant-ordinary-cli.ts participant.json prepare-booking-signature consent.json
node --import tsx examples/spark-dao/v15/participant-ordinary-cli.ts participant.json prepare-booking-adoption adoption.json
node --import tsx examples/spark-dao/v15/participant-ordinary-cli.ts participant.json prepare-occurrence occurrence.json
node --import tsx examples/spark-dao/v15/participant-ordinary-cli.ts participant.json prepare-prefunding prefunding.json
node --import tsx examples/spark-dao/v15/participant-ordinary-cli.ts participant.json prepare-notice notice.json
```

- `grant.json` has `account` (allocator wallet) and `terms` with `obligationId`, `executor`, `ceiling` (asset base units) and `validThrough` (Unix seconds). Integers use decimal strings. The wallet sends the returned call from `call.from` as a first grant. The executor uses the existing payment procedure after approval. Exceptions and replacement approvals use the existing Core path.
- `consent.json` has `account`, `formId`, `role` (`provider`, `tutor`, `customer` or a distinct `payer`) and `kind` (`AdoptBookingAcceptance`, or `AdoptTeachingAgreement` for provider and tutor on installations that adopt both together). Review the form, prefunding and terms in the output, then sign the returned `typedData` in the matching wallet. Keep the signed input with the local booking records.
- `adoption.json` has the coordinator's `account`, the `formId`, the form's `rechargeDebits` array of `{receiptId, amount}` decimal strings, and `bookingSignatures` in provider, tutor, customer, distinct payer order. Supply 65-byte wallet signatures as hex strings. For an installation with the separate teaching-signature argument, also send `teachingSignatures` in provider, tutor order. The three-argument entry uses earlier recorded teaching agreement signatures. The coordinator signs and sends the prepared transaction in their own wallet.

For first adoption of both deliveries, the signing input also carries `deliveredTermsRefs` in customer and tutor order. Each recipient should review the actual delivered terms. The adoption input uses `deliveries` in the same order, with `deliveryRef` and a Source consent containing `sourceRole`, `sourceAuthorityId`, `disclosurePolicyId`, `r` and `vs`. The installed Opening verifies the deliveries before the teaching agreement and form take effect, and Booking debits the named recharge account in the same transaction. The existing path can still use deliveries recorded earlier.

On the draft route, the verifier uses the installed Opening to adopt the coordinator's paid one-to-one draft while reserving funds. The role signatures above can then be prepared against the resulting form and prefunding evidence. [Positive attendance can be adopted separately at settlement](settlement-support-pilot.md#positive-student-attendance).

An installation with signed prefunding evidence can use `prepare-prefunding` with the verifier's `account`, the independent `source`, the precise `lesson` and `place`, the verified `requiredUnits` and `fundingRef`, and the signature deadlines `validThrough` and `draftValidThrough`. Use decimal strings for integer fields. The Source signs `sourceTypedData`, and the coordinator signs `draftTypedData` for the exact proof and draft. Add the signatures as `sourceSignature` and `draftSignature` and prepare again. The designated verifier can submit the signed draft within those windows. A private withdrawal before submission is visible only to the participants. A successful verifier transaction first adopts the proof and reserves the funds. The registered path handles earlier independently effective evidence or lifecycle actions. Form acceptance and the original account debit remain separate participant actions.

## Teaching start, end and service reports

Prepare `occurrence.json` with the evidence `source` wallet, the participant `account`, and a `validThrough` Unix timestamp as a decimal string. For `kind: "teaching-end"`, include `lessonId`, actual `occurredAt` as a decimal Unix timestamp, and `occurrenceRef`. The account is the verifier. For `kind: "full-service-feedback"`, include `formId` and `receivedRef`. The account is the student on that form. For `kind: "tutor-completion"`, include `lessonId` and `detailsRef`, with the effective tutor as the account. The tutor reports after actual teaching ends. A successful completion report enters the tutor's lesson history immediately.

For `kind: "teaching-start"`, the verifier supplies `lessonId` and the complete `observation`. Include actual `occurredAt` as a decimal Unix timestamp, `providerWentAhead`, `studentsTakingLesson`, `occurrenceRef` and `unmetConditionRef`. Use this command for an ordinary lesson that started under its original arrangement. The verifier's successful transaction records the start and applies the existing permission checks at that time.

The Source reviews and signs the returned `typedData`. Add the 65-byte hex `signature` to the same input and run the command again to prepare the call. The verifier, student or tutor sends their respective call from their own wallet. Keep the exact statement, signature and receipt with the local records. The shared fact and its proof become effective upon successful execution. `validThrough` limits adoption. A later lifecycle action can change whether the proof is usable while the report stays in the lesson history. Earlier Core records and other outcomes use their existing procedures.

## Course notices

Prepare one `notice.json` for each actual delivery. Use `kind: "student"` and `formId` for the student notice. Use `kind: "tutor"`, `lessonId` and `channelRef` for the tutor notice. Both inputs include the submitting wallet as `account`, the independent `source` wallet, `deliveryRef`, and `deliveredAt` and `validThrough` as decimal Unix timestamps. The coordinator records the student notice. The provider or coordinator records the tutor notice.

The Source signs the returned `typedData` for that delivery. Add the signature as `signature`, prepare the call again, then send it from the named wallet. Keep each signed statement and receipt with the delivery record. Each successful transaction records its own notice at that point. The original delivery time remains separately readable. Any later decision that needs both notices checks both records. Existing registered notices use their original procedure.
