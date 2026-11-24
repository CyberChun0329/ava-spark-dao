# Record delivery of course terms

Use the existing local `participant.json` and its exported deployment on chain 31337 over HTTP `127.0.0.1`. The Source and coordinator each use their own wallet.

Create an input JSON file with `action` set to `source`, and `source`, `coordinator`, `formId`, `recipient`, and `deliveryRef` set to the addresses or exact bytes32 identifiers for this delivery. Run:

```sh
node --import tsx examples/spark-dao/v15/participant-terms-cli.ts participant.json prepare source.json
```

The Source reviews and signs the returned `typedData` with their own EOA wallet. The signature authorizes first adoption of the specified evidence in the coordinator's delivery transaction. Use the existing Core receipt when the delivery depends on prior registration or prior availability. The `formVersion`, `lessonId`, and `serviceTermsRef` identify the terms. Confirm the actual terms and delivery material independently.

Create a second input with the same fields, `action` set to `coordinator`, and `signature` set to the Source's 65-byte signature. Run the same command with that file. Preparation checks the current installation, actors, form and recipient, verifies the signature, and simulates the coordinator call. Use the returned `call` with the coordinator's wallet. The contract checks the conditions at execution. A successful transaction records delivery before a relevant commitment.
