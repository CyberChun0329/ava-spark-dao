# Engineering observations

The ledgers below use synthetic classes, accounts and test assets. They record separate experiments. The archived SDK run, Forge tests, Lean witnesses and independently mined course transactions have distinct starting states and clocks.

## B1 run-04

This was an earlier local historical run through the SDK on Anvil 1.5.1, chain 31337, with Solc 0.8.26 and Cancun. The archived Spark material module was `b090c88645a6092b7f79be43e732f8b120352b58eb9e2774794b630d497ac935`. The [selected readbacks](data/b1-run-04.json) give the source-record digests, block and log coordinates, obligation and receipt IDs, clock fields and accounting outcomes. The contract-level replay at published Preview 2 is [`testOriginalB1ContractSequence`](https://github.com/CyberChun0329/ava-spark-dao/blob/a43a56eb41ab904edf19527afae603313ae1fabc/test/spark/v15/InstalledOriginalB1.t.sol#L126). Its transfers, verification and refund give a separate implementation check. The historical SDK sequence and on-chain filing are established by the archived run.

| Block | Saved observation |
| ---: | --- |
| Before 223 | M42 material 7 use and charge support shares of 2 and 4. The charge is 5% of the normal fee of 120, with an actual discounted debit of 4. Material 8 has its own provision of 6. |
| 223–225 | Core request 2 is created for vested state 2 on object 2, with evidence 33. It is allocated at 224 and consumed and completed in the same transaction as App approval at 225. The approved ceiling is 4. Paid is still zero. |
| 226–228 | Opening cash is 194 + 4 + 4 = 202. The first native transfer pays 2 to the first material payee, leaving cash 200 and material protection 12 pending verification. |
| 231–232 | The independent verification of receipt 1 makes its evidence usable. At the next execution check, there is no active hold, the beneficiary version is 0 and 4 is unpaid. The same pool has cash 200 and protection of 182 for M42, 14 for T100 and 4 in the separate payment allocation. M42's recorded protection includes 124 in other costs and the separate material 8 still requiring cover of 6. |
| 233 | The approved executor pays 4 to the second material payee. The token transfer and App receipt 2 agree. Cash and total protection are 196. Receipt 2 has yet to be verified. |
| 236 | An independent verifier checks receipt 2 with evidence 35. Material protection falls from 10 to 6 within M42's existing protection. |
| 245 | The App credits 2 to T100's original debit account, restoring its internal balance from 0 to 2. The issued course credit of 4 is preserved and vault cash remains 196. |
| 246–247 | The coordinator files receipts 1 and 2 separately. Vault cash and material protection remain 196 and 6. |

The archived transaction evidence supports the stated actions and readbacks. Original signed transaction bytes, some raw event fields and parts of the third-party runtime were unavailable to the archive check. The JSON selects from the saved records and omits signatures, wallets' private material and full traces. Transaction identifiers refer to the synthetic local chains.

## Receipt timing and historical reads

In Preview 2, paying 4 would leave 143 against required protection of 145. Verification lowers the requirement to 143 and payment of 4 succeeds on the same approval in the same recorded second. [`testCurrentProtectionCountsAReceiptAfterSameSecondVerification`](https://github.com/CyberChun0329/ava-spark-dao/blob/a43a56eb41ab904edf19527afae603313ae1fabc/test/spark/v15/MaterialsFunding.t.sol#L658)

A separate test checks that verified receipts support the next provision without waiting for filing. [`testSameSecondVerifiedReceiptsBackNextProvisionAtOriginalCash`](https://github.com/CyberChun0329/ava-spark-dao/blob/a43a56eb41ab904edf19527afae603313ae1fabc/test/spark/v15/MaterialsFunding.t.sol#L684)

An older [G5 two-block export](data/g5-two-blocks.json) records material protection of 12 at block 228 after payment of 2 and 10 at block 230 after independent verification. Both blocks have the same timestamp and cash of 200. The read with the next payment proposed changes from 8 to 6, and re-reading block 228 still gives 12 for current material protection at that block. The next payment of 4 passes **simulation** at both cuts. This export has no actual next transfer. Its blocks are from a different run than B1 run-04.

### Sufficient-funding control

The saved `testFundedReceiptTimingAllowsBothActualPayments` is an earlier offline Forge test, using the material source SHA-256 `f131231a6627122792d18e07b8b4f859064f98919d3229eca6d03b714e8cc79b`. Test source SHA-256 is `e706636f3cc4f4b0dc2322d30f1e302e70596329f2ba18e20b331557e0042235`. The exported rows come from trace SHA-256 `804f24db9c4fc157101a1cc09a71bc4a243ca9cba2ce2d80b5d271a2dc2e73cc`. The checked-in Preview 2 tests above exercise the tight-balance contrast and same-second consumer. The paired sufficient-funding history is a saved result of this earlier targeted fixture.

The test deposits an additional 6 in the common prefix, with the previous share of 2 already paid. Both branches then pay the same recipient 4 on the same obligation, approval request 2 and execution timestamp 1000045. First-receipt verification occurs at 1000044 or 1000046. Cash goes from 153 to 149 in both. Each payment uses the dedicated allocation of 4, and both branches keep the refund reserve of 120 and credit of 17 protected.

| Read point | Early | Late |
| --- | ---: | ---: |
| Extra cover from the proposed-payment query with the allocation still in place | 6 | 6 |
| Protection at the actual execution check, after separating the allocation | 143 | 145 |
| Total protection just after paying, before verifying receipt 2 | 147 | 149 |
| Total protection after both verifications | 143 | 143 |

The [six funding observations](data/sufficient-funding.tsv) show the component values and their read points. The [six selected frame readings](data/sufficient-funding-frames.tsv) total 984,159 gas for the early branch and 923,616 for the late branch. Each sum covers independent verification of the first receipt, payment of the second share and independent verification of the second receipt. Their order differs with the timing choice. These frames exclude earlier evidence registration, other fixture work, off-chain work, and any later filing. Forge restores a common state before the late branch. These are call-frame readings within one test, with its access and execution context. They do not identify transaction fees or the causal monetary cost of verifying earlier. [Cost comparison inputs](funding.md#comparing-the-resources-used-by-a-payment-history)

## Ordinary one-to-one gas

The 11-transaction signed workflow was run on separate local installations of Spark App **Preview 3** [`c9501ad`](https://github.com/CyberChun0329/ava-spark-dao/commit/c9501ad5a32c9c223f49378463f534f74e81de33) and **Preview 2** [`a43a56e`](https://github.com/CyberChun0329/ava-spark-dao/commit/a43a56eb41ab904edf19527afae603313ae1fabc), both with AVA Core, SDK and local service `0.1.0-preview.12`. The fixture was fully paid, undisputed and used no materials. The first counted transaction publishes the lesson and form and reserves funds in one verifier-led operation. The last transfers the wage of 8 to the tutor. At separate approval no money had moved. After payment the shared vault fell from 400 to 392, the balance of the tutor rose from 0 to 8, and the separate payment reservation fell from 8 to 0. [Selected balance and fulfilment observations](data/ordinary-lesson.json)

| Run and scope | Count | Gas | USD at the stipulated rate |
| --- | ---: | ---: | ---: |
| Preview 3 signed route, root execution before refunds | 11 | 6,507,082 | 0.054496811750 |
| Preview 3 signed route, receipt gas used | 11 | 6,785,178 | 0.056825865750 |
| Preview 2 same signed route, root execution | 11 | 6,956,741 | 0.058262705875 |
| Preview 2 same signed route, receipt gas used | 11 | 7,234,837 | 0.060591759875 |
| Preview 2 individually registered route, selected Forge execution frames | 46 | 12,247,794 | 0.102575274750 |

The fixed calculation is `gas × 0.005 × 10⁻⁹ × 1,675 USD`. L1 data fees, priority fees and other bill components lie outside it. The signed-route receipt reduction is 449,659 gas (6.215%). The Preview 3 execution subtotals are 2,282,387 for publication through notices, 1,486,085 for class start through delivery reports, 1,840,496 for settlement, 461,994 for approval and 436,120 for payment. The receipt sum adds 302,796 gas in intrinsic and calldata charges and deducts 24,700 in refunds. Both signed runs report first reusable recharge separately at 492,205 execution gas and 528,741 receipt gas. Synthetic funding setup and installation are outside the course total.

- [Preview 3 signed ledger](data/preview-3-signed.tsv) and [Preview 2 signed ledger](data/preview-2-signed.tsv) each give one row per independently mined transaction, ordered by appearance. The `course` rows are the 11 measured transactions. Root execution includes internal calls once.
- [Preview 2 Forge ledger](data/preview-2-individual-forge.tsv) gives the actual selected outer call frames in one test. Its `lesson` rows include 15 independent evidence registrations. Tool and submission context differ from Anvil. The seven approval actions that follow Core support registration in that route are replaced by one distinct App approval on the signed route. The approval and payment remain separate.

### Reproduce the measurements

For the individually registered Forge route, check out Preview 2, use its package lock, and run the targeted test below. The selected frame list identifies the calls to count, from `publishLesson` to `pay`. Count the seven independent Core and App approval calls and their support registration while excluding the enclosing test helper. Installation, minting, first recharge, views and fixture work sit outside the course total. The saved call frames came from a bytecode-matched build as recorded in [the compact provenance](data/ordinary-lesson.json).

```sh
npm ci --ignore-scripts
forge test --offline --threads 0 --match-path test/spark/v15/InstalledPhaseOne.t.sol   --match-test testInstalledOrdinaryOneToOneThroughTutorReceipt -vvvv
```

For the signed route, check out each release and use the [local installation](../../docs/local-installation.md) on a fresh Anvil 1.5.1 Cancun chain, 31337, with `--steps-tracing`. Use distinct test roles for provider, tutor, coordinator, evidence Source, verifier, allocator, executor, customer, payer and student. Use package 1 and disclosure policy 1 on the fresh installation. The fixture starts with reusable prepaid credit of 40 and provider backing of 360 in the shared vault. Use the original arranged one-hour single-seat lesson, normal charge and actual original debit of 20, reserve 58 and wage 8. The stored run uses start 1795772800, finish 1795776400 and wage due 1798364800 (synthetic Unix seconds). The approval covers the original obligation through 1798451200. The signed course uses the opening rule at [prefunding and booking](../../docs/ordinary-participant-pilot.md), including two actual term deliveries attested for the exact form before the signatures take effect. The signed booking and teaching agreement are adopted together with the debit. Record student and tutor notices separately. At the agreed start and finish record their actual occurrences, followed by the tutor's completion report and the student's complete-service feedback. For settlement use the [signed records procedure](../../docs/settlement-support-pilot.md), including attendance, completion confirmations by student and coordinator, the coordinator's proposal, independent settlement support and a distinct signed wage basis. Use the allocator's first ordinary wage approval for 8 and a separate executor payment on the due date. These are the same 11 actions and entry points in the exported ledgers. Record the recharge and any synthetic funding separately. Signature creation, previews and test-clock advancement do not enter the total.

For an independent local repeat, collect `eth_getTransactionByHash`, `eth_getTransactionReceipt` and the opcode `debug_traceTransaction` responses for those transactions from the local node. Put their result objects in a JSON file for each transaction as `tx`, `receipt` and `trace`. Run `python3 research/spark-v1.5/recalculate.py trace-*.json` to get the root, intrinsic, refund and receipt gas per transaction. Root gas is the initial root opcode's balance less the balance after the root's final `RETURN` or `STOP`. Sum one row per successful transaction. Calldata length, installation and access patterns can change a new run, so report the actual measured values. This procedure reruns the business and metering from the named public release. The original runner's full traces, signing material and machine configuration stay outside the package.

To recompute the saved results and fixed-rate conversion without a node, run `python3 research/spark-v1.5/recalculate.py` from the repository root.
