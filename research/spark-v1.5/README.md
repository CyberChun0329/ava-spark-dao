# Spark DAO v1.5 research evidence

This directory supports Appendix B's selected formal comparisons and synthetic engineering observations. The [published rules and Lean specifications](../../spec/v1.5/README.md) give the v1.5 baseline. The two published Lean workflows are equivalent within their shared formal domain. The implementation observations support the named cases at their stated versions.

| Appendix entry | Public evidence |
| --- | --- |
| B.1 Continuous holds, interruption and original approval | [Fixed hold witness](lean/Continuous_Hold_Release_Witness.lean) and [Round 19 comparison excerpt](lean/Round19-hold-execution.diff) |
| B.2 Transfer and eligibility | [Four-step review path](lean/TransferReviewPath.lean) and [decision-time interest candidate](lean/ReviewInterestCandidate.lean) |
| B.3 Payment and event counts | [Accepted-compensation branch](lean/OtherBranches.lean), [funding and event projection](lean/CostProjection.lean), [payment evidence and paths](lean/EvidencePayment.lean) and [funding and cost calculation](funding.md) |
| B.3 Retained lesson fees and resource comparison | [Retained-fee witness](lean/AcceptedRetainedFees.lean), [T100 accounting](funding.md#separate-retained-fee-accounting) and [same-scope comparison](funding.md#comparing-the-resources-used-by-a-payment-history) |
| B.4 Approval, transfer, verification and filing | [B1 run-04](engineering.md#b1-run-04), [selected archived business records](data/b1-run-04.json), [split timing witness](lean/SplitReceipt.lean) and [filing invariance](lean/ReceiptFiling.lean) |
| B.4 Shared protection before booking | [Competing prefunding](lean/CompetingPrefunding.lean) |
| B.4 Receipt timing | [Historical G5 two-block readbacks](data/g5-two-blocks.json), [sufficient-funding control](engineering.md#sufficient-funding-control) and the linked public tight-balance tests |
| B.4 Material transfer after settlement | [Frozen G3 counterexample](lean/TransferReserve.lean), [G3-revised model](../../spec/v1.5/README.md), [fixed same-second witness](lean/G3SameSecond.lean) and [App tests and observation times](g3-same-cut/README.md) |
| B.4 One ordinary lesson | [Versioned Preview 2 and Preview 3 ledgers, pricing and repeat instructions](engineering.md#ordinary-one-to-one-gas) |

## Evidence versions

| Run or input | Version |
| --- | --- |
| Original frozen formal pair | 21 November 2026, Lean 4.36.0. The [73-file source and toolchain manifest](lean/frozen-inputs.sha256) identifies both projects after reversing the G3 patch. |
| Published formal pair | 25 November 2026 G3 revision, as included in [Spark App Preview 3](https://github.com/CyberChun0329/ava-spark-dao/tree/c9501ad5a32c9c223f49378463f534f74e81de33/spec/v1.5). |
| B1 SDK run-04 and the sufficient-funding test | Two separate historical runs. Their App builds, runtime identities and preserved observations are described in [B1](engineering.md#b1-run-04) and the [sufficient-funding record](sufficient-funding/README.md). |
| Individually registered teaching route | Historical Forge candidate `b6aaf443…` compared with public Preview 2 `a43a56e…`. See the [source, compilation and trace record](forge-preview2/README.md). |
| G3 App renewal | The [published Preview 2 tests](g3-same-cut/README.md) use different observation times. The common-time candidate has a build result only. |

## Check the Lean witnesses

From the repository root, with Lean 4.36.0 available through Elan, run

```sh
bash research/spark-v1.5/lean/check.sh
python3 research/spark-v1.5/recalculate.py
```

The Lean command uses fresh temporary builds. Supply `hold`, `frozen` or `revised` to run a single set.

| Inputs | Scope |
| --- | --- |
| **Section 6.6 v1.5 candidate, 20 November** | Runs the original `Continuous_Hold_Release_Witness.lean`. A [source delta](lean/hold-candidate-input.diff) recovers just the import dependency tree of the earlier direct candidate from the published source and verifies the recovered files against their [digests](lean/hold-candidate-input.sha256). The separate Round 19 excerpt shows the earlier cutoff and revised check. With the original day-8 deadline, the earlier calculation reaches day 12 in both histories. The executable candidate distinguishes first full release at day 20 under continuous coverage from day 10 with a gap, retaining the two-day allowance and day-23 approval expiry. The Round 19 side is a source comparison. The full earlier model is outside this package. |
| **Frozen pair, 21 November** | Reconstructs the original material calculation by reversing the [exact single-file G3 patch](lean/G3.actual.diff) in a temporary project. Before compiling, it checks all 73 Lean source, Lake project and toolchain files against the [21 November freeze manifest](lean/frozen-inputs.sha256). The hashes come from the two locked source projects, checked against the original translation source list and recognised-state verification record. All other files match the public G3 revision. Runs the transfer and review comparisons, accepted history, funding and retained fees, split receipt, competing prefunding, filing, and the original G3 counterexample. |
| **G3-revised pair, 25 November** | Uses the public [v1.5 specification](../../spec/v1.5/README.md) to check `G3SameSecond`, where the original 2 + 4 has been paid and verified before the effective transfer and the next requirement stays at 6. |

The payment histories and executable fixtures supply synthetic terms and evidence. The old private confirmation-form file served an identity check in the private archives. The public script checks its own specified source inputs and the supplied synthetic histories. Historical receipts and fixed term assumptions have their own scope. The package omits the standalone confirmation form, raw signing material, private review packages, full node logs and unrelated research runs.
