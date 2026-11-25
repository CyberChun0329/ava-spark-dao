# Funding and cost comparison

## Payment at checkpoint 45

All quantities below use the synthetic accounting unit of the Lean witnesses. For a recipient-specific obligation, let (A) be the amount established by the applicable terms and (P) the amount demonstrably received, retained and attributable to that obligation at the check. Required cover is `max(0, A − P)`. A transfer of money can reduce cash before its receipt is usable for this calculation.

The formal instruction fixes payment 13 of 4 to holder 3 for material 7 in lesson M42, on obligation 51, at checkpoint 45. Material 8 independently needs 6. Holder 2 already received 2 at 40. Set `I = 1` only if verification of that matching receipt is usable at 45. Verification with reference 81 at 44 qualifies. Verification at 46, a nonmatching receipt, or no verification leaves `I = 0`. Filing is a later step. The second share's due time is 50 and its original execution deadline is 60. [Payment condition and evidence](lean/EvidencePayment.lean)

The provider has 22 at 29, including the top-up at 25. This covers M's two material provisions of 6 and T's booking provision of 10. Charging 4 to prepaid credit at 31 and releasing 4 of protection at 41 do not change cash. The previous material transfer of 2 at 40 and an external debit of 4 or 2 at 43 leave cash `G = 16 or 18` at 45, provided the records reconcile to the same funding entry in the order `29 < 40 < 43 < 45`. The supplied bank reconciliation is a premise. With T's actual protection `K`, the condition is

```text
G − K ≥ 4 + 6 + 2(1 − I) = 12 − 2I
Shortfall = max(0, K + 12 − 2I − G)
```

| T protection at the check | Cash 16, late | Cash 16, early | Cash 18, late | Cash 18, early |
| ---: | ---: | ---: | ---: | ---: |
| 10 | 6 | 4 | 4 | 2 |
| 8 | 4 | 2 | 2 | 0 |
| 6 | 2 | 0 | 0 | 0 |
| 7, conditional additional expense | 3 | 1 | 1 | 0 |

Zero is sufficient on the stated funding condition. At 16 with `K = 6`, only early verification permits the proposed payment and leaves 12 to cover T and material 8. At 18 with `K = 6`, both paths can pay. With an extra 2 of retained lesson fees still protected, `K = 8`, early verification at 16 still leaves a shortfall of 2. At 18 early verification suffices. [Lean comparison](lean/CostProjection.lean) · [Retained-fee check](lean/AcceptedRetainedFees.lean)

In the pending branch, verified partial delivery removes the no-teaching expense case, lowering the possible expense maximum from 10 to 8. Excluding relevant provider fault lowers it further to 6 with tutor fault still open. The recorded reservation stays at 10 until a separately effective release of 2 or 4. The pending witness assumes the effective release when it uses the lower amount. The accepted-compensation branch instead protects a refund of 2 and issued course credit of 4. Adding an unpaid expense of 1 for any taught case makes the comparable amount 7. The largest taught case rises from 8 to 9 and the pre-commitment maximum stays 10. The `K = 7` row is conditional arithmetic, with no new release or payment history. [Pending branch](lean/PendingReserve.lean) · [Accepted branch](lean/OtherBranches.lean)

## Event count and observation window

The comparison starts immediately before T's top-up, with M's existing lesson, use, charge, two shares, provisions and approvals already in place. T tops up and confirms (2 events), records both notices, start and end (4), records tutor delivery, attendance and feedback (3), records the initial finding, retains the original outcome and records the fault outcome (3), assesses the refund, accepts compensation and issues credit (3). M then pays the old share and T's reserve is released (2). The early path verifies the first receipt at 44 (1) before the common last event, posting 4 at 45 (1). The external bank debit enters the balance as evidence.

At cash 18 and protection 6, the formal paths reach the same selected payment and reservation entries in 18 events without early verification and 19 with it. The comparison stops at the payment. The earlier receipt is still unverified on the late path, so the counts cannot stand in for a cost comparison through verification. [Fixed events and projection](lean/CostProjection.lean)

## Separate retained-fee accounting

In the historical single-lesson T100 accounting run, the final partial release leaves 8 protected in a pool with 14 cash. The 8 consists of a refund still due (2), issued credit (4) and retained lesson fees (2). The earlier protection peaks at 14 after credit is issued. This observation is separate from the formal 22-unit histories and the B1 shared-pool SDK run. It supports retaining the extra 2 as a condition to check. The rules govern any eventual transfer to the guarantee reserve. Pure release and a transfer out of the pool have different effects. [Saved T100 ledger](data/t100-retained-fee.json)

## Comparing the resources used by a payment history

Use the same obligation, amount, recipient, execution time and deadline, with the other obligations protected. Follow both routes through every verification included in the comparison and identify open work at the endpoint. Record active work by role, metered execution on disjoint operations, waiting by obligation, and the integral of the actual restricted balance over time. Include unsuccessful attempts that use resources. Count a metered child only in its measured parent and allocate shared work once across the obligations it serves.

At cash 16 with protection 6, the early route needs no additional money while a late route requires 2 more in the same pool by 45. If both routes make the same authorised payment and complete verification within the comparison window, let `c` be incremental early-route work and execution costs relative to the late route. If the incremental financing cost for the late route is `r` per unit over the actual holding period and other costs are equal, early verification costs less when `c < 2r`. The formal path and thresholds fix neither these prices nor the holding period. The separate App figures meter only selected frames, with the same operations in both branches. [Saved sufficient-funding comparison](engineering.md#sufficient-funding-control)
