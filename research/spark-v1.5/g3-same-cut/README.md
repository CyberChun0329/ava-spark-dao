# Material renewal evidence and observation times

The published tests cover two separately supported outcomes. Both start with the original two payments, of 2 and 4, and preserve the verified receipts after transfer. Both use vault cash of 143, with `reservedUnits()` of 137, and attempt to provision 6 for the other material.

| Published Preview 2 test | Transfer | Observation | Verified assertions |
| --- | ---: | ---: | --- |
| [Source linked to the booking expense](https://github.com/CyberChun0329/ava-spark-dao/blob/a43a56eb41ab904edf19527afae603313ae1fabc/test/spark/v15/MaterialsFunding.t.sol#L740) | `EPOCH + 45` | `EPOCH + 48` | `requiredBeyondLessonHold(..., true)` is 6. The call records a new provision of 6. Cash and reserves stay at 143 and 137. |
| [Source unlinked to the booking expense](https://github.com/CyberChun0329/ava-spark-dao/blob/a43a56eb41ab904edf19527afae603313ae1fabc/test/spark/v15/MaterialsFunding.t.sol#L778) | `EPOCH + 45` | `EPOCH + 45` | `provisioningNeed` is 6. `requiredBeyondLessonHold(..., true)` is 12. `recordProvision` rejects the renewal and leaves the existing backing unchanged. |

The tests assert the separate outcomes at their own observation times. A common-time comparison would need to hold the actual payment and verification order, effective transfer, opening cash, other reserves and observation time fixed while varying the source reference. An isolated candidate compiled against the Preview 3 App source in the [public research baseline](https://github.com/CyberChun0329/ava-spark-dao/tree/0ed04569cd9888b5acf7a116f9b9d7a67f9fcaea). The first Forge invocation selected no tests, and the follow-up was interrupted. There is no new executed common-time comparison in this package.

The historical M42 estimate and charge retain their separate references. The synthetic tests supply no authorised connection between those historical records. [Frozen G3 witness](../lean/TransferReserve.lean) · [Revised same-second witness](../lean/G3SameSecond.lean)
