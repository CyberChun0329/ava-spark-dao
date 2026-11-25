# Historical Forge evidence for the Preview 2 route

The source is one saved synthetic Forge test. `frame-headers.tsv` records the source log's one-based line coordinate, scope, entry point and reported frame gas, omitting argument payloads. The selected lesson has 46 frames totalling **12,247,794 gas**, including 15 separate Core evidence registrations. Three reusable-balance recharge frames (438,605) and three test-asset setup frames (74,237) are separate. The test begins at `publishLesson` (line 18922) and ends at `pay` (line 22310). The ledger includes the business calls inside the test harness's wage-approval helper. The helper frame, child calls of already counted business frames, static calls and test instrumentation are excluded. Installation, transaction intrinsic and calldata charges, L1 fees and other costs are excluded. Warmth and storage context are those of the saved test.

## Source and build identities

The measured candidate was Git commit `b6aaf443344729b51dd3a26f5042e8e2f10b954e`, tree `c21c8f224d3040a5530df93d403425c8e844d9e8`. `source-tree-git-blobs.txt` lists its 89 tracked paths and Git blob identities without publishing its private Git history. Compared byte for byte with the archived Preview 2 staging files, only `README.md`, `docs/ordinary-participant-pilot.md`, `docs/terms-delivery-pilot.md`, `package.json` and `package-lock.json` differ. The release commit was `a43a56eb41ab904edf19527afae603313ae1fabc`, tree `089b77e3bd2aba879bb71a8dad87ad1a196faf50`. The Solidity source, fixture, Foundry configuration and four dependency archives were the same. The dependency archive hashes are given below.

- `ava-protocol-contracts-0.1.0-preview.12.tgz`: `05a8c971c09d51fbf6b07efa18079111cbfaf7be37a6d1aad8788fe275122bc7`
- `ava-protocol-local-service-0.1.0-preview.12.tgz`: `ff79bcc24b19062fd07c5c9d8306040380e585c0254dc8adbcdc7061d787e1eb`
- `ava-protocol-sdk-0.1.0-preview.12.tgz`: `a69a1a21d7d821414a9e12787641616ab789a21b787f621b493f401b3dffb504`
- `ava-protocol-workbench-0.1.0-preview.5.tgz`: `ea1af32e66ff60e68480a123d9dd680759aa6365b9d0ba2458f5c730f7dd7d8f`

The saved compiler profile specifies Solc 0.8.26, Cancun, via IR, optimizer enabled with 200 runs, and `bytecode_hash = none`. The archived run reports offline Foundry and `--threads 0`. Its log reports compilation of 25 files and a successful compiler run. The fixture is `test/spark/v15/InstalledPhaseOne.t.sol`, `testInstalledOrdinaryOneToOneThroughTutorReceipt`. The saved test and separate Preview 2 test log both report whole-test gas of 14,139,043. The course ledger selects the individual business frames within that test.

## Bytecode evidence and limits

The two saved `InstalledPhaseOneTest` JSON artifacts have different full-file SHA-256 (`88a0798b2d17e4330e32ff29658bb47d56ee1b43d8542629cb190a20d9e8bc69` measured, `fcd801e53798e507160daf981df309360f575030414dda83f69f7a2a4e11ae28` release). A direct comparison of each artifact's creation and deployed `object` strings and each `linkReferences` structure found them equal. The shared exact strings and link references are supplied in `bytecode-objects.json.gz`. The SHA-256 digests cover the exact UTF-8 object strings, including their prefixes and unlinked placeholders.

- creation: `33f7f38902dd297380c87af220384217a804fccbb0cbeee13ece615f00917af7`
- runtime: `2b34c4f6a89a994cf7f5a3eb13ec237bb95bdbd95171ddf41f65f86deb30f56a`

These are compiler artifact objects, not independently captured on-chain deployed bytecode. The earlier archived comparison also reports equality of five linked library artifacts and 65 cached Spark production objects. Their full comparison preimages and the complete historical standard-json compiler input are not included here; the report alone does not independently establish those comparisons. The selected original log SHA-256 was `3e40a17f808371787aac748757853629db67e5bcef814fd3fab2eb47f079dc31`; the full log is withheld because it contains raw inputs. The archived selected ledger SHA-256 was `b3b7cc432a25815cba894aa67d4707d54c6a75eaa1e07de197b8b31fb8880b05`. The frame headers here were checked against the saved log at each coordinate. Readers can recompute the published sums. Authenticating the extraction against the full trace requires that original.

Run `python3 research/spark-v1.5/forge-preview2/check.py` from the repository root to check the object hashes and frame totals. You can pass a locally built `InstalledPhaseOneTest.json` as an additional argument to compare its creation and runtime objects and link references. The [pinned test source](https://github.com/CyberChun0329/ava-spark-dao/blob/a43a56eb41ab904edf19527afae603313ae1fabc/test/spark/v15/InstalledPhaseOne.t.sol) and [repeat command](../engineering.md#reproduce-the-measurements) identify the public build. Actual linking or deployment of the historical objects would require separate evidence.
