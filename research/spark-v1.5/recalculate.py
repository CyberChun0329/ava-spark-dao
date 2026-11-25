"""Recompute the published gas and funding tables using Python's standard library."""

import csv
from decimal import Decimal
import gzip
import json
from pathlib import Path
import sys

DATA = Path(__file__).resolve().with_name("data")
USD_PER_GAS = Decimal("0.005") * Decimal("1e-9") * Decimal(1675)


def rows(name):
    with (DATA / name).open(newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def signed(number):
    entries = rows(f"preview-{number}-signed.tsv")
    assert len({row["txHash"] for row in entries}) == len(entries)
    for row in entries:
        assert int(row["frame"]) == int(row["startGas"]) - int(row["terminalGas"]) + int(row["terminalCost"])
        assert int(row["receiptGas"]) == int(row["frame"]) + int(row["intrinsic"]) - int(row["refund"])
    results = {}
    for phase in ("course", "first-recharge", "fixture-funding"):
        chosen = [row for row in entries if row["phase"] == phase]
        root, receipt = (sum(int(row[key]) for row in chosen) for key in ("frame", "receiptGas"))
        results[phase] = (len(chosen), root, receipt)
        print(f"Preview {number} {phase}: {len(chosen)}, root {root:,} (${root * USD_PER_GAS:.12f}), "
              f"receipts {receipt:,} (${receipt * USD_PER_GAS:.12f})")
    return results


def recompute():
    before = signed(2)["course"]
    after = signed(3)["course"]
    assert before == (11, 6956741, 7234837) and after == (11, 6507082, 6785178)
    saving = before[2] - after[2]
    print(f"Receipt reduction: {saving:,} ({Decimal(saving) * 100 / before[2]:.3f}%)")
    forge = rows("preview-2-individual-forge.tsv")
    for scope in ("lesson", "recharge", "test-funding"):
        group = [row for row in forge if row["scope"] == scope]
        gas = sum(int(row["gas"]) for row in group)
        print(f"Preview 2 Forge {scope}: {len(group)} frames, {gas:,} gas (${gas * USD_PER_GAS:.12f})")
    assert len([row for row in forge if row["scope"] == "lesson"]) == 46
    assert sum(int(row["gas"]) for row in forge if row["scope"] == "lesson") == 12247794
    assert sum(row["call"].endswith("::registerEvidence") for row in forge if row["scope"] == "lesson") == 15
    frames = rows("sufficient-funding-frames.tsv")
    print("Sufficient-funding frames, early and late:",
          *(sum(int(row["frame_gas"]) for row in frames if row["branch"] == branch)
            for branch in ("early", "late")))
    for k in (10, 8, 6, 7):
        shortfalls = [max(0, k + 12 - 2 * i - g) for g in (16, 18) for i in (0, 1)]
        print(f"K={k}, shortfalls at 16 late/early and 18 late/early: {shortfalls}")


def trace_measurement(path):
    """Read a local Anvil trace bundle with tx, receipt and trace fields."""
    open_trace = gzip.open if path.suffix == ".gz" else open
    with open_trace(path, "rt") as stream:
        bundle = json.load(stream)
    tx, receipt, trace = (bundle[name] for name in ("tx", "receipt", "trace"))
    initial, terminal = trace["structLogs"][0], trace["structLogs"][-1]
    assert receipt["status"] == "0x1" and not trace["failed"]
    assert tx["type"] in ("0x0", "0x1", "0x2") and not tx.get("accessList")
    assert initial["depth"] == terminal["depth"] == 1 and terminal["op"] in ("RETURN", "STOP")
    intrinsic = 21000 + sum(4 if byte == 0 else 16 for byte in bytes.fromhex(tx["input"][2:]))
    assert int(tx["gas"], 16) - int(initial["gas"]) == intrinsic
    root = int(initial["gas"]) - int(terminal["gas"]) + int(terminal["gasCost"])
    used = int(receipt["gasUsed"], 16)
    refund = root + intrinsic - used
    assert 0 <= refund <= (root + intrinsic) // 5
    return (receipt["transactionHash"], root, intrinsic, refund, used)


if __name__ == "__main__":
    if len(sys.argv) == 1:
        recompute()
    else:
        print("txHash\tframe\tintrinsic\trefund\treceiptGas")
        for name in sys.argv[1:]:
            print(*trace_measurement(Path(name)), sep="\t")
