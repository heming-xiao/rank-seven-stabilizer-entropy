"""Check the exact union of completed rank-seven tail-ratio receipts."""

import argparse
import hashlib
import re
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
SOURCE_HASHES = {
    "verify_rank7_fourth_tie_bilinear.cpp": (
        "ffd06e81b72842e64752b9c3f62f73344e39a60d70cd73f3fc2dcf311bca66d5"
    ),
    "verify_rank7_equal_fifth_sixth.cpp": (
        "db8df09e4e34c9f42953085f2363a43c6f152db5a1d9ee39be00b81ac3b8e71a"
    ),
}
LOW = Fraction(9, 16)
HIGH = Fraction(3, 4)
RECEIPT_NAME = re.compile(r"upper_fifth_(\d+)_(\d+)_of_(\d+)\.log")
COMPLETED = re.compile(r"Completed slab 1 with (\d+) leaves at observed depth (\d+)")
SUMMARY = re.compile(
    r"Verified (\d+) exact leaves at depth (\d+): "
    r"old domain (\d+), weighted (\d+), bilinear (\d+)"
)


def read_completed_receipt(path):
    """Return (lower, upper, leaves, depth) for one successful receipt."""
    name = RECEIPT_NAME.fullmatch(path.name)
    if name is None:
        raise ValueError(f"Invalid receipt name: {path.name}")
    lower_num, upper_num, denominator = map(int, name.groups())
    lower, upper = Fraction(lower_num, denominator), Fraction(upper_num, denominator)
    if not LOW <= lower < upper <= HIGH:
        raise ValueError(f"Receipt outside the remaining ratio band: {path.name}")

    lines = path.read_text(encoding="utf-8-sig").splitlines()
    if not lines or lines[-1] != "exit 0":
        return None
    header = f"Requested d/b interval [{lower_num}/{denominator},{upper_num}/{denominator}]"
    completed = COMPLETED.fullmatch(lines[-3]) if len(lines) >= 4 else None
    summary = SUMMARY.fullmatch(lines[-2]) if len(lines) >= 4 else None
    if lines[0] != header or completed is None or summary is None:
        raise ValueError(f"Incomplete receipt with zero exit code: {path.name}")

    leaves, depth = map(int, completed.groups())
    verified_leaves, verified_depth, old, weighted, bilinear = map(int, summary.groups())
    if (leaves, depth) != (verified_leaves, verified_depth) or leaves != old + weighted + bilinear:
        raise ValueError(f"Inconsistent receipt totals: {path.name}")
    if leaves <= 0 or not 0 <= depth <= 72:
        raise ValueError(f"Invalid receipt leaf count or depth: {path.name}")
    return lower, upper, leaves, depth


def coverage_gaps(intervals):
    """Find each open gap left by the closed certified intervals."""
    cursor = LOW
    gaps = []
    for lower, upper in sorted(intervals):
        if lower > cursor:
            gaps.append((cursor, lower))
        cursor = max(cursor, upper)
    if cursor < HIGH:
        gaps.append((cursor, HIGH))
    return gaps


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()

    for name, expected in SOURCE_HASHES.items():
        actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Source hash mismatch: {name}")

    intervals = []
    total = 0
    receipt_dir = ROOT.parent / "certificates" / "rank7"
    for path in sorted(receipt_dir.glob("upper_fifth_*_of_*.log")):
        receipt = read_completed_receipt(path)
        if receipt is None:
            continue
        lower, upper, leaves, depth = receipt
        intervals.append((lower, upper))
        total += leaves
        print(f"[{lower},{upper}]  {leaves:,} leaves, depth {depth}")

    print(f"{len(intervals)} completed receipts, {total:,} recorded leaves.")
    gaps = coverage_gaps(intervals)
    if not gaps:
        print(f"The completed receipts cover all of d/b in [{LOW},{HIGH}].")
        return 0
    for lower, upper in gaps:
        print(f"An open d/b interval still needs coverage: ({lower},{upper}).")
    return 1 if args.require_complete else 0


if __name__ == "__main__":
    raise SystemExit(main())
