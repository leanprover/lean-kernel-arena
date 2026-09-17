#!/usr/bin/env python3
# /// script
# dependencies = [
#     "pyyaml>=6.0.3",
# ]
# ///
"""Set the `timeout` field of the test YAML files from the live arena results.

Fetches the latest results.json from the arena website and distributes a
total timeout budget over the test YAML files marked `compare-perf: true`
(the real-world corpora and the perf/ tests; these are the only ones where a
checker is expected to take long, so the many small corner-case tests are
left without a timeout). The distribution is based on the official checker's
wall time w on each test, taken to be at least MIN_OFFICIAL so that tests the
official checker finishes in milliseconds still get a sensible time limit.

The budget is BUDGET_FACTOR times the sum of all official wall times, so it
grows automatically with the test suite. It is distributed as a power law,
timeout = c * w^ALPHA, with c chosen to exhaust the budget. With ALPHA < 1
this biases towards small tests: relative to the official time, the largest
test (mathlib) gets a factor of about 2, while small tests get a factor of
10 or more, and about a minute for the tiny ones. Timeouts are rounded up to
ROUND_TO seconds.

Based on the same results, also reports which checker runs would have been
affected by the updated timeouts, i.e. which runs would newly exceed (or no
longer exceed) their test's time limit.
"""

import argparse
import json
import math
import re
import sys
import urllib.request
from pathlib import Path

import yaml

RESULTS_URL = "https://arena.lean-lang.org/results.json"
BUDGET_FACTOR = 3.0   # total budget, in multiples of the total official wall time
ALPHA = 0.6           # exponent of the power law distributing the budget
MIN_OFFICIAL = 1.0    # official wall time is taken to be at least this many seconds
ROUND_TO = 10         # round up to this many seconds

TIMEOUT_LINE = re.compile(r"^timeout:.*\n?", re.MULTILINE)


def compute_timeouts(official_wall: dict[str, float], budget_factor: float, alpha: float,
                     min_official: float) -> dict[str, int]:
    """Distribute budget_factor * sum(official_wall) as timeout = c * w^alpha."""
    budget = budget_factor * sum(official_wall.values())
    w = {yaml_file: max(min_official, wall) for yaml_file, wall in official_wall.items()}
    c = budget / sum(x ** alpha for x in w.values())
    return {
        yaml_file: math.ceil(c * x ** alpha / ROUND_TO) * ROUND_TO
        for yaml_file, x in w.items()
    }


def format_duration(seconds: float) -> str:
    if seconds >= 3600:
        return f"{seconds / 3600:.1f}h"
    elif seconds >= 60:
        return f"{seconds / 60:.1f}m"
    else:
        return f"{seconds:.1f}s"


def load_results(source: str) -> dict:
    if source.startswith("http://") or source.startswith("https://"):
        print(f"Fetching {source} ...")
        with urllib.request.urlopen(source) as resp:
            return json.load(resp)
    with open(source) as f:
        return json.load(f)


def set_timeout_in_yaml(yaml_path: Path, timeout: int | None) -> None:
    """Set (or with None, remove) the top-level `timeout` key, preserving the rest of the file verbatim."""
    text = yaml_path.read_text()
    if timeout is None:
        text = TIMEOUT_LINE.sub("", text, count=1)
    elif TIMEOUT_LINE.search(text):
        text = TIMEOUT_LINE.sub(f"timeout: {timeout}\n", text, count=1)
    else:
        if text and not text.endswith("\n"):
            text += "\n"
        text += f"timeout: {timeout}\n"
    yaml_path.write_text(text)
    # Sanity check that the edit did what we intended
    if yaml.safe_load(text).get("timeout") != timeout:
        sys.exit(f"Error: failed to set timeout in {yaml_path}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--results", default=RESULTS_URL,
                        help=f"results.json to use, URL or local file (default: {RESULTS_URL})")
    parser.add_argument("--official", default="official",
                        help="Name of the checker whose wall times the timeouts are based on (default: official)")
    parser.add_argument("--budget-factor", type=float, default=BUDGET_FACTOR,
                        help=f"Total timeout budget, in multiples of the total official wall time (default: {BUDGET_FACTOR})")
    parser.add_argument("--alpha", type=float, default=ALPHA,
                        help=f"Exponent of the power law distributing the budget; 1 is proportional, smaller values favour small tests (default: {ALPHA})")
    parser.add_argument("--min-official", type=float, default=MIN_OFFICIAL,
                        help=f"Official wall time is taken to be at least this many seconds (default: {MIN_OFFICIAL})")
    parser.add_argument("--dry-run", action="store_true",
                        help="Only report what would change, do not modify the YAML files")
    args = parser.parse_args()

    root = Path(__file__).resolve().parent
    data = load_results(args.results)
    meta = data.get("meta", {})
    print(f"Results from {meta.get('timestamp', '?')} (arena revision {meta.get('git_revision_short', '?')})")

    # Map tests to their YAML files
    yaml_of_test = {t["name"]: t["yaml_file"] for t in data["tests"]}
    tests_of_yaml: dict[str, list[str]] = {}
    for test_name, yaml_file in yaml_of_test.items():
        tests_of_yaml.setdefault(yaml_file, []).append(test_name)

    # Official wall time per YAML file: the slowest of its (sub)tests
    official_wall: dict[str, float] = {}
    for r in data["results"]:
        if r["checker"] != args.official:
            continue
        yaml_file = yaml_of_test.get(r["test"])
        if yaml_file is None:
            continue
        official_wall[yaml_file] = max(official_wall.get(yaml_file, 0.0), r["wall_time"])

    # Only consider YAML files present in this checkout; only those marked
    # compare-perf get a timeout, the others have theirs removed (if any)
    old_timeouts: dict[str, int | None] = {}
    selected: set[str] = set()
    for yaml_file in sorted(tests_of_yaml):
        yaml_path = root / yaml_file
        if not yaml_path.exists():
            print(f"  {yaml_file}: not in this checkout, skipping")
            continue
        config = yaml.safe_load(yaml_path.read_text())
        old_timeouts[yaml_file] = config.get("timeout")
        if not config.get("compare-perf"):
            continue
        if yaml_file not in official_wall:
            print(f"  {yaml_file}: no result for checker '{args.official}', leaving timeout unchanged")
            continue
        selected.add(yaml_file)
    total_official = sum(official_wall.values())
    official_wall = {y: w for y, w in official_wall.items() if y in selected}

    # Compute new timeouts and update the YAML files
    new_timeouts: dict[str, int | None] = compute_timeouts(official_wall, args.budget_factor, args.alpha, args.min_official)
    for yaml_file in old_timeouts:
        if yaml_file not in selected and old_timeouts[yaml_file] is not None:
            new_timeouts[yaml_file] = None
    print(f"Total official wall time {format_duration(total_official)}, "
          f"budget {format_duration(args.budget_factor * total_official)}, "
          f"sum of timeouts {format_duration(sum(t for t in new_timeouts.values() if t))} "
          f"over {len(official_wall)} tests (minimum {format_duration(min(t for t in new_timeouts.values() if t))})")

    changed = 0
    for yaml_file, new in new_timeouts.items():
        old = old_timeouts[yaml_file]
        if old == new:
            continue
        changed += 1
        old_str = format_duration(old) if old is not None else "none"
        if new is None:
            print(f"  {yaml_file}: {old_str} -> none (not compare-perf)")
        else:
            print(f"  {yaml_file}: {old_str} -> {format_duration(new)} "
                  f"(official: {format_duration(official_wall[yaml_file])}, {new / official_wall[yaml_file]:.1f}x)")
        if not args.dry_run:
            set_timeout_in_yaml(root / yaml_file, new)
    if changed == 0:
        print("  All timeouts are up to date.")
    elif args.dry_run:
        print(f"  {changed} file(s) would be updated (dry run).")
    else:
        print(f"  {changed} file(s) updated.")

    # Predict which checker runs are affected by the updated timeouts: those
    # whose wall time exceeds the new limit but not the old one (or vice versa)
    def exceeds(wall_time: float, limit: int | None) -> bool:
        return limit is not None and wall_time > limit

    newly_timed_out = []
    no_longer_timed_out = []
    for r in data["results"]:
        yaml_file = yaml_of_test.get(r["test"])
        if yaml_file not in new_timeouts:
            continue
        old_hit = exceeds(r["wall_time"], old_timeouts[yaml_file])
        new_hit = exceeds(r["wall_time"], new_timeouts[yaml_file])
        if new_hit and not old_hit:
            newly_timed_out.append(r)
        elif old_hit and not new_hit:
            no_longer_timed_out.append(r)

    def describe(r: dict) -> str:
        limit = new_timeouts[yaml_of_test[r["test"]]]
        limit_str = format_duration(limit) if limit is not None else "none"
        return (f"  {r['checker']} on {r['test']}: {r['status']} after {format_duration(r['wall_time'])} "
                f"(limit {limit_str})")

    print()
    if newly_timed_out:
        print(f"{len(newly_timed_out)} checker run(s) would now time out:")
        for r in sorted(newly_timed_out, key=lambda r: (r["checker"], r["test"])):
            print(describe(r))
    else:
        print("No checker run would newly time out.")
    if no_longer_timed_out:
        print(f"{len(no_longer_timed_out)} checker run(s) would no longer time out:")
        for r in sorted(no_longer_timed_out, key=lambda r: (r["checker"], r["test"])):
            print(describe(r))

    return 0


if __name__ == "__main__":
    sys.exit(main())
