"""
run_step3_fol_challenge_experiment.py

Step 3 experiment: first-order challenge benchmark.
Runs baseline and improved provers on manually encoded Pelletier Problems 18-34.

Purpose:
  - Complement the large synthetic dataset.
  - Test quantifier-heavy first-order formulas.
  - Compare timeout/solved behaviour of the baseline and improved provers.
"""

import sys
import csv
import time
from pathlib import Path

# Allow this file to be run from the tests/ folder while importing modules from src/.
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from baseline import run_baseline
from improved import run_improved
from pelletier import get_pelletier_18_34_formulas


# configuration
TIMEOUT_SECONDS = 60.0
OUTPUT_FILENAME = "step3_fol_challenge_results_60s.csv"



# run experiment
def normalize_status(status: str) -> str:
    """Normalize old status names for consistency."""
    if status == "invalid":
        return "not_proved"
    return status

def safe_run(prover_fn, formula):
    """
    Run a prover safely.

    Some hard first-order formulas can make the recursive baseline prover
    exceed Python's recursion limit before the timeout is returned.
    In this experiment, we treat RecursionError as a resource-limit outcome.
    """
    start = time.perf_counter()

    try:
        result = prover_fn(formula, timeout_seconds=TIMEOUT_SECONDS)
        return normalize_status(result.status), result.elapsed_time

    except RecursionError:
        # This is not a syntax error. It means the recursive proof search
        # became too deep on this hard FOL benchmark.
        return "timeout", time.perf_counter() - start

    except TimeoutError:
        return "timeout", time.perf_counter() - start

    except Exception as exc:
        # Keep the experiment running even if one formula causes an error.
        return f"error:{type(exc).__name__}", time.perf_counter() - start


def run_one(name: str, formula, expected: str = "valid"):
    """Run baseline + improved on a single Pelletier FOL challenge formula."""
    b_status, b_time = safe_run(run_baseline, formula)
    i_status, i_time = safe_run(run_improved, formula)

    return {
        "section": "Pelletier 18-34 FOL Challenge",
        "name": name,
        "formula": str(formula),
        "expected": expected,
        "baseline_status": b_status,
        "baseline_time": b_time,
        "improved_status": i_status,
        "improved_time": i_time,
        "same_status": b_status == i_status,
        "improved_succeeded_baseline_timeout": (
            b_status == "timeout" and i_status == "valid"
        ),
        "baseline_succeeded_improved_timeout": (
            b_status == "valid" and i_status == "timeout"
        ),
    }


def collect_results():
    """Collect results for Pelletier Problems 18-34."""
    results = []
    problems = get_pelletier_18_34_formulas()

    print("=" * 80)
    print("  Section: Pelletier 18-34 First-Order Challenge")
    print("=" * 80)

    for name, formula in problems:
        result = run_one(name=name, formula=formula, expected="valid")
        results.append(result)
        print_one_result(result)

    return results


def print_one_result(result: dict):
    """Print one experiment result in a readable format."""
    name = result["name"][:40]
    expected = result["expected"]
    b_status = result["baseline_status"]
    i_status = result["improved_status"]
    b_time = result["baseline_time"]
    i_time = result["improved_time"]

    b_matched = b_status == expected
    i_matched = i_status == expected
    b_sym = "✓" if b_matched else "✗"
    i_sym = "✓" if i_matched else "✗"

    print(
        f"  {name:42s}  "
        f"B: {b_sym} {b_status:11s} {b_time:7.4f}s  |  "
        f"I: {i_sym} {i_status:11s} {i_time:7.4f}s"
    )


# Analysis
def analyze(results):
    """Print summary statistics for the FOL challenge benchmark."""
    print("\n" + "=" * 80)
    print("  Summary Analysis")
    print("=" * 80)

    n = len(results)

    baseline_valid = sum(1 for r in results if r["baseline_status"] == "valid")
    improved_valid = sum(1 for r in results if r["improved_status"] == "valid")

    baseline_not_proved = sum(1 for r in results if r["baseline_status"] == "not_proved")
    improved_not_proved = sum(1 for r in results if r["improved_status"] == "not_proved")

    baseline_timeouts = sum(1 for r in results if r["baseline_status"] == "timeout")
    improved_timeouts = sum(1 for r in results if r["improved_status"] == "timeout")

    improved_succeeded_baseline_timeout = sum(
        1 for r in results if r["improved_succeeded_baseline_timeout"]
    )
    baseline_succeeded_improved_timeout = sum(
        1 for r in results if r["baseline_succeeded_improved_timeout"]
    )

    both_timeout = sum(
        1
        for r in results
        if r["baseline_status"] == "timeout" and r["improved_status"] == "timeout"
    )

    same_status = sum(1 for r in results if r["same_status"])

    completed_by_both = [
        r
        for r in results
        if r["baseline_status"] != "timeout" and r["improved_status"] != "timeout"
    ]

    b_completed_times = [
        r["baseline_time"] for r in results if r["baseline_status"] != "timeout"
    ]
    i_completed_times = [
        r["improved_time"] for r in results if r["improved_status"] != "timeout"
    ]

    print(f"Total formulae tested: {n}")
    print(f"Same status: {same_status}/{n} ({100*same_status/n:.1f}%)")
    print()
    print("Status distribution:")
    print(f"  Baseline valid: {baseline_valid}/{n}")
    print(f"  Improved valid: {improved_valid}/{n}")
    print(f"  Baseline not_proved: {baseline_not_proved}/{n}")
    print(f"  Improved not_proved: {improved_not_proved}/{n}")
    print(f"  Baseline timeout: {baseline_timeouts}/{n}")
    print(f"  Improved timeout: {improved_timeouts}/{n}")
    print()
    print("Notable cases:")
    print(f"  Improved valid, baseline timeout: {improved_succeeded_baseline_timeout}")
    print(f"  Baseline valid, improved timeout: {baseline_succeeded_improved_timeout}")
    print(f"  Both timeout: {both_timeout}")
    print()

    if b_completed_times:
        print(f"Avg baseline time excluding timeouts: {sum(b_completed_times)/len(b_completed_times):.4f}s")
    else:
        print("Avg baseline time excluding timeouts: N/A")

    if i_completed_times:
        print(f"Avg improved time excluding timeouts: {sum(i_completed_times)/len(i_completed_times):.4f}s")
    else:
        print("Avg improved time excluding timeouts: N/A")

    # Time ratio is only useful for cases that take a non-trivial amount of time.
    nontrivial = []
    for r in completed_by_both:
        b_t = r["baseline_time"]
        i_t = r["improved_time"]
        if b_t > 0.001 and i_t > 0:
            nontrivial.append(b_t / i_t)

    print()
    print("Time ratio analysis (baseline/improved, cases > 0.001s):")
    print(f"  Sample size: {len(nontrivial)}")
    if nontrivial:
        print(f"  Mean time ratio: {sum(nontrivial)/len(nontrivial):.2f}x")
        print(f"  Max time ratio: {max(nontrivial):.2f}x")
        print(f"  Min time ratio: {min(nontrivial):.2f}x")
    else:
        print("  Not enough non-trivial completed cases for a stable time-ratio analysis.")


# CSV Export
def save_csv(results, output_dir: Path):
    """Save results to CSV for use in the report."""
    csv_path = output_dir / OUTPUT_FILENAME

    with open(csv_path, "w", newline="", encoding="utf-8") as fp:
        writer = csv.DictWriter(
            fp,
            fieldnames=[
                "section",
                "name",
                "expected",
                "baseline_status",
                "baseline_time",
                "improved_status",
                "improved_time",
                "same_status",
                "improved_succeeded_baseline_timeout",
                "baseline_succeeded_improved_timeout",
                "formula",
            ],
        )
        writer.writeheader()
        writer.writerows(results)

    print(f"\n✓ Saved CSV to: {csv_path}")


# main
if __name__ == "__main__":
    output_dir = Path(__file__).parent.parent / "data"
    output_dir.mkdir(exist_ok=True)

    problems = get_pelletier_18_34_formulas()

    print("=" * 80)
    print("  Step 3 Experiment: FOL Challenge Benchmark")
    print("=" * 80)
    print(f"  Pelletier 18-34 Problems: {len(problems)} formulae")
    print(f"  Timeout: {TIMEOUT_SECONDS}s per formula")
    print()

    start = time.perf_counter()
    results = collect_results()
    elapsed = time.perf_counter() - start

    analyze(results)

    print(f"\n  Total experiment time: {elapsed:.1f}s")

    save_csv(results, output_dir)

    print("\n" + "=" * 80)
    print("  Step 3 Experiment is finished")
    print("=" * 80)
