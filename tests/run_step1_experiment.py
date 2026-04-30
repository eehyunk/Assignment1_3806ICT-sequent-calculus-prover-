"""
run_step1_experiment.py

Step 1 experiment: standard benchmark suite
Combines:
  - Custom Test Suite (Tests 1-10) — designed to exercise Algorithm 2
  - Pelletier 1-17 (propositional) — standard benchmark from Pelletier (1986)

Generates a qualitative comparison table for the report.
"""

import sys
import csv
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from baseline import run_baseline
from improved import run_improved
from test_formulae import ALL_TESTS
from pelletier import get_pelletier_1_17_formulas


# Configuration
TIMEOUT_SECONDS = 5.0


# Run Experiment
def normalize_status(status: str) -> str:
    """Normalize old status names for consistency."""
    if status == "invalid":
        return "not_proved"
    return status

def run_one(name: str, formula, expected: str):
    """Run baseline + improved on a single formula."""
    b_result = run_baseline(formula, timeout_seconds=TIMEOUT_SECONDS)
    i_result = run_improved(formula, timeout_seconds=TIMEOUT_SECONDS)

    b_status = normalize_status(b_result.status)
    i_status = normalize_status(i_result.status)
    
    return {
        "name": name,
        "formula": str(formula),
        "expected": expected,
        "baseline_status": b_status,
        "baseline_time": b_result.elapsed_time,
        "improved_status": i_status,
        "improved_time": i_result.elapsed_time,
    }


def collect_results():
    """Collect results for both Custom Test Suite and Pelletier 1-17."""
    results = []
    
    # Section A: custon test (Tests 1-10) 
    print("=" * 80)
    print("  Section A: Custom Test (Tests 1-10)")
    print("=" * 80)
    
    for test in ALL_TESTS:
        result = run_one(
            name=test['name'],
            formula=test['formula'],
            expected=test['expected'],
        )
        result['section'] = 'Custom Test'
        results.append(result)
        print_one_result(result)
    
    # Section B: Pelletier 1-17 Problems
    print("\n" + "=" * 80)
    print("  Section B: Pelletier 1-17 Problems (Propositional Logic)")
    print("=" * 80)
    
    pelletier_problems = get_pelletier_1_17_formulas()
    for name, formula in pelletier_problems:
        result = run_one(
            name=name,
            formula=formula,
            expected="valid",  # Pelletier problems are all valid theorems
        )
        result['section'] = 'Pelletier'
        results.append(result)
        print_one_result(result)
    
    return results


def print_one_result(result: dict):
    """Print one experiment result in a readable format."""
    name = result['name'][:40]
    expected = result['expected']
    b_status = result['baseline_status']
    i_status = result['improved_status']
    b_time = result['baseline_time']
    i_time = result['improved_time']
    
    # Symbols
    b_correct = (b_status == expected) or (expected == "invalid" and b_status == "not_proved")
    i_correct = (i_status == expected) or (expected == "invalid" and i_status == "not_proved")
    b_sym = "✓" if b_correct else "✗"
    i_sym = "✓" if i_correct else "✗"
    
    # Format
    print(f"  {name:42s}  "
          f"B: {b_sym} {b_status:11s} {b_time:7.4f}s  |  "
          f"I: {i_sym} {i_status:11s} {i_time:7.4f}s")


# Analysis
def analyze(results):
    """Print summary statistics."""
    print("\n" + "=" * 80)
    print("  Summary Analysis")
    print("=" * 80)
    
    n = len(results)
    
    # Correctness counts
    def is_correct(r, prover_prefix):
        s = r[f'{prover_prefix}_status']
        e = r['expected']
        return s == e or (e == "invalid" and s == "not_proved")
    
    b_correct = sum(1 for r in results if is_correct(r, 'baseline'))
    i_correct = sum(1 for r in results if is_correct(r, 'improved'))
    
    # Timeout counts
    b_timeouts = sum(1 for r in results if r['baseline_status'] == 'timeout')
    i_timeouts = sum(1 for r in results if r['improved_status'] == 'timeout')
    
    # Speedup analysis (when both completed)
    speedups = []
    for r in results:
        b_t = r['baseline_time']
        i_t = r['improved_time']
        if r['baseline_status'] != 'timeout' and r['improved_status'] != 'timeout':
            if i_t > 0:
                speedups.append(b_t / max(i_t, 0.0001))
    
    print(f"Total formulae tested: {n}")
    print(f"Baseline matched expected: {b_correct}/{n} ({100*b_correct/n:.1f}%)")
    print(f"Improved matched expected: {i_correct}/{n} ({100*i_correct/n:.1f}%)")
    print(f"Baseline timeouts: {b_timeouts}")
    print(f"Improved timeouts: {i_timeouts}")
    
    if speedups:
        avg_speedup = sum(speedups) / len(speedups)
        max_speedup = max(speedups)
        print(f"Average time ratio (baseline/improved): {avg_speedup:.2f}x")
        print(f"Max speedup observed: {max_speedup:.2f}x")



# CSV file exported
def save_csv(results, output_dir):
    """Save results to CSV for use in the report."""
    csv_path = output_dir / "step1_results.csv"
    
    with open(csv_path, 'w', newline='', encoding='utf-8') as fp:
        writer = csv.DictWriter(fp, fieldnames=[
            'section', 'name', 'expected',
            'baseline_status', 'baseline_time',
            'improved_status', 'improved_time',
            'formula'
        ])
        writer.writeheader()
        writer.writerows(results)
    
    print(f"\n✓ Saved CSV to: {csv_path}")



# Main 
if __name__ == "__main__":
    output_dir = Path(__file__).parent.parent / "data"
    output_dir.mkdir(exist_ok=True)
    
    print("=" * 80)
    print("  STEP 1 Experiment: Standard Benchmark")
    print("=" * 80)
    print(f"  Custom Test: 10 formulae")
    print(f"  Pelletier 1-17 Problems: 17 formulae")
    print(f"  Timeout: {TIMEOUT_SECONDS}s per formula")
    print()
    
    start = time.perf_counter()
    results = collect_results()
    elapsed = time.perf_counter() - start
    
    analyze(results)
    
    print(f"\n Total experiment time: {elapsed:.1f}s")
    
    save_csv(results, output_dir)
    
    print("\n" + "=" * 80)
    print("  Step 1 Experiment is finished")
    print("=" * 80)