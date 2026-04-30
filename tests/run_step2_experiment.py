"""
run_step2_experiment.py

Step 2 experiment: large-scale synthetic dataset
Run baseline + improved on all 1081 synthetic formulas.
Generates quantitative comparison statistics for the report.
"""

import sys
import csv
import time
import pickle
import statistics
from pathlib import Path
from dataclasses import dataclass

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from baseline import run_baseline
from improved import run_improved


# Configuration
TIMEOUT_SECONDS = 5.0
DATASET_PATH = Path(__file__).parent.parent / "data" / "synthetic_dataset.pkl"
OUTPUT_DIR = Path(__file__).parent.parent / "data"
PROGRESS_INTERVAL = 50  # Print progress every N formulas


# Load dataset
def load_dataset():
    """Load the synthetic dataset from pickle."""
    if not DATASET_PATH.exists():
        raise FileNotFoundError(
            f"Dataset not found at {DATASET_PATH}. "
            f"Run build_dataset.py first."
        )
    
    with open(DATASET_PATH, "rb") as fp:
        dataset = pickle.load(fp)
    
    return dataset

@dataclass
class SafeResult:
    status: str
    elapsed_time: float


def safe_run(prover_fn, formula):
    """
    Run a prover safely.

    Some first-order formulas can make the recursive baseline prover
    exceed Python's recursion limit before the timeout is returned.
    In this experiment, RecursionError is treated as a resource-limit
    outcome, equivalent to timeout.
    """
    start = time.perf_counter()

    try:
        result = prover_fn(formula, timeout_seconds=TIMEOUT_SECONDS)

        status = result.status
        if status == "invalid":
            status = "not_proved"

        return SafeResult(status=status, elapsed_time=result.elapsed_time)

    except RecursionError:
        return SafeResult(
            status="timeout",
            elapsed_time=time.perf_counter() - start,
        )

    except TimeoutError:
        return SafeResult(
            status="timeout",
            elapsed_time=time.perf_counter() - start,
        )
    

# Run Experiment
def run_experiment(dataset):
    """Run both provers on every formula in the dataset."""
    results = []
    n = len(dataset)
    
    print(f"\nRunning experiment on {n} formulae...")
    print(f"Timeout per formula: {TIMEOUT_SECONDS}s\n")
    
    start_total = time.perf_counter()
    
    for idx, (formula, expected_label) in enumerate(dataset, start=1):
        # Run baseline safely 
        b_result = safe_run(run_baseline, formula)
        
        # Run improved safely
        i_result = safe_run(run_improved, formula)
        
        results.append({
            "index": idx,
            "formula": str(formula),
            "expected": expected_label,
            "baseline_status": b_result.status,
            "baseline_time": b_result.elapsed_time,
            "improved_status": i_result.status,
            "improved_time": i_result.elapsed_time,
        })
        
        # Progress indicator
        if idx % PROGRESS_INTERVAL == 0 or idx == n:
            elapsed = time.perf_counter() - start_total
            rate = idx / elapsed
            eta = (n - idx) / rate if rate > 0 else 0
            print(f"  Progress: {idx}/{n} "
                  f"({100*idx/n:.1f}%) | "
                  f"elapsed: {elapsed:.1f}s | "
                  f"rate: {rate:.1f}/s | "
                  f"ETA: {eta:.0f}s")
    
    total_elapsed = time.perf_counter() - start_total
    print(f"\n✓ Experiment is finished in {total_elapsed:.1f}s ({total_elapsed/60:.1f}min)")
    
    return results, total_elapsed


# Analysis
def analyze(results):
    """Compute and print summary statistics."""
    n = len(results)
    
    # correctness
    def is_correct(r, prover_prefix):
        s = r[f'{prover_prefix}_status']
        e = r['expected']
        return s == e or (e == "invalid" and s == "not_proved")
    
    b_correct = sum(1 for r in results if is_correct(r, 'baseline'))
    i_correct = sum(1 for r in results if is_correct(r, 'improved'))
    
    # Timeout
    b_timeouts = sum(1 for r in results if r['baseline_status'] == 'timeout')
    i_timeouts = sum(1 for r in results if r['improved_status'] == 'timeout')
    
    # status distribution
    def status_counts(prover_prefix):
        counts = {}
        for r in results:
            s = r[f'{prover_prefix}_status']
            counts[s] = counts.get(s, 0) + 1
        return counts
    
    b_counts = status_counts('baseline')
    i_counts = status_counts('improved')
    
    # time analysis (excluding timeout)
    b_times_no_timeout = [r['baseline_time'] for r in results 
                          if r['baseline_status'] != 'timeout']
    i_times_no_timeout = [r['improved_time'] for r in results 
                          if r['improved_status'] != 'timeout']
    
  
    # speedup analysis
    # Only consider cases where BOTH completed (no timeout)
    speedups = []
    speedup_details = []  # store (baseline_time, improved_time, speedup) for analysis
    
    for r in results:
        b_t = r['baseline_time']
        i_t = r['improved_time']
        if r['baseline_status'] != 'timeout' and r['improved_status'] != 'timeout':
            # Skip very small times (noise)
            if b_t > 0.001 and i_t > 0.0001:
                speedup = b_t / i_t
                speedups.append(speedup)
                speedup_details.append((b_t, i_t, speedup))
    

    # results
    print("\n" + "=" * 80)
    print("  Step 2: Large Scale Synthetic Experiment - results ")
    print("=" * 80)
    
    print(f"\n Dataset Size: {n} formulae")
    
    print(f"\n Correctness:")
    print(f"  Baseline: {b_correct}/{n} ({100*b_correct/n:.1f}%)")
    print(f"  Improved: {i_correct}/{n} ({100*i_correct/n:.1f}%)")
    
    print(f"\n Status Distribution:")
    print(f"  {'Status':<15s} {'Baseline':>10s} {'Improved':>10s}")
    all_statuses = set(b_counts.keys()) | set(i_counts.keys())
    for status in sorted(all_statuses):
        b_c = b_counts.get(status, 0)
        i_c = i_counts.get(status, 0)
        print(f"  {status:<15s} {b_c:>10d} {i_c:>10d}")
    
    print(f"\n Timeout:")
    print(f"  Baseline: {b_timeouts} ({100*b_timeouts/n:.1f}%)")
    print(f"  Improved: {i_timeouts} ({100*i_timeouts/n:.1f}%)")
    print(f"  Difference:{b_timeouts - i_timeouts:+d}")
    
    if b_times_no_timeout:
        print(f"\n Solve Times (exclude timeout):")
        print(f"  {'Metric':<20s} {'Baseline':>12s} {'Improved':>12s}")
        print(f"  {'Mean':<20s} {statistics.mean(b_times_no_timeout):>10.4f}s  "
              f"{statistics.mean(i_times_no_timeout):>10.4f}s")
        print(f"  {'Median':<20s} {statistics.median(b_times_no_timeout):>10.4f}s  "
              f"{statistics.median(i_times_no_timeout):>10.4f}s")
        print(f"  {'Max':<20s} {max(b_times_no_timeout):>10.4f}s  "
              f"{max(i_times_no_timeout):>10.4f}s")
        if len(b_times_no_timeout) > 1:
            print(f"  {'Stdev':<20s} {statistics.stdev(b_times_no_timeout):>10.4f}s  "
                  f"{statistics.stdev(i_times_no_timeout):>10.4f}s")
    
    if speedups:
        print(f"\n Speedup Analysis (formulae > 0.001s, both completed):")
        print(f"  Sample size: {len(speedups)}")
        print(f"  Mean speedup: {statistics.mean(speedups):.2f}x")
        print(f"  Median speedup: {statistics.median(speedups):.2f}x")
        print(f"  Max speedup: {max(speedups):.2f}x")
        print(f"  Min speedup: {min(speedups):.2f}x")
        
        # How many cases where improved is faster?
        improved_faster = sum(1 for s in speedups if s > 1.0)
        improved_slower = sum(1 for s in speedups if s < 1.0)
        print(f"\n  Improved faster: {improved_faster}/{len(speedups)} "
              f"({100*improved_faster/len(speedups):.1f}%)")
        print(f"  Improved slower: {improved_slower}/{len(speedups)} "
              f"({100*improved_slower/len(speedups):.1f}%)")
    
    # ---- Notable cases ----
    print(f"\n Notable Cases:")
    
    # Cases where improved succeeded but baseline timed out
    improved_wins = [r for r in results 
                     if r['baseline_status'] == 'timeout' 
                     and r['improved_status'] != 'timeout']
    print(f"  Improved succeeded, baseline timeout: {len(improved_wins)}")
    
    # Cases where baseline succeeded but improved timed out
    baseline_wins = [r for r in results 
                     if r['improved_status'] == 'timeout' 
                     and r['baseline_status'] != 'timeout']
    print(f"  Baseline succeeded, improved timeout: {len(baseline_wins)}")
    
    return {
        'n': n,
        'baseline_correct': b_correct,
        'improved_correct': i_correct,
        'baseline_timeouts': b_timeouts,
        'improved_timeouts': i_timeouts,
        'speedup_data': speedup_details,
        'improved_wins': len(improved_wins),
        'baseline_wins': len(baseline_wins),
    }


# CSV Export
def save_results(results, output_dir):
    """Save full results to CSV."""
    csv_path = output_dir / "step2_results.csv"
    
    with open(csv_path, 'w', newline='', encoding='utf-8') as fp:
        writer = csv.DictWriter(fp, fieldnames=[
            'index', 'expected',
            'baseline_status', 'baseline_time',
            'improved_status', 'improved_time',
            'formula',
        ])
        writer.writeheader()
        writer.writerows(results)
    
    print(f"\n✓ Saved CSV to: {csv_path}")


# Main
if __name__ == "__main__":
    print("=" * 80)
    print("  Step 2 Experiment: Large Scale Synthetic Evaluation")
    print("=" * 80)
    print(f"  Dataset: {DATASET_PATH.name}")
    print(f"  Timeout: {TIMEOUT_SECONDS}s per formula")
    print()
    
    # Load dataset
    print("Loading dataset...")
    dataset = load_dataset()
    print(f"✓ Loaded {len(dataset)} formulae")
    
    # Run experiment
    results, total_time = run_experiment(dataset)
    
    # Analyze
    summary = analyze(results)
    
    # Save
    save_results(results, OUTPUT_DIR)
    
    print("\n" + "=" * 80)
    print("  Step 2 Experiment is finished")
    print("=" * 80)