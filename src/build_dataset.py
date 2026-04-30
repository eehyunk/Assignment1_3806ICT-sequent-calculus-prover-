"""
build the synthetic labeled dataset and save it to disk.
This script:
  1. generates a balanced labeled dataset
  2. adds curated FOL/quantifier formulas
  3. saves to JSON and pickle
  4. reports dataset statistics
"""

from __future__ import annotations

import sys
import json
import time
from pathlib import Path

# add src to path
sys.path.insert(0, str(Path(__file__).parent))

from generator import generate_labeled_dataset, add_curated_fol_formulas
from formula import (
    Formula,
    Top,
    Bottom,
    Prop,
    Relation,
    Not,
    And,
    Or,
    Implies,
    Forall,
    Exists,
)


def contains_fol(formula: Formula) -> bool:
    # return True if the formula contains FOL-specific elements
    if isinstance(formula, Relation):
        return True
    if isinstance(formula, (Forall, Exists)):
        return True
    if isinstance(formula, Not):
        return contains_fol(formula.operand)
    if isinstance(formula, (And, Or, Implies)):
        return contains_fol(formula.left) or contains_fol(formula.right)
    return False


def contains_quantifier(formula: Formula) -> bool:
    # return True if the formula contains ∀ or ∃
    if isinstance(formula, (Forall, Exists)):
        return True
    if isinstance(formula, Not):
        return contains_quantifier(formula.operand)
    if isinstance(formula, (And, Or, Implies)):
        return contains_quantifier(formula.left) or contains_quantifier(formula.right)
    return False


def contains_branching_connective(formula: Formula) -> bool:
    """
    return True if the formula contains ∧, ∨, or →.
    These connectives may create branches depending on the side of the sequent.
    """
    if isinstance(formula, (And, Or, Implies)):
        return True
    if isinstance(formula, Not):
        return contains_branching_connective(formula.operand)
    if isinstance(formula, (Forall, Exists)):
        return contains_branching_connective(formula.body)
    return False


def formula_depth(formula: Formula) -> int:
    # compute a simple syntactic depth measure
    if isinstance(formula, (Top, Bottom, Prop, Relation)):
        return 1
    if isinstance(formula, Not):
        return 1 + formula_depth(formula.operand)
    if isinstance(formula, (And, Or, Implies)):
        return 1 + max(formula_depth(formula.left), formula_depth(formula.right))
    if isinstance(formula, (Forall, Exists)):
        return 1 + formula_depth(formula.body)
    return 1


def count_connectives(formula: Formula) -> int:
    # count logical connectives and quantifiers
    if isinstance(formula, (Top, Bottom, Prop, Relation)):
        return 0
    if isinstance(formula, Not):
        return 1 + count_connectives(formula.operand)
    if isinstance(formula, (And, Or, Implies)):
        return 1 + count_connectives(formula.left) + count_connectives(formula.right)
    if isinstance(formula, (Forall, Exists)):
        return 1 + count_connectives(formula.body)
    return 0


def print_dataset_statistics(dataset: list[tuple[Formula, str]]) -> None:
    # print summary statistics for the generated synthetic dataset
    n = len(dataset)
    if n == 0:
        print("Dataset is empty.")
        return

    valid_count = sum(1 for _, label in dataset if label == "valid")
    not_proved_count = sum(1 for _, label in dataset if label == "not_proved")

    fol_count = sum(1 for f, _ in dataset if contains_fol(f))
    prop_count = n - fol_count

    quantifier_count = sum(1 for f, _ in dataset if contains_quantifier(f))
    branching_count = sum(1 for f, _ in dataset if contains_branching_connective(f))

    depths = [formula_depth(f) for f, _ in dataset]
    connective_counts = [count_connectives(f) for f, _ in dataset]

    print("\n" + "=" * 80)
    print("Synthetic Dataset Statistics")
    print("=" * 80)

    print(f"Total formulae: {n}")
    print(f"Valid: {valid_count} ({100 * valid_count / n:.1f}%)")
    print(f"Not proved: {not_proved_count} ({100 * not_proved_count / n:.1f}%)")

    print(f"Propositional formulae: {prop_count} ({100 * prop_count / n:.1f}%)")
    print(f"FOL formulae: {fol_count} ({100 * fol_count / n:.1f}%)")

    print(f"With quantifiers: {quantifier_count} ({100 * quantifier_count / n:.1f}%)")
    print(f"With branching connectives: {branching_count} ({100 * branching_count / n:.1f}%)")

    print(f"Average formula depth: {sum(depths) / n:.2f}")
    print(f"Max formula depth: {max(depths)}")

    print(f"Average connective count: {sum(connective_counts) / n:.2f}")
    print(f"Max connective count: {max(connective_counts)}")


def print_duplicate_check(dataset: list[tuple[Formula, str]]) -> None:
    # print duplicate statistics
    formula_strings = [str(f) for f, _ in dataset]
    unique_formula_strings = set(formula_strings)
    duplicate_count = len(formula_strings) - len(unique_formula_strings)

    print("\n" + "=" * 80)
    print("Duplication check")
    print("=" * 80)
    print(f"Total formulae: {len(formula_strings)}")
    print(f"Unique formulae: {len(unique_formula_strings)}")
    print(f"Duplicate formulae: {duplicate_count}")
    if formula_strings:
        print(f"Duplicate rate: {100 * duplicate_count / len(formula_strings):.1f}%")


def save_dataset(dataset: list[tuple[Formula, str]], filepath: Path) -> None:
    # save dataset to JSON and pickle
    serializable = [
        {"formula": str(f), "label": label}
        for f, label in dataset
    ]

    formula_strings = [str(f) for f, _ in dataset]
    unique_count = len(set(formula_strings))
    duplicate_count = len(formula_strings) - unique_count

    with open(filepath, "w", encoding="utf-8") as fp:
        json.dump(
            {
                "metadata": {
                    "dataset_type": "GenAI-assisted synthetic FOL/propositional benchmark with curated FOL additions",
                    "size": len(dataset),
                    "unique_formula_count": unique_count,
                    "duplicate_count": duplicate_count,
                    "duplicate_rate": (duplicate_count / len(formula_strings) if formula_strings else 0),
                    "note": (
                        "The label not_proved is an operational label, "
                        "not a semantic proof of invalidity."
                    ),
                },
                "label_counts": {
                    "valid": sum(1 for _, lbl in dataset if lbl == "valid"),
                    "not_proved": sum(1 for _, lbl in dataset if lbl == "not_proved"),
                },
                "formulas": serializable,
            },
            fp,
            indent=2,
            ensure_ascii=False,
        )

    # Also save as pickle for direct loading in experiment scripts.
    import pickle

    pickle_path = filepath.with_suffix(".pkl")
    with open(pickle_path, "wb") as fp:
        pickle.dump(dataset, fp)

    print(f"\n✓ Saved JSON to:   {filepath}")
    print(f"✓ Saved pickle to: {pickle_path}")


if __name__ == "__main__":
    # Configuration
    N_TARGET = 1000
    CURATED_FOL_EXTRA = 100
    SEED = 42
    TIMEOUT_PER_FORMULA = 2.0
    MAX_ATTEMPTS = 5000
    VALID_RATIO = 0.5

    # Output directory
    output_dir = Path(__file__).parent.parent / "data"
    output_dir.mkdir(exist_ok=True)
    output_file = output_dir / "synthetic_dataset.json"

    print("=" * 80)
    print("Building Synthetic Dataset")
    print("=" * 80)
    print(f"Random target size: {N_TARGET}")
    print(f"Curated FOL extra: {CURATED_FOL_EXTRA}")
    print(f"Valid ratio: {VALID_RATIO:.0%}")
    print(f"Timeout per item: {TIMEOUT_PER_FORMULA}s")
    print(f"Seed: {SEED}")
    print(f"Output: {output_file}")
    print("=" * 80)

    start = time.perf_counter()

    dataset = generate_labeled_dataset(
        n_target=N_TARGET,
        seed=SEED,
        timeout_seconds=TIMEOUT_PER_FORMULA,
        max_attempts=MAX_ATTEMPTS,
        valid_ratio=VALID_RATIO,
    )

    dataset = add_curated_fol_formulas(
        dataset,
        target_extra=CURATED_FOL_EXTRA,
        timeout_seconds=TIMEOUT_PER_FORMULA,
    )

    elapsed = time.perf_counter() - start

    print(f"\n  Total time: {elapsed:.1f}s ({elapsed / 60:.1f}min)")
    if dataset:
        print(f" Average per formula: {elapsed / len(dataset):.2f}s")

    print_dataset_statistics(dataset)
    print_duplicate_check(dataset)
    save_dataset(dataset, output_file)

    print("\n" + "=" * 80)
    print("Dataset build complete")
    print("=" * 80)
