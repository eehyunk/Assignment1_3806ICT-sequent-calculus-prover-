"""
Synthetic dataset generator: creates random propositional and FOL formulae
for benchmarking baseline vs improved prover.

Strategy:
  1. create random formulae with variable count and controlled path 
  2. to identify an operaitional label, use baseline  + improved
  3. filter out timeouts, disagreements, errors
  4. add carefully chosen FOL / quantifier formulae if desired. 
"""

from __future__ import annotations

import random
from typing import List, Tuple, Optional

from formula import (
    Formula,
    Term,
    Top,
    Bottom,
    Prop,
    Relation,
    Var,
    Const,
    Not,
    And,
    Or,
    Implies,
    Forall,
    Exists,
)


class FormulaGenerator:
    # generates random propositional and first-order formulas
    def __init__(self, seed: int = 42):
        # initialize with a seed for reproducibility
        self.rng = random.Random(seed)

        # variable pools — kept small so atoms repeat
        # this increases the chance that proof branches can close by [id] rule
        self.prop_names = ["A", "B", "C", "D", "E"]
        self.pred_names = ["P", "Q", "R"]
        self.const_names = ["a", "b", "c"]
        self.var_names = ["x", "y", "z"]

    def random_proposition(self) -> Formula:
        # pick a random atomic proposition or logical constant
        choice = self.rng.random()
        if choice < 0.05:
            return Top()
        elif choice < 0.10:
            return Bottom()
        else:
            name = self.rng.choice(self.prop_names)
            return Prop(name)

    def random_propositional(self, depth: int) -> Formula:
        # generate a random propositional formula with the given depth
        if depth <= 0:
            return self.random_proposition()

        connective = self.rng.choices(
            ["not", "and", "or", "implies", "atom"],
            weights=[15, 25, 25, 25, 10],
        )[0]

        if connective == "atom":
            return self.random_proposition()
        elif connective == "not":
            return Not(self.random_propositional(depth - 1))
        elif connective == "and":
            return And(
                self.random_propositional(depth - 1),
                self.random_propositional(depth - 1),
            )
        elif connective == "or":
            return Or(
                self.random_propositional(depth - 1),
                self.random_propositional(depth - 1),
            )
        else:  # implies
            return Implies(
                self.random_propositional(depth - 1),
                self.random_propositional(depth - 1),
            )

    def random_term(self, available_vars: List[str]) -> Term:
        # pick a random term: a variable from available_vars or a constant
        if available_vars and self.rng.random() < 0.5:
            name = self.rng.choice(available_vars)
            return Var(name)
        else:
            name = self.rng.choice(self.const_names)
            return Const(name)

    def random_atom_fol(self, available_vars: List[str]) -> Formula:
        # generate an atomic FOL formula, e.g., P(x) or R(a, y)
        choice = self.rng.random()
        if choice < 0.05:
            return Top()
        elif choice < 0.10:
            return Bottom()
        else:
            pred_name = self.rng.choice(self.pred_names)
            arity = self.rng.choice([1, 2])
            args = tuple(self.random_term(available_vars) for _ in range(arity))
            return Relation(pred_name, args)

    def random_fol(self, depth: int, available_vars: Optional[List[str]] = None) -> Formula:
        # generate a random FOL formula with optional quantifiers
        if available_vars is None:
            available_vars = []

        if depth <= 0:
            return self.random_atom_fol(available_vars)

        connective = self.rng.choices(
            ["not", "and", "or", "implies", "forall", "exists", "atom"],
            weights=[10, 18, 18, 18, 12, 12, 12],
        )[0]

        if connective == "atom":
            return self.random_atom_fol(available_vars)
        elif connective == "not":
            return Not(self.random_fol(depth - 1, available_vars))
        elif connective == "and":
            return And(
                self.random_fol(depth - 1, available_vars),
                self.random_fol(depth - 1, available_vars),
            )
        elif connective == "or":
            return Or(
                self.random_fol(depth - 1, available_vars),
                self.random_fol(depth - 1, available_vars),
            )
        elif connective == "implies":
            return Implies(
                self.random_fol(depth - 1, available_vars),
                self.random_fol(depth - 1, available_vars),
            )
        elif connective == "forall":
            var_name = self.rng.choice(self.var_names)
            new_available = available_vars + [var_name]
            body = self.random_fol(depth - 1, new_available)
            return Forall(var_name, body)
        else:  # exists
            var_name = self.rng.choice(self.var_names)
            new_available = available_vars + [var_name]
            body = self.random_fol(depth - 1, new_available)
            return Exists(var_name, body)

    def random_valid_propositional(self, depth: int) -> Formula:
        a = self.random_propositional(depth=depth)
        b = self.random_propositional(depth=depth)
        c = self.random_propositional(depth=depth)

        schema = self.rng.choice([
            "identity",          # A → A
            "and_elim_left",     # (A ∧ B) → A
            "and_elim_right",    # (A ∧ B) → B
            "or_intro_left",     # A → (A ∨ B)
            "or_intro_right",    # B → (A ∨ B)
            "excluded_middle",   # A ∨ ¬A
            "double_neg",        # ¬¬A → A
            "contrapositive",    # (A → B) → (¬B → ¬A)
            "transitivity",      # ((A → B) ∧ (B → C)) → (A → C)
            "modus_ponens",      # (A ∧ (A → B)) → B
        ])

        if schema == "identity":
            return Implies(a, a)
        elif schema == "and_elim_left":
            return Implies(And(a, b), a)
        elif schema == "and_elim_right":
            return Implies(And(a, b), b)
        elif schema == "or_intro_left":
            return Implies(a, Or(a, b))
        elif schema == "or_intro_right":
            return Implies(b, Or(a, b))
        elif schema == "excluded_middle":
            return Or(a, Not(a))
        elif schema == "double_neg":
            return Implies(Not(Not(a)), a)
        elif schema == "contrapositive":
            return Implies(Implies(a, b), Implies(Not(b), Not(a)))
        elif schema == "transitivity":
            return Implies(And(Implies(a, b), Implies(b, c)), Implies(a, c))
        else:  # modus_ponens
            return Implies(And(a, Implies(a, b)), b)


# ============================================================
# Auto labeling & random datset generation
# ============================================================
def label_formula(formula: Formula, timeout_seconds: float = 2.0) -> Optional[str]:
    """
    Label a formula using consensus from baseline + improved.

    Returns:
    valid = if both provers say valid
    not_proved = if both provers say not_proved
    None = if uncertain, timeout, disagreement, or error

    Note: not_proved is an operational label, not a semantic proof of invalidity.
    """
    from baseline import run_baseline
    from improved import run_improved

    try:
        baseline_result = run_baseline(formula, timeout_seconds=timeout_seconds)
        improved_result = run_improved(formula, timeout_seconds=timeout_seconds)
    except Exception:
        return None

    b_status = baseline_result.status
    i_status = improved_result.status

    # normalise old status names for compatibility
    if b_status == "invalid":
        b_status = "not_proved"
    if i_status == "invalid":
        i_status = "not_proved"

    if b_status == "valid" and i_status == "valid":
        return "valid"
    elif b_status == "not_proved" and i_status == "not_proved":
        return "not_proved"
    else:
        return None


def generate_labeled_dataset(
    n_target: int = 1000,
    seed: int = 42,
    timeout_seconds: float = 2.0,
    max_attempts: int = 5000,
    valid_ratio: float = 0.5,
) -> List[Tuple[Formula, str]]:
    # generate a labeled dataset with a roughly balanced valid/not_proved ratio
    gen = FormulaGenerator(seed=seed)
    dataset: List[Tuple[Formula, str]] = []
    seen = set()
    attempts = 0

    print(f"Generating {n_target} labeled formulas (target valid ratio: {valid_ratio:.0%})...")

    while len(dataset) < n_target and attempts < max_attempts:
        attempts += 1

        n_valid_so_far = sum(1 for _, lbl in dataset if lbl == "valid")
        current_valid_ratio = n_valid_so_far / max(1, len(dataset))

        # If we need more valid formulas, generate from valid schemata more often.
        if current_valid_ratio < valid_ratio and gen.rng.random() < 0.6:
            depth = gen.rng.choice([1, 2, 3])
            formula = gen.random_valid_propositional(depth=depth)
        else:
            is_fol = gen.rng.random() < 0.4
            depth = gen.rng.choice([2, 3, 4])
            formula = gen.random_fol(depth=depth) if is_fol else gen.random_propositional(depth=depth)

        formula_key = str(formula)
        if formula_key in seen:
            continue

        label = label_formula(formula, timeout_seconds=timeout_seconds)
        if label is None:
            continue

        dataset.append((formula, label))
        seen.add(formula_key)

        if len(dataset) % 50 == 0:
            v_count = sum(1 for _, lbl in dataset if lbl == "valid")
            print(
                f"  Progress: {len(dataset)}/{n_target} "
                f"(valid: {v_count}, attempts: {attempts}, "
                f"success rate: {100 * len(dataset) / attempts:.1f}%)"
            )

    print(f"\nDone! {len(dataset)} formulas labeled in {attempts} attempts.")

    if dataset:
        valid_count = sum(1 for _, lbl in dataset if lbl == "valid")
        not_proved_count = sum(1 for _, lbl in dataset if lbl == "not_proved")
        print(f"  Valid:      {valid_count} ({100 * valid_count / len(dataset):.1f}%)")
        print(f"  Not proved: {not_proved_count} ({100 * not_proved_count / len(dataset):.1f}%)")

    return dataset


# ============================================================
# Curated FOL / quantifier formulae
# ============================================================
# generate_labeled_dataset(). This allows build_dataset.py to import
# add_curated_fol_formulas directly.
def _uv(pred: str, var: str) -> Relation:
    # unary relation with a variable argument, e.g., P(x)
    return Relation(pred, (Var(var),))


def _uc(pred: str, const: str) -> Relation:
    # unary relation with a constant argument, e.g., P(a)
    return Relation(pred, (Const(const),))


def _bv(rel: str, v1: str, v2: str) -> Relation:
    # binary relation with variable arguments, e.g., R(x, y)
    return Relation(rel, (Var(v1), Var(v2)))


def _bc(rel: str, c1: str, c2: str) -> Relation:
    # binary relation with constant arguments, e.g., R(a, b)
    return Relation(rel, (Const(c1), Const(c2)))


def curated_fol_candidates() -> List[Formula]:
    # return curated FOL / quantifier candidate formulae 
    # the final label is still checked by labe_formla()
    candidates: List[Formula] = []

    unary_pairs = [
        ("P", "Q"),
        ("P", "R"),
        ("Q", "R"),
        ("M", "N"),
        ("A1", "B1"),
    ]
    constants = ["a", "b", "c"]

    # unary predicate schemas.
    for p, q in unary_pairs:
        for c in constants:
            pc = _uc(p, c)
            qc = _uc(q, c)

            # valid / provable-style FOL formulas.
            candidates.append(Implies(Forall("x", _uv(p, "x")), pc))
            candidates.append(Implies(pc, Exists("x", _uv(p, "x"))))
            candidates.append(
                Implies(
                    Forall("x", Implies(_uv(p, "x"), _uv(q, "x"))),
                    Implies(pc, qc),
                )
            )

            # challenge / not_proved-style formulas.
            candidates.append(Implies(Exists("x", _uv(p, "x")), Forall("x", _uv(p, "x"))))
            candidates.append(Implies(pc, Forall("x", _uv(p, "x"))))
            candidates.append(Implies(Exists("x", _uv(p, "x")), pc))

        # more general valid schemas.
        candidates.append(
            Implies(
                Forall("x", Implies(_uv(p, "x"), _uv(q, "x"))),
                Implies(Forall("x", _uv(p, "x")), Forall("x", _uv(q, "x"))),
            )
        )
        candidates.append(
            Implies(
                Forall("x", Implies(_uv(p, "x"), _uv(q, "x"))),
                Implies(Exists("x", _uv(p, "x")), Exists("x", _uv(q, "x"))),
            )
        )
        candidates.append(Implies(Exists("x", _uv(p, "x")), Exists("x", Or(_uv(p, "x"), _uv(q, "x")))))
        candidates.append(
            Implies(
                Exists("x", And(_uv(p, "x"), _uv(q, "x"))),
                And(Exists("x", _uv(p, "x")), Exists("x", _uv(q, "x"))),
            )
        )
        candidates.append(
            Implies(
                And(Forall("x", _uv(p, "x")), Forall("x", _uv(q, "x"))),
                Forall("x", And(_uv(p, "x"), _uv(q, "x"))),
            )
        )
        candidates.append(
            Implies(
                Forall("x", And(_uv(p, "x"), _uv(q, "x"))),
                And(Forall("x", _uv(p, "x")), Forall("x", _uv(q, "x"))),
            )
        )
        candidates.append(Implies(Not(Exists("x", _uv(p, "x"))), Forall("x", Not(_uv(p, "x")))))
        candidates.append(Implies(Not(Forall("x", _uv(p, "x"))), Exists("x", Not(_uv(p, "x")))))

        # Challenge schema
        candidates.append(
            Implies(
                Forall("x", Or(_uv(p, "x"), _uv(q, "x"))),
                Or(Forall("x", _uv(p, "x")), Forall("x", _uv(q, "x"))),
            )
        )
        candidates.append(
            Implies(
                And(Exists("x", _uv(p, "x")), Exists("x", _uv(q, "x"))),
                Exists("x", And(_uv(p, "x"), _uv(q, "x"))),
            )
        )
        candidates.append(
            Implies(
                Exists("x", Or(_uv(p, "x"), _uv(q, "x"))),
                And(Exists("x", _uv(p, "x")), Exists("x", _uv(q, "x"))),
            )
        )
        candidates.append(
            Implies(
                Forall("x", Implies(_uv(p, "x"), _uv(q, "x"))),
                Implies(Forall("x", _uv(q, "x")), Forall("x", _uv(p, "x"))),
            )
        )

    # binary relation schemas.
    binary_rels = ["R", "S", "T"]
    for r in binary_rels:
        # Valid / provable-style schema
        candidates.append(
            Implies(
                Exists("x", Forall("y", _bv(r, "x", "y"))),
                Forall("y", Exists("x", _bv(r, "x", "y"))),
            )
        )
        candidates.append(
            Implies(
                Forall("x", Forall("y", _bv(r, "x", "y"))),
                Forall("y", Forall("x", _bv(r, "x", "y"))),
            )
        )
        candidates.append(
            Implies(
                Exists("x", Exists("y", _bv(r, "x", "y"))),
                Exists("y", Exists("x", _bv(r, "x", "y"))),
            )
        )
        candidates.append(Implies(Forall("x", Forall("y", _bv(r, "x", "y"))), _bc(r, "a", "b")))
        candidates.append(Implies(_bc(r, "a", "b"), Exists("x", Exists("y", _bv(r, "x", "y")))))

        # challenge / not_proved-style schema
        candidates.append(
            Implies(
                Forall("x", Exists("y", _bv(r, "x", "y"))),
                Exists("y", Forall("x", _bv(r, "x", "y"))),
            )
        )
        candidates.append(Implies(_bc(r, "a", "b"), Forall("x", Exists("y", _bv(r, "x", "y")))))
        candidates.append(Implies(Exists("x", Exists("y", _bv(r, "x", "y"))), _bc(r, "a", "b")))

    return candidates


def add_curated_fol_formulas(
    dataset: List[Tuple[Formula, str]],
    target_extra: int = 100,
    timeout_seconds: float = 2.0,
) -> List[Tuple[Formula, str]]:
    """
    Add curated FOL/quantifier formulas to an existing dataset

    The function attempts to add a balanced number of 'valid' and 'not_proved'
    formulas, based on the same label_formula() function used by the generator
    """
    existing = {str(f) for f, _ in dataset}
    added: List[Tuple[Formula, str]] = []

    target_valid = target_extra // 2
    target_not_proved = target_extra - target_valid

    valid_added = 0
    not_proved_added = 0

    candidates = curated_fol_candidates()

    print("\n" + "=" * 80)
    print("Adding Curated FOL / qauntifier formulae")
    print("=" * 80)
    print(f"Target extra formulae: {target_extra}")
    print(f"Target valid: {target_valid}")
    print(f"Target not_proved: {target_not_proved}")

    for formula in candidates:
        if str(formula) in existing:
            continue

        label = label_formula(formula, timeout_seconds=timeout_seconds)

        if label == "valid":
            if valid_added >= target_valid:
                continue
            added.append((formula, label))
            existing.add(str(formula))
            valid_added += 1

        elif label == "not_proved":
            if not_proved_added >= target_not_proved:
                continue
            added.append((formula, label))
            existing.add(str(formula))
            not_proved_added += 1

        if len(added) >= target_extra:
            break

    print(f"Actually added: {len(added)}")
    print(f"Valid added: {valid_added}")
    print(f"Not_proved added: {not_proved_added}")

    if len(added) < target_extra:
        print("Warning: fewer curated FOL formulae were added than requested")

    return dataset + added
