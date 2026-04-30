"""
improved.py

Algorithm 2 backward proof-search prover for FOL utilising LK's has been improved 

The improved prover incorpartes useful search control features while 
maintaining the saem sequent calculus rules at the baseline

1. Timeout checking: 
A safeguard against very deep or non terminating first order proof search 

2. Memoization:
Only sequents that have been correctly proven are cahsed. 
Since failure in first order proof search may depend on the current quantifier 
instantiation history, failed sequents are not memoized

3. Loop detection:
branch is terminated if same sequent reappears on the current recursive proof path. 
this is not evidence of semantic invalidity; rather, it's a practical heuristic. 

4. Safer branching:
To prevent decisions made in one branch from incorrectly constraining sibling branches, 
branch local copies of quantifier instantiation history are utilised. 


5. Safer quantifier instantiation:
For reproducible experiments, the prover employs deterministic formula / term ordering 
and steers clear of no progress instantitaionss. 

Status interpretation:
valid = a closed derivation was found 
not_proved = this strategy and resource limit didn't yield any evidence. 
this is not a semantic proof of invalidity. 
timeout = The alloted time was used up 
"""

from __future__ import annotations

import sys
import time
from dataclasses import dataclass, field
from typing import FrozenSet, Optional, Set

from formula import (
    Formula,
    Term,
    Var,
    Const,
    Func,
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
    substitute,
)
from sequent import (
    Sequent,
    with_added_left,
    with_added_right,
    with_removed_left,
    with_removed_right,
)


# Hard first-order formulae can create deep proof-search trees.
sys.setrecursionlimit(100000)


# ============================================================
# Result types
# ============================================================

@dataclass(frozen=True)
class ProofResult:
    """
    Baseline-compatible result object.

    This object has the same public interface as baseline.ProofResult for
    direct comparison in experiment scripts.
    """
    status: str
    elapsed_time: float

    def __repr__(self) -> str:
        return f"ProofResult(status={self.status}, time={self.elapsed_time:.4f}s)"


@dataclass(frozen=True)
class ImprovedProofResult:
    """
    Detailed result object for experiments.

    Use run_improved_detailed() when extra metrics such as steps, branches,
    memo hits, and loop hits are needed.
    """
    status: str
    elapsed_time: float
    steps: int
    branches: int
    memo_hits: int
    loop_hits: int
    memo_size: int

    def __repr__(self) -> str:
        return (
            f"ImprovedProofResult(status={self.status}, "
            f"time={self.elapsed_time:.4f}s, "
            f"steps={self.steps}, branches={self.branches}, "
            f"memo_hits={self.memo_hits}, loop_hits={self.loop_hits}, "
            f"memo_size={self.memo_size})"
        )


# ============================================================
# Timeout management
# ============================================================

class TimeoutException(Exception):
    """Raised when the improved prover exhausts its time budget."""


class TimeBudget:
    """
    Portable timeout mechanism.

    This operates by monitoring the amount of time that has passed during 
    the recursive proof search, in contrast to signal based timeouts. 
    This facilitates the improved prover's operation across many platforms. 
    """

    def __init__(self, budget_seconds: float):
        self.budget_seconds = budget_seconds
        self.start_time = time.perf_counter()

    def check(self) -> None:
        # raise TimeoutException if the time budget has been exhausted.
        if time.perf_counter() - self.start_time > self.budget_seconds:
            raise TimeoutException()

    def elapsed(self) -> float:
        # return elapsed time in seconds
        return time.perf_counter() - self.start_time


# ============================================================
# Fresh term generator
# ============================================================

class FreshTermGenerator:
    """
    Generate fresh constants c0, c1, c2, ...

    A copy method is provided so sibling branches can use independent fresh
    generator states.
    """

    def __init__(self, prefix: str = "c", counter: int = 0):
        self.prefix = prefix
        self.counter = counter

    def fresh(self) -> Const:
        # return the next fresh constant.
        name = f"{self.prefix}{self.counter}"
        self.counter += 1
        return Const(name)

    def copy(self) -> "FreshTermGenerator":
        # return a copy with the same counter state.
        return FreshTermGenerator(prefix=self.prefix, counter=self.counter)


def fresh_avoiding(fresh_gen: FreshTermGenerator, forbidden_terms: Set[Term]) -> Const:
    # generate a fresh constant that does not occur in forbidden_terms.
    while True:
        candidate = fresh_gen.fresh()
        if candidate not in forbidden_terms:
            return candidate


# ============================================================
# Experiment metrics and prover state
# ============================================================
@dataclass
class ProofStats:
    # mutable counters used for experiment summaries
    steps: int = 0
    branches: int = 0
    memo_hits: int = 0
    loop_hits: int = 0


@dataclass
class ProverState:
    """
    Mutable state passed through recursive proof search.

    Attributes:
        memo_success: Sequents already proved successfully.
        in_progress: Sequents currently on the recursive proof path.
        budget: Shared time budget for this proof attempt.
        fresh_gen: Fresh constant generator.
        used: Branch-local quantifier-instantiation history.
        stats: Shared experiment counters.
    """
    memo_success: Set[Sequent]
    in_progress: Set[Sequent]
    budget: TimeBudget
    fresh_gen: FreshTermGenerator
    used: Set[tuple]
    stats: ProofStats = field(default_factory=ProofStats)

    @classmethod
    def new(cls, timeout_seconds: float) -> "ProverState":
        # create a fresh prover state for one proof attempt
        return cls(
            memo_success=set(),
            in_progress=set(),
            budget=TimeBudget(timeout_seconds),
            fresh_gen=FreshTermGenerator(),
            used=set(),
            stats=ProofStats(),
        )

    def fork_for_branch(self) -> "ProverState":
        """
        Create a branch-local copy of the state.

        The memo table, time budget, and statistics are shared across the
        whole proof attempt. The current path, used instantiations, and fresh
        generator state are copied so sibling branches do not interfere with
        each other.
        """
        return ProverState(
            memo_success=self.memo_success,
            in_progress=set(self.in_progress),
            budget=self.budget,
            fresh_gen=self.fresh_gen.copy(),
            used=set(self.used),
            stats=self.stats,
        )


# ============================================================
# Term collection
# ============================================================

def _func_args(term: Func) -> tuple:
    """
    Return function arguments.

    This helper supports both `args` and `arg` as a defensive measure, but the
    preferred field name in formula.py is `args`.
    """
    return getattr(term, "args", getattr(term, "arg", ()))


def collect_terms_from_term(
    term: Term,
    bound_vars: FrozenSet[str] = frozenset(),
) -> Set[Term]:
    """
    Collect free terms recursively from a term.

    Bound variables are not treated as existing terms for quantifier
    instantiation.
    """
    if isinstance(term, Var):
        if term.name in bound_vars:
            return set()
        return {term}

    if isinstance(term, Const):
        return {term}

    if isinstance(term, Func):
        result: Set[Term] = {term}
        for arg in _func_args(term):
            result |= collect_terms_from_term(arg, bound_vars)
        return result

    return set()


def collect_terms_from_formula(
    formula: Formula,
    bound_vars: FrozenSet[str] = frozenset(),
) -> Set[Term]:
    # collect free terms/constants appearing in a formula
    if isinstance(formula, (Top, Bottom, Prop)):
        return set()

    if isinstance(formula, Relation):
        result: Set[Term] = set()
        for arg in formula.args:
            result |= collect_terms_from_term(arg, bound_vars)
        return result

    if isinstance(formula, Not):
        return collect_terms_from_formula(formula.operand, bound_vars)

    if isinstance(formula, (And, Or, Implies)):
        return (
            collect_terms_from_formula(formula.left, bound_vars)
            | collect_terms_from_formula(formula.right, bound_vars)
        )

    if isinstance(formula, (Forall, Exists)):
        return collect_terms_from_formula(
            formula.body,
            bound_vars | frozenset({formula.var}),
        )

    return set()


def collect_terms_from_sequent(seq: Sequent) -> Set[Term]:
    # collect free terms from both sides of a sequent
    result: Set[Term] = set()

    for formula in seq.antecedent:
        result |= collect_terms_from_formula(formula)

    for formula in seq.succedent:
        result |= collect_terms_from_formula(formula)

    return result


# ============================================================
# Deterministic ordering helpers
# ============================================================

def sorted_formulas(formulas) -> list:
    # return formulae in deterministic order for reproducible experiments
    return sorted(formulas, key=repr)


def sorted_terms(terms) -> list:
    # return terms in deterministic order for reproducible experiments
    return sorted(terms, key=repr)


# ============================================================
# Tier 1: branch-closing rules
# ============================================================

def can_close_branch(seq: Sequent) -> bool:
    """
    Check id, ⊤R, and ⊥L.

    - id:  some formula appears on both sides.
    - ⊤R:  top appears in the succedent.
    - ⊥L:  bottom appears in the antecedent.
    """
    if Top() in seq.succedent:
        return True

    if Bottom() in seq.antecedent:
        return True

    if seq.antecedent & seq.succedent:
        return True

    return False


# ============================================================
# Tier 2a: non-branching propositional rules
# ============================================================

def try_and_left(seq: Sequent) -> Optional[Sequent]:
    # try to apply ∧L
    for formula in sorted_formulas(seq.antecedent):
        if isinstance(formula, And):
            new_seq = with_removed_left(seq, formula)
            return with_added_left(new_seq, formula.left, formula.right)
    return None


def try_or_right(seq: Sequent) -> Optional[Sequent]:
    # try to apply ∨R
    for formula in sorted_formulas(seq.succedent):
        if isinstance(formula, Or):
            new_seq = with_removed_right(seq, formula)
            return with_added_right(new_seq, formula.left, formula.right)
    return None


def try_not_left(seq: Sequent) -> Optional[Sequent]:
    # ry to apply ¬L
    for formula in sorted_formulas(seq.antecedent):
        if isinstance(formula, Not):
            new_seq = with_removed_left(seq, formula)
            return with_added_right(new_seq, formula.operand)
    return None


def try_not_right(seq: Sequent) -> Optional[Sequent]:
    # try to apply ¬R
    for formula in sorted_formulas(seq.succedent):
        if isinstance(formula, Not):
            new_seq = with_removed_right(seq, formula)
            return with_added_left(new_seq, formula.operand)
    return None


def try_implies_right(seq: Sequent) -> Optional[Sequent]:
    # try to apply →R 
    for formula in sorted_formulas(seq.succedent):
        if isinstance(formula, Implies):
            new_seq = with_removed_right(seq, formula)
            new_seq = with_added_left(new_seq, formula.left)
            return with_added_right(new_seq, formula.right)
    return None


# ============================================================
# Tier 2b: fresh-term quantifier rules
# ============================================================

def try_forall_right(seq: Sequent, fresh_gen: FreshTermGenerator) -> Optional[Sequent]:
    """
    Try to apply ∀R.

    A fresh constant is selected so that it does not already occur in the
    current sequent.
    """
    for formula in sorted_formulas(seq.succedent):
        if isinstance(formula, Forall):
            forbidden = collect_terms_from_sequent(seq)
            fresh_const = fresh_avoiding(fresh_gen, forbidden)
            substituted = substitute(formula.body, formula.var, fresh_const)
            new_seq = with_removed_right(seq, formula)
            return with_added_right(new_seq, substituted)
    return None


def try_exists_left(seq: Sequent, fresh_gen: FreshTermGenerator) -> Optional[Sequent]:
    """
    Try to apply ∃L.

    A fresh constant is selected so that it does not already occur in the
    current sequent.
    """
    for formula in sorted_formulas(seq.antecedent):
        if isinstance(formula, Exists):
            forbidden = collect_terms_from_sequent(seq)
            fresh_const = fresh_avoiding(fresh_gen, forbidden)
            substituted = substitute(formula.body, formula.var, fresh_const)
            new_seq = with_removed_left(seq, formula)
            return with_added_left(new_seq, substituted)
    return None


# ============================================================
# Tier 3: branching rules
# ============================================================

def try_and_right(seq: Sequent) -> Optional[tuple[Sequent, Sequent]]:
    # try to apply ∧R
    for formula in sorted_formulas(seq.succedent):
        if isinstance(formula, And):
            left_seq = with_removed_right(seq, formula)
            left_seq = with_added_right(left_seq, formula.left)

            right_seq = with_removed_right(seq, formula)
            right_seq = with_added_right(right_seq, formula.right)

            return left_seq, right_seq
    return None


def try_or_left(seq: Sequent) -> Optional[tuple[Sequent, Sequent]]:
    # try to apply ∨L 
    for formula in sorted_formulas(seq.antecedent):
        if isinstance(formula, Or):
            left_seq = with_removed_left(seq, formula)
            left_seq = with_added_left(left_seq, formula.left)

            right_seq = with_removed_left(seq, formula)
            right_seq = with_added_left(right_seq, formula.right)

            return left_seq, right_seq
    return None


def try_implies_left(seq: Sequent) -> Optional[tuple[Sequent, Sequent]]:
    # try to apply →L
    for formula in sorted_formulas(seq.antecedent):
        if isinstance(formula, Implies):
            left_seq = with_removed_left(seq, formula)
            left_seq = with_added_right(left_seq, formula.left)

            right_seq = with_removed_left(seq, formula)
            right_seq = with_added_left(right_seq, formula.right)

            return left_seq, right_seq
    return None


# ============================================================
# Tier 4: ∀L and ∃R with loop-safer instantiation
# ============================================================

def try_forall_left(seq: Sequent, state: ProverState) -> Optional[Sequent]:
    """
    Try to apply ∀L using a loop-safer instantiation strategy.

    Existing terms are tried first in deterministic order. Instantiations that
    would not add a new formula are skipped. If no existing term works, a fresh
    constant is generated.
    """
    existing_terms = sorted_terms(collect_terms_from_sequent(seq))

    # Try existing terms for all applicable universal formulae.
    for formula in sorted_formulas(seq.antecedent):
        if not isinstance(formula, Forall):
            continue

        for term in existing_terms:
            if (formula, term) in state.used:
                continue

            substituted = substitute(formula.body, formula.var, term)

            # Avoid no-progress instantiations that reproduce the same sequent.
            if substituted in seq.antecedent:
                continue

            state.used.add((formula, term))
            return with_added_left(seq, substituted)

    # If existing terms do not help, try one fresh constant.
    for formula in sorted_formulas(seq.antecedent):
        if not isinstance(formula, Forall):
            continue

        forbidden = collect_terms_from_sequent(seq)
        term = fresh_avoiding(state.fresh_gen, forbidden)
        substituted = substitute(formula.body, formula.var, term)

        if substituted in seq.antecedent:
            continue

        state.used.add((formula, term))
        return with_added_left(seq, substituted)

    return None


def try_exists_right(seq: Sequent, state: ProverState) -> Optional[Sequent]:
    """
    Try to apply ∃R using a loop-safer instantiation strategy.

    Existing terms are tried first in deterministic order. Instantiations that
    would not add a new formula are skipped. If no existing term works, a fresh
    constant is generated.
    """
    existing_terms = sorted_terms(collect_terms_from_sequent(seq))

    # Try existing terms for all applicable existential formulae.
    for formula in sorted_formulas(seq.succedent):
        if not isinstance(formula, Exists):
            continue

        for term in existing_terms:
            if (formula, term) in state.used:
                continue

            substituted = substitute(formula.body, formula.var, term)

            # Avoid no-progress instantiations that reproduce the same sequent.
            if substituted in seq.succedent:
                continue

            state.used.add((formula, term))
            return with_added_right(seq, substituted)

    # If existing terms do not help, try one fresh constant.
    for formula in sorted_formulas(seq.succedent):
        if not isinstance(formula, Exists):
            continue

        forbidden = collect_terms_from_sequent(seq)
        term = fresh_avoiding(state.fresh_gen, forbidden)
        substituted = substitute(formula.body, formula.var, term)

        if substituted in seq.succedent:
            continue

        state.used.add((formula, term))
        return with_added_right(seq, substituted)

    return None


# ============================================================
# Main improved proof search
# ============================================================

def prove_improved(seq: Sequent, state: ProverState) -> bool:
    """
    Improved backward proof search for LK'.

    Returns True if the sequent is proved. Returns False if search stops with
    an open or cut-off branch.
    """
    state.budget.check()
    state.stats.steps += 1

    # Memoization: only successfully proved sequents are reused.
    if seq in state.memo_success:
        state.stats.memo_hits += 1
        return True

    # Loop detection: current-path cutoff, not semantic invalidity.
    if seq in state.in_progress:
        state.stats.loop_hits += 1
        return False

    state.in_progress.add(seq)

    try:
        result = _prove_core(seq, state)
    finally:
        state.in_progress.discard(seq)

    if result:
        state.memo_success.add(seq)

    return result


def _prove_core(seq: Sequent, state: ProverState) -> bool:
    """Apply the tiered rule ordering of Algorithm 2."""

    # Tier 1: branch-closing rules.
    if can_close_branch(seq):
        return True

    # Tier 2a: non-branching propositional rules.
    for try_rule in [
        try_and_left,
        try_or_right,
        try_not_left,
        try_not_right,
        try_implies_right,
    ]:
        new_seq = try_rule(seq)
        if new_seq is not None:
            return prove_improved(new_seq, state)

    # Tier 2b: fresh-term quantifier rules.
    for try_rule in [try_forall_right, try_exists_left]:
        new_seq = try_rule(seq, state.fresh_gen)
        if new_seq is not None:
            return prove_improved(new_seq, state)

    # Tier 3: branching rules. Both branches must close.
    for try_rule in [try_and_right, try_or_left, try_implies_left]:
        branch_pair = try_rule(seq)
        if branch_pair is not None:
            state.stats.branches += 1
            left_seq, right_seq = branch_pair

            left_state = state.fork_for_branch()
            right_state = state.fork_for_branch()

            return (
                prove_improved(left_seq, left_state)
                and prove_improved(right_seq, right_state)
            )

    # Tier 4: ∀L and ∃R. These can cause repeated instantiation.
    for try_rule in [try_forall_left, try_exists_right]:
        new_seq = try_rule(seq, state)
        if new_seq is not None:
            return prove_improved(new_seq, state)

    # No rule applies: open branch under this search strategy.
    return False


# ============================================================
# Experiment wrappers
# ============================================================

def run_improved(formula: Formula, timeout_seconds: float = 5.0) -> ProofResult:
    """
    Baseline-compatible wrapper.

    This returns only status and elapsed_time, making it easy to compare with
    baseline.run_baseline().
    """
    detailed = run_improved_detailed(formula, timeout_seconds)
    return ProofResult(status=detailed.status, elapsed_time=detailed.elapsed_time)


def run_improved_detailed(
    formula: Formula,
    timeout_seconds: float = 5.0,
) -> ImprovedProofResult:
    """
    Run the improved prover and return detailed experiment metrics.
    """
    bottom_seq = Sequent(
        antecedent=frozenset(),
        succedent=frozenset({formula}),
    )

    state = ProverState.new(timeout_seconds=timeout_seconds)

    try:
        is_valid = prove_improved(bottom_seq, state)
        status = "valid" if is_valid else "not_proved"
    except TimeoutException:
        status = "timeout"

    elapsed = state.budget.elapsed()

    return ImprovedProofResult(
        status=status,
        elapsed_time=elapsed,
        steps=state.stats.steps,
        branches=state.stats.branches,
        memo_hits=state.stats.memo_hits,
        loop_hits=state.stats.loop_hits,
        memo_size=len(state.memo_success),
    )
