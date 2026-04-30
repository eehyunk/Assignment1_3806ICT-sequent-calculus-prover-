"""
Algorithm 2's baseline implementation from the text book (p. 67)
LK's naive backward proo search method for FOL

sequent calculus rules are applied by the baseline prover in the textbook order:
<pattern matching tier list>
1. rules for branch closure immediately
2. logical rules that don't branch 
3. rules for fresh term quantifiers 
4. rules for branching 
5. quantifier rules maintain the original formula

this implementation is intentionally naive. It may not terminate on invalid or difficutl first-order formluae.
Algorithm 2 doesn't include the timeout used in run_baseline; it's an experimental safety measure. 
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Optional, List

from formula import (
    Formula, Term, Var, Const, Func, 
    Top, Bottom, Prop, Relation,
    Not, And, Or, Implies,
    Forall, Exists,
    substitute
)

from sequent import (
    Sequent, 
    with_added_left, with_added_right, 
    with_removed_left, with_removed_right
)

import sys        
# higher recursion limit is useful for deep proof search tree                  
sys.setrecursionlimit(10000)         

# ============================================================
# PROOF RESULT Proof result 
# ============================================================
@dataclass(frozen=True)
class ProofResult: # when running experiments, we can check the success/failure status and the time taken for each formula 
    status: str
    elapsed_time: float
    steps: int = 0
    branches: int = 0
    max_depth: int = 0

    def __repr__(self) -> str:
        return f"ProofResult(status={self.status}, time={self.elapsed_time:.4f}s)"

# ============================================================
# FRESH TERM GENERATOR Fresh term generator
# ============================================================
class FreshTermGenerator:
    """generates fresh for ∀R and ∃L
    c0, c1, c2 and so on are new constants
    The function fresh_avoiding guarantees that the created constant is
    not already present in a specified list of prohibited phrases. 
    """ 

    def __init__(self, prefix: str = "c"):
        self.prefix = prefix
        self.counter = 0 

    def fresh_avoiding(self, forbidden_terms: set) -> Const:
        # return a fresh term not contained in forbidden_terms
        while True:
            candidate = Const(f"{self.prefix}{self.counter}")
            self.counter += 1
            if candidate not in forbidden_terms:
                return candidate

# ============================================================
# Collecting terms 
# ============================================================
def collect_terms_from_term(term: Term, bound_vars=frozenset()) -> set:
    """return all terms appearing (recursively) in the given term
    when collecting exisitng terms for quantifier instantiation, bound variables are disregarded. 

    """
    if isinstance(term, Var):
        if term.name in bound_vars:
            return set()
        return {term}

    elif isinstance(term, Const):
        return {term}

    elif isinstance(term, Func):
        result = {term}
        for arg in term.args:
            result |= collect_terms_from_term(arg, bound_vars)
        return result

    return set()
    
def collect_terms_from_formula(formula: Formula, bound_vars=frozenset()) -> set:
    # return all free terms appearing in a formula 
    if isinstance(formula, (Top, Bottom, Prop)):
        return set()

    elif isinstance(formula, Relation):
        result = set()
        for arg in formula.args:
            result |= collect_terms_from_term(arg, bound_vars)
        return result

    elif isinstance(formula, Not):
        return collect_terms_from_formula(formula.operand, bound_vars)

    elif isinstance(formula, (And, Or, Implies)):
        return (
            collect_terms_from_formula(formula.left, bound_vars)
            | collect_terms_from_formula(formula.right, bound_vars)
        )

    elif isinstance(formula, (Forall, Exists)):
        return collect_terms_from_formula(
            formula.body,
            bound_vars | frozenset({formula.var})
        )

    return set()

def collect_terms_from_sequent(seq: Sequent) -> set: 
    # return all terms appearing in either side of the sequent
    result = set()
    for f in seq.antecedent:
        result |= collect_terms_from_formula(f)
    for f in seq.succedent:
        result |= collect_terms_from_formula(f) 
    return result   

# ============================================================
# Pattern Matching Tier 1: branch closing rules 
# ============================================================
# These rules close a branch — no further work needed.
def can_close_branch(seq: Sequent) -> bool: 
    """
    Check if any of id, ⊤R, ⊥L can close this sequent.
    
    - [id]:  some formula appears in both antecednet and succedent 
    - [⊤R]:  top appears in succedent 
    - [⊥L]:  bottom appears in antecedent 
    """
    # [⊤R]: is ⊤ anywhere in the succedent? 
    if Top() in seq.succedent:
        return True
    
    # [⊥L]: is ⊥ anywhere in the antecedent?
    if Bottom() in seq.antecedent:
        return True
    
    # [id]: does any formula appear on both sides? eg A ⊢ A ...
    if seq.antecedent & seq.succedent:
        return True
    
    return False

# ============================================================
# Pattern Matching Tier 2a: non-branching logical rules
# ============================================================
def try_and_left(seq: Sequent) -> Optional[Sequent]:
    """
    try to apply [∧L]
    Γ, A, B ⊢ Δ
    ------------- (just convert ∧ into comma)
    Γ, A ∧ B ⊢ Δ
    eg. ((A ∧ B) → A)
    """
    for f in seq.antecedent: 
        if isinstance(f, And): 
            # remove A ∧ B, and add A and B
            new_seq = with_removed_left(seq, f) # ⊢ A
            new_seq = with_added_left(new_seq, f.left, f.right) 
            return new_seq # A, B ⊢ A 
    return None

def try_or_right(seq: Sequent) -> Optional[Sequent]:
    """
    Try to apply [∨R]:
        Γ ⊢ A, B, Δ
        ──────────── (just convert ∨ into comma)
        Γ ⊢ A ∨ B, Δ    
    """
    for f in seq.succedent:
        if isinstance(f, Or):
            new_seq = with_removed_right(seq, f)
            new_seq = with_added_right(new_seq, f.left, f.right)
            return new_seq
    return None

def try_not_left(seq: Sequent) -> Optional[Sequent]:
    """
    Try to apply [¬L]:
        Γ ⊢ A, Δ
        ──────────
        Γ, ¬A ⊢ Δ
    Moves A from antecedent (as ¬A) to succedent (as A)
    """
    for f in seq.antecedent:
        if isinstance(f, Not):
            new_seq = with_removed_left(seq, f)
            new_seq = with_added_right(new_seq, f.operand)
            return new_seq
    return None

def try_not_right(seq: Sequent) -> Optional[Sequent]:
    """
    Try to apply [¬R]:
        Γ, A ⊢ Δ
        ──────────
        Γ ⊢ ¬A, Δ
    Moves A from succedent (as ¬A) to antecedent (as A).    
    """
    for f in seq.succedent:
        if isinstance(f, Not):
            new_seq = with_removed_right(seq, f)
            new_seq = with_added_left(new_seq, f.operand)
            return new_seq
    return None

def try_implies_right(seq: Sequent) -> Optional[Sequent]:
    """
    Try to apply [→R]:
        Γ, A ⊢ B, Δ
        ─────────────
        Γ ⊢ A → B, Δ
    """
    for f in seq.succedent:
        if isinstance(f, Implies):
            new_seq = with_removed_right(seq, f)
            new_seq = with_added_left(new_seq, f.left)
            new_seq = with_added_right(new_seq, f.right)
            return new_seq
    return None

# ============================================================
# Pattern Matching Tier 2b: Quantifier rules with fresh terms (∀R, ∃L)
# ============================================================
# These rules require a fresh constant that hasn't appeared yet.
def try_forall_right(seq: Sequent, fresh_gen: FreshTermGenerator) -> Optional[Sequent]:
    """
    Try to apply [∀R]:
        Γ ⊢ A[a/x], Δ     (a is fresh)
        ──────────────
        Γ ⊢ ∀x.A, Δ
    """
    for f in seq.succedent: 
        if isinstance(f, Forall):
            # create a fresh constant
            forbidden = collect_terms_from_sequent(seq)
            a = fresh_gen.fresh_avoiding(forbidden)
            # substitute x with a in the body: A[a/x] 
            substituted = substitute(f.body, f.var, a)
            # remove ∀x.A, add A[a/x]
            new_seq = with_removed_right(seq, f)
            new_seq = with_added_right(new_seq, substituted)
            return new_seq
    return None

def try_exists_left(seq: Sequent, fresh_gen: FreshTermGenerator) -> Optional[Sequent]:
    """
    Try to apply [∃L]:
        Γ, A[a/x] ⊢ Δ     (a is fresh)
        ─────────────
        Γ, ∃x.A ⊢ Δ
    """
    for f in seq.antecedent:
        if isinstance(f, Exists):
            # create a fresh constant
            forbidden = collect_terms_from_sequent(seq)
            a = fresh_gen.fresh_avoiding(forbidden)
            # substitute x with a in the body: A[a/x]
            substituted = substitute(f.body, f.var, a)
            # remove ∃x.A, add A[a/x]
            new_seq = with_removed_left(seq, f)
            new_seq = with_added_left(new_seq, substituted)
            return new_seq
    return None

# ============================================================
# Pattern Matching Tier 3: branching logical rules (∧R, ∨L, →L)
# ============================================================
# These rules produce two premises — the proof splits into branches.
def try_and_right(seq: Sequent) -> Optional[tuple]:
    """
    Try to apply [∧R]:
        Γ ⊢ A, Δ      Γ ⊢ B, Δ
        ─────────────────────
           Γ ⊢ A ∧ B, Δ
    Returns a tuple of two sequents, or None if no A ∧ B found.    
    """
    for f in seq.succedent:
        if isinstance(f, And):
            # left branch: Γ ⊢ A, Δ
            left_seq = with_removed_right(seq, f)
            left_seq = with_added_right(left_seq, f.left)
            
            # right branch: Γ ⊢ B, Δ
            right_seq = with_removed_right(seq, f)
            right_seq = with_added_right(right_seq, f.right)
            return (left_seq, right_seq)
    return None

def try_or_left(seq: Sequent) -> Optional[tuple]:
    """
    Try to apply [∨L]:
        Γ, A ⊢ Δ      Γ, B ⊢ Δ
        ─────────────────────
           Γ, A ∨ B ⊢ Δ
    """
    for f in seq.antecedent:
        if isinstance(f, Or):
            # left branch: Γ, A ⊢ Δ
            left_seq = with_removed_left(seq, f)
            left_seq = with_added_left(left_seq, f.left)

            # right branch: Γ, B ⊢ Δ
            right_seq = with_removed_left(seq, f)
            right_seq = with_added_left(right_seq, f.right)
            return (left_seq, right_seq)
    return None

def try_implies_left(seq: Sequent) -> Optional[tuple]:
    """
    Try to apply [→L]:
        Γ ⊢ A, Δ      Γ, B ⊢ Δ
        ─────────────────────
           Γ, A → B ⊢ Δ
    Note (from Dr. Hou): A moves to succedent, B moves to antecedent.
    """
    for f in seq.antecedent:
        if isinstance(f, Implies):
            # left branch: Γ ⊢ A, Δ 
            left_seq = with_removed_left(seq, f)
            left_seq = with_added_right(left_seq, f.left)

            # right branch: Γ, B ⊢ Δ
            right_seq = with_removed_left(seq, f)
            right_seq = with_added_left(right_seq, f.right)
            return (left_seq, right_seq)
    return None

# ============================================================
# Pattern Matching Tier 4: quantifier rules that keep the original (∀L, ∃R)
# ============================================================
# These rules don't remove the original formula — it stays as "insurance"
# so the rule can be applied again with a different term.
# This is why termination is not guaranteed

def try_forall_left(
        seq: Sequent, 
        used: set, 
        fresh_gen: FreshTermGenerator
) -> Optional[Sequent]:
    """
    Try to apply [∀L]:
        Γ, (∀x.A), A[t/x] ⊢ Δ       (original ∀x.A stays(=''' in the workshop))
        ─────────────────────
              Γ, ∀x.A ⊢ Δ
    
    Note:
      1. For each ∀x.A in antecedent:
         - Try each existing term t not yet used with this formula.
         - If all have been used, create a fresh term.
      2. Track usage in `used` set to avoid infinite loops on same (formula, term).    
    """
    existing_terms = collect_terms_from_sequent(seq)

    for f in seq.antecedent:
        if isinstance(f, Forall):
            # try to find a term we haven't used with this formula yet
            chosen_term = None

            # First: try existing terms
            for t in existing_terms:
                if (f, t) not in used: 
                    chosen_term = t
                    break
            
            # if no unused existing term, create a fresh one
            if chosen_term is None:
                chosen_term = fresh_gen.fresh_avoiding(existing_terms)
            
            # mark this (formula, term) pair as used
            used.add((f, chosen_term))

            # apply the rule: add A[t/x] (keep orginal ∀x.A)
            substituted = substitute(f.body, f.var, chosen_term)
            new_seq = with_added_left(seq, substituted)
            return new_seq
    return None

def try_exists_right(
        seq: Sequent, 
        used: set, 
        fresh_gen: FreshTermGenerator
) -> Optional[Sequent]:
    """
    Try to apply [∃R]:
        Γ ⊢ ∃x.A, A[t/x], Δ       (original ∃x.A stays!)
        ───────────────────────
              Γ ⊢ ∃x.A, Δ
    """
    existing_terms = collect_terms_from_sequent(seq)

    for f in seq.succedent:
        if isinstance(f, Exists):
            chosen_term = None

            # First: try existing terms
            for t in existing_terms:
                if (f, t) not in used: 
                    chosen_term = t
                    break
            
            # fall back : fresh term
            if chosen_term is None:
                chosen_term = fresh_gen.fresh_avoiding(existing_terms)
            
            # mark this (formula, term) pair as used
            used.add((f, chosen_term))

            # apply the rule: add A[t/x] (keep orginal ∃x.A)
            substituted = substitute(f.body, f.var, chosen_term)
            new_seq = with_added_right(seq, substituted)
            return new_seq
    return None

# ============================================================
# Main proof function
# ============================================================
def prove(
        seq: Sequent, 
        used: Optional[set] = None,
        fresh_gen: Optional[FreshTermGenerator] = None
) -> bool:
    """
    Algorithm 2 (textbook p.67) — naive backward proof search for LK'.
    
    Args:
        seq: the sequent to prove
        used: set tracking (formula, term) pairs already used in ∀L/∃R
        fresh_gen: generator for fresh constants
    
    Returns:
        True if the sequent is provable (branch closes),
        False if no rule applies (open branch).
    
    This naive version may not terminate on not proved formulas  
    """
    # initialise tracking state on first call
    if used is None: 
        used = set()
    if fresh_gen is None:
        fresh_gen = FreshTermGenerator()
    
    # tier 1: try to close the brach immediately 
    if can_close_branch(seq):
        return True
    
    # tier 2a: non-branching, non-quantifier rules
    for try_rule in [try_and_left, try_or_right, try_not_left, try_not_right, try_implies_right]:
        new_seq = try_rule(seq)
        if new_seq is not None:
            return prove(new_seq, used, fresh_gen)
        
    # tier 2b: quantifier rules w/ fresh terms
    for try_rule in [try_forall_right, try_exists_left]:
        new_seq = try_rule(seq, fresh_gen)
        if new_seq is not None: 
            return prove(new_seq, used, fresh_gen)
    
    # tier 3: branching rule
    for try_rule in [try_and_right, try_or_left, try_implies_left]:
        result = try_rule(seq)
        if result is not None:
            left_seq, right_seq = result
            # both branches must succeed
            return (prove(left_seq, used, fresh_gen) and prove(right_seq, used, fresh_gen))

    # tier 4: keep original (may loop)
    for try_rule in [try_forall_left, try_exists_right]:
        new_seq = try_rule(seq, used, fresh_gen)
        if new_seq is not None:
            return prove(new_seq, used, fresh_gen)

    # no rule applies: branch is open
    return False    

# ============================================================
# experiment wrapper: run baseline with timing and timeout
# ============================================================
# Note: Algorithm 2 itself has no timeout. The timeout below is
# purely an experimental safeguard to prevent the script from hanging
# forever when given an invalid formula. It is NOT part of the algorithm.
import time
import signal

class _TimeoutError(Exception):
    # Internal exception to signal experimental timeout.
    pass


def _timeout_handler(signum, frame):
    raise _TimeoutError()


def run_baseline(formula: Formula, timeout_seconds: float = 5.0) -> ProofResult:
    """
    Run the baseline prover on a formula with timing and safety timeout.
    
    Args:
        formula: the FOL formula to test
        timeout_seconds: experimental timeout (not part of Algorithm 2)
    
    Returns:
        ProofResult with status "valid", "not proved", or "timeout" and elapsed time.
    """
    seq = Sequent(
        antecedent=frozenset(),
        succedent=frozenset({formula})
    )
    
    # Set up experimental timeout using SIGALRM. This project was tested on macOS
    signal.signal(signal.SIGALRM, _timeout_handler)
    signal.setitimer(signal.ITIMER_REAL, timeout_seconds)
    
    start = time.perf_counter()
    try:
        is_valid = prove(seq, set(), FreshTermGenerator())
        elapsed = time.perf_counter() - start
        status = "valid" if is_valid else "not_proved"
    except _TimeoutError:
        elapsed = time.perf_counter() - start
        status = "timeout"
    finally:
        # Always disable the timer
        signal.setitimer(signal.ITIMER_REAL, 0)
    
    return ProofResult(status=status, elapsed_time=elapsed)