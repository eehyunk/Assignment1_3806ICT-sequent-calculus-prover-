"""
Sequent representation for LK' proof system
A sequent has the form: Γ ⊢ Δ
where Γ (antecedent) and Δ (succedent) are sets of formulae. In this project,
both sides are represented as immutable sets of formulae. This follows
the set-based view of LK', where formula order and duplication are not
important for proof search.

"""
from __future__ import annotations
from dataclasses import dataclass
from typing import FrozenSet
from formula import Formula

# ============================================================
# Sequent representation
# ============================================================
@dataclass(frozen=True)
class Sequent:
    """A sequent Γ ⊢ Δ where, Γ, Δ are sets of formulae"""
    antecedent: FrozenSet[Formula] # Γ: left of ⊢
    succedent: frozenset[Formula] # Δ: right of ⊢

    def __repr__(self) -> str:
        """
        return a readable version of the sequent 

        Formulae are sorted by their string to make the ouput determinisitc
        Debugging, testing, and experiment logs can all benefit from this. 
        """
        left = ", ".join(
            repr(f) for f in sorted(self.antecedent, key=repr)
        )
        right = ", ".join(
            repr(f) for f in sorted(self.succedent, key=repr)
        )
        
        return f"{left} ⊢ {right}"
    
# ============================================================
# Helper functions
# ============================================================
def empty_sequent() -> Sequent:
    # return empty sequent: ⊢
    return Sequent(
        antecedent=frozenset(),
        succedent=frozenset(),
    )

def sequent_from_formula(formula: Formula) -> Sequent:
    # Build the initial bottom sequent: ⊢ formula 
    return Sequent(
        antecedent=frozenset(),
        succedent=frozenset({formula})
    )


def with_added_left(seq: Sequent, *formulas: Formula) -> Sequent:
    # return a new sequent with formulas added to the antecedent.
    # original sequent is not modified sicne sequent is immutable 
    return Sequent(
        antecedent=seq.antecedent | frozenset(formulas),
        succedent=seq.succedent
    )


def with_added_right(seq: Sequent, *formulas: Formula) -> Sequent:
    # return a new sequent with formulas added to the succedent
    return Sequent(
        antecedent=seq.antecedent,
        succedent=seq.succedent | frozenset(formulas)
    )


def with_removed_left(seq: Sequent, formula: Formula) -> Sequent:
    # return a new sequent with a formula removed from the antecedent.
    return Sequent(
        antecedent=seq.antecedent - frozenset({formula}),
        succedent=seq.succedent
    )


def with_removed_right(seq: Sequent, formula: Formula) -> Sequent:
    # return a new sequent with a formula removed from the succedent
    return Sequent(
        antecedent=seq.antecedent,
        succedent=seq.succedent - frozenset({formula})
    )