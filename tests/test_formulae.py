"""
encodes the 10 test formulae from our test suit using formula.py classes.
This validates our data structures can express all planned test cases
"""

import sys
from pathlib import Path

# add src/ to python path so we can import formula.py and sequent.py
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from formula import (
    Formula, Term, Var, Const, Func, 
    Top, Bottom, Prop, Relation, 
    Not, And, Or, Implies, 
    Forall, Exists

)
from sequent import Sequent, sequent_from_formula

# ============================================================
# Test suite: 10 formulas for validating our prover
# ============================================================
# shared propositional variables (used in tests 1~6)
A = Prop("A")
B = Prop("B")

# ------------------------------------------------------------
# Level 1: Propositional — basic rules
# ------------------------------------------------------------
# Test 1: A → A
test1_formula = Implies(A, A)
test1 = {
    "name": "Test 1: A → A", 
    "formula": test1_formula, 
    "expected": "valid", 
    "description": "Basic tautology - tests [→R] and [id]"
}

# Test 2: (A ∧ B) → A
test2_formula = Implies(And(A, B), A)
test2 = {
    "name": "Test 2: (A ∧ B) → A",
    "formula": test2_formula,
    "expected": "valid",
    "description": "Conjuction elimination - tests [→R], [∧L], and [id]"
}

# Test 3: A → (A ∨ B)
test3_formula = Implies(A, Or(A, B))
test3 = {
    "name": "Test 3: A → (A ∨ B)",
    "formula": test3_formula,
    "expected": "valid",
    "description": "Disjunction elimination - tests [→R], [∨R], and [id]"    
}

# Test 4: A ∨ ¬A
test4_formula = Or(A, Not(A))
test4 = {
    "name": "Test 4: A ∨ ¬A",
    "formula": test4_formula,
    "expected": "valid",
    "description": "Law of excluded middle- tests [∨R], [¬R], and [id]"  
}

# ------------------------------------------------------------
# Level 2: More complex propositional
# ------------------------------------------------------------
# Test 5: (A → B) → (¬B → ¬A) - Contrapositive
test5_formula = Implies(
    Implies(A, B), 
    Implies(Not(B), Not(A))
)
test5 = {
    "name": "Test 5: (A → B) → (¬B → ¬A)", 
    "formula": test5_formula,
    "expected": "valid", 
    "description": "Contrapositive - tests branching rule [→L]"
}

# Test 6: (A ∨ B) → (A ∧ B) - Invalid (example 2.6)
test6_formula = Implies(Or(A, B), And(A, B))
test6 = {
    "name": "Test 6: (A ∨ B) → (A ∧ B)", 
    "formula": test6_formula,
    "expected": "invalid", 
    "description": "Not a tautology - prover should find counterexample"
}

# ------------------------------------------------------------
# Level 3: First-order logic(FOL) with quantifiers (easy)
# ------------------------------------------------------------
# shared terms for FOL tests
x = Var("x")
y = Var("y")
a = Const("a")
Rx = Relation("R", (x,)) # R(x)
Ra = Relation("R", (a,)) # R(a)
Rxy = Relation("R", (x, y)) # R(x, y)

# Test 7: ∀x.R(x) → R(a)
test7_formula = Implies(
    Forall("x", Rx),
    Ra
)
test7 = {
    "name": "Test 7: ∀x.R(x) → R(a)", 
    "formula": test7_formula,
    "expected": "valid", 
    "description": "Universal instantiation - tests [∀L]"    
}

# Test 8: R(a) → ∃x.R(x)
test8_formula = Implies(
    Ra, 
    Exists("x", Rx)
)
test8 = {
    "name": "Test 8: R(a) → ∃x.R(x)", 
    "formula": test8_formula,
    "expected": "valid", 
    "description": "Existential introduction - tests [∃R]"   
}

# ------------------------------------------------------------
# Level 4: First-order logic with quantifiers (hard)
# ------------------------------------------------------------
# Test 9: ∃x.∀y.R(x,y) → ∀y.∃x.R(x,y) — Valid (example 1 from week 5: Lemma 2.7)
test9_formula = Implies(
    Exists("x", Forall("y", Rxy)),
    Forall("y", Exists("x", Rxy))
)
test9 = {
    "name": "Test 9: ∃x.∀y.R(x,y) → ∀y.∃x.R(x,y)", 
    "formula": test9_formula,
    "expected": "valid", 
    "description": "Example 1 from w.5 (lemma 2.7) - EA implies AE direction"   
}

# Test 10: ∀y.∃x.R(x,y) → ∃x.∀y.R(x,y) — Invalid (example 2.4)
test10_formula = Implies(
    Forall("y", Exists("x", Rxy)),
    Exists("x", Forall("y", Rxy))
)
test10 = {
    "name": "Test 10: ∀y.∃x.R(x,y) → ∃x.∀y.R(x,y)", 
    "formula": test10_formula,
    "expected": "invalid", 
    "description": "Example 2.4 - baseline might be loop infinitely, motivates timeout (improved version)"     
}

# Full test suite
ALL_TESTS = [
    test1, test2, test3, test4, test5,
    test6, test7, test8, test9, test10
]


# ============================================================
# VERIFICATION: print all tests to confirm they're built correctly
# ============================================================

# Verification: pritn all tests to confirm they're built correctly 
if __name__ == "__main__":
    print("=" * 80)
    print("Test suite — 10 formulae")
    print("=" * 80)

    for i, test in enumerate(ALL_TESTS, start=1):
        print(f"\n[{i}] {test['name']}")
        print(f"Formula: {test['formula']}")
        print(f"Expected: {test['expected']}")
        print(f"Description: {test['description']}")

        # Also build the bottom sequent that the prover will use
        seq = sequent_from_formula(test['formula'])
        print(f"Sequent: {seq}")

    print("\n" + "=" * 80)
    print(f"Total: {len(ALL_TESTS)} tests")
    print("=" * 80)