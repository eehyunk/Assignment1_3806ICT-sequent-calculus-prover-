"""
Selected Pelletier benchmark problems are manually encoded

This file is not a TPTP parser. The prover's internal formula representation 
was manually encoded with the chosen TPTP / Pelletier formulae

iff(A, B) is used to translate biconditional, expanding A <-> B into (A -> B) and (B -> A). 
A single implication from the conjuction of axioms to the conjecture encodes problems
involving axioms and a conjecture 

"""
from formula import (
    Formula,
    Var, Const, Relation,
    Top, Prop,
    Not, And, Or, Implies,
    Forall, Exists,
)


# Helper: bidirectional implication (P ↔ Q) = (P → Q) ∧ (Q → P)
def Iff(left: Formula, right: Formula) -> Formula:
    """Biconditional: P ↔ Q is equivalent to (P → Q) ∧ (Q → P)."""
    return And(Implies(left, right), Implies(right, left))


# ============================================================
# Pelletier 1-17: Propositional Logic
# ============================================================

def pelletier_1():
    """Pelletier 1: (P → Q) ↔ (¬Q → ¬P)
    Contrapositive."""
    P, Q = Prop("P"), Prop("Q")
    return Iff(
        Implies(P, Q),
        Implies(Not(Q), Not(P))
    )


def pelletier_2():
    """Pelletier 2: ¬¬P ↔ P
    Double negation."""
    P = Prop("P")
    return Iff(Not(Not(P)), P)


def pelletier_3():
    """Pelletier 3: ¬(P → Q) → (Q → P)"""
    P, Q = Prop("P"), Prop("Q")
    return Implies(
        Not(Implies(P, Q)),
        Implies(Q, P)
    )


def pelletier_4():
    """Pelletier 4: (¬P → Q) ↔ (¬Q → P)"""
    P, Q = Prop("P"), Prop("Q")
    return Iff(
        Implies(Not(P), Q),
        Implies(Not(Q), P)
    )


def pelletier_5():
    """Pelletier 5: ((P ∨ Q) → (P ∨ R)) → (P ∨ (Q → R))"""
    P, Q, R = Prop("P"), Prop("Q"), Prop("R")
    return Implies(
        Implies(Or(P, Q), Or(P, R)),
        Or(P, Implies(Q, R))
    )


def pelletier_6():
    """Pelletier 6: P ∨ ¬P (Excluded middle)."""
    P = Prop("P")
    return Or(P, Not(P))


def pelletier_7():
    """Pelletier 7: P ∨ ¬¬¬P"""
    P = Prop("P")
    return Or(P, Not(Not(Not(P))))


def pelletier_8():
    """Pelletier 8: ((P → Q) → P) → P (Peirce's law)."""
    P, Q = Prop("P"), Prop("Q")
    return Implies(
        Implies(Implies(P, Q), P),
        P
    )


def pelletier_9():
    """Pelletier 9: ((P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q)) → ¬(¬P ∨ ¬Q)"""
    P, Q = Prop("P"), Prop("Q")
    return Implies(
        And(
            And(Or(P, Q), Or(Not(P), Q)),
            Or(P, Not(Q))
        ),
        Not(Or(Not(P), Not(Q)))
    )


def pelletier_10():
    """Pelletier 10:
    ((Q → R) ∧ (R → (P ∧ Q)) ∧ (P → (Q ∨ R))) → (P ↔ Q)"""
    P, Q, R = Prop("P"), Prop("Q"), Prop("R")
    return Implies(
        And(
            And(
                Implies(Q, R),
                Implies(R, And(P, Q))
            ),
            Implies(P, Or(Q, R))
        ),
        Iff(P, Q)
    )


def pelletier_11():
    """Pelletier 11: P ↔ P"""
    P = Prop("P")
    return Iff(P, P)


def pelletier_12():
    """Pelletier 12: ((P ↔ Q) ↔ R) ↔ (P ↔ (Q ↔ R))"""
    P, Q, R = Prop("P"), Prop("Q"), Prop("R")
    return Iff(
        Iff(Iff(P, Q), R),
        Iff(P, Iff(Q, R))
    )


def pelletier_13():
    """Pelletier 13: (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R))
    Distributivity."""
    P, Q, R = Prop("P"), Prop("Q"), Prop("R")
    return Iff(
        Or(P, And(Q, R)),
        And(Or(P, Q), Or(P, R))
    )


def pelletier_14():
    """Pelletier 14: (P ↔ Q) ↔ ((Q ∨ ¬P) ∧ (¬Q ∨ P))"""
    P, Q = Prop("P"), Prop("Q")
    return Iff(
        Iff(P, Q),
        And(Or(Q, Not(P)), Or(Not(Q), P))
    )


def pelletier_15():
    """Pelletier 15: (P → Q) ↔ (¬P ∨ Q)"""
    P, Q = Prop("P"), Prop("Q")
    return Iff(
        Implies(P, Q),
        Or(Not(P), Q)
    )


def pelletier_16():
    """Pelletier 16: (P → Q) ∨ (Q → P)"""
    P, Q = Prop("P"), Prop("Q")
    return Or(
        Implies(P, Q),
        Implies(Q, P)
    )


def pelletier_17():
    """Pelletier 17: ((P ∧ (Q → R)) → S) ↔ ((¬P ∨ Q ∨ S) ∧ (¬P ∨ ¬R ∨ S))"""
    P, Q, R, S = Prop("P"), Prop("Q"), Prop("R"), Prop("S")
    return Iff(
        Implies(And(P, Implies(Q, R)), S),
        And(
            Or(Or(Not(P), Q), S),
            Or(Or(Not(P), Not(R)), S)
        )
    )

# ============================================================
# Helper functions for Pelletier 18–34
# ============================================================

def U(pred: str, var: str) -> Formula:
    """Unary predicate with a variable argument, e.g., P(x)."""
    return Relation(pred, (Var(var),))


def UC(pred: str, const: str) -> Formula:
    """Unary predicate with a constant argument, e.g., P(a)."""
    return Relation(pred, (Const(const),))


def And_many(formulas):
    """Build conjunction A1 ∧ A2 ∧ ... ∧ An."""
    if not formulas:
        return Top()

    result = formulas[0]
    for f in formulas[1:]:
        result = And(result, f)
    return result


# ============================================================
# Pelletier 18–34: First-order challenge problems
# Manually encoded from selected TPTP files.
# ============================================================

def pelletier_18():
    """Pelletier 18: ∃y∀x(F(y) → F(x))."""
    return Exists(
        "y",
        Forall(
            "x",
            Implies(U("big_f", "y"), U("big_f", "x"))
        )
    )


def pelletier_19():
    """Pelletier 19."""
    return Exists(
        "x",
        Forall(
            "y",
            Forall(
                "z",
                Implies(
                    Implies(U("big_p", "y"), U("big_q", "z")),
                    Implies(U("big_p", "x"), U("big_q", "x"))
                )
            )
        )
    )


def pelletier_20():
    """Pelletier 20."""
    antecedent = Forall(
        "x",
        Forall(
            "y",
            Exists(
                "z",
                Forall(
                    "w",
                    Implies(
                        And(U("big_p", "x"), U("big_q", "y")),
                        And(U("big_r", "z"), U("big_s", "w"))
                    )
                )
            )
        )
    )

    consequent = Exists(
        "x1",
        Exists(
            "y1",
            Implies(
                And(U("big_p", "x1"), U("big_q", "y1")),
                Exists("z1", U("big_r", "z1"))
            )
        )
    )

    return Implies(antecedent, consequent)


def pelletier_21():
    """Pelletier 21: axioms encoded as (A1 ∧ A2) → conjecture."""
    p = Prop("p")

    a1 = Exists("x", Implies(p, U("big_f", "x")))
    a2 = Exists("x", Implies(U("big_f", "x"), p))

    conjecture = Exists("x", Iff(p, U("big_f", "x")))

    return Implies(And_many([a1, a2]), conjecture)


def pelletier_22():
    """Pelletier 22."""
    p = Prop("p")

    antecedent = Forall("x", Iff(p, U("big_f", "x")))
    consequent = Iff(p, Forall("x1", U("big_f", "x1")))

    return Implies(antecedent, consequent)


def pelletier_23():
    """Pelletier 23."""
    p = Prop("p")

    left = Forall("x", Or(p, U("big_f", "x")))
    right = Or(p, Forall("x1", U("big_f", "x1")))

    return Iff(left, right)


def pelletier_24():
    """Pelletier 24: axioms encoded as conjunction → conjecture."""
    a1 = Not(
        Exists(
            "x",
            And(U("big_s", "x"), U("big_q", "x"))
        )
    )

    a2 = Forall(
        "x",
        Implies(
            U("big_p", "x"),
            Or(U("big_q", "x"), U("big_r", "x"))
        )
    )

    a3 = Implies(
        Not(Exists("x", U("big_p", "x"))),
        Exists("y", U("big_q", "y"))
    )

    a4 = Forall(
        "x",
        Implies(
            Or(U("big_q", "x"), U("big_r", "x")),
            U("big_s", "x")
        )
    )

    conjecture = Exists(
        "x",
        And(U("big_p", "x"), U("big_r", "x"))
    )

    return Implies(And_many([a1, a2, a3, a4]), conjecture)


def pelletier_25():
    """
    Pelletier 25.
    Note: TPTP marks this as ContradictoryAxioms.
    """
    a1 = Exists("x", U("big_p", "x"))

    a2 = Forall(
        "x",
        Implies(
            U("big_f", "x"),
            And(Not(U("big_g", "x")), U("big_r", "x"))
        )
    )

    a3 = Forall(
        "x",
        Implies(
            U("big_p", "x"),
            And(U("big_g", "x"), U("big_f", "x"))
        )
    )

    a4 = Or(
        Forall(
            "x",
            Implies(U("big_p", "x"), U("big_q", "x"))
        ),
        Exists(
            "z",
            And(U("big_p", "z"), U("big_r", "z"))
        )
    )

    conjecture = Exists(
        "x",
        And(U("big_q", "x"), U("big_p", "x"))
    )

    return Implies(And_many([a1, a2, a3, a4]), conjecture)


def pelletier_26():
    """Pelletier 26."""
    a1 = Iff(
        Exists("x", U("big_p", "x")),
        Exists("y", U("big_q", "y"))
    )

    a2 = Forall(
        "x",
        Forall(
            "y",
            Implies(
                And(U("big_p", "x"), U("big_q", "y")),
                Iff(U("big_r", "x"), U("big_s", "y"))
            )
        )
    )

    conjecture = Iff(
        Forall("x", Implies(U("big_p", "x"), U("big_r", "x"))),
        Forall("y", Implies(U("big_q", "y"), U("big_s", "y")))
    )

    return Implies(And_many([a1, a2]), conjecture)


def pelletier_27():
    """Pelletier 27."""
    a1 = Exists(
        "x",
        And(U("big_f", "x"), Not(U("big_g", "x")))
    )

    a2 = Forall(
        "x",
        Implies(U("big_f", "x"), U("big_h", "x"))
    )

    a3 = Forall(
        "x",
        Implies(
            And(U("big_j", "x"), U("big_i", "x")),
            U("big_f", "x")
        )
    )

    a4 = Implies(
        Exists(
            "x",
            And(U("big_h", "x"), Not(U("big_g", "x")))
        ),
        Forall(
            "x1",
            Implies(U("big_i", "x1"), Not(U("big_h", "x1")))
        )
    )

    conjecture = Forall(
        "x",
        Implies(U("big_j", "x"), Not(U("big_i", "x")))
    )

    return Implies(And_many([a1, a2, a3, a4]), conjecture)


def pelletier_28():
    """Pelletier 28."""
    a1 = Forall(
        "x",
        Implies(
            U("big_p", "x"),
            Forall("z", U("big_q", "z"))
        )
    )

    a2 = Implies(
        Forall(
            "x",
            Or(U("big_q", "x"), U("big_r", "x"))
        ),
        Exists(
            "x1",
            And(U("big_q", "x1"), U("big_s", "x1"))
        )
    )

    a3 = Implies(
        Exists("x", U("big_s", "x")),
        Forall(
            "x1",
            Implies(U("big_f", "x1"), U("big_g", "x1"))
        )
    )

    conjecture = Forall(
        "x",
        Implies(
            And(U("big_p", "x"), U("big_f", "x")),
            U("big_g", "x")
        )
    )

    return Implies(And_many([a1, a2, a3]), conjecture)


def pelletier_29():
    """Pelletier 29."""
    a1 = Exists("x", U("big_f", "x"))
    a2 = Exists("y", U("big_g", "y"))

    left = And(
        Forall("x", Implies(U("big_f", "x"), U("big_h", "x"))),
        Forall("u", Implies(U("big_g", "u"), U("big_j", "u")))
    )

    right = Forall(
        "w",
        Forall(
            "y",
            Implies(
                And(U("big_f", "w"), U("big_g", "y")),
                And(U("big_h", "w"), U("big_j", "y"))
            )
        )
    )

    conjecture = Iff(left, right)

    return Implies(And_many([a1, a2]), conjecture)


def pelletier_30():
    """Pelletier 30."""
    a1 = Forall(
        "x",
        Implies(
            Or(U("big_f", "x"), U("big_g", "x")),
            Not(U("big_h", "x"))
        )
    )

    a2 = Forall(
        "x",
        Implies(
            Implies(U("big_g", "x"), Not(U("big_i", "x"))),
            And(U("big_f", "x"), U("big_h", "x"))
        )
    )

    conjecture = Forall("x", U("big_i", "x"))

    return Implies(And_many([a1, a2]), conjecture)


def pelletier_31():
    """Pelletier 31."""
    a1 = Not(
        Exists(
            "x",
            And(
                U("big_f", "x"),
                Or(U("big_g", "x"), U("big_h", "x"))
            )
        )
    )

    a2 = Exists(
        "x",
        And(U("big_i", "x"), U("big_f", "x"))
    )

    a3 = Forall(
        "x",
        Implies(Not(U("big_h", "x")), U("big_j", "x"))
    )

    conjecture = Exists(
        "x",
        And(U("big_i", "x"), U("big_j", "x"))
    )

    return Implies(And_many([a1, a2, a3]), conjecture)


def pelletier_32():
    """Pelletier 32."""
    a1 = Forall(
        "x",
        Implies(
            And(
                U("big_f", "x"),
                Or(U("big_g", "x"), U("big_h", "x"))
            ),
            U("big_i", "x")
        )
    )

    a2 = Forall(
        "x",
        Implies(
            And(U("big_i", "x"), U("big_h", "x")),
            U("big_j", "x")
        )
    )

    a3 = Forall(
        "x",
        Implies(U("big_k", "x"), U("big_h", "x"))
    )

    conjecture = Forall(
        "x",
        Implies(
            And(U("big_f", "x"), U("big_k", "x")),
            U("big_j", "x")
        )
    )

    return Implies(And_many([a1, a2, a3]), conjecture)


def pelletier_33():
    """Pelletier 33."""
    left = Forall(
        "x",
        Implies(
            And(
                UC("big_p", "a"),
                Implies(U("big_p", "x"), UC("big_p", "b"))
            ),
            UC("big_p", "c")
        )
    )

    right = Forall(
        "x1",
        And(
            Or(
                Or(Not(UC("big_p", "a")), U("big_p", "x1")),
                UC("big_p", "c")
            ),
            Or(
                Or(Not(UC("big_p", "a")), Not(UC("big_p", "b"))),
                UC("big_p", "c")
            )
        )
    )

    return Iff(left, right)


def pelletier_34():
    """
    Pelletier 34: Andrews Challenge Problem.
    This is expected to be substantially harder than the earlier problems.
    """
    left = Iff(
        Exists(
            "x",
            Forall(
                "y",
                Iff(U("big_p", "x"), U("big_p", "y"))
            )
        ),
        Iff(
            Exists("u", U("big_q", "u")),
            Forall("w", U("big_q", "w"))
        )
    )

    right = Iff(
        Exists(
            "x1",
            Forall(
                "y1",
                Iff(U("big_q", "x1"), U("big_q", "y1"))
            )
        ),
        Iff(
            Exists("u1", U("big_p", "u1")),
            Forall("w1", U("big_p", "w1"))
        )
    )

    return Iff(left, right)

# ============================================================
# Collection of Pelletier problems
# ============================================================

PELLETIER_PROBLEMS_PROPOSITIONAL = [
    ("Pelletier 1", pelletier_1),
    ("Pelletier 2", pelletier_2),
    ("Pelletier 3", pelletier_3),
    ("Pelletier 4", pelletier_4),
    ("Pelletier 5", pelletier_5),
    ("Pelletier 6", pelletier_6),
    ("Pelletier 7", pelletier_7),
    ("Pelletier 8", pelletier_8),
    ("Pelletier 9", pelletier_9),
    ("Pelletier 10", pelletier_10),
    ("Pelletier 11", pelletier_11),
    ("Pelletier 12", pelletier_12),
    ("Pelletier 13", pelletier_13),
    ("Pelletier 14", pelletier_14),
    ("Pelletier 15", pelletier_15),
    ("Pelletier 16", pelletier_16),
    ("Pelletier 17", pelletier_17),
]


PELLETIER_PROBLEMS_FOL_18_34 = [
    ("Pelletier 18", pelletier_18),
    ("Pelletier 19", pelletier_19),
    ("Pelletier 20", pelletier_20),
    ("Pelletier 21", pelletier_21),
    ("Pelletier 22", pelletier_22),
    ("Pelletier 23", pelletier_23),
    ("Pelletier 24", pelletier_24),
    ("Pelletier 25", pelletier_25),
    ("Pelletier 26", pelletier_26),
    ("Pelletier 27", pelletier_27),
    ("Pelletier 28", pelletier_28),
    ("Pelletier 29", pelletier_29),
    ("Pelletier 30", pelletier_30),
    ("Pelletier 31", pelletier_31),
    ("Pelletier 32", pelletier_32),
    ("Pelletier 33", pelletier_33),
    ("Pelletier 34", pelletier_34),
]


ALL_PELLETIER_PROBLEMS = (
    PELLETIER_PROBLEMS_PROPOSITIONAL
    + PELLETIER_PROBLEMS_FOL_18_34
)


def get_pelletier_1_17_formulas():
    """Return list of (name, formula) for Pelletier 1–17."""
    return [(name, fn()) for name, fn in PELLETIER_PROBLEMS_PROPOSITIONAL]


def get_pelletier_18_34_formulas():
    """Return list of (name, formula) for Pelletier 18–34."""
    return [(name, fn()) for name, fn in PELLETIER_PROBLEMS_FOL_18_34]


def get_all_pelletier_formulas():
    """Return list of (name, formula) for all encoded Pelletier problems."""
    return [(name, fn()) for name, fn in ALL_PELLETIER_PROBLEMS]