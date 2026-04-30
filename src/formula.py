"""
Class hierachy is used to express the FOL formula 
Based on the syntax: F :: = ⊤ | ⊥ | R(t, ..., t) | ¬F | F ∧ F | F ∨ F | F → F | ∀x.F | ∃x.F | in lecture notes
""" 
from __future__ import annotations
from dataclasses import dataclass
from typing import Tuple

# ============================================================
# Term Hierarchy
# ============================================================
# Terms indicate domain objects (not truth values)
# Syntax: t :: = a (constant, scope) | x (variables, any datatype) | f(t, ..., t) (function application)

class Term: # abstract base class for first-order terms
    pass

@dataclass(frozen=True)
class Var(Term):
    # A variable, e.g., x, y, z
    name: str

    def __repr__(self) -> str:
        return self.name
    
@dataclass(frozen=True) # frozen=true: once created, cannot be modified -> can be added to a set or dic
class Const(Term):
    # A constant, e.g., a, b, 1, even colour, seasons, spring,,, any object!
    name: str
    
    def __repr__(self) -> str:
        return self.name
    
@dataclass(frozen=True)
class Func(Term): 
    # "A function application, e.g., f(x, y), next(spring)
    name: str
    args: Tuple[Term, ...] 

    def __repr__(self) -> str:
        args_str = ", ".join(repr(arg) for arg in self.args)
        return f"{self.name}({args_str})"
    

# ============================================================
# Formula Hierarchy
# ============================================================
# Formulae have truth values (unlike terms)
# Syntax: F :: = ⊤ | ⊥ | Prop | R(t, ..., t) | ¬F | F ∧ F | F ∨ F | F → F | ∀x.F | ∃x.F |

class Formula: 
    # Abstract base class for all formulae
    pass


# Atomic formulas — cannot be broken down further
@dataclass(frozen=True) # [⊤R]
class Top(Formula):
    def __repr__(self) -> str: 
        return "⊤"

@dataclass(frozen=True) # [⊥L]
class Bottom(Formula):
    def __repr__(self) -> str:
        return "⊥"   
    
@dataclass(frozen=True)
class Prop(Formula):
    # A propositional variable, such as A, B.
    name: str

    def __repr__(self) -> str:
        return self.name

@dataclass(frozen=True)
class Relation(Formula):
    # A relation application, such as R(x), R(x, y)
    name: str
    args: Tuple[Term, ...]

    def __repr__(self) -> str:
        args_str = ", ".join(repr(arg) for arg in self.args)
        return f"{self.name}({args_str})"
    

# Connectives — compound formulas built from other formulas
@dataclass(frozen=True)
class Not(Formula):
    """Negation: ¬F"""
    operand: Formula

    def __repr__(self) -> str:
        return f"¬{self.operand}"

@dataclass(frozen=True)
class And(Formula):
    # Conjuction: F_1 ∧ F_2
    left: Formula
    right: Formula

    def __repr__(self) -> str:
        return f"({self.left} ∧ {self.right})"
    
@dataclass(frozen=True)
class Or(Formula):
    # Disjuction: F_1 ∨ F_2
    left: Formula
    right: Formula

    def __repr__(self) -> str:
        return f"({self.left} ∨ {self.right})"     

@dataclass(frozen=True)
class Implies(Formula):
    # Implication: F_1 → F_2 
    left: Formula
    right: Formula

    def __repr__(self) -> str:
        return f"({self.left} → {self.right})"    
    

# Quantifiers — bind variables over formulas
@dataclass(frozen=True)
class Forall(Formula):
    # forall quantifier: ∀x.F
    var: str # the bound variable name, e.g., "x"
    body: Formula # the formula being quantified

    def __repr__(self) -> str:
        return f"∀{self.var}.{self.body}"
    
@dataclass(frozen=True)
class Exists(Formula):
    # Existential quantifier: ∃x.F
    var: str # the bound variable name, e.g., "x"
    body: Formula # the formula being quantified

    def __repr__(self) -> str:
        return f"∃{self.var}.{self.body}"
    

# ============================================================
# Substitution
# ============================================================
# Substitution A[t/x] means: replace every occurrence of variable x in A with term t
# Critical: do not substitute inside a quantifier that binds x.

def substitute_term(term: Term, var_name: str, replacement: Term) -> Term:
    """
    substitute all occurrences of Var(var_name) in term with replacement
    returns a new term (terms are immutable)
    """
    if isinstance(term, Var): 
        # if this is the variable we're looking for, replace it
        if term.name == var_name:
            return replacement
        else:
            return term 
    
    elif isinstance(term, Const): 
        # constants don't contain variables - return as-is
        return term
    
    elif isinstance(term, Func): # since there may be variables within the function arguments, a recursive call
        # eg: f(x, g(x,y))[t/x] = f(t, g(t,y))
        # recursively substitute inside function arguments
        new_args = tuple(
            substitute_term(arg, var_name, replacement)
            for arg in term.args
        )
        return Func(term.name, new_args)
    
    else: 
        raise ValueError(f"Unknown term type: {type(term)}")
    
# main substitution 
def substitute(formula: Formula, var_name: str, replacement: Term) -> Formula:
    """
    substitute all free occurrences of Var(var_name) in formula with replacement. 
    Returns a new formula (formulas are immutable)
    """
    # --- Atomic Cases --- 
    if isinstance(formula, Top) or isinstance(formula, Bottom):
        return formula
    elif isinstance(formula, Prop):
        # propositional variables don't contain term variables
        return formula 
    
    elif isinstance(formula, Relation):
        # in FOL, a relation must be applied to a term, such as R(x), to form an atomic formula
        # substitute inside each argument term 
        new_args = tuple(
            substitute_term(arg, var_name, replacement)
            for arg in formula.args
        )
        return Relation(formula.name, new_args)
    
    # connectives: recurse on sub-formulas
    # create a new instance and return it (since it's immutable, always return a new ojject)
    elif isinstance(formula, Not):
        return Not(substitute(formula.operand, var_name, replacement))
    
    elif isinstance(formula, And):
        return And(
            substitute(formula.left, var_name, replacement),
            substitute(formula.right, var_name, replacement)
        )
    elif isinstance(formula, Or):
        return Or(
            substitute(formula.left, var_name, replacement),
            substitute(formula.right, var_name, replacement)
        )    

    elif isinstance(formula, Implies):
        return Implies(
            substitute(formula.left, var_name, replacement),
            substitute(formula.right, var_name, replacement)
        )
    
    # quantifiers: stop if this quantifier binds var_name  
    # eg. ∀x.R(x, y)[t/x] -> this is forall over x, we can simply return [t/x]
    # eg. ∀x.R(x, y)[t/y] -> conversely, forall over x, but since we need to substitute y with t, 
    elif isinstance(formula, Forall):
        if formula.var == var_name:
            # this ∀ binds the variable we're substituting - don't go inside
            return formula
        else: 
            # different variable - recurse into body
            return Forall(
                formula.var, 
                substitute(formula.body, var_name, replacement)
            )
        
    elif isinstance(formula, Exists):
        if formula.var == var_name:
            # this ∃ binds the variable we're substituting - don't go inside
            return formula
        else: 
            return Exists(
                formula.var, 
                substitute(formula.body, var_name, replacement)
            )
    else: 
        raise ValueError(f"Unknown formula type: {type(formula)}")    