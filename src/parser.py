"""
A minimal parser for the FOL syntax used in this project.
syntax:
    ¬A
    ~A
    A ∧ B
    A & B
    A ∨ B
    A | B
    A → B
    A -> B
    ∀x.P(x)
    forall x. P(x)
    ∃x.P(x)
    exists x. P(x)

Note:
    This parser doesn't support biconditionals:
        A <-> B
        A ↔ B

    If a benchmark formula contains biconditional, it should be manually
    translated as:
        A ↔ B  =  (A → B) ∧ (B → A)

Note: this isn't a full TPTP parser. It's a small project specific parser 
designed to convert formula strings into internal formula representation
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import List, Optional, Set

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


# ============================================================
# Tokenizer
# ============================================================
TOKEN_PATTERN = re.compile(
    r"""
    \s*
    (
        ->|→|
        forall\b|exists\b|
        ∀|∃|
        true\b|false\b|
        top\b|bottom\b|
        ⊤|⊥|
        [A-Za-z_][A-Za-z0-9_]*|
        [(),.]|
        [~¬&∧|∨]
    )
    """,
    re.VERBOSE,
)


class ParserError(Exception):
    # raised when parsing fails
    pass


def tokenize(text: str) -> List[str]:
    # convert an input string into tokens
    tokens = []
    pos = 0

    while pos < len(text):
        match = TOKEN_PATTERN.match(text, pos)

        if not match:
            raise ParserError(
                f"Unexpected character at position {pos}: {text[pos]!r}"
            )

        token = match.group(1)
        tokens.append(token)
        pos = match.end()

    return tokens


# ============================================================
# Recursive descent parser
# ============================================================
class FormulaParser:
    def __init__(self, tokens: List[str]):
        self.tokens = tokens
        self.pos = 0
        self.bound_vars: Set[str] = set()

    def peek(self) -> Optional[str]:
        # return current token wo/ consuming it
        if self.pos >= len(self.tokens):
            return None
        return self.tokens[self.pos]

    def consume(self, expected: Optional[str] = None) -> str:
        # consume and return the current token 
        # if expected is provided, the current token must match it 
        token = self.peek()
        if token is None:
            raise ParserError("Unexpected end of input")

        if expected is not None and token != expected:
            raise ParserError(f"Expected {expected!r}, got {token!r}")

        self.pos += 1
        return token

    def match(self, *choices: str) -> bool:
        if self.peek() in choices:
            self.pos += 1
            return True
        return False

    # Entry point
    def parse(self) -> Formula:
        formula = self.parse_implies()

        if self.peek() is not None:
            raise ParserError(f"Unexpected token at end: {self.peek()!r}")

        return formula

    # Formula grammar with precedence
    def parse_implies(self) -> Formula:
        left = self.parse_or()

        # Implication is right-associative:
        # A -> B -> C means A -> (B -> C)
        if self.match("→", "->"):
            right = self.parse_implies()
            return Implies(left, right)

        return left

    def parse_or(self) -> Formula:
        left = self.parse_and()

        while self.match("∨", "|"):
            right = self.parse_and()
            left = Or(left, right)

        return left

    def parse_and(self) -> Formula:
        left = self.parse_unary()

        while self.match("∧", "&"):
            right = self.parse_unary()
            left = And(left, right)

        return left

    def parse_unary(self) -> Formula:
        token = self.peek()

        if token is None:
            raise ParserError("Unexpected end of input while parsing formula")

        # Negation
        if self.match("¬", "~"):
            return Not(self.parse_unary())

        # Universal quantifier
        if self.match("∀", "forall"):
            var_name = self.consume_identifier()
            self.consume(".")

            old_bound = set(self.bound_vars)
            self.bound_vars.add(var_name)

            # Quantifiers bind tightly.
            # Example: forall x. P(x) -> P(a)
            # parses as: (forall x. P(x)) -> P(a)
            body = self.parse_unary()

            self.bound_vars = old_bound
            return Forall(var_name, body)

        # existential quantifier
        if self.match("∃", "exists"):
            var_name = self.consume_identifier()
            self.consume(".")

            old_bound = set(self.bound_vars)
            self.bound_vars.add(var_name)

            body = self.parse_unary()

            self.bound_vars = old_bound
            return Exists(var_name, body)

        # parenthesised formula
        if self.match("("):
            formula = self.parse_implies()
            self.consume(")")
            return formula

        # Atomic formula
        return self.parse_atom()

    # Atomic formulas and terms
    def parse_atom(self) -> Formula:
        token = self.peek()

        if token is None:
            raise ParserError("Unexpected end of input while parsing atom")

        # Logical constants
        if token in {"⊤", "true", "top"}:
            self.consume()
            return Top()

        if token in {"⊥", "false", "bottom"}:
            self.consume()
            return Bottom()

        name = self.consume_identifier()

        # Relation: P(x), R(a, b), big_f(x)
        if self.match("("):
            args = []

            if self.peek() != ")":
                while True:
                    args.append(self.parse_term())

                    if self.match(","):
                        continue
                    break

            self.consume(")")
            return Relation(name, tuple(args))

        # Propositional variable: A, B, P, Q
        return Prop(name)

    def parse_term(self) -> Term:
        name = self.consume_identifier()

        # This minimal parser doesn't support function terms such as f(x).
        # It only supports variables and constants as relation arguments.
        if self.peek() == "(":
            raise ParserError(
                "Function terms such as f(x) are not supported by this minimal parser. "
                "Use constants/variables as relation arguments instead."
            )

        # bound variables are parsed as Var.
        if name in self.bound_vars:
            return Var(name)

        # common unbound variable names are also parsed as Var.
        # constants such as a, b, c are parsed as Const.
        if name in {"x", "y", "z", "u", "v", "w"}:
            return Var(name)

        return Const(name)

    def consume_identifier(self) -> str:
        token = self.peek()

        if token is None:
            raise ParserError("Expected identifier, got end of input")

        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", token):
            raise ParserError(f"Expected identifier, got {token!r}")

        self.pos += 1
        return token


# ============================================================
# Public functions
# ============================================================
def parse_formula(text: str) -> Formula:
    """Parse one formula string into a Formula object."""
    tokens = tokenize(text)
    parser = FormulaParser(tokens)
    return parser.parse()


def parse_formula_file(filepath: str | Path) -> List[Formula]:
    """
    Parse a text file containing one formula per line.

    Blank lines and lines starting with # are ignored.
    """
    filepath = Path(filepath)
    formulas = []

    with open(filepath, "r", encoding="utf-8") as fp:
        for line_number, line in enumerate(fp, start=1):
            line = line.strip()

            if not line or line.startswith("#"):
                continue

            try:
                formulas.append(parse_formula(line))
            except ParserError as exc:
                raise ParserError(
                    f"Error parsing {filepath} at line {line_number}: {exc}"
                ) from exc

    return formulas


# ============================================================
# self-test
# ============================================================
if __name__ == "__main__":
    examples = [
        "¬A",
        "~A",
        "(A ∧ B)",
        "(A & B)",
        "(A ∨ B)",
        "(A | B)",
        "(A → B)",
        "(A -> B)",
        "∀x.P(x)",
        "forall x. P(x)",
        "∃x.P(x)",
        "exists x. P(x)",
        "forall x. P(x) -> P(a)",
        "forall x. (P(x) -> Q(x))",
        "exists x. forall y. R(x, y)",
        "∃x.∀y.R(x, y) -> ∀y.∃x.R(x, y)",
    ]

    for example in examples:
        parsed = parse_formula(example)
        print(f"{example}")
        print(f"  => {parsed}")