from pysmt.shortcuts import (
    And, Or, Not, Int, Symbol, Equals, Implies, is_valid, Iff
)
from theorydd.walkers.walker_bool_abstraction import BooleanAbstractionWalker


def test_bool_abstraction_walker():
    ten = Int(10)
    zero = Int(0)
    a = Symbol("a", ten.get_type())
    b = Symbol("b", ten.get_type())
    c = Symbol("c", ten.get_type())

    or_1 = Or(
        Implies(Equals(a, ten), Equals(b, zero)),
        Implies(Equals(a, zero), Equals(b, ten))
    )

    or_2 = Or(
        Implies(Equals(b, ten), Equals(c, zero)),
        Implies(Equals(b, zero), Equals(c, ten))
    )

    formula = And(or_1, or_2)

    walker = BooleanAbstractionWalker()
    abstracted_formula = walker.walk(formula)

    assert len(walker.abstraction) == 6, "There should be 6 abstracted atoms"

    expected_abstracted = And(
        Or(
            Implies(
                walker.abstraction[Equals(a, ten)],
                walker.abstraction[Equals(b, zero)]
            ),
            Implies(
                walker.abstraction[Equals(a, zero)],
                walker.abstraction[Equals(b, ten)]
            )
        ),
        Or(
            Implies(
                walker.abstraction[Equals(b, ten)],
                walker.abstraction[Equals(c, zero)]
            ),
            Implies(
                walker.abstraction[Equals(b, zero)],
                walker.abstraction[Equals(c, ten)]
            )
        )
    )

    assert is_valid(Iff(abstracted_formula, expected_abstracted)), "Abstracted formula does not match expected structure"