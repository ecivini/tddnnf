from typing import NamedTuple

import pytest
from pysmt.fnode import FNode
from pysmt.formula import FormulaContextualizer
from pysmt.shortcuts import And, LE, LT, Or, Solver, Symbol, read_smtlib
from pysmt.typing import REAL

from theorydd.formula import get_normalized
from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.walkers.walker_bool_abstraction import BooleanAbstractionWalker
from theorydd.walkers.walker_refinement import RefinementWalker

w, x, y, z = (Symbol(name, REAL) for name in "wxyz")

Example = NamedTuple(
    "Example", [("formula", str | FNode), ("is_sat", bool), ("tlemmas_expected", bool)]
)

# formulas to test: (formula, is_sat, tlemmas_expected)
EXAMPLES: list[Example] = [
    Example("tests/items/test_lemmas.smt2", True, True),
    Example(And(LE(x, y), LE(y, x)), True, False),
    Example(And(LT(x, y), LT(y, x)), False, True),
    Example(And(LE(x, y), LE(z, w)), True, False),
    Example(Or(LT(x, y), LT(y, z), LT(z, x)), True, True),
]

SOLVERS = [
    ("total", MathSATTotalEnumerator, {}),
    ("partial-1", MathSATExtendedPartialEnumerator, {"parallel_procs": 1}),
    ("partial-8", MathSATExtendedPartialEnumerator, {"parallel_procs": 8}),
]


@pytest.fixture(params=SOLVERS, ids=lambda s: s[0])
def solver(request):
    _, solver_cls, params = request.param
    return solver_cls(**params)


@pytest.fixture(params=EXAMPLES, ids=lambda e: str(e.formula))
def example(request):
    ex = request.param
    ctxzer = FormulaContextualizer()
    formula = ctxzer.walk(ex.formula) if isinstance(ex.formula, FNode) else read_smtlib(ex.formula)
    return Example(formula, ex.is_sat, ex.tlemmas_expected)


def test_lemmas_correctness(example, solver):
    _solver = Solver("msat")
    converter = _solver.converter
    phi = example.formula
    phi = get_normalized(phi, converter)

    # ---- Generate lemmas ----
    phi_atoms = phi.get_atoms()
    phi_sat = solver.check_all_sat(phi, list(phi.get_atoms()), store_models=True)
    assert phi_sat == example.is_sat, "Satisfiability should match expected"

    lemmas = solver.get_theory_lemmas()
    if example.tlemmas_expected:
        assert len(lemmas) > 0, "Expected theory lemmas, but none were found"
    else:
        assert len(lemmas) == 0, "Did not expect theory lemmas, but some were found"

    # ---- Build Boolean abstraction of phi & lemmas ----
    phi_and_lemmas = And(phi, get_normalized(And(lemmas), converter))
    phi_and_lemmas_atoms = phi_and_lemmas.get_atoms()
    assert phi_atoms <= phi_and_lemmas_atoms
    bool_walker = BooleanAbstractionWalker(atoms=phi_and_lemmas_atoms)
    phi_and_lemmas_abstr = bool_walker.walk(phi_and_lemmas)
    phi_abstr = bool_walker.walk(phi)

    # ---- Check that every truth assignment of phi & lemmas is theory-sat ----
    solver_abstr = MathSATTotalEnumerator()
    abstr_sat = solver_abstr.check_all_sat(
        phi_and_lemmas_abstr,
        atoms=list(phi_abstr.get_atoms()),
        store_models=True,
    )
    assert abstr_sat == phi_sat, "Satisfiability of abstracted formula with lemmas should match original"

    with Solver() as check_solver:
        t_unsat_models = []
        for abstr_model in solver_abstr.get_models():
            walker = RefinementWalker(abstraction=bool_walker.abstraction)
            refined = walker.walk(And(abstr_model))

            check_solver.push()
            check_solver.add_assertion(refined)
            sat = check_solver.solve()
            if not sat:
                t_unsat_models.append(refined)
            check_solver.pop()

    assert len(t_unsat_models) == 0, "There should be no theory-unsat models"
