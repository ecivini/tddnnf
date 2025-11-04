import pytest

from theorydd.solvers.mathsat_partial_extended import (
    MathSATExtendedPartialEnumerator
)
from theorydd.tddnnf.theory_ddnnf import TheoryDDNNF
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.walkers.walker_bool_abstraction import BooleanAbstractionWalker
from theorydd.walkers.walker_refinement import RefinementWalker
from pysmt.shortcuts import read_smtlib, And, Solver, Not, Or, Iff, is_valid

FORMULAS = [
    "tests/items/test_lemmas.smt2",
]

TEST_PARAMETERS = [
    (FORMULAS[0], MathSATTotalEnumerator),
    (FORMULAS[0], MathSATExtendedPartialEnumerator),
]


@pytest.mark.parametrize("phi_path,solver_class", TEST_PARAMETERS)
def test_lemmas_correctness(phi_path, solver_class):
    phi = read_smtlib(phi_path)

    solver = solver_class()
    sat = solver.check_all_sat(phi)
    assert sat is True, "The formula should be satisfiable"

    bool_walker = BooleanAbstractionWalker()

    phi_and_lemmas = And(phi, *solver.get_theory_lemmas())
    phi_and_lemmas_abstr = bool_walker.walk(phi_and_lemmas)

    solver_abstr = solver_class()
    sat_abstr = solver_abstr.check_all_sat(phi_and_lemmas_abstr)
    assert sat_abstr is True, "The abstracted formula should be satisfiable"

    t_unsat_models = set()
    for abstr_model in solver_abstr.get_models():
        walker = RefinementWalker(abstraction=bool_walker.abstraction)
        refined = walker.walk(And(abstr_model))

        solver = Solver()
        solver.add_assertion(refined)
        sat = solver.solve()

        if not sat:
            t_unsat_models.add(refined)

    assert len(t_unsat_models) == 0, "There should be no theory-unsat models"
