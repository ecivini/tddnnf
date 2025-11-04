import pytest

from theorydd.solvers.mathsat_partial_extended import (
    MathSATExtendedPartialEnumerator
)
from theorydd.tddnnf.theory_ddnnf import TheoryDDNNF
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.walkers.walker_bool_abstraction import BooleanAbstractionWalker
from theorydd.walkers.walker_refinement import RefinementWalker
from pysmt.shortcuts import read_smtlib, And, Solver, Not, Or, Iff, is_valid, is_sat
from theorydd.formula import get_normalized

FORMULAS = [
    "tests/items/test_lemmas.smt2",
]

TEST_PARAMETERS = [
    (FORMULAS[0], MathSATTotalEnumerator),
    (FORMULAS[0], MathSATExtendedPartialEnumerator),
]


# @pytest.mark.parametrize("phi_path,solver_class", TEST_PARAMETERS)
# def test_t_reduction_correctness(phi_path, solver_class):
#     phi = read_smtlib(phi_path)

#     phi_bool_walker = BooleanAbstractionWalker()
#     phi_abstr = phi_bool_walker.walk(phi)

#     solver_lemmas = solver_class()
#     sat_lemmas = solver_lemmas.check_all_sat(phi)
#     assert sat_lemmas is True, "The formula should be satisfiable"

#     models = []
#     raw_models = solver_lemmas.get_models()
#     for raw_model in raw_models:
#         models.append(And(raw_model))

#     conj_models = Or(models)
#     conj_models_abstr = phi_bool_walker.walk(conj_models)

#     solver_check = Solver()

#     print(phi_abstr)
#     print()
#     print(conj_models_abstr)

#     solver_check.add_assertion(And(phi_abstr, Not(conj_models_abstr)))
#     sat_check = solver_check.solve()
#     assert sat_check is False, """
#         The conjunction of lemmas should be equivalent to the original formula
#     """


@pytest.mark.parametrize("phi_path,solver_class", TEST_PARAMETERS)
def test_lemmas_correctness(phi_path, solver_class):
    _solver = Solver()
    converter = _solver.converter

    phi = read_smtlib(phi_path)
    phi = get_normalized(phi, converter)

    is_parallelized = (
        solver_class == MathSATExtendedPartialEnumerator
    )
    solver = solver_class()
    procs_num = 8 if is_parallelized else 1
    sat = solver.check_all_sat(phi, parallel_procs=procs_num)
    assert sat is True, "The formula should be satisfiable"

    print("LEMMAS:\n", set(solver.get_theory_lemmas()))

    phi_and_lemmas = And(phi, *set(solver.get_theory_lemmas()))
    phi_and_lemmas = get_normalized(phi_and_lemmas, converter)

    atoms = phi_and_lemmas.get_atoms()
    bool_walker = BooleanAbstractionWalker(atoms=atoms)
    phi_and_lemmas_abstr = bool_walker.walk(phi_and_lemmas)

    phi_abstr = bool_walker.walk(phi)

    solver_abstr = solver_class()
    sat_abstr = solver_abstr.check_all_sat(
        phi_and_lemmas_abstr,
        parallel_procs=procs_num,
        atoms=list(phi_abstr.get_atoms())
    )
    assert sat_abstr is True, "The abstracted formula should be satisfiable"

    t_unsat_models = set()
    for abstr_model in solver_abstr.get_models():
        walker = RefinementWalker(abstraction=bool_walker.abstraction)
        refined = walker.walk(And(abstr_model))

        solver = Solver()
        solver.add_assertion(refined)
        sat = solver.solve()

        if not sat:
            if len(t_unsat_models) == 0:
                print("UNSAT Model:", refined)
                print()
                print("UNSAT Abstr:", abstr_model)
            t_unsat_models.add(refined)

    assert len(t_unsat_models) == 0, "There should be no theory-unsat models"
