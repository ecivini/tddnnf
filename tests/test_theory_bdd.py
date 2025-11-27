"""tests for T-BDDS"""

from copy import deepcopy

from pysmt.shortcuts import And, Iff, Not, Or, Solver

from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.tdd.theory_bdd import TheoryBDD


def test_init_default(sat_formula):
    """tests BDD generation"""
    partial = MathSATExtendedPartialEnumerator()
    partial.check_all_sat(sat_formula, None, store_models=True)
    models = partial.get_models()
    tbdd = TheoryBDD(sat_formula, "total")
    assert tbdd.count_nodes() > 1, "TBDD is not only True or False node"
    assert tbdd.count_models() == len(models), "TBDD should have the same models found during All-SMT computation"


def test_init_with_known_lemmas(sat_formula):
    """tests BDD generation"""
    partial = MathSATExtendedPartialEnumerator()
    partial.check_all_sat(sat_formula, None, store_models=True)
    lemmas = partial.get_theory_lemmas()
    models = partial.get_models()
    tbdd = TheoryBDD(sat_formula, "total", tlemmas=lemmas)
    assert tbdd.count_nodes() > 1, "TBDD is not only True or False node"
    assert tbdd.count_models() == len(models), "TBDD should have the same models found during All-SMT computation"


def test_init_updated_computation_logger(sat_formula):
    """tests BDD generation"""
    partial = MathSATExtendedPartialEnumerator()
    partial.check_all_sat(sat_formula, None, store_models=True)
    models = partial.get_models()
    logger = {"hi": "hello"}
    copy_logger = deepcopy(logger)
    tbdd = TheoryBDD(sat_formula, "total", computation_logger=logger)
    assert tbdd.count_nodes() > 1, "TBDD is not only True or False node"
    assert tbdd.count_models() == len(models), "TBDD should have the same models found during All-SMT computation"
    assert logger != copy_logger, "Computation logger should be updated"
    assert logger["hi"] == copy_logger["hi"], "Old field of Logger should not be changed"


def test_init_unsat_formula(unsat_formula):
    """tests BDD generation"""
    partial = MathSATExtendedPartialEnumerator()
    partial.check_all_sat(unsat_formula, None, store_models=True)
    tbdd = TheoryBDD(unsat_formula, "total")
    assert tbdd.count_nodes() == 1, "TBDD is only False node"
    assert tbdd.count_models() == 0, "TBDD should have no models"


def test_init_tautology(prop_valid_formula):
    """tests BDD generation"""
    partial = MathSATExtendedPartialEnumerator()
    partial.check_all_sat(prop_valid_formula, None, store_models=True)
    tbdd = TheoryBDD(prop_valid_formula, "total")
    assert tbdd.count_nodes() == 1, "TBDD should be only True node"
    assert tbdd.count_models() == 2, "TBDD should have 2 models (atom True and atom false)"


def test_init_models(solver_info, any_formula):
    """tests that models of the T-BDD are also models of phi"""
    solver, _ = solver_info
    solver.check_all_sat(any_formula, None, store_models=True)
    tlemmas = solver.get_theory_lemmas()
    tbdd = TheoryBDD(any_formula, solver=solver, tlemmas=tlemmas)
    ddmodels = tbdd.pick_all()

    # check SMT of not (phi <=> encoding)
    # if UNSAT => encoding is correct
    phi_iff_encoding = Iff(
        any_formula, Or(And(atom if truth else Not(atom) for atom, truth in m.items()) for m in ddmodels)
    )

    with Solver() as check_solver:
        assert check_solver.is_valid(phi_iff_encoding), "The encoding should be theory-equivalent to phi"

    # check all models are also models of phi
    with Solver() as check_solver:
        check_solver.add_assertion(any_formula)
        for model in ddmodels:
            check_solver.push()
            check_solver.add_assertions([atom if truth else Not(atom) for atom, truth in model.items()])
            sat = check_solver.solve()
            assert sat, "Every model should be also a model for phi"
            check_solver.pop()


def test_lemma_loading(rangen_formula):
    """tests loading data with solver"""
    solver = MathSATExtendedPartialEnumerator()
    tbdd = TheoryBDD(rangen_formula, solver=solver, load_lemmas="./tests/items/rng_lemmas.smt")
    solver.reset()
    other_tbdd = TheoryBDD(rangen_formula, solver=solver)
    assert tbdd.count_models() == other_tbdd.count_models(), "Same modles should come from different loading"
