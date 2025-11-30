"""tests for T-SDDS"""

from copy import deepcopy

from pysmt.shortcuts import LT, REAL, Symbol

from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.tdd.theory_sdd import TheorySDD


def test_init_default(sat_formula):
    """tests SDD generation"""
    solver = MathSATExtendedPartialEnumerator(project_on_theory_atoms=False)
    solver.check_all_sat(sat_formula, None, store_models=True)
    models = solver.get_models()
    print("MODELS:", models)
    tsdd = TheorySDD(sat_formula, "total")
    assert tsdd.count_nodes() > 1, "TSDD is not only True or False node"
    assert tsdd.count_models() == len(models), "TSDD should have the same models found during All-SMT computation"


def test_init_with_known_lemmas(sat_formula):
    """tests SDD generation"""
    solver = MathSATExtendedPartialEnumerator()
    solver.check_all_sat(sat_formula, None, store_models=True)
    lemmas = solver.get_theory_lemmas()
    models = solver.get_models()
    tsdd = TheorySDD(sat_formula, "total", tlemmas=lemmas)
    assert tsdd.count_nodes() > 1, "TSDD is not only True or False node"
    assert tsdd.count_models() == len(models), "TSDD should have the same models found during All-SMT computation"


def test_init_updated_computation_logger(sat_formula):
    """tests SDD generation"""
    solver = MathSATExtendedPartialEnumerator()
    solver.check_all_sat(sat_formula, None, store_models=True)
    models = solver.get_models()
    logger = {"hi": "hello"}
    copy_logger = deepcopy(logger)
    tsdd = TheorySDD(sat_formula, "total", computation_logger=logger)
    assert tsdd.count_nodes() > 1, "TSDD is not only True or False node"
    assert tsdd.count_models() == len(models), "TSDD should have the same models found during All-SMT computation"
    assert logger != copy_logger, "Computation logger should be updated"
    assert logger["hi"] == copy_logger["hi"], "Old field of Logger should not be touched"


def test_init_unsat_formula(unsat_formula):
    """tests SDD generation"""
    solver = MathSATExtendedPartialEnumerator()
    solver.check_all_sat(unsat_formula, None)
    tsdd = TheorySDD(unsat_formula, "total")
    assert tsdd.count_nodes() == 1, "TSDD is only False node"
    assert tsdd.count_models() == 0, "TSDD should have no models"


def test_init_tautology(prop_valid_formula):
    """tests SDD generation"""
    solver = MathSATExtendedPartialEnumerator()
    solver.check_all_sat(prop_valid_formula, None)
    tsdd = TheorySDD(prop_valid_formula, "total")
    assert tsdd.count_nodes() == 1, "TSDD should be only True node"
    assert tsdd.count_models() == 2, "TSDD should have 2 models (atom True and atom false)"


def test_one_variable():
    """tests SDD generation"""
    phi = LT(Symbol("test_sdd_a", REAL), Symbol("test_sdd_b", REAL))
    tsdd = TheorySDD(phi, "total")
    assert tsdd.count_nodes() <= 1, "TSDD is only True node"
    assert tsdd.count_models() == 1, "TSDD should have 1 model (atom True)"


def test_lemma_loading(rangen_formula):
    """tests loading data with a solver"""
    solver = MathSATExtendedPartialEnumerator()
    tbdd = TheorySDD(rangen_formula, solver=solver, load_lemmas="./tests/items/rng_lemmas.smt")
    solver.reset()
    other_tbdd = TheorySDD(rangen_formula, solver=solver)
    assert tbdd.count_models() == other_tbdd.count_models(), "Same modles should come from different loading"
