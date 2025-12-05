"""tests for Abstraction BDDs"""

from copy import deepcopy
from theorydd.abstractdd.abstraction_bdd import AbstractionBDD
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from pysmt.shortcuts import Or, LT, REAL, Symbol, And, Not


def test_init_default(sat_formula):
    """tests abstraction BDD generation"""
    partial = MathSATTotalEnumerator()
    partial.check_all_sat(sat_formula, None)
    models = partial.get_models()
    abdd = AbstractionBDD(sat_formula, "total")
    assert abdd.count_nodes() > 1, "abstr. BDD is not only True or False node"
    assert abdd.count_models() > len(
        models
    ), "abstr. BDD should have more models then the models found during All-SMT computation"


def test_init_updated_computation_logger(sat_formula):
    """tests abstraction BDD generation"""
    partial = MathSATTotalEnumerator()
    partial.check_all_sat(sat_formula, None)
    models = partial.get_models()
    logger = {"hi": "hello"}
    copy_logger = deepcopy(logger)
    abdd = AbstractionBDD(sat_formula, "total", computation_logger=logger)
    assert abdd.count_nodes() > 1, "abstr. BDD is not only True or False node"
    assert abdd.count_models() >= len(
        models
    ), "abstr. BDD should have more models then the models found during All-SMT computation"
    assert logger != copy_logger, "Computation logger should be updated"
    assert (
        logger["hi"] == copy_logger["hi"]
    ), "Old field of Logger should not be touched"


def test_init_t_unsat_formula(unsat_formula):
    """tests abstraction BDD generation"""
    partial = MathSATTotalEnumerator()
    partial.check_all_sat(unsat_formula, None)
    abdd = AbstractionBDD(unsat_formula, "total")
    assert abdd.count_nodes() > 1, "abstr. BDD is not only False node"
    assert abdd.count_models() > 0, "abstr. BDD should have models"


def test_init_prop_unsat_formula(prop_unsat_formula):
    """tests abstraction BDD generation"""
    partial = MathSATTotalEnumerator()
    partial.check_all_sat(prop_unsat_formula, None)
    abdd = AbstractionBDD(prop_unsat_formula, "total")
    assert abdd.count_nodes() == 1, "abstr. BDD is only False node"
    assert abdd.count_models() == 0, "abstr. BDD should have no models"


def test_init_tautology(prop_valid_formula):
    """tests abstraction BDD generation"""
    partial = MathSATTotalEnumerator()
    partial.check_all_sat(prop_valid_formula, None)
    abdd = AbstractionBDD(prop_valid_formula, "total")
    assert abdd.count_nodes() == 1, "TBDD is only True node"
    assert (
        abdd.count_models() == 2
    ), "TBDD should have 2 models (atom True and atom false)"
