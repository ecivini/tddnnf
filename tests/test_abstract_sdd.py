"""tests for Abstraction SDDs"""

from copy import deepcopy

from theorydd.abstractdd.abstraction_sdd import AbstractionSDD
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator


def test_init_default(sat_formula):
    """tests abstraction SDD generation"""
    solver = MathSATTotalEnumerator()
    solver.check_all_sat(sat_formula, None)
    models = solver.get_models()
    asdd = AbstractionSDD(sat_formula, "total")
    assert asdd.count_nodes() > 1, "abstr. SDD is not only True or False node"
    assert asdd.count_models() > len(
        models
    ), "abstr. SDD should have more models then the models found during All-SMT computation"


def test_init_updated_computation_logger(sat_formula):
    """tests abstraction SDD generation"""
    solver = MathSATTotalEnumerator()
    solver.check_all_sat(sat_formula, None)
    models = solver.get_models()
    logger = {"hi": "hello"}
    copy_logger = deepcopy(logger)
    asdd = AbstractionSDD(sat_formula, "total", computation_logger=logger)
    assert asdd.count_nodes() > 1, "abstr. SDD is not only True or False node"
    assert asdd.count_models() >= len(
        models
    ), "abstr. SDD should have more models then the models found during All-SMT computation"
    assert logger != copy_logger, "Computation logger should be updated"
    assert (
        logger["hi"] == copy_logger["hi"]
    ), "Old field of Logger should not be touched"


def test_init_t_unsat_formula(unsat_formula):
    """tests abstraction SDD generation"""
    solver = MathSATTotalEnumerator()
    solver.check_all_sat(unsat_formula, None)
    asdd = AbstractionSDD(unsat_formula, "total")
    assert asdd.count_nodes() > 1, "abstr. SDD is not only False node"
    assert asdd.count_models() > 0, "abstr. SDD should have models"


def test_init_prop_unsat_formula(prop_unsat_formula):
    """tests abstraction SDD generation"""
    solver = MathSATTotalEnumerator()
    solver.check_all_sat(prop_unsat_formula, None)
    asdd = AbstractionSDD(prop_unsat_formula, "total")
    assert asdd.count_nodes() == 1, "abstr. SDD is only False node"
    assert asdd.count_models() == 0, "abstr. SDD should have no models"


def test_init_tautology(prop_valid_formula):
    """tests abstraction SDD generation"""
    solver = MathSATTotalEnumerator()
    solver.check_all_sat(prop_valid_formula, None)
    asdd = AbstractionSDD(prop_valid_formula, "total")
    assert asdd.count_nodes() == 1, "TSDD is only True node"
    assert (
        asdd.count_models() == 2
    ), "TSDD should have 2 models (atom True and atom false)"
