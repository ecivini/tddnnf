import pysmt.environment
import pytest
from pysmt.shortcuts import And, Equals, LT, Not, Or, REAL, Real, Symbol

from theorydd.formula import read_phi
from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.solvers.solver import SMTEnumerator


def pytest_runtest_setup():
    env: pysmt.environment.Environment = pysmt.environment.reset_env()
    env.enable_infix_notation = True


SOLVERS = [
    ("total", MathSATTotalEnumerator, {"project_on_theory_atoms": False}),
    ("total-project", MathSATTotalEnumerator, {"project_on_theory_atoms": True}),
    ("partial-1", MathSATExtendedPartialEnumerator, {"project_on_theory_atoms": False, "parallel_procs": 1}),
    ("partial-project-1", MathSATExtendedPartialEnumerator, {"project_on_theory_atoms": True, "parallel_procs": 1}),
    ("partial-8", MathSATExtendedPartialEnumerator, {"project_on_theory_atoms": False, "parallel_procs": 8}),
    ("partial-project-8", MathSATExtendedPartialEnumerator, {"project_on_theory_atoms": True, "parallel_procs": 8}),
]


@pytest.fixture(params=SOLVERS, ids=lambda s: s[0])
def solver_info(request) -> tuple[SMTEnumerator, bool]:
    _, solver_cls, params = request.param
    return solver_cls(**params), params.get("project_on_theory_atoms", False)


@pytest.fixture
def sat_formula():
    """SAT formula fixture"""
    return Or(
        LT(Symbol("X", REAL), Symbol("Y", REAL)),
        LT(Symbol("Y", REAL), Symbol("Zr", REAL)),
        LT(Symbol("Zr", REAL), Symbol("X", REAL)),
        Equals(Symbol("X", REAL), Real(5)),
    )


@pytest.fixture
def unsat_formula():
    """UNSAT formula fixture (cyclic inequalities)"""
    return And(
        LT(Symbol("X", REAL), Symbol("Y", REAL)),
        LT(Symbol("Y", REAL), Symbol("Zr", REAL)),
        LT(Symbol("Zr", REAL), Symbol("X", REAL)),
    )

@pytest.fixture
def prop_unsat_formula():
    """Propositional UNSAT formula fixture"""
    return And(
        LT(Symbol("X", REAL), Symbol("Y", REAL)),
        Not(LT(Symbol("X", REAL), Symbol("Y", REAL))),
    )


@pytest.fixture
def valid_formula():
    """Valid/tautology formula fixture"""
    return Or(
        LT(Symbol("X", REAL), Real(1)),
        Not(LT(Symbol("X", REAL), Real(0))),
    )

@pytest.fixture
def prop_valid_formula():
    """Propositional valid/tautology formula fixture"""
    return Or(
        LT(Symbol("X", REAL), Symbol("Y", REAL)),
        Not(LT(Symbol("X", REAL), Symbol("Y", REAL))),
    )


@pytest.fixture
def rangen_formula():
    """Rangen formula fixture"""
    return read_phi("./tests/items/rng.smt")


@pytest.fixture(params=["sat_formula", "unsat_formula", "valid_formula", "rangen_formula"])
def any_formula(request):
    """Return all formula fixtures one by one via parametrization"""
    return request.getfixturevalue(request.param)
