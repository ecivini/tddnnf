import pysmt.environment
import pytest
from pysmt.shortcuts import REAL, Symbol
from pysmt.typing import ArrayType, BOOL, INT

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
def solver(request) -> SMTEnumerator:
    _, solver_cls, params = request.param
    return solver_cls(**params)


@pytest.fixture
def solver_info(solver) -> tuple[SMTEnumerator, bool]:
    return solver, getattr(solver, "_project_on_theory_atoms", False)


# ---- Real variables ----
@pytest.fixture
def w():
    return Symbol("w", REAL)


@pytest.fixture
def x():
    return Symbol("x", REAL)


@pytest.fixture
def y():
    return Symbol("y", REAL)


@pytest.fixture
def z():
    return Symbol("z", REAL)


# ---- Integer variables ----


@pytest.fixture
def i():
    return Symbol("i", INT)


@pytest.fixture
def j():
    return Symbol("j", INT)


@pytest.fixture
def k():
    return Symbol("k", INT)


# ---- Boolean variables ----


@pytest.fixture
def a():
    return Symbol("a", BOOL)


@pytest.fixture
def b():
    return Symbol("b", BOOL)


# ---- BV variables ----
@pytest.fixture
def bv1():
    return Symbol("bv1", pysmt.typing.BV8)


@pytest.fixture
def bv2():
    return Symbol("bv2", pysmt.typing.BV8)


# ---- Array variables ----


@pytest.fixture
def array1():
    return Symbol("arr1", ArrayType(INT, INT))


@pytest.fixture
def array2():
    return Symbol("arr2", ArrayType(INT, INT))


@pytest.fixture
def sat_formula(x, y, z):
    return (x < y) | (y < z) | (z < x) | x.Equals(5)


@pytest.fixture
def unsat_formula(x, y, z):
    return (x < y) & (y < z) & (z < x)


@pytest.fixture
def prop_unsat_formula(x, y):
    return (x < y) & ~(x < y)


@pytest.fixture
def valid_formula(x):
    return (x < 1) | ~(x < 0)


@pytest.fixture
def prop_valid_formula(x, y):
    return (x < y) | ~(x < y)


@pytest.fixture
def rangen_formula():
    """Rangen formula fixture"""
    return read_phi("./tests/items/rng.smt")


@pytest.fixture(params=["sat_formula", "unsat_formula", "valid_formula", "rangen_formula"])
def any_formula(request):
    """Return all formula fixtures one by one via parametrization"""
    return request.getfixturevalue(request.param)
