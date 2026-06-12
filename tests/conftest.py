import pysmt.environment
import pytest
from pysmt.shortcuts import REAL, Symbol
from pysmt.typing import ArrayType, BOOL, INT
import pysmt.typing

from theorydd.formula import read_phi
from enumerators.solvers import MathSATDivideAndConquerEnumerator
from enumerators.solvers.mathsat_total import MathSATTotalEnumerator
from enumerators.solvers.with_partitioning import WithPartitioningWrapper
from enumerators.solvers.with_projection import WithProjectionWrapper
from enumerators.solvers.solver import SMTEnumerator


def pytest_runtest_setup():
    env: pysmt.environment.Environment = pysmt.environment.reset_env()
    env.enable_infix_notation = True


def _make_solver(base_cls, proj: bool, **kwargs):
    s = base_cls(**kwargs)
    return WithProjectionWrapper(s) if proj else s


SOLVERS = [
    ("total", lambda: _make_solver(MathSATTotalEnumerator, False)),
    ("total-project", lambda: _make_solver(MathSATTotalEnumerator, True)),
    ("partial-1", lambda: _make_solver(MathSATDivideAndConquerEnumerator, False, parallel_procs=1)),
    ("partial-project-1", lambda: _make_solver(MathSATDivideAndConquerEnumerator, True, parallel_procs=1)),
    ("partial-8", lambda: _make_solver(MathSATDivideAndConquerEnumerator, False, parallel_procs=8)),
    ("partial-project-8", lambda: _make_solver(MathSATDivideAndConquerEnumerator, True, parallel_procs=8)),
]


@pytest.fixture(params=SOLVERS, ids=lambda s: s[0])
def solver(request) -> SMTEnumerator:
    _, solver_factory = request.param
    return solver_factory()


@pytest.fixture(params=["raw", "partitioned"], ids=["mode:raw", "mode:part"])
def wsolver(solver, request):
    if request.param == "raw":
        return solver
    return WithPartitioningWrapper(base_solver=solver)


def _is_projected(s):
    while hasattr(s, "_base_solver"):
        if isinstance(s, WithProjectionWrapper):
            return True
        s = s._base_solver
    return False


@pytest.fixture
def solver_info(wsolver) -> tuple[SMTEnumerator, bool, bool]:
    return wsolver, _is_projected(wsolver), isinstance(wsolver, WithPartitioningWrapper)


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


@pytest.fixture()
def default_phi(x, y, b):
    """Returns a default SMT formula
    [(x>0) ∧ (x<1)] ∧ [(y<1) ∨ ((x>y) ∧ (y>1/2))] ∧ b1
    """
    return ((0 < x) & (x < 1)) & ((y < 1) | (y < x) & (0.5 < y)) & b


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
