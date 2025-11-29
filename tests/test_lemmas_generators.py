import multiprocessing
from dataclasses import dataclass
from typing import Callable, Iterable
from unittest import TestCase

import pytest
from pysmt.fnode import FNode
from pysmt.shortcuts import BV, BVSGE, And, Iff, Int, Ite, Or, Real, Solver, ToReal, read_smtlib

from theorydd.formula import get_normalized
from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.walkers.walker_bool_abstraction import BooleanAbstractionWalker
from theorydd.walkers.walker_refinement import RefinementWalker


@dataclass
class TCase:
    name: str
    formula_builder: Callable[[dict[str, FNode]], FNode]
    model_count: int
    projected_model_count: int


@pytest.fixture
def bool_vars(a, b) -> dict[str, FNode]:
    return {"A": a, "B": b}


@pytest.fixture
def real_vars(w, x, y, z) -> dict[str, FNode]:
    return {"x": x, "y": y, "z": z, "w": w}


@pytest.fixture
def int_vars(i, j, k) -> dict[str, FNode]:
    return {"i": i, "j": j, "k": k}


@pytest.fixture
def bv_vars(bv1, bv2) -> dict[str, FNode]:
    return {"bv1": bv1, "bv2": bv2}


@pytest.fixture
def array_vars(array1, array2) -> dict[str, FNode]:
    return {"arr1": array1, "arr2": array2}


@pytest.fixture
def all_vars(bool_vars, real_vars, int_vars, bv_vars, array_vars) -> dict[str, dict[str, FNode]]:
    all_vars = {}
    all_vars.update(bool_vars)
    all_vars.update(real_vars)
    all_vars.update(int_vars)
    all_vars.update(bv_vars)
    all_vars.update(array_vars)
    return all_vars


ALL_RAW_TEST_CASES = [
    TCase("Bool only", lambda s: (s["A"] | s["B"]) & (~s["A"] | ~s["B"]), 2, 2),
    TCase("Eq unsat", lambda s: s["x"].Equals(s["y"]) & s["x"].Equals(s["z"]) & ~s["y"].Equals(s["z"]), 0, 0),
    TCase("LRA unsat", lambda s: (s["x"] <= 0) & (s["x"] >= 1), 0, 0),
    TCase("LRA unsat eq", lambda s: s["x"].Equals(0) & (s["x"] + 1).Equals(0), 0, 0),
    TCase("LRA no lemmas", lambda s: (s["x"] >= 0) ^ (s["x"] <= 1), 2, 2),
    TCase("LRA disj lemma", lambda s: (s["x"] <= 0) | (s["x"] >= 1), 2, 2),
    TCase("LRA two vars", lambda s: (s["x"] + s["y"] >= 1) | (s["x"] + s["y"] <= 0), 2, 2),
    TCase("LRA+Bool simple", lambda s: ((s["x"] + s["y"] >= 1) & s["A"]) | ((s["x"] + s["y"] <= 0) & ~s["A"]), 2, 2),
    TCase("LRA+Bool unsat", lambda s: (s["A"] | (s["x"] > 0)) & (~s["A"] | (s["x"] < 0)) & s["x"].Equals(0), 0, 0),
    TCase("LRA+Bool proj", lambda s: ((~s["A"] | (s["x"] + s["y"] >= 1)) & (~s["B"] | (s["x"] <= 0))), 9, 4),
    TCase(
        "LRA eq lemma", lambda s: ~s["x"].Equals(s["y"]) | ((s["x"] >= Real(1)) & (s["x"] + s["y"] <= Real(0))), 4, 4
    ),
    TCase("LIRA simple", lambda s: (s["x"] >= 0.5) & (s["x"] <= 1.5) & ToReal(s["i"]).Equals(s["x"]), 1, 1),
    TCase("LIRA disj", lambda s: (s["x"] + ToReal(s["i"]) >= 2.5) | (ToReal(s["i"]) <= 0.5), 3, 3),
    TCase(
        "LIRA complex",
        lambda s: ((s["x"] + ToReal(s["i"]) >= 3.5) & (s["y"] <= 1.0))
        | (s["A"] & (s["x"] + 2 * ToReal(s["i"]) <= 0.0)),
        7,
        5,
    ),
    TCase("LIRA unsat", lambda s: (ToReal(s["i"]) > 1) & (ToReal(s["i"]) < 2), 0, 0),
    TCase(
        "LIRA unsat 2 vars", lambda s: (s["x"] + s["y"] < 5) & (s["x"] + s["y"] > 10) & s["y"].Equals(s["x"] + 1), 0, 0
    ),
    TCase(
        "LIRA+Bool",
        lambda s: (~s["A"] & (2 * s["i"]).Equals(3 * s["j"])) | ((s["i"] < 10) & (s["i"] + s["j"] > 10)),
        6,
        4,
    ),
    TCase(
        "BV lemma",
        lambda s: s["bv2"].Equals(BV(1, 8)) & ~(s["bv1"] + s["bv2"]).Equals(BV(0, 8)) | s["bv1"].Equals(BV(255, 8)),
        3,
        3,
    ),
    TCase("BV disj", lambda s: (s["bv1"] + s["bv2"] < BV(10, 8)) | (s["bv1"] + s["bv2"] > BV(20, 8)), 2, 2),
    TCase(
        "BV unsat",
        lambda s: And((s["bv1"] - BV(1, 8)).Equals(BV(127, 8)) & ~s["bv1"].Equals(BV(128, 8))),
        0,
        0,
    ),
    TCase(
        "BV disj one side",
        lambda s: And(
            (s["bv1"] ^ BV(1, 8)).Equals(BV(0, 8)),
            Or((s["bv1"] & BV(2, 8)).Equals(BV(2, 8)), BVSGE(s["bv1"], BV(0, 8))),
        ),
        1,
        1,
    ),
    TCase(
        "Arrays select-store",
        lambda s: ~s["arr1"].Select(s["i"]).Equals(s["j"]) | ~s["arr2"].Equals(s["arr1"].Store(s["i"], s["j"])),
        3,
        3,
    ),
    TCase("Arrays unsat", lambda s: s["arr1"].Store(s["i"], Int(1)).Select(s["i"]).Equals(0), 0, 0),
    TCase(
        "Arrays+LIA simple",
        lambda s: s["arr1"].Select(s["i"]).Equals(s["j"])
        | (s["j"].Equals(s["j"]) | s["arr2"].Store(s["i"], s["j"] + 1).Select(s["i"]).Equals(s["arr1"].Select(s["i"]))),
        3,
        3,
    ),
    TCase(
        "Arrays+LRA unsat",
        lambda s: s["arr1"].Select(s["i"]).Equals(s["j"])
        & s["arr2"].Equals(s["arr1"].Store(s["i"], s["j"] + 1))
        & s["arr2"].Select(s["i"]).Equals(s["arr1"].Select(s["i"])),
        0,
        0,
    ),
    TCase("Test lemmas", lambda _: read_smtlib("./tests/items/test_lemmas.smt2"), 1, 1),
    TCase("Planning", lambda _: read_smtlib("./tests/items/6_2.smt2"), 360, 360),
    TCase("Randgen", lambda _: read_smtlib("./tests/items/rng.smt"), 12, 2),
]


@pytest.fixture(params=ALL_RAW_TEST_CASES, ids=lambda tc: tc.name)
def example(request, all_vars) -> tuple[FNode, int, int]:
    """
    Note: formulas must be built in the current pysmt environment.
    This is ensured by building them inside this fixture.
    """
    test_case = request.param
    formula = test_case.formula_builder(all_vars)
    return formula, test_case.model_count, test_case.projected_model_count


def assert_models_are_tsat(phi: FNode, models: list[Iterable[FNode]]) -> None:
    with Solver() as check_solver:
        check_solver.add_assertion(phi)
        for model in models:
            check_solver.push()
            check_solver.add_assertions(model)
            sat = check_solver.solve()
            assert sat, "T-UNSAT model found: {}".format(model)
            check_solver.pop()


def assert_lemmas_are_tvalid(lemmas: list[FNode]):
    with Solver("msat") as check_solver:
        for lemma in lemmas:
            check_solver.push()
            assert check_solver.is_valid(lemma), "Lemma {} is not valid, counterexample {}".format(
                lemma.serialize(), check_solver.get_model()
            )
            check_solver.pop()


def test_lemmas_correctness(example, solver_info):
    phi, mc, pmc = example
    solver, is_projected = solver_info

    normalize_solver = Solver("msat")
    phi = get_normalized(phi, normalize_solver.converter)
    expected_models_count: int = mc
    expected_lemmas_models_count = pmc if is_projected else mc

    # ---- Generate lemmas ----
    phi_atoms = list(phi.get_atoms())
    phi_sat = solver.check_all_sat(phi, atoms=phi_atoms, store_models=True)
    assert solver.get_models_count() == expected_lemmas_models_count, "Model count should match expected: {}".format(
        solver.get_models()
    )

    assert_models_are_tsat(phi, solver.get_models())

    # ---- Build Boolean abstraction of phi & lemmas ----
    lemmas = [get_normalized(lemma, normalize_solver.converter) for lemma in solver.get_theory_lemmas()]

    phi_and_lemmas = And(phi, And(lemmas))
    phi_and_lemmas_atoms = phi_and_lemmas.get_atoms()
    assert set(phi_atoms) <= phi_and_lemmas_atoms
    bool_walker = BooleanAbstractionWalker(atoms=phi_and_lemmas_atoms)
    phi_and_lemmas_abstr = bool_walker.walk(phi_and_lemmas)
    phi_abstr = bool_walker.walk(phi)
    assert len(phi_abstr.get_atoms()) == len(phi_atoms), "Abstraction should preserve atoms of phi"

    assert_lemmas_are_tvalid(lemmas)

    assert_phi_equiv_phi_and_lemmas(phi, phi_and_lemmas)

    solver_abstr = MathSATTotalEnumerator(project_on_theory_atoms=False)
    abstr_sat = solver_abstr.check_all_sat(
        phi_and_lemmas_abstr,
        atoms=list(phi_abstr.get_atoms()),
        store_models=True,
    )
    assert abstr_sat == phi_sat, "Satisfiability of abstracted formula with lemmas should match original"
    assert solver_abstr.get_models_count() == expected_models_count, "Model count should match expected"

    # Check phi_and_lemmas is t-reduced
    refinement_walker = RefinementWalker(abstraction=bool_walker.abstraction)
    refined_models = [[refinement_walker.walk(lit) for lit in model] for model in solver_abstr.get_models()]
    assert_models_are_tsat(phi, refined_models)


def assert_phi_equiv_phi_and_lemmas(phi: FNode, phi_and_lemmas):
    with Solver("msat") as check_solver:
        assert check_solver.is_valid(Iff(phi, phi_and_lemmas)), "Phi and Phi & lemmas are not theory-equivalent"


def test_term_ite_exception(solver, x, y, a):
    phi = Or(And(x >= Ite(a, Real(0), Real(1)), y >= 0), a)

    with pytest.raises(AssertionError, match="Term-ITE are not supported yet"):
        solver.check_supports(phi)


@pytest.mark.parametrize("parallel_procs", [0, -1, multiprocessing.cpu_count() + 1])
def test_invalid_parallel_procs(parallel_procs, sat_formula):
    """Test that invalid parallel_procs (0) raises error"""
    with pytest.raises(ValueError, match="parallel_procs must be between 1"):
        _ = MathSATExtendedPartialEnumerator(parallel_procs=parallel_procs)
