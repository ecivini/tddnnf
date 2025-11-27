import multiprocessing
from typing import NamedTuple

import pytest
from pysmt.fnode import FNode
from pysmt.formula import FormulaContextualizer
from pysmt.shortcuts import And, Iff, Ite, Not, Or, Real, Solver, Symbol, Xor, read_smtlib
from pysmt.typing import BOOL, REAL

from theorydd.formula import get_normalized
from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.walkers.walker_bool_abstraction import BooleanAbstractionWalker
from theorydd.walkers.walker_refinement import RefinementWalker

w, x, y, z = (Symbol(name, REAL) for name in "wxyz")

xp3yp2zp1LExp3yp2z = x + 3 * y + 2 * z + 1 <= x + 3 * y + 2 * z
xp3yp2zp1LE05 = x + 3 * y + 2 * z + 1 <= 0.5
xp3yp2zLE05 = x + 3 * y + 2 * z <= 0.5
xp3yLE05 = x + 3 * y <= 0.5
yLE05 = y <= 0.5
xLE05 = x <= 0.5
a, b = (Symbol(name, BOOL) for name in "ab")

Example = NamedTuple("Example", [("formula", FNode), ("model_count", int), ("projected_model_count", int)])


# formulas to test: (formula, is_sat, tlemmas_expected)
EXAMPLES: list[Example] = [
    Example(xLE05, 1, 1),
    Example(And(xLE05, yLE05), 1, 1),
    Example(Or(xLE05, yLE05), 3, 3),
    Example(And(xLE05, yLE05, xp3yLE05, xp3yp2zLE05), 1, 1),
    Example(Or(xLE05, yLE05, xp3yLE05, xp3yp2zLE05), 13, 13),
    Example(Not(xLE05), 1, 1),
    Example(Not(Not(xLE05)), 1, 1),
    Example(Not(Not(And(xLE05, yLE05))), 1, 1),
    Example(Not(Not(Or(xLE05, yLE05))), 3, 3),
    Example(And(x <= y, y <= x), 1, 1),
    Example(And(x < y, y < x), 0, 0),
    Example(And(x <= y, z <= w), 1, 1),
    Example(Or(x < y, y < z, z < x), 6, 6),
    Example(And(Or(xLE05, yLE05), Or(xp3yLE05, xp3yp2zLE05)), 9, 9),
    Example(Or(And(xLE05, yLE05), And(xp3yLE05, xp3yp2zLE05)), 6, 6),
    Example(Not(Or(xLE05, Not(And(yLE05, Not(Or(xp3yLE05, xp3yp2zLE05)))))), 1, 1),
    Example(
        Or(
            Or(Or(And(xLE05, yLE05), And(xp3yLE05, xp3yp2zLE05)), And(xp3yp2zp1LE05, a)),
            Not(And(b, xp3yp2zp1LExp3yp2z)),
        ),
        84,
        21,
    ),
    Example(Or(And(xLE05, yLE05), And(xp3yLE05, Or(Not(And(xLE05, yLE05)), xp3yp2zLE05))), 8, 8),
    Example(Iff(And(xp3yLE05, xp3yp2zLE05), Or(xp3yp2zLE05, And(yLE05, xLE05))), 8, 8),
    Example(
        Or(And(xp3yLE05, xp3yp2zLE05), Not(Iff(And(xp3yLE05, xp3yp2zLE05), Or(xp3yp2zLE05, And(yLE05, xLE05))))),
        9,
        9,
    ),
    Example(
        Xor(
            And(Not(And(Not(xLE05), xp3yLE05)), Or(Not(yLE05), Not(xp3yp2zLE05))),
            And(Not(And(xp3yp2zLE05, Not(a))), Not(And(Not(yLE05), a))),
        ),
        15,
        11,
    ),
    Example(read_smtlib("tests/items/test_lemmas.smt2"), 1, 1),
    Example(read_smtlib("tests/items/6_2.smt2"), 360, 360),
]


@pytest.fixture(params=EXAMPLES, ids=lambda e: str(e.formula))
def example(request) -> Example:
    ex = request.param
    ctxzer = FormulaContextualizer()
    formula = ctxzer.walk(ex.formula)
    return Example(formula, ex.model_count, ex.projected_model_count)


def test_lemmas_correctness(example, solver_info):
    solver, is_projected = solver_info
    expected_models_count: int = example.model_count
    expected_lemmas_models_count = example.projected_model_count if is_projected else example.model_count

    _solver = Solver("msat")
    converter = _solver.converter
    phi = example.formula
    phi = get_normalized(phi, converter)

    # ---- Generate lemmas ----
    phi_atoms = list(phi.get_atoms())
    phi_sat = solver.check_all_sat(phi, atoms=phi_atoms, store_models=True)
    assert solver.get_models_count() == expected_lemmas_models_count, "Model count should match expected: {}".format(
        solver.get_models()
    )

    lemmas = solver.get_theory_lemmas()

    # # ---- Check that every truth assignment returned by all-sat is theory-sat ----
    # with Solver() as check_solver:
    #     check_solver.add_assertion(phi)
    #     for model in solver.get_models():
    #         check_solver.push()
    #         check_solver.add_assertions(model)
    #         sat = check_solver.solve()
    #         assert sat, "T-UNSAT model found: {}".format(model)
    #         check_solver.pop()

    # ---- Build Boolean abstraction of phi & lemmas ----
    phi_and_lemmas = And(phi, get_normalized(And(lemmas), converter))
    phi_and_lemmas_atoms = phi_and_lemmas.get_atoms()
    assert set(phi_atoms) <= phi_and_lemmas_atoms
    bool_walker = BooleanAbstractionWalker(atoms=phi_and_lemmas_atoms)
    phi_and_lemmas_abstr = bool_walker.walk(phi_and_lemmas)
    phi_abstr = bool_walker.walk(phi)
    assert len(phi_abstr.get_atoms()) == len(phi_atoms), "Abstraction should preserve atoms of phi"

    # ---- Check that phi and phi & lemmas are theory-equivalent ----
    with Solver() as check_solver:
        check_solver.add_assertion(Xor(phi, phi_and_lemmas))
        sat = check_solver.solve()
        assert not sat, "Phi and Phi & lemmas should be theory-equivalent"

    # ---- Check that every truth assignment of phi & lemmas is theory-sat ----
    solver_abstr = MathSATTotalEnumerator(project_on_theory_atoms=False)
    abstr_sat = solver_abstr.check_all_sat(
        phi_and_lemmas_abstr,
        atoms=list(phi_abstr.get_atoms()),
        store_models=True,
    )
    assert abstr_sat == phi_sat, "Satisfiability of abstracted formula with lemmas should match original"
    assert (
        solver_abstr.get_models_count() == expected_models_count
    ), "Model count of abstracted formula with lemmas should match expected"

    with Solver() as check_solver:
        t_unsat_models = []
        for abstr_model in solver_abstr.get_models():
            walker = RefinementWalker(abstraction=bool_walker.abstraction)
            refined = walker.walk(And(abstr_model))

            check_solver.push()
            check_solver.add_assertion(refined)
            sat = check_solver.solve()
            if not sat:
                t_unsat_models.append(refined)
            check_solver.pop()

    assert len(t_unsat_models) == 0, "There should be no theory-unsat models, found {}".format(len(t_unsat_models))


def test_term_ite_exception(solver_info):
    solver, _ = solver_info
    phi = Or(And(x >= Ite(a, Real(0), Real(1)), y >= 0), a)

    with pytest.raises(AssertionError, match="Term-ITE are not supported yet"):
        solver.check_supports(phi)


# ==================== Parallel Processing Tests ====================

@pytest.mark.parametrize("parallel_procs", [0, -1, multiprocessing.cpu_count() + 1])
def test_invalid_parallel_procs(parallel_procs, sat_formula):
    """Test that invalid parallel_procs (0) raises error"""
    with pytest.raises(ValueError, match="parallel_procs must be between 1"):
        _ = MathSATExtendedPartialEnumerator(parallel_procs=parallel_procs)
