"""tests for module formula"""

from pysmt.fnode import FNode
from pysmt.shortcuts import And, BOOL, LE, Not, Or, Plus, REAL, Real, Symbol, Times

import theorydd.formula as formula
from enumerators.solvers.mathsat_total import MathSATTotalEnumerator


def test_get_phi_and_lemmas():
    """tests for forula.get_phi_and_lemmas()"""
    phi = Or(Symbol("A", BOOL), Symbol("B", BOOL))
    tlemmas = [Symbol("C", BOOL), Or(Symbol("A", BOOL), Symbol("C", BOOL))]
    phi_and_lemmas = formula.get_phi_and_lemmas(phi, tlemmas)
    assert isinstance(phi_and_lemmas, FNode), "phi and lemmas should be an FNode"
    assert phi_and_lemmas == And(phi, tlemmas[0], tlemmas[1]), "phi and lemmas is the big and of phi and all the lemmas"


def test_atom_diff():
    """tests for formula.atoms_difference()"""
    phi_atoms = [Symbol("A", BOOL), Symbol("B", BOOL)]
    tlemmas_atoms = [Symbol("A", BOOL), Symbol("B", BOOL), Symbol("C", BOOL)]
    diff = formula.atoms_difference(phi_atoms, tlemmas_atoms)
    assert diff == [Symbol("C", BOOL)], (
        "atom difference should show all items in the second list which are not in the first"
    )
    tlemmas_atoms = [
        Symbol("A", BOOL),
        Symbol("B", BOOL),
        Symbol("C", BOOL),
        Symbol("C", BOOL),
    ]
    diff = formula.atoms_difference(phi_atoms, tlemmas_atoms)
    assert diff == [Symbol("C", BOOL)], "duplicate items shall not be counted twice"
    tlemmas_atoms = [Symbol("A", BOOL), Symbol("C", BOOL), Symbol("C", BOOL)]
    diff = formula.atoms_difference(phi_atoms, tlemmas_atoms)
    assert diff == [Symbol("C", BOOL)], "items missing in the second set should not be considered"


def test_get_atoms():
    """tyests for get atoms"""
    phi = And(
        Symbol("F", BOOL),
        LE(Symbol("X", REAL), Symbol("Y", REAL)),
        LE(Symbol("Y", REAL), Symbol("X", REAL)),
        Symbol("Z", BOOL),
    )
    assert len(formula.get_atoms(phi)) == 4, "the normalized formula has 4 atoms"
    phi = Or(
        And(
            Symbol("F", BOOL),
            LE(Symbol("X", REAL), Symbol("Y", REAL)),
            LE(Symbol("Y", REAL), Symbol("X", REAL)),
            Symbol("Z", BOOL),
        ),
        Not(LE(Symbol("X", REAL), Symbol("Y", REAL))),
        Not(LE(Symbol("Y", REAL), Symbol("X", REAL))),
    )
    assert len(formula.get_atoms(phi)) == 4, "the normalized formula has 4 atoms, even if some appear more than once"


def test_normalization():
    """tests for get_normalized"""
    solver = MathSATTotalEnumerator()
    converter = solver.get_converter()
    # all atoms are different
    phi = And(
        Symbol("F", BOOL),
        LE(Symbol("X", REAL), Symbol("Y", REAL)),
        LE(Symbol("Y", REAL), Symbol("X", REAL)),
        Symbol("Z", BOOL),
    )
    normal = formula.get_normalized(phi, converter)
    assert len(formula.get_atoms(normal)) == 4, "the normalized formula has 4 atoms"
    assert len(formula.get_atoms(normal)) == len(formula.get_atoms(phi)), (
        "different atoms should be normalized into different atoms"
    )
    # 1st and 3rd LE are actually the same
    phi = And(
        Symbol("F", BOOL),
        LE(Symbol("X", REAL), Symbol("Y", REAL)),
        LE(Symbol("Y", REAL), Symbol("X", REAL)),
        LE(Plus(Symbol("X", REAL), Times(Real(-1), Symbol("Y", REAL))), Real(0)),
        Symbol("Z", BOOL),
    )
    normal = formula.get_normalized(phi, converter)
    assert len(formula.get_atoms(normal)) == 4, "the normalized formula has 4 atoms"
    assert len(formula.get_atoms(normal)) < len(formula.get_atoms(phi)), (
        "equivalent atoms should be normalized into the same atom"
    )
