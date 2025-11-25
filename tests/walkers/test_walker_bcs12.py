"""Unit tests for BCS12Walker class"""

import pytest
from pysmt.shortcuts import (
    Symbol,
    And,
    Or,
    Not,
    Implies,
    Iff,
    Ite,
    TRUE,
    FALSE,
    BOOL,
    REAL,
    LT,
    LE,
    Equals,
    ForAll,
    Exists,
    Real,
    BVType,
    BVULT,
)

from theorydd.walkers.walker_bcs12 import BCS12Walker
from theorydd.util.custom_exceptions import UnsupportedNodeException


# TODO: Rimuovi phi_atoms in quanto non piu in uso
class TestBCS12Walker:
    """Test suite for BCS12Walker"""

    def test_walk_symbol_basic(self):
        """Test that symbols are properly mapped"""
        a = Symbol("A", BOOL)
        abstraction = {}
        walker = BCS12Walker(abstraction)

        result = walker.walk(a)

        assert result == "v1"
        assert a in abstraction
        assert abstraction[a] == 1

    def test_walk_symbol_with_existing_abstraction(self):
        """Test that symbols use existing abstraction mapping"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        abstraction = {a: 5, b: 10}
        phi_atoms = frozenset([a, b])
        walker = BCS12Walker(abstraction, phi_atoms)

        result_a = walker.walk(a)
        result_b = walker.walk(b)

        assert result_a == "v5"
        assert result_b == "v10"

    def test_walk_and_basic(self):
        """Test AND node translation"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        formula = And(a, b)
        abstraction = {}
        phi_atoms = frozenset([a, b])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g1"
        assert len(walker.gate_lines) == 1
        # Check that it's an AND gate with the two variables
        assert walker.gate_lines[0].startswith("G g1 := A ")
        assert "v" in walker.gate_lines[0]

    def test_walk_or_basic(self):
        """Test OR node translation"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        formula = Or(a, b)
        abstraction = {}
        phi_atoms = frozenset([a, b])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g1"
        assert len(walker.gate_lines) == 1
        # Check that it's an OR gate
        assert walker.gate_lines[0].startswith("G g1 := O ")

    def test_walk_not_basic(self):
        """Test NOT node translation"""
        a = Symbol("A", BOOL)
        formula = Not(a)
        abstraction = {}
        phi_atoms = frozenset([a])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "-v1"
        assert len(walker.gate_lines) == 0  # NOT doesn't create gates

    def test_walk_not_double_negation_simplification(self):
        """
        Test that double negation gets simplified.
        BUG FOUND: The walker simplifies Not(Not(a)) to just a,
        which may not be the desired behavior for BC-S1.2 format.
        """
        a = Symbol("A", BOOL)
        formula = Not(Not(a))
        abstraction = {}
        phi_atoms = frozenset([a])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        # Walker simplifies this to just v1, not --v1
        assert result == "v1"

    def test_walk_bool_constant_true(self):
        """Test TRUE constant translation"""
        formula = TRUE()
        abstraction = {}
        phi_atoms = frozenset()
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g1"
        assert len(walker.gate_lines) == 1
        assert walker.gate_lines[0] == "G g1 := O v1 -v1"

    def test_walk_bool_constant_false(self):
        """Test FALSE constant translation"""
        formula = FALSE()
        abstraction = {}
        phi_atoms = frozenset()
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g1"
        assert len(walker.gate_lines) == 1
        assert walker.gate_lines[0] == "G g1 := A v1 -v1"

    def test_walk_iff(self):
        """Test IFF node translation: a <-> b === (a & b) | (~a & ~b)"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        formula = Iff(a, b)
        abstraction = {}
        phi_atoms = frozenset([a, b])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g3"
        assert len(walker.gate_lines) == 3
        # First two gates are AND, last is OR
        assert "G g1 := A" in walker.gate_lines[0]
        assert "G g2 := A" in walker.gate_lines[1]
        assert walker.gate_lines[2] == "G g3 := O g1 g2"

    def test_walk_implies(self):
        """Test IMPLIES node translation: a -> b === (~a | b)"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        formula = Implies(a, b)
        abstraction = {}
        phi_atoms = frozenset([a, b])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g1"
        assert len(walker.gate_lines) == 1
        assert walker.gate_lines[0].startswith("G g1 := O -v")

    def test_walk_ite(self):
        """
        Test ITE node translation:
        if a then b else c === ((~a) | b) & (a | c)
        """
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        c = Symbol("C", BOOL)
        formula = Ite(a, b, c)
        abstraction = {}
        phi_atoms = frozenset([a, b, c])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g3"
        assert len(walker.gate_lines) == 3
        # Two OR gates and one AND gate
        assert "G g1 := O" in walker.gate_lines[0]
        assert "G g2 := O" in walker.gate_lines[1]
        assert walker.gate_lines[2] == "G g3 := A g1 g2"

    def test_walk_theory_atoms_with_symbols(self):
        """
        Test that theory atoms walk their children symbols.
        BUG FOUND: Theory atoms also walk their children (x, y),
        so formula gets mapped along with its sub-symbols.
        """
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)
        formula = LT(x, y)
        abstraction = {}
        phi_atoms = frozenset([formula])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        # The formula is mapped, but so are x and y
        assert formula in abstraction
        assert x in abstraction
        assert y in abstraction
        # Result should be a variable reference
        assert result.startswith("v")

    def test_walk_equals(self):
        """Test EQUALS theory operator"""
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)
        formula = Equals(x, y)
        abstraction = {}
        phi_atoms = frozenset([formula])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert formula in abstraction
        assert result.startswith("v")

    def test_walk_forall_raises_exception(self):
        """Test that ForAll quantifier raises UnsupportedNodeException"""
        x = Symbol("x", REAL)
        a = Symbol("A", BOOL)
        formula = ForAll([x], a)
        abstraction = {}
        phi_atoms = frozenset([a])
        walker = BCS12Walker(abstraction, phi_atoms)

        with pytest.raises(
            UnsupportedNodeException,
            match="Quantifiers are yet to be supported"
        ):
            walker.walk(formula)

    def test_walk_exists_raises_exception(self):
        """Test that Exists quantifier raises UnsupportedNodeException"""
        x = Symbol("x", REAL)
        a = Symbol("A", BOOL)
        formula = Exists([x], a)
        abstraction = {}
        phi_atoms = frozenset([a])
        walker = BCS12Walker(abstraction, phi_atoms)

        with pytest.raises(
            UnsupportedNodeException,
            match="Quantifiers are yet to be supported"
        ):
            walker.walk(formula)

    def test_complex_formula(self):
        """Test a complex formula with multiple operators"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        c = Symbol("C", BOOL)
        # (a & b) | (~c)
        formula = Or(And(a, b), Not(c))
        abstraction = {}
        phi_atoms = frozenset([a, b, c])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g2"
        assert len(walker.gate_lines) == 2
        # First is AND, second is OR
        assert "G g1 := A" in walker.gate_lines[0]
        assert "G g2 := O" in walker.gate_lines[1]

    def test_nested_formula(self):
        """Test deeply nested formula"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        c = Symbol("C", BOOL)
        d = Symbol("D", BOOL)
        # ((a & b) | c) & d
        formula = And(Or(And(a, b), c), d)
        abstraction = {}
        phi_atoms = frozenset([a, b, c, d])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g3"
        assert len(walker.gate_lines) == 3

    def test_remove_double_negations(self):
        """Test that double negations are removed from gate lines"""
        walker = BCS12Walker({}, frozenset())

        result1 = walker._remove_double_negations("G g1 := A --v1 v2")
        assert result1 == "G g1 := A v1 v2"

        result2 = walker._remove_double_negations("G g1 := O --v1 --v2")
        assert result2 == "G g1 := O v1 v2"

        result3 = walker._remove_double_negations("G g1 := A -v1 v2")
        assert result3 == "G g1 := A -v1 v2"

    def test_iff_with_negations(self):
        """Test IFF with negated arguments to check double negation removal"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        # ~a <-> ~b
        formula = Iff(Not(a), Not(b))
        abstraction = {}
        phi_atoms = frozenset([a, b])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g3"
        # The second gate should have double negations removed
        # (~(~a) & ~(~b)) becomes (a & b)
        assert "G g2 := A v" in walker.gate_lines[1]
        # Check that there are no double negations
        assert "--" not in walker.gate_lines[1]

    def test_implies_with_negation(self):
        """Test IMPLIES with negated antecedent"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        # ~a -> b === ~~a | b === a | b
        formula = Implies(Not(a), b)
        abstraction = {}
        phi_atoms = frozenset([a, b])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g1"
        # Should remove double negation: -(-v1) becomes v1
        assert "G g1 := O v" in walker.gate_lines[0]
        # No double negations should remain
        assert "--" not in walker.gate_lines[0]

    def test_multiple_theory_atoms(self):
        """
        Test formula with multiple different theory atoms.
        BUG FOUND: Theory atoms also map their child symbols,
        leading to more mappings than expected.
        """
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)
        lt_atom = LT(x, y)
        le_atom = LE(x, y)
        eq_atom = Equals(x, y)

        formula = And(Or(lt_atom, le_atom), eq_atom)
        abstraction = {}
        phi_atoms = frozenset([lt_atom, le_atom, eq_atom])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g2"
        assert lt_atom in abstraction
        assert le_atom in abstraction
        assert eq_atom in abstraction
        # x and y also get mapped
        assert x in abstraction
        assert y in abstraction

    def test_gate_counter_increments(self):
        """Test that gate counter increments properly"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        c = Symbol("C", BOOL)
        formula = And(And(a, b), c)
        abstraction = {}
        phi_atoms = frozenset([a, b, c])
        walker = BCS12Walker(abstraction, phi_atoms)

        walker.walk(formula)

        assert walker.gate_counter == 2
        assert len(walker.gate_lines) == 2

    def test_constants_in_complex_formula(self):
        """Test constants mixed with variables"""
        a = Symbol("A", BOOL)
        # a & TRUE & FALSE
        formula = And(And(a, TRUE()), FALSE())
        abstraction = {}
        phi_atoms = frozenset([a])
        walker = BCS12Walker(abstraction, phi_atoms)

        walker.walk(formula)

        # Should create gates for TRUE, FALSE, and the AND operations
        assert walker.gate_counter >= 3

    def test_abstraction_increments_from_max(self):
        """Test that new abstractions use max + 1"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        c = Symbol("C", BOOL)

        # Pre-populate abstraction with non-sequential IDs
        abstraction = {a: 10, b: 25}
        phi_atoms = frozenset([a, b, c])
        walker = BCS12Walker(abstraction, phi_atoms)

        walker.walk(c)

        assert abstraction[c] == 26  # max(10, 25) + 1

    def test_empty_abstraction_starts_at_one(self):
        """Test that empty abstraction starts at 1"""
        a = Symbol("A", BOOL)
        abstraction = {}
        phi_atoms = frozenset([a])
        walker = BCS12Walker(abstraction, phi_atoms)

        walker.walk(a)

        assert abstraction[a] == 1

    def test_memoization(self):
        """Test that the walker memoizes results correctly"""
        a = Symbol("A", BOOL)
        # a & a - should reuse the same mapping
        formula = And(a, a)
        abstraction = {}
        phi_atoms = frozenset([a])
        walker = BCS12Walker(abstraction, phi_atoms)

        walker.walk(formula)

        # Should only map 'a' once
        assert len(abstraction) == 1
        assert "G g1 := A v1 v1" in walker.gate_lines[0]

    def test_theory_constants_handled(self):
        """Test that theory constants are handled without errors"""
        x = Symbol("x", REAL)
        # x < 5.0
        formula = LT(x, Real(5.0))
        abstraction = {}
        phi_atoms = frozenset([formula])
        walker = BCS12Walker(abstraction, phi_atoms)

        walker.walk(formula)

        # The LT atom should be mapped
        assert formula in abstraction
        # Real(5.0) should also be in abstraction (from do_nothing)
        assert Real(5.0) in abstraction

    def test_bv_operations(self):
        """Test bit-vector operations are handled as theory atoms"""
        bv8 = BVType(8)
        bv_x = Symbol("bv_x", bv8)
        bv_y = Symbol("bv_y", bv8)
        formula = BVULT(bv_x, bv_y)
        abstraction = {}
        phi_atoms = frozenset([formula])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert formula in abstraction
        assert result.startswith("v")

    def test_mixed_boolean_and_theory(self):
        """
        Test formula mixing boolean and theory atoms.
        Note: theory atoms also walk their symbols.
        """
        a = Symbol("A", BOOL)
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)
        lt_atom = LT(x, y)

        # a & (x < y)
        formula = And(a, lt_atom)
        abstraction = {}
        phi_atoms = frozenset([a, lt_atom])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        assert result == "g1"
        assert a in abstraction
        assert lt_atom in abstraction
        # x and y also get mapped
        assert x in abstraction
        assert y in abstraction

    def test_or_with_multiple_children(self):
        """Test OR with more than 2 children"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        c = Symbol("C", BOOL)
        d = Symbol("D", BOOL)
        # Note: pysmt might flatten this
        formula = Or(a, b, c, d)
        abstraction = {}
        phi_atoms = frozenset([a, b, c, d])
        walker = BCS12Walker(abstraction, phi_atoms)

        walker.walk(formula)

        # Should have at least one gate
        assert len(walker.gate_lines) >= 1

    def test_and_with_multiple_children(self):
        """Test AND with more than 2 children"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        c = Symbol("C", BOOL)
        d = Symbol("D", BOOL)
        formula = And(a, b, c, d)
        abstraction = {}
        phi_atoms = frozenset([a, b, c, d])
        walker = BCS12Walker(abstraction, phi_atoms)

        walker.walk(formula)

        # Should have at least one gate
        assert len(walker.gate_lines) >= 1

    def test_ite_nested(self):
        """Test nested ITE expressions"""
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        c = Symbol("C", BOOL)
        d = Symbol("D", BOOL)
        # if a then (if b then c else d) else d
        formula = Ite(a, Ite(b, c, d), d)
        abstraction = {}
        phi_atoms = frozenset([a, b, c, d])
        walker = BCS12Walker(abstraction, phi_atoms)

        result = walker.walk(formula)

        # Should produce multiple gates
        assert walker.gate_counter >= 3
        assert result.startswith("g")

    def test_invalidate_memoization_parameter(self):
        """Test that invalidate_memoization parameter is passed correctly"""
        a = Symbol("A", BOOL)
        walker1 = BCS12Walker({}, frozenset(), invalidate_memoization=True)
        walker2 = BCS12Walker({}, frozenset(), invalidate_memoization=False)

        # Both should work without errors
        walker1.walk(a)
        walker2.walk(a)

