"""this module defines a Walker that takes a pysmt formula and converts it into BC-S1.2 format"""

from pysmt.fnode import FNode
from pysmt.walkers import DagWalker, handles
import pysmt.operators as op

from theorydd.util.custom_exceptions import UnsupportedNodeException


class BCS12Walker(DagWalker):
    """A walker to translate the DAG formula quickly with memoization into BC-S1.2"""

    def __init__(
        self,
        abstraction: dict[FNode, int],
        phi_atoms: frozenset,
        env=None,
        invalidate_memoization=False,
    ):
        DagWalker.__init__(self, env, invalidate_memoization)
        self.abstraction = abstraction
        self.phi_atoms = phi_atoms
        self.gate_counter = 0
        self.gate_lines = []

    def _apply_mapping(self, formula: FNode):
        """applies the mapping when possible, returns the variable name"""
        if formula in self.abstraction:
            return f"v{self.abstraction[formula]}"
        return None

    def walk_and(self, formula: FNode, args, **kwargs):
        """translate AND node"""
        # pylint: disable=unused-argument
        child_names = [arg for arg in args if arg is not None]
        if not child_names:
            return None
        
        self.gate_counter += 1
        gate_name = f"g{self.gate_counter}"
        self.gate_lines.append(f"G {gate_name} := A " + " ".join(child_names))
        return gate_name

    def walk_or(self, formula: FNode, args, **kwargs):
        """translate OR node"""
        # pylint: disable=unused-argument
        child_names = [arg for arg in args if arg is not None]
        if not child_names:
            return None
        
        self.gate_counter += 1
        gate_name = f"g{self.gate_counter}"
        self.gate_lines.append(f"G {gate_name} := O " + " ".join(child_names))
        return gate_name

    def walk_not(self, formula: FNode, args, **kwargs):
        """translate NOT node"""
        # pylint: disable=unused-argument
        if args[0] is None:
            return None
        return f"-{args[0]}"

    def walk_symbol(self, formula: FNode, args, **kwargs):
        """translate SYMBOL node"""
        # pylint: disable=unused-argument
        if formula in self.phi_atoms:
            return f"v{self.abstraction[formula]}"
        return None

    def walk_bool_constant(self, formula: FNode, args, **kwargs):
        """translate BOOL const node"""
        # pylint: disable=unused-argument
        value = formula.constant_value()
        
        self.gate_counter += 1
        gate_name = f"g{self.gate_counter}"
        
        if value:
            # BC-S1.2 does not have a specific term for true, so we create
            # a gate that always evaluates to true
            self.gate_lines.append(f"G {gate_name} := O v1 -v1")
        else:
            # BC-S1.2 does not have a specific term for false, so we create
            # a gate that always evaluates to false
            self.gate_lines.append(f"G {gate_name} := A v1 -v1")
        
        return gate_name

    def walk_iff(self, formula, args, **kwargs):
        """translate IFF node"""
        # pylint: disable=unused-argument
        # IFF: a <-> b === (a & b) | (~a & ~b)
        if args[0] is None or args[1] is None:
            return None
        
        # Create: (a & b)
        self.gate_counter += 1
        gate_and1 = f"g{self.gate_counter}"
        self.gate_lines.append(f"G {gate_and1} := A {args[0]} {args[1]}")
        
        # Create: (~a & ~b)
        self.gate_counter += 1
        gate_and2 = f"g{self.gate_counter}"
        self.gate_lines.append(f"G {gate_and2} := A -{args[0]} -{args[1]}")
        
        # Create: (a & b) | (~a & ~b)
        self.gate_counter += 1
        gate_or = f"g{self.gate_counter}"
        self.gate_lines.append(f"G {gate_or} := O {gate_and1} {gate_and2}")
        
        return gate_or

    def walk_implies(self, formula, args, **kwargs):
        """translate IMPLIES node"""
        # pylint: disable=unused-argument
        # IMPLIES: a -> b === (~a | b)
        if args[0] is None or args[1] is None:
            return None
        
        self.gate_counter += 1
        gate_name = f"g{self.gate_counter}"
        self.gate_lines.append(f"G {gate_name} := O -{args[0]} {args[1]}")
        
        return gate_name

    def walk_ite(self, formula, args, **kwargs):
        """translate ITE node"""
        # pylint: disable=unused-argument
        # ITE: if a then b else c === ((~a) | b) & (a | c)
        if args[0] is None or args[1] is None or args[2] is None:
            return None
        
        # Create: (~a | b)
        self.gate_counter += 1
        gate_or1 = f"g{self.gate_counter}"
        self.gate_lines.append(f"G {gate_or1} := O -{args[0]} {args[1]}")
        
        # Create: (a | c)
        self.gate_counter += 1
        gate_or2 = f"g{self.gate_counter}"
        self.gate_lines.append(f"G {gate_or2} := O {args[0]} {args[2]}")
        
        # Create: ((~a) | b) & (a | c)
        self.gate_counter += 1
        gate_and = f"g{self.gate_counter}"
        self.gate_lines.append(f"G {gate_and} := A {gate_or1} {gate_or2}")
        
        return gate_and

    def walk_forall(self, formula, args, **kwargs):
        """translate For-all node"""
        # pylint: disable=unused-argument
        raise UnsupportedNodeException("Quantifiers are yet to be supported")

    def walk_exists(self, formula, args, **kwargs):
        """translate Exists node"""
        # pylint: disable=unused-argument
        raise UnsupportedNodeException("Quantifiers are yet to be supported")

    @handles(
        *op.THEORY_OPERATORS,
        *op.BV_RELATIONS,
        *op.IRA_RELATIONS,
        *op.STR_RELATIONS,
        op.EQUALS,
        op.FUNCTION
    )
    def walk_theory(self, formula, args, **kwargs):
        """translate theory node"""
        # pylint: disable=unused-argument
        if formula in self.phi_atoms:
            return f"v{self.abstraction[formula]}"
        return None

    @handles(op.REAL_CONSTANT, op.INT_CONSTANT, op.BV_CONSTANT)
    def do_nothing(self, formula, args, **kwargs):
        """do nothing when seeing theory constants"""
        # pylint: disable=unused-argument
        return None
