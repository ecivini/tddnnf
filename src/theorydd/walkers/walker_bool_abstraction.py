from pysmt.walkers import DagWalker, handles
import pysmt.operators as op
from pysmt.fnode import FNode

from pysmt.shortcuts import And, Or, Iff, Implies, TRUE, FALSE, Not, Ite, BOOL

from theorydd.util.custom_exceptions import UnsupportedNodeException


class BooleanAbstractionWalker(DagWalker):
    '''A walker to normalize smt formulas into its boolean abstraction'''

    def __init__(self, atoms={}, abstraction={}, env=None, invalidate_memoization=False):
        DagWalker.__init__(self, env, invalidate_memoization)
        self.atoms = atoms
        self.abstraction = abstraction

        for atom in atoms:
            self._abstract(atom)

        return

    def walk_and(self, formula: FNode, args, **kwargs):
        '''translate AND node'''
        # pylint: disable=unused-argument
        return And(*args)

    def walk_or(self, formula: FNode, args, **kwargs):
        '''translate OR node'''
        # pylint: disable=unused-argument
        return Or(*args)

    def walk_not(self, formula: FNode, args, **kwargs):
        '''translate NOT node'''
        # pylint: disable=unused-argument
        return Not(args[0])

    def walk_symbol(self, formula: FNode, args, **kwargs):
        '''translate SYMBOL node'''
        # pylint: disable=unused-argument
        return formula

    def walk_iff(self, formula, args, **kwargs):
        '''translate IFF node'''
        # pylint: disable=unused-argument
        return Iff(args[0], args[1])

    def walk_implies(self, formula, args, **kwargs):
        '''translate IMPLIES node'''  # a -> b === (~ a) v b
        # pylint: disable=unused-argument
        return Implies(args[0], args[1])

    def walk_ite(self, formula, args, **kwargs):
        '''translate ITE node'''
        # pylint: disable=unused-argument
        return Ite(args[0], args[1], args[2])

    def _abstract(self, formula):
        if formula not in self.abstraction:
            var_name = f"v{len(self.abstraction)}"
            abstr_var = self.env.formula_manager.Symbol(var_name, BOOL)
            self.abstraction[formula] = abstr_var
        return self.abstraction[formula]

    def walk_forall(self, formula, args, **kwargs):
        '''translate For-all node'''
        # pylint: disable=unused-argument
        raise UnsupportedNodeException('Quantifiers are yet to be supported')

    def walk_exists(self, formula, args, **kwargs):
        '''translate Exists node'''
        # pylint: disable=unused-argument
        raise UnsupportedNodeException('Quantifiers are yet to be supported')

    @handles(*op.CONSTANTS, *op.THEORY_OPERATORS)
    def walk_constants(self, formula, args, **kwargs):
        '''translate Equals node'''
        # pylint: disable=unused-argument
        return formula

    @handles(*op.RELATIONS, op.FUNCTION)
    def walk_theory(self, formula, args, **kwargs):
        '''translate theory node'''
        # pylint: disable=unused-argument
        return self._abstract(formula)
