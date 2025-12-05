import pysmt.operators as op
from pysmt.fnode import FNode
from pysmt.walkers import DagWalker, handles


class TermIteChecker(DagWalker):
    @handles(
        *op.BOOL_CONNECTIVES, *op.THEORY_OPERATORS, *op.RELATIONS, *op.CONSTANTS, op.EQUALS, op.FUNCTION, op.SYMBOL
    )
    def walk_supported(self, formula, args, **kwargs):
        return all(args)

    @handles(op.QUANTIFIERS)
    def walk_quantifier(self, formula, args, **kwargs):
        return False

    def walk_ite(self, formula: FNode, args, **kwargs):
        return self.env.stc.get_type(formula).is_bool_type()