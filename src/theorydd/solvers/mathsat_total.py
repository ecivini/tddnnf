"""this module handles interactions with the mathsat solver"""

from typing import Dict, Iterable, List

import mathsat
from pysmt.fnode import FNode
from pysmt.shortcuts import Solver

from theorydd.constants import SAT, UNSAT
from theorydd.formula import get_theory_atoms
from theorydd.solvers.solver import SMTEnumerator
from .mathsat_utils import MSAT_TOTAL_ENUM_OPTIONS, _allsat_callback_count, _allsat_callback_store


class MathSATTotalEnumerator(SMTEnumerator):
    """A wrapper for the mathsat T-solver"""

    def __init__(self, computation_logger: Dict | None = None, project_on_theory_atoms: bool = True) -> None:
        super().__init__(computation_logger)
        solver_options_dict = MSAT_TOTAL_ENUM_OPTIONS
        self._solver = Solver("msat", solver_options=solver_options_dict)
        self._converter = self._solver.converter
        self._project_on_theory_atoms = project_on_theory_atoms
        self.reset()

    def reset(self):
        """Resets the internal state of the solver"""
        self._solver.reset_assertions()
        self._tlemmas = []
        self._models = []
        self._models_count = 0

    def check_all_sat(self, phi: FNode, atoms: List[FNode] | None = None, store_models: bool = False) -> bool:
        self.check_supports(phi)
        self.reset()

        atoms = phi.get_atoms() if atoms is None else atoms
        if self._project_on_theory_atoms:
            atoms = get_theory_atoms(atoms)
        self.atoms = atoms

        self._solver.add_assertion(phi)

        if store_models:
            mathsat.msat_all_sat(
                self._solver.msat_env(),
                self.get_converted_atoms(atoms),
                callback=lambda model: _allsat_callback_store(model, self._converter, self._models),
            )
            self._models_count = len(self._models)
        else:
            models_count_l = [0]
            mathsat.msat_all_sat(
                self._solver.msat_env(),
                self.get_converted_atoms(atoms),
                callback=lambda _: _allsat_callback_count(models_count_l),
            )
            self._models_count = models_count_l[0]

        self._tlemmas = [self._converter.back(l) for l in mathsat.msat_get_theory_lemmas(self._solver.msat_env())]

        if self._models_count == 0:
            return UNSAT

        if self._computation_logger is not None:
            self._computation_logger["Total models"] = self._models_count

        return SAT

    def get_theory_lemmas(self) -> List[FNode]:
        """Returns the theory lemmas found during the All-SAT computation"""
        return self._tlemmas

    def get_models(self) -> list:
        """Returns the models found during the All-SAT computation"""
        return self._models

    def get_models_count(self) -> int:
        """Returns the models found during the All-SAT computation"""
        return self._models_count

    def get_converter(self) -> object:
        """Returns the converter used for the normalization of T-atoms"""
        return self._converter

    def get_converted_atoms(self, atoms: Iterable[FNode]) -> List[FNode]:
        """Returns a list of normalized atoms

        Args:
            atoms (Iterable[FNode]): a list of pysmt atoms

        Returns:
            List[FNode]: a list of normalized atoms
        """
        return [self._converter.convert(a) for a in atoms]
