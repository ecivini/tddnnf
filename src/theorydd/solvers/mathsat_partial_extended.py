"""this module handles interactions with the mathsat solver"""

import multiprocessing
import time
from typing import Dict, List

import mathsat
from allsat_cnf.polarity_cnfizer import PolarityCNFizer
from pysmt.fnode import FNode
from pysmt.formula import FormulaContextualizer
from pysmt.shortcuts import And, Solver
from pysmt.solvers.msat import MathSAT5Solver

from theorydd.constants import SAT, UNSAT
from theorydd.formula import get_theory_atoms
from theorydd.solvers.solver import SMTEnumerator
from theorydd.util.collections import Nested, map_nested
from theorydd.util.pysmt import SuspendTypeChecking
from .mathsat_utils import (
    MSAT_PARTIAL_ENUM_OPTIONS,
    MSAT_TOTAL_ENUM_OPTIONS,
    _allsat_callback_count,
    _allsat_callback_store,
)


def _contextualize(contextualizer: FormulaContextualizer, formulas: Nested[FNode]) -> Nested[FNode]:
    """Contextualizes a collection of formulas using the provided contextualizer

    Args:
        contextualizer: the FormulaContextualizer to use
        formulas: collection of formulas to contextualize

    Returns:
        the contextualized formulas
    """
    with SuspendTypeChecking():
        return map_nested(lambda f: contextualizer.walk(f), formulas)


_PARTIAL_MODELS = []
_TLEMMAS = []
_PHI = None
_PHI_ATOMS = []
_SOLVER: MathSAT5Solver | None = None


def _initialize_worker(
    partial_models: List[List[FNode]], phi: FNode, phi_atoms: List[FNode], tlemmas: List[FNode], solver_options: dict
) -> None:
    global _PARTIAL_MODELS, _PHI, _TLEMMAS, _SOLVER, _PHI_ATOMS

    contextualizer = FormulaContextualizer()

    _PARTIAL_MODELS = partial_models
    _TLEMMAS = _contextualize(contextualizer, tlemmas)
    _PHI = _contextualize(contextualizer, phi)

    _SOLVER = Solver("msat", solver_options=solver_options)

    _PHI_ATOMS = _contextualize(contextualizer, phi_atoms)
    _PHI_ATOMS = [_SOLVER.converter.convert(a) for a in _PHI_ATOMS]

    _SOLVER.add_assertion(_PHI)
    _SOLVER.add_assertion(And(_TLEMMAS))


def _parallel_worker(args: tuple) -> tuple:
    """Worker function for parallel all-smt extension

    Args:
        args: tuple of (partial_model, phi, atoms, solver_options_dict_total, tlemmas)

    Returns:
        tuple of local_models, total_lemmas
    """
    global _SOLVER, _TLEMMAS, _PHI, _PHI_ATOMS, _PARTIAL_MODELS

    model_id, store_models = args

    local_solver = _SOLVER
    local_converter = local_solver.converter

    contextualizer = FormulaContextualizer()
    converted_atoms = _PHI_ATOMS

    model = _PARTIAL_MODELS[model_id]

    local_solver.push()

    model = _contextualize(contextualizer, model)
    local_solver.add_assertions(model)

    found_models = []
    found_models_count = 0
    if store_models:
        mathsat.msat_all_sat(
            local_solver.msat_env(),
            converted_atoms,
            callback=lambda model: _allsat_callback_store(model, local_converter, found_models),
        )
        found_models_count = len(found_models)
    else:
        models_count_l = [0]
        mathsat.msat_all_sat(
            local_solver.msat_env(), converted_atoms, callback=lambda _: _allsat_callback_count(models_count_l)
        )
        found_models_count = models_count_l[0]

    found_tlemmas = [local_converter.back(l) for l in mathsat.msat_get_theory_lemmas(local_solver.msat_env())]

    local_solver.pop()
    local_solver.add_assertion(And(found_tlemmas))

    return found_models, found_models_count, found_tlemmas


class MathSATExtendedPartialEnumerator(SMTEnumerator):
    """A wrapper for the mathsat T-solver.

    Computes all-SMT by first computing partial assignments and then extending them to total ones.
    The result of the enumeration is a total enumeration of truth assignments."""

    def __init__(
        self, computation_logger: Dict | None = None, project_on_theory_atoms: bool = True, parallel_procs: int = 1
    ):
        super().__init__(computation_logger=computation_logger)
        if parallel_procs < 1 or parallel_procs > multiprocessing.cpu_count():
            raise ValueError("parallel_procs must be between 1 and the number of CPU cores")
        self.solver_partial = Solver("msat", solver_options=MSAT_PARTIAL_ENUM_OPTIONS)
        self.solver_total = Solver("msat", solver_options=MSAT_TOTAL_ENUM_OPTIONS)
        self.reset()
        self._converter_partial = self.solver_partial.converter
        self._converter_total = self.solver_total.converter
        self._project_on_theory_atoms = project_on_theory_atoms
        self._parallel_procs = parallel_procs

    def reset(self):
        self.solver_partial.reset_assertions()
        self.solver_total.reset_assertions()
        self._tlemmas = []
        self._models = []
        self._models_count = 0

    def check_all_sat(self, phi: FNode, atoms: List[FNode] | None = None, store_models: bool = False) -> bool:
        self.check_supports(phi)
        self.reset()

        atoms = phi.get_atoms() if atoms is None else atoms
        if self._project_on_theory_atoms:
            atoms = get_theory_atoms(atoms)

        phi_cnf = PolarityCNFizer(nnf=True, mutex_nnf_labels=True).convert_as_formula(phi)
        self.solver_partial.add_assertion(phi_cnf)

        start_time = time.time()
        partial_models = []
        mathsat.msat_all_sat(
            self.solver_partial.msat_env(),
            self.get_converted_atoms(atoms, self._converter_partial),
            callback=lambda model: _allsat_callback_store(model, self._converter_partial, partial_models),
        )

        self._tlemmas = [
            self._converter_partial.back(l) for l in mathsat.msat_get_theory_lemmas(self.solver_partial.msat_env())
        ]

        end_time = time.time()
        if self._computation_logger is not None:
            self._computation_logger["Partial AllSMT time"] = end_time - start_time
            self._computation_logger["Partial models"] = len(partial_models)

        if len(partial_models) == 0:
            return UNSAT

        if self._parallel_procs <= 1:
            self.solver_total.add_assertion(phi)
            self.solver_total.add_assertions(self._tlemmas)
            converted_atoms = self.get_converted_atoms(atoms, self._converter_total)

            for m in partial_models:
                self.solver_total.push()
                self.solver_total.add_assertions(m)

                if store_models:
                    models = []
                    mathsat.msat_all_sat(
                        self.solver_total.msat_env(),
                        converted_atoms,
                        callback=lambda model: _allsat_callback_store(model, self._converter_total, models),
                    )
                    self._models_count += len(models)
                    self._models.extend(models)
                else:
                    models_count_l = [0]
                    mathsat.msat_all_sat(
                        self.solver_total.msat_env(),
                        converted_atoms,
                        callback=lambda _: _allsat_callback_count(models_count_l),
                    )
                    self._models_count += models_count_l[0]

                tlemmas_total = [
                    self._converter_total.back(l) for l in mathsat.msat_get_theory_lemmas(self.solver_total.msat_env())
                ]

                self._tlemmas += tlemmas_total
                self.solver_total.pop()

                self.solver_total.add_assertion(And(tlemmas_total))

        else:
            # Prepare arguments for each worker
            worker_args = [(i, store_models) for i in range(len(partial_models))]

            # Use a process pool to maintain constant number of workers
            new_tlemmas = []
            pool = multiprocessing.Pool(
                processes=self._parallel_procs,
                initializer=_initialize_worker,
                initargs=(partial_models, phi, atoms, self._tlemmas, MSAT_TOTAL_ENUM_OPTIONS),
            )
            with pool:
                # Use imap_unordered to process results as they complete
                for models, models_count, lemmas_batch in pool.imap_unordered(_parallel_worker, worker_args):
                    contextualizer = FormulaContextualizer()
                    self._models.extend(_contextualize(contextualizer, models))
                    new_tlemmas.extend(_contextualize(contextualizer, lemmas_batch))
                    self._models_count += models_count

            self._tlemmas.extend(new_tlemmas)

        self._tlemmas = list(set(self._tlemmas))

        if self._computation_logger is not None:
            self._computation_logger["Total models"] = self._models_count

        return SAT

    def get_theory_lemmas(self) -> List[FNode]:
        """Returns the theory lemmas found during the All-SAT computation"""
        return self._tlemmas

    def get_models(self) -> List:
        """Returns the models found during the All-SAT computation"""
        return self._models

    def get_models_count(self) -> int:
        return self._models_count

    def get_converter(self):
        """Returns the converter used for the normalization of T-atoms"""
        return self._converter_partial

    def get_converted_atoms(self, atoms, converter) -> List[FNode]:
        """Returns a list of normalized atoms"""
        return [converter.convert(a) for a in atoms]
