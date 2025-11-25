"""this module handles interactions with the mathsat solver"""
import multiprocessing
import time
from typing import Dict, List

import mathsat
from allsat_cnf.polarity_cnfizer import PolarityCNFizer
from pysmt.fnode import FNode
from pysmt.formula import FormulaContextualizer
from pysmt.shortcuts import And, Solver

from theorydd.constants import SAT, UNSAT
from theorydd.solvers.solver import SMTEnumerator
from theorydd.util.collections import Nested, map_nested
from theorydd.util.pysmt import SuspendTypeChecking
from theorydd.formula import get_theory_atoms

from .mathsat_utils import _allsat_callback_count, _allsat_callback_store


def _contextualize(
        contextualizer: FormulaContextualizer, formulas: Nested[FNode]
) -> Nested[FNode]:
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
_SOLVER = None


def _initialize_worker(
    partial_models: List[List[FNode]],
    phi: FNode,
    phi_atoms: List[FNode],
    tlemmas: List[FNode],
    solver_options: dict
) -> None:
    global _PARTIAL_MODELS, _PHI, _TLEMMAS, _SOLVER, _PHI_ATOMS

    contextualizer = FormulaContextualizer()

    _PARTIAL_MODELS = partial_models
    _TLEMMAS = _contextualize(contextualizer, tlemmas)
    _PHI = _contextualize(contextualizer, phi)

    _SOLVER = Solver(
        "msat",
        solver_options=solver_options
    )

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
            callback=lambda model:
                _allsat_callback_store(
                    model,
                    local_converter,
                    found_models
                )
        )
        found_models_count = len(found_models)
    else:
        models_count_l = [0]
        mathsat.msat_all_sat(
            local_solver.msat_env(),
            converted_atoms,
            callback=lambda model:
                _allsat_callback_count(
                    models_count_l
                )
        )
        found_models_count = models_count_l[0]

    found_tlemmas = [
        local_converter.back(l)
        for l in mathsat.msat_get_theory_lemmas(local_solver.msat_env())
    ]

    local_solver.pop()
    local_solver.add_assertion(And(found_tlemmas))

    return found_models, found_models_count, found_tlemmas


class MathSATExtendedPartialEnumerator(SMTEnumerator):
    """A wrapper for the mathsat T-solver.

    Computes all-SMT by first computing partial assignments and then extending them to total ones.
    The result of the enumeration is a total enumeration of truth assignments."""

    def __init__(self) -> None:
        solver_options_dict = {
            "dpll.allsat_minimize_model": "true",  # - total truth assignments
            # "theory.pure_literal_filtering": "true",
            # "dpll.allsat_allow_duplicates": "false", # - to produce not necessarily disjoint truth assignments.
            #                                          # can be set to true only if minimize_model=true.
            # - necessary to disable some processing steps
            "preprocessor.toplevel_propagation": "false",
            "preprocessor.simplification": "0",  # from mathsat
            "dpll.store_tlemmas": "true",  # - necessary to obtain t-lemmas
            "theory.la.split_rat_eq": "false",
            "theory.la.laz_internal_branch_and_bound": "true",
            "theory.la.laz_internal_branch_and_bound_limit": "0"
        }
        self.solver_options_dict_total = {
            "dpll.allsat_minimize_model": "false",  # - total truth assignments
            # "theory.pure_literal_filtering": "true",
            # "dpll.allsat_allow_duplicates": "false", # - to produce not necessarily disjoint truth assignments.
            #                                          # can be set to true only if minimize_model=true.
            # - necessary to disable some processing steps
            "preprocessor.toplevel_propagation": "false",
            "preprocessor.simplification": "0",  # from mathsat
            "dpll.store_tlemmas": "true",  # - necessary to obtain t-lemmas
            "theory.la.split_rat_eq": "false",
            "theory.la.laz_internal_branch_and_bound": "true",
            "theory.la.laz_internal_branch_and_bound_limit": "0"
        }
        self.solver = Solver("msat", solver_options=solver_options_dict)
        self.solver_total = Solver("msat", solver_options=self.solver_options_dict_total)
        self._last_phi = None
        self._tlemmas = []
        self._models = []
        self._models_count = 0
        self._converter = self.solver.converter
        self._converter_total = self.solver_total.converter
        self._atoms = []

    def check_all_sat(
            self, phi: FNode, boolean_mapping: Dict[FNode, FNode] | None = None, 
            parallel_procs: int = 1, atoms: List[FNode] | None = None,
            computation_logger: dict | None = None, store_models: bool = False
    ) -> bool:
        """Computes All-SMT for the SMT-formula phi using partial assignment and Tsetsin CNF-ization

        Args:
            phi (FNode): a pysmt formula
            boolean_mapping (Dict[FNode, FNode]) [None]: unused, for compatibility with SMTSolver
            parallel (bool) [False]: if True, parallelizes the computation of total truth assignments
        """
        if boolean_mapping is not None:
            boolean_mapping = None

        self._last_phi = phi
        self._tlemmas = []
        self._models = []
        self._models_count = 0
        self._atoms = get_theory_atoms(phi) if not atoms else atoms

        self.solver.reset_assertions()
        self.solver_total.reset_assertions()
        phi_tsetsin = PolarityCNFizer(
            nnf=True, mutex_nnf_labels=True
        ).convert_as_formula(phi)
        self.solver.add_assertion(phi_tsetsin)

        partial_models = []
        start_time = time.time()
        mathsat.msat_all_sat(
            self.solver.msat_env(),
            self.get_converted_atoms(self._atoms),
            # self.get_converted_atoms(
            #    list(boolean_mapping.keys())),
            callback=lambda model: _allsat_callback_store(
                model, self._converter, partial_models
            ),
        )

        self._tlemmas = [
            self._converter.back(l)
            for l in mathsat.msat_get_theory_lemmas(self.solver.msat_env())
        ]

        end_time = time.time()
        if computation_logger is not None:
            computation_logger["Partial AllSMT time"] = end_time - start_time
            computation_logger["Partial models"] = len(partial_models)

        if len(partial_models) == 0:
            return UNSAT

        if parallel_procs <= 1:
            self.solver_total.add_assertion(phi)
            self.solver_total.add_assertion(And(self._tlemmas))
            
            for m in partial_models:
                self.solver_total.push()
                self.solver_total.add_assertion(And(m))

                if store_models:
                    mathsat.msat_all_sat(
                        self.solver_total.msat_env(),
                        [self._converter_total.convert(a) for a in self._atoms],
                        callback=lambda model:
                            _allsat_callback_store(
                                model,
                                self._converter_total,
                                self._models
                            )
                    )
                    self._models_count = len(self._models)
                else:
                    models_count_l = [0]
                    mathsat.msat_all_sat(
                        self.solver_total.msat_env(),
                        [self._converter_total.convert(a) for a in self._atoms],
                        callback=lambda _:
                            _allsat_callback_count(
                                models_count_l
                            )
                    )
                    self._models_count += models_count_l[0]

                tlemmas_total = [
                    self._converter_total.back(l)
                    for l in mathsat.msat_get_theory_lemmas(self.solver_total.msat_env())
                ]

                self._tlemmas += tlemmas_total
                self.solver_total.pop()

                self.solver_total.add_assertion(And(tlemmas_total))

        else:
            # Prepare arguments for each worker
            worker_args = [
                (i, store_models)
                for i in range(len(partial_models))
            ]

            # Use a process pool to maintain constant number of workers  
            new_tlemmas = []
            pool = multiprocessing.Pool(
                processes=parallel_procs,
                initializer=_initialize_worker,
                initargs=(
                    partial_models,
                    phi,
                    self._atoms,
                    self._tlemmas,
                    self.solver_options_dict_total
                )
            )
            with pool:
                # Use imap_unordered to process results as they complete
                for (models, models_count, lemmas_batch) in pool.imap_unordered(_parallel_worker, worker_args):
                    contextualizer = FormulaContextualizer()
                    self._models.extend(_contextualize(contextualizer, models)) 
                    new_tlemmas.extend(_contextualize(contextualizer, lemmas_batch))   
                    self._models_count += models_count

            self._tlemmas.extend(new_tlemmas)

        self._tlemmas = list(set(self._tlemmas))

        if computation_logger is not None:
            computation_logger["Total models"] = self._models_count

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
        return self._converter

    def get_converted_atoms(self, atoms):
        """Returns a list of normalized atoms"""
        return [self._converter.convert(a) for a in atoms]
