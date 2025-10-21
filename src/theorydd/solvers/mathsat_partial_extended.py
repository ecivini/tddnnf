"""this module handles interactions with the mathsat solver"""

from typing import List, Dict
from pysmt.shortcuts import Solver, And
from pysmt.parsing import parse
from pysmt.fnode import FNode
import mathsat
from allsat_cnf.polarity_cnfizer import PolarityCNFizer
from theorydd.constants import SAT, UNSAT
from theorydd.solvers.solver import SMTEnumerator
import multiprocessing
import itertools
from theorydd import formula


def _allsat_callback(model, converter, models):
    """callback for all-sat"""
    py_model = {converter.back(v) for v in model}
    models.append(py_model)
    return 1


def _parallel_worker(args: tuple) -> list:
    """Worker function for parallel all-smt extension
    
    Args:
        args: tuple of (partial_model, phi, atoms, solver_options_dict_total, shared_lemmas)
    
    Returns:
        tuple of local_models
    """
    partial_models, phi, atoms, solver_options_dict_total, shared_lemmas = args
    
    local_solver = Solver("msat", solver_options=solver_options_dict_total)
    local_solver.add_assertion(phi)
    total_models = []

    for model in partial_models:
        local_solver.push()
        local_solver.add_assertion(And(model))
        # Use current shared lemmas
        local_solver.add_assertion(And(list(shared_lemmas)))
        local_converter = local_solver.converter
        local_models = []

        mathsat.msat_all_sat(
            local_solver.msat_env(),
            [local_converter.convert(a) for a in atoms],
            callback=lambda model: _allsat_callback(
                model, local_converter, local_models
            ),
        )
        
        # Update shared lemmas
        for lemma in mathsat.msat_get_theory_lemmas(local_converter.msat_env()):
            parsed_lemma = local_converter.back(lemma)
            normalized_lemma = formula.get_normalized(parsed_lemma, local_converter)
            if normalized_lemma not in shared_lemmas:
                shared_lemmas.append(normalized_lemma)

        local_solver.pop()

        total_models += local_models

    return total_models


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
        }
        self.solver = Solver("msat", solver_options=solver_options_dict)
        self.solver_total = Solver("msat", solver_options=self.solver_options_dict_total)
        self._last_phi = None
        self._tlemmas = []
        self._models = []
        self._converter = self.solver.converter
        self._converter_total = self.solver_total.converter
        self._atoms = []

    def check_all_sat(
        self, phi: FNode, boolean_mapping: Dict[FNode, FNode] | None = None, parallel_procs: int = 1
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
        self._atoms = []

        self._atoms = phi.get_atoms()

        self.solver.reset_assertions()
        self.solver_total.reset_assertions()
        phi_tsetsin = PolarityCNFizer(
            nnf=True, mutex_nnf_labels=True
        ).convert_as_formula(phi)
        self.solver.add_assertion(phi_tsetsin)

        partial_models = []
        mathsat.msat_all_sat(
            self.solver.msat_env(),
            self.get_converted_atoms(self._atoms),
            # self.get_converted_atoms(
            #    list(boolean_mapping.keys())),
            callback=lambda model: _allsat_callback(
                model, self._converter, partial_models
            ),
        )

        self._tlemmas = [
            self._converter.back(l)
            for l in mathsat.msat_get_theory_lemmas(self.solver.msat_env())
        ]

        if len(partial_models) == 0:
            return UNSAT

        self.solver_total.add_assertion(phi)
        self._models = []
        if parallel_procs <= 1:
            for m in partial_models:
                self.solver_total.push()
                self.solver_total.add_assertion(And(m))
                # Theorylemmas added to solver total
                self.solver_total.add_assertion(And(self._tlemmas))
                models_total = []
                mathsat.msat_all_sat(
                    self.solver_total.msat_env(),
                    [self._converter_total.convert(a) for a in self._atoms],
                    callback=lambda model: _allsat_callback(
                        model, self._converter_total, models_total
                    ),
                )
                tlemmas_total = [
                    formula.get_normalized(self._converter_total.back(l), self._converter_total)
                    for l in mathsat.msat_get_theory_lemmas(self.solver_total.msat_env())
                ]
                self._models += models_total
                self._tlemmas += tlemmas_total
                self.solver_total.pop()
            
        else:            
            # Create shared list for lemmas that can be updated by workers
            manager = multiprocessing.Manager()
            shared_lemmas = manager.list(self._tlemmas)
            
            # Prepare arguments for each worker
            chunks_size = max(1, len(partial_models) // parallel_procs)
            partial_models_chunks = itertools.batched(partial_models, chunks_size)
            worker_args = [
                (chunk, phi, self._atoms, self.solver_options_dict_total, shared_lemmas)
                for chunk in partial_models_chunks
            ]

            # Use a process pool to maintain constant number of workers            
            with multiprocessing.Pool(processes=parallel_procs) as pool:
                # Use imap_unordered to process results as they complete
                for models_batch in pool.imap_unordered(_parallel_worker, worker_args):
                    self._models.extend(models_batch)
            
            # Update instance lemmas with all collected lemmas
            self._tlemmas = list(shared_lemmas)

        return SAT

    def get_theory_lemmas(self) -> List[FNode]:
        """Returns the theory lemmas found during the All-SAT computation"""
        return self._tlemmas

    def get_models(self) -> List:
        """Returns the models found during the All-SAT computation"""
        return self._models

    def get_converter(self):
        """Returns the converter used for the normalization of T-atoms"""
        return self._converter

    def get_converted_atoms(self, atoms):
        """Returns a list of normalized atoms"""
        return [self._converter.convert(a) for a in atoms]