from typing import Dict, Tuple, List
import time
import logging
import os

from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.ddnnf.d4_compiler import D4Compiler
from pysmt.fnode import FNode
from pysmt.shortcuts import write_smtlib
from theorydd.solvers.solver import SMTEnumerator
from theorydd import formula
from theorydd.solvers.lemma_extractor import find_qvars, extract
from theorydd.formula import get_atoms
from theorydd.constants import SAT
import multiprocessing


class TheoryDDNNF():
    
    def __init__(
        self, 
        phi: FNode, 
        solver: MathSATExtendedPartialEnumerator | None = None,
        base_out_path: str | None = None,
        tlemmas: List[FNode] | None = None,
        load_lemmas: str | None = None,
        sat_result: bool | None = None,
        computation_logger: Dict | None = None,
        parallel_allsmt_procs: int = 1
    ) -> None:
        if not hasattr(self, "structure_name"):
            self.structure_name = "T-DDNNF"

        if not hasattr(self, "logger"):
            self.logger = logging.getLogger("theory_ddnnf")

        if solver is None:
            solver = MathSATExtendedPartialEnumerator()
    
        if computation_logger is None:
            computation_logger = {}
        if computation_logger.get(self.structure_name) is None:
            computation_logger[self.structure_name] = {}

        if parallel_allsmt_procs < 1 or parallel_allsmt_procs > multiprocessing.cpu_count():
            raise ValueError(
                "parallel_allsmt_procs must be between 1 and the number of CPU cores"
            )

        # NORMALIZE PHI
        phi = self._normalize_input(
            phi, solver, computation_logger[self.structure_name]
        )

        # LOAD LEMMAS
        tlemmas, sat_result = self._load_lemmas(
            phi,
            solver,
            parallel_allsmt_procs,
            tlemmas,
            load_lemmas,
            sat_result,
            computation_logger[self.structure_name],
        )
        self.sat_result = sat_result
        self.tlemmas = tlemmas

        # Compile to d-DNNF
        if sat_result == SAT:
            d4 = D4Compiler()
            self.phi_ddnnf, _, _ = d4.compile_dDNNF(
                phi=phi,
                tlemmas=tlemmas,
                back_to_fnode=True,
                computation_logger=computation_logger[self.structure_name],
                save_path=base_out_path
            )

            if base_out_path is not None:
                # Store the d-DNNF to a file
                tddnf_out_path = os.path.join(base_out_path, "tddnnf.smt2")
                write_smtlib(self.phi_ddnnf, tddnf_out_path)


    # Taken From theory_dd.py
    # TODO: Is there the need to create an abstract TDDNNF class containing these methods?
    def _normalize_input(
        self, phi: FNode, solver: SMTEnumerator, computation_logger: Dict
    ) -> FNode:
        """normalizes the input"""
        start_time = time.time()
        self.logger.info("Normalizing phi according to solver...")
        phi = formula.get_normalized(phi, solver.get_converter())
        elapsed_time = time.time() - start_time
        self.logger.info("Phi was normalized in %s seconds", str(elapsed_time))
        computation_logger["phi normalization time"] = elapsed_time
        return phi

    # Taken From theory_dd.py
    # TODO: Is there the need to create an abstract TDDNNF class containing these methods?
    def _load_lemmas(
        self,
        phi: FNode,
        smt_solver: SMTEnumerator,
        parallel_procs: int,
        tlemmas: List[FNode] | None,
        load_lemmas: str | None,
        sat_result: bool | None,
        computation_logger: Dict,
    ) -> Tuple[List[FNode], bool | None]:
        """loads the lemmas"""
        # LOADING LEMMAS
        start_time = time.time()
        self.logger.info("Loading Lemmas...")
        if tlemmas is not None:
            computation_logger["ALL SMT mode"] = "loaded"
        elif load_lemmas is not None:
            computation_logger["ALL SMT mode"] = "loaded"
            tlemmas = [formula.read_phi(load_lemmas)]
        else:
            computation_logger["ALL SMT mode"] = "computed"
            sat_result, tlemmas, _ = extract(
                phi,
                smt_solver,
                computation_logger=computation_logger,
                parallel_procs=parallel_procs
            )
        # tlemmas = list(
        #     map(
        #         lambda l: formula.get_normalized(l, smt_solver.get_converter()), tlemmas
        #     )
        # )
        # BASICALLY PADDING TO AVOID POSSIBLE ISSUES
        while len(tlemmas) < 2:
            tlemmas.append(formula.top())
        elapsed_time = time.time() - start_time
        self.logger.info("Lemmas loaded in %s seconds", str(elapsed_time))
        computation_logger["lemmas loading time"] = elapsed_time
        return tlemmas, sat_result
    
    # # Taken From theory_bdd.py
    # # TODO: Is there the need to create an abstract TDDNNF class containing these methods?
    # def _compute_mapping(
    #     self, atoms: List[FNode], computation_logger: dict
    # ) -> Dict[FNode, str]:
    #     """computes the mapping"""
    #     start_time = time.time()
    #     self.logger.info("Creating mapping...")
    #     mapping = {}

    #     string_generator = SequentialStringGenerator()
    #     for atom in atoms:
    #         mapping[atom] = string_generator.next_string()
    #     elapsed_time = time.time() - start_time
    #     self.logger.info("Mapping created in %s seconds", str(elapsed_time))
    #     computation_logger["variable mapping creation time"] = elapsed_time
    #     return mapping