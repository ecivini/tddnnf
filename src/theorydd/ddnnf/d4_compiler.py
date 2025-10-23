"""midddleware for pysmt-d4 compatibility"""

import json
import logging
import os
import time
from typing import Dict, List, Set, Tuple, TypeVar
from dataclasses import dataclass
from pysmt.shortcuts import (
    And,
    Or,
    get_atoms,
    TRUE,
    FALSE,
    Not,
)
from pysmt.fnode import FNode
from pysmt.walkers import DagWalker
from allsat_cnf.label_cnfizer import LabelCNFizer
from theorydd.formula import (
    save_refinement,
    load_refinement,
    get_phi_and_lemmas,
    get_normalized,
)
from theorydd.walkers.walker_bcs12 import BCS12Walker
from theorydd.constants import (
    UNSAT,
    D4_COMMAND as _D4_COMMAND,
    D4_AND_NODE as _D4_AND_NODE,
    D4_OR_NODE as _D4_OR_NODE,
    D4_TRUE_NODE as _D4_TRUE_NODE,
    D4_FALSE_NODE as _D4_FALSE_NODE,
    RE_NNF_EDGE as _RE_NNF_EDGE,
)
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator

from theorydd.ddnnf.ddnnf_compiler import DDNNFCompiler

_SelfD4Node = TypeVar("SelfD4Node", bound="D4Node")

@dataclass
class D4Node:
    """a node that results from a d4 compilation process"""

    node_type: int
    edges: Dict[int, List[int]]
    memo: None | FNode

    def __init__(self, node_type: int):
        # check if d4 is available and executable
        if not os.path.isfile(_D4_COMMAND):
            raise FileNotFoundError(
                'The binary for the d4 compiler is missing. Please run "theorydd_install --d4" to install or install manually.'
            )
        if not os.access(_D4_COMMAND, os.X_OK):
            raise PermissionError(
                "The d4 binary is not executable. Please check the permissions for the file and grant execution rights."
            )
        super().__init__()
        self.node_type = node_type
        self.edges = {}
        self.memo = None

    def is_ready(self) -> bool:
        """checks if the result for this node has already been computed"""
        return self.memo is not None

    def add_edge(self, dst: int, label: List[int]) -> None:
        """adds an edge to the node"""
        self.edges[dst] = label

    def to_pysmt(
        self, mapping: Dict[int, FNode], graph: Dict[int, _SelfD4Node]
    ) -> FNode:
        """
        translates the D4Node into a pysmt formula recirsively with memoization

        Args:
            mapping (Dict[int,FNode]) -> a mapping that associates to integers a pysmt atom,
                used to translate the variables from their abstraction in the nnf format to pysmt
            graph (Dict[int,D4Node]) -> the graph containing all the nodes

        Returns:
            (FNode) -> the pysmt formula corresponding to the node
        """
        if self.is_ready():
            return self.memo
        if self.node_type == _D4_TRUE_NODE:
            self.memo = TRUE()
        elif self.node_type == _D4_FALSE_NODE:
            self.memo = FALSE()
        elif self.node_type == _D4_AND_NODE:
            children_pysmts = []
            for dst in self.edges.keys():
                children_pysmts.append(graph[dst].to_pysmt(mapping, graph))
            if len(children_pysmts) == 0:
                raise ValueError("AND node with no children")
            self.memo = And(*children_pysmts)
        elif self.node_type == _D4_OR_NODE:
            children_pysmts = []
            for dst, label in self.edges.items():
                child_translation = graph[dst].to_pysmt(mapping, graph)
                var_pysmts = []
                for item in label:
                    if item < 0:
                        var_pysmts.append(Not(mapping[abs(item)]))
                    else:
                        var_pysmts.append(mapping[item])
                if len(var_pysmts) == 0:
                    children_pysmts.append(child_translation)
                else:
                    children_pysmts.append(And(*var_pysmts, child_translation))
            if len(children_pysmts) == 0:
                raise ValueError("OR node with no children")
            self.memo = Or(*children_pysmts)
        return self.memo


class D4Compiler(DDNNFCompiler):
    """D4 compiler implementation for the DDNNFCompiler interface"""

    def __init__(self):
        self.important_atoms_labels = []
        self.normalizer_solver = MathSATTotalEnumerator()
        super().__init__()
        self.logger = logging.getLogger("d4_ddnnf_compiler")

    def from_pysmt_to_bcs12(
        self,
        phi: FNode,
        bcs12_out_file_path: str,
        tlemmas: List[FNode] | None = None,
        do_not_quantify: bool = False,
    ) -> None:
        """
        Parses a pysmt formula and saves it in bcs12 format.
        Reference: https://github.com/crillab/d4v2?tab=readme-ov-file#1-circuit-format

        Args:
            phi (FNode) -> the input formula
            bcs12_out_file_path (str) -> the path to the file where the bcs12 output need to be saved
            tlemmas (List[FNode] | None) = None -> a list of theory lemmas to be added to the formula
        """
        phi_atoms: frozenset = get_atoms(phi)
        if tlemmas is not None:
            phi_and_lemmas = get_phi_and_lemmas(phi, tlemmas)
            phi_and_lemmas = get_normalized(phi_and_lemmas, self.normalizer_solver.get_converter())
        else:
            phi_and_lemmas = phi

        if do_not_quantify:
            fresh_atoms:Set[FNode] = frozenset()
        else:
            fresh_atoms: Set[FNode] = frozenset(phi_atoms)

        important_atoms_labels: List[int] = []

        # create mapping
        count = 1
        self.abstraction = {}
        for atom in phi_atoms:
            if atom not in fresh_atoms:
                important_atoms_labels.append(count)
            self.abstraction[atom] = count
            count += 1

        self.refinement = {v: k for k, v in self.abstraction.items()}
        self.important_atoms_labels = important_atoms_labels

        # Use the BCS12Walker to traverse the formula
        walker = BCS12Walker(self.abstraction, phi_atoms)
        root = walker.walk(phi_and_lemmas)

        # Now write file
        with open(bcs12_out_file_path, "w") as f:
            f.write("c BC-S1.2\n")
            # Input variable declarations
            for v in phi_atoms:
                name = f"v{self.abstraction[v]}"
                f.write(f"I {name}\n")

            # Gate definitions
            for ln in walker.gate_lines:
                f.write(ln + "\n")

            # Final target
            f.write(f"T {root}\n")


    def from_nnf_to_pysmt(self, nnf_file: str) -> Tuple[FNode, int, int]:
        """
        Translates the formula contained in the file d4_file from nnf format to a pysmt FNode

        Args:
            nnf_file (str) -> the path to the file where the dimacs output need to be saved

        Returns:
            (FNode) -> the pysmt formula read from the file
            (int) -> the amount of nodes in the dDNNF
            (int) -> the amount of edges in the dDNNF
        """
        with open(nnf_file, "r", encoding="utf8") as data:
            lines: List[str] = data.readlines()
        lines = list(filter(lambda x: x != "", lines))
        total_nodes = 0
        total_arcs = 0
        d4_graph: Dict[int, D4Node] = {}
        for line in lines:
            if line.startswith("o"):
                # OR NODE
                total_nodes += 1
                tokens = line.split(" ")
                if len(tokens) != 3:
                    raise ValueError(
                        "Invalid d4 format: OR node with wrong number of tokens"
                    )
                node_id = int(tokens[1])
                d4_graph[node_id] = D4Node(_D4_OR_NODE)
            elif line.startswith("a"):
                # AND NODE
                total_nodes += 1
                tokens = line.split(" ")
                if len(tokens) != 3:
                    raise ValueError(
                        "Invalid d4 format: AND node with wrong number of tokens"
                    )
                node_id = int(tokens[1])
                d4_graph[node_id] = D4Node(_D4_AND_NODE)
            elif line.startswith("f"):
                # FALSE NODE
                total_nodes += 1
                tokens = line.split(" ")
                if len(tokens) != 3:
                    raise ValueError(
                        "Invalid d4 format: FALSE node with wrong number of tokens"
                    )
                node_id = int(tokens[1])
                d4_graph[node_id] = D4Node(_D4_FALSE_NODE)
            elif line.startswith("t"):
                # TRUE NODE
                total_nodes += 1
                tokens = line.split(" ")
                if len(tokens) != 3:
                    raise ValueError(
                        "Invalid d4 format: TRUE node with wrong number of tokens"
                    )
                node_id = int(tokens[1])
                d4_graph[node_id] = D4Node(_D4_TRUE_NODE)
            elif line[0].isdigit():
                # ARC
                total_arcs += 1
                tokens = line.split(" ")
                if len(tokens) < 3:
                    raise ValueError(
                        "Invalid d4 format: ARC with insufficient amount of tokens"
                    )
                src_id = int(tokens[0])  # source node
                dst_id = int(tokens[1])  # destination node
                label = list(map(int, tokens[2:]))
                # remove last item from label since it is the 0
                label.pop()
                d4_graph[src_id].add_edge(dst_id, label)

        # DFS TO COMPUTE FORMULA
        # 1 is always the id of the root node after D4 compilation
        pysmt_node = d4_graph[1].to_pysmt(self.refinement, d4_graph)

        return pysmt_node, total_nodes, total_arcs

    def count_nodes_and_edges_from_nnf(self, nnf_file: str) -> Tuple[int, int]:
        """
        Counts nodes and edges of the formula contained in the file d4_file from nnf format to a pysmt FNode

        Args:
            nnf_file (str) -> the path to the file where the dimacs output needs to be saved

        Returns:
            (int,int) -> the total nodes and edges of the formula (#nodes,#edges)
        """
        total_nodes = 0
        total_edges = 0
        with open(nnf_file, "r", encoding="utf8") as data:
            contents = data.read()
        lines: List[str] = contents.split("\n")
        lines = list(filter(lambda x: x != "", lines))
        for line in lines:
            if (
                line.startswith("f")
                or line.startswith("o")
                or line.startswith("t")
                or line.startswith("a")
            ):
                total_nodes += 1
            elif line[0].isdigit():
                total_edges += 1
        return (total_nodes, total_edges)

    def compile_dDNNF(
        self,
        phi: FNode,
        tlemmas: List[FNode] | None = None,
        save_path: str | None = None,
        back_to_fnode: bool = False,
        sat_result: bool | None = None,
        quantify_tseitsin: bool = False,
        do_not_quantify: bool = False,
        computation_logger: Dict | None = None,
        timeout: int = 3600,
    ) -> Tuple[FNode | None, int, int]:
        """
        Compiles an FNode in dDNNF through the d4 compiler

        Args:
            phi (FNode) -> a pysmt formula
            tlemmas (List[FNode] | None) = None -> a list of theory lemmas to be added to the formula
            save_path (str | None) = None -> the path where dDNNF data will be saved.
                If it is set to None a random temporary folder starting with temp_ will be created
                and deleted once the computation ends
            back_to_fnode (bool) = True -> set it to False to avoid the final pysmt translation
            sat_result: (bool | None) = None -> the result of the SAT check on the formula
            quantify_tseitsin (bool) = False -> set it to True to quantify over the tseitsin variables
                during dDNNF compilation
            do_not_quantify (bool) = False -> set it to True to avoid quantifying over any fresh variable
            computation_logger (Dict | None) = None -> a dictionary that will be filled with
                data about the computation
            timeout (int) = 3600 -> the maximum time in seconds the computation is allowed to run

        Returns:
            (FNode | None) -> the input pysmt formula in dDNNF, or None if back_to_fnode is False
            (int) -> the number of nodes in the dDNNF
            (int) -> the number of edges in the dDNNF
        """

        # failsafe for computation_logger
        if computation_logger is None:
            computation_logger = {}

        computation_logger["dDNNF compiler"] = "d4"

        # choose temporary folder
        tmp_folder = self._choose_tmp_folder(save_path) 

        # translate to BC-S1.2 and get mapping used for translation
        if not os.path.exists(tmp_folder):
            os.mkdir(tmp_folder)
        start_time = time.time()
        self.logger.info("Translating to BC-S1.2...")
        #phi = get_normalized(phi, self.normalizer_solver.get_converter())
        self.from_pysmt_to_bcs12(
            phi,
            f"{tmp_folder}/circuit.bc",
            tlemmas,
            do_not_quantify=do_not_quantify,
        )
        elapsed_time = time.time() - start_time
        computation_logger["BC-S1.2 translation time"] = elapsed_time
        self.logger.info(
            "BC-S1.2 translation completed in %s seconds", str(elapsed_time)
        )

        # save mapping for refinement
        start_time = time.time()
        if not os.path.exists(f"{tmp_folder}/mapping"):
            os.mkdir(f"{tmp_folder}/mapping")
        self.logger.info("Saving refinement...")
        save_refinement(self.refinement, f"{tmp_folder}/mapping/mapping.json")
        with open(
            f"{tmp_folder}/mapping/important_labels.json", "w", encoding="utf8"
        ) as f:
            json.dump(self.important_atoms_labels, f)
        elapsed_time = time.time() - start_time
        self.logger.info("Refinement saved in %s seconds", str(elapsed_time))
        computation_logger["refinement serialization time"] = elapsed_time

        # call d4 for compilation
        # output should be in file temp_folder/compilation_output.nnf
        start_time = time.time()
        self.logger.info("Compiling dDNNF...")
        timeout_string = ""
        if timeout > 0:
            timeout_string = f"timeout {timeout}s "
        result = os.system(
            f"{timeout_string}{_D4_COMMAND} -i {tmp_folder}/circuit.bc --input-type circuit --dump-file {tmp_folder}/compilation_output.nnf > /dev/null"
        )
        if result != 0:
            if save_path is None:
                self._clean_tmp_folder(tmp_folder)
            raise TimeoutError("d4 compilation failed: timeout")
        elapsed_time = time.time() - start_time
        computation_logger["dDNNF compilation time"] = elapsed_time
        self.logger.info("dDNNF compilation completed in %s seconds", str(elapsed_time))

        # fix output
        self._fix_ddnnf(f"{tmp_folder}/compilation_output.nnf", get_atoms(phi))

        # return if not back to fnode
        if not back_to_fnode:
            nodes, edges = self.count_nodes_and_edges_from_nnf(
                f"{tmp_folder}/compilation_output.nnf"
            )
            return None, nodes, edges

        # translate to pysmt
        start_time = time.time()
        self.logger.info("Translating to pysmt...")
        phi_ddnnf, nodes, edges = self.from_nnf_to_pysmt(
            f"{tmp_folder}/compilation_output.nnf"
        )
        if save_path is None:
            self._clean_tmp_folder(tmp_folder)
        elapsed_time = time.time() - start_time
        computation_logger["pysmt translation time"] = elapsed_time
        self.logger.info("pysmt translation completed in %s seconds", str(elapsed_time))
        return phi_ddnnf, nodes, edges

    def load_dDNNF(self, nnf_path: str, mapping_path: str) -> FNode:
        """
        Load a dDNNF from file and translate it to pysmt

        Args:
            nnf_path (str) ->       the path to the file containing the dDNNF in
                                    NNF format provided by the d4 compiler
            mapping_path (str) ->   the path to the file containing the mapping

        Returns:
            (FNode) -> the pysmt formula translated from the dDNNF
        """
        self.refinement = load_refinement(mapping_path)
        self.abstraction = {v: k for k, v in self.refinement.items()}
        return self.from_nnf_to_pysmt(nnf_path)

    def _fix_ddnnf(self, nnf_file: str, projected_vars: set[FNode]):
        """
        Author: Masinag

        The d-DNNF output by d4 can contain variables that are not in the projected variables set.
        However, it should be safe to simply remove them from the d-DNNF file.

        Args:
            nnf_file (str) -> the path to the nnf file where the ddnnf is stored
            var_map (Dict[FNode,int]) -> a mapping between nodes and integers
            projected_vars (Set[Fnode]) -> the set of variables that have to be kept
        """
        with open(nnf_file, "r", encoding="utf8") as f:
            lines = f.readlines()

        projected_ids: Set[int] = {self.abstraction[v] for v in projected_vars}

        with open(nnf_file, "w", encoding="utf8") as f:
            for line in lines:
                if m := _RE_NNF_EDGE.match(line):
                    a, b, ll = m.groups()
                    f.write(f"{a} {b}")
                    for l in (ll or "").split():
                        i = int(l)
                        a = abs(i)
                        s = 1 if i > 0 else -1
                        if a in projected_ids:
                            f.write(f" {s * a}")
                    f.write(" 0\n")
                else:
                    f.write(line)


if __name__ == "__main__":
    from theorydd.formula import read_phi

    test_phi = read_phi("input/shortest_path.smt")

    print(test_phi.serialize())

    d4_compiler = D4Compiler()

    _phi_ddnnf, _a, _b = d4_compiler.compile_dDNNF(
        test_phi, None, back_to_fnode=False, save_path="tmp"
    )
