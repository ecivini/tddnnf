import itertools as it
import time
from typing import List

from pysmt.fnode import FNode
from pysmt.shortcuts import And

from theorydd.formula import get_theory_atoms
from theorydd.solvers.solver import SMTEnumerator


class UnionFind:
    def __init__(self):
        self.parent = {}

    def find(self, item):
        if item not in self.parent:
            self.parent[item] = item
        if self.parent[item] != item:
            self.parent[item] = self.find(self.parent[item])
        return self.parent[item]

    def union(self, item1, item2):
        root1 = self.find(item1)
        root2 = self.find(item2)
        if root1 != root2:
            self.parent[root2] = root1


class WithPartitioningWrapper(SMTEnumerator):

    def __init__(self, base_solver: SMTEnumerator, computation_logger: dict | None = None):
        super().__init__(computation_logger)
        self._base_solver = base_solver
        self._project_on_theory_atoms = True
        self._tlemmas = []
        self._models = []
        self._models_count = 0

    def reset(self):
        self._tlemmas = []
        self._models = []
        self._models_count = 0
        self._base_solver.reset()

    def check_all_sat(self, phi, atoms=None, store_models=False) -> bool:
        self.reset()
        # Partition atoms based on their variables
        start_time = time.time()
        uf = UnionFind()
        all_vars = set()
        atoms = phi.get_atoms() if atoms is None else atoms
        atoms = get_theory_atoms(atoms)
        for atom in atoms:
            theory_vars = [v for v in atom.get_free_variables()]
            all_vars.update(theory_vars)
            for v1, v2 in it.combinations(theory_vars, 2):
                uf.union(v1, v2)

        partitions = {}
        for atom in atoms:
            root = uf.find(next(iter(atom.get_free_variables())))
            if root not in partitions:
                partitions[root] = []
            partitions[root].append(atom)
        end_time = time.time()
        if self._computation_logger is not None:
            self._computation_logger["Partitioning time"] = end_time - start_time
            self._computation_logger["Number of partitions"] = len(partitions)

        # Solve each partition separately
        overall_result = True
        for part_atoms in sorted(partitions.values(), key=lambda x: len(x)):
            self._base_solver.reset()
            result = self._base_solver.check_all_sat(And(phi, *self._tlemmas), part_atoms, store_models)
            if not result:
                overall_result = False
            self._tlemmas.extend(self._base_solver.get_theory_lemmas())
            self._models_count += self._base_solver.get_models_count()
            if store_models:
                self._models.extend(self._base_solver.get_models())
        return overall_result

    def get_theory_lemmas(self) -> List[FNode]:
        return self._tlemmas

    def get_converter(self) -> object:
        return self._base_solver.get_converter()

    def get_models(self) -> List:
        return self._models

    def get_models_count(self) -> int:
        return self._models_count
