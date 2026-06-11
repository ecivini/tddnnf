import argparse

from pysmt.shortcuts import Solver, read_smtlib, reset_env

from theorydd.formula import get_normalized
from enumerators.solvers.mathsat_total import MathSATTotalEnumerator
from enumerators.solvers.with_partitioning import WithPartitioningWrapper, partition_atoms
import os


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("input_dir", type=str, help="Input directory containing SMT files")
    return parser.parse_args()


def get_files(input_dir: str) -> list[str]:
    if os.path.isfile(input_dir) and input_dir.endswith(".smt2"):
        return [input_dir]
    smt_files = []
    for root, _, files in os.walk(input_dir):
        for file in files:
            if file.endswith(".smt2"):
                smt_files.append(os.path.join(root, file))
    return smt_files


def main() -> None:
    args = parse_args()
    input_dir = args.input_dir
    smt_files = get_files(input_dir)
    n_partitionable = 0
    for smt_file in smt_files:
        reset_env()
        phi = read_smtlib(smt_file)
        with Solver("msat") as msat:
            phi = get_normalized(phi, msat.converter)
        atoms = phi.get_atoms()
        partitions = partition_atoms(atoms)
        if len(partitions) > 1:
            n_partitionable += 1
            print(f"File: {smt_file} has {len(partitions)} partitions:")
            for i, (_, partition) in enumerate(partitions.items()):
                print(f"  Partition {i + 1}: {len(partition)} atoms: {', '.join(str(atom) for atom in partition)}")

        solver = WithPartitioningWrapper(
            # MathSATExtendedPartialEnumerator(project_on_theory_atoms=True, parallel_procs=1),
            MathSATTotalEnumerator()
        )

        solver.check_all_sat(phi, atoms=list(atoms))

    print(f"Total partitionable files: {n_partitionable} out of {len(smt_files)}")


if __name__ == "__main__":
    main()
