import os

from pysmt.shortcuts import read_smtlib

from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.tddnnf.theory_ddnnf import TheoryDDNNF

EXAMPLE_CODE = "22"


def main():
    # BUILD YOUR T-FORMULA FROM THE PYSMT LIBRARY
    phi = read_smtlib(
        f"/home/gabriele/Documents/phd/theorykc/tddnnf-testbench/data/benchmark/randgen/data/"
        f"problems_b10_r10_d4_m25_s1234/{EXAMPLE_CODE}/b10_d4_r10_s1234_{EXAMPLE_CODE}.smt2"
    )
    base_path = f"data/randgen{EXAMPLE_CODE}"
    os.makedirs(base_path)

    logger = {}

    # BUILD YOUR DD WITH THE CONSTRUCTOR

    tddnnf = TheoryDDNNF(
        phi,
        computation_logger=logger,
        base_out_path=base_path,
        store_tlemmas=True,
        stop_after_allsmt=True,
        solver=MathSATTotalEnumerator(),
    )

    # solver = Solver()
    # converter = solver.converter

    # phi = get_normalized(phi, converter)
    # phi_ddnnf = get_normalized(tddnnf.phi_ddnnf, converter)

    # p_atoms = set(phi.get_atoms())
    # t_atoms = set(phi_ddnnf.get_atoms())

    # print("Atoms difference:", t_atoms - p_atoms)
    # assert t_atoms.issubset(p_atoms), "d-DNNF contains atoms not in the original formula."

    # phi_atoms = set(tddnnf.phi.get_atoms())
    # lemmas = tddnnf.tlemmas
    # for lemma in lemmas:
    #     lemma_atoms = set(lemma.get_atoms())
    #     assert lemma_atoms.issubset(phi_atoms), "Lemma contains atoms not in the original formula."

    # USE YOUR t-d-DNNF
    # print("PHI:", phi)
    # print("d-DDNF PHI:", ddnnf.phi_ddnnf)

    # CHECK YOUR LOGGER
    print(logger)


if __name__ == "__main__":
    main()
