import os

from pysmt.shortcuts import read_smtlib

from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.tddnnf.theory_ddnnf import TheoryDDNNF

EXAMPLE_CODE = "09"


def main():
    # BUILD YOUR T-FORMULA FROM THE PYSMT LIBRARY
    phi = read_smtlib(f"data/{EXAMPLE_CODE}/test.smt2")

    logger = {}

    # BUILD YOUR DD WITH THE CONSTRUCTOR

    tddnnf = TheoryDDNNF(
        phi,
        computation_logger=logger,
        base_out_path=f"data/{EXAMPLE_CODE}",
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
