from theorydd.tddnnf.theory_ddnnf import TheoryDDNNF
from pysmt.shortcuts import read_smtlib

EXAMPLE_CODE = "07"

def main():
    # BUILD YOUR T-FORMULA FROM THE PYSMT LIBRARY
    phi = read_smtlib(f"data/{EXAMPLE_CODE}/test.smt2")

    logger = {}

    # BUILD YOUR DD WITH THE CONSTRUCTOR
    tddnnf = TheoryDDNNF(
        phi,
        computation_logger=logger,
        base_out_path=f"data/{EXAMPLE_CODE}",
        parallel_allsmt_procs=12,
        store_tlemmas=True,
        stop_after_allsmt=True,
    )

    phi_atoms = set(tddnnf.phi.get_atoms())
    lemmas = tddnnf.tlemmas
    for lemma in lemmas:
        lemma_atoms = set(lemma.get_atoms())
        assert lemma_atoms.issubset(phi_atoms), "Lemma contains atoms not in the original formula."

    # USE YOUR t-d-DNNF
    # print("PHI:", phi)
    # print("d-DDNF PHI:", ddnnf.phi_ddnnf)

    # CHECK YOUR LOGGER
    print(logger)


if __name__ == "__main__":
    main()
