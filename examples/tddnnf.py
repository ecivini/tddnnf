from theorydd.tddnnf.theory_ddnnf import TheoryDDNNF
from pysmt.shortcuts import read_smtlib, And, Not, Iff, is_valid, Solver
from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.formula import get_normalized

EXAMPLE_CODE = "08"

def main():
    # BUILD YOUR T-FORMULA FROM THE PYSMT LIBRARY
    phi = read_smtlib(f"data/{EXAMPLE_CODE}/test.smt2")

    logger = {}

    # BUILD YOUR DD WITH THE CONSTRUCTOR
    tddnnf_builder = TheoryDDNNF(
        phi,
        computation_logger=logger,
        base_out_path=f"data/{EXAMPLE_CODE}",
        parallel_allsmt_procs=6,
        store_tlemmas=False,
        stop_after_allsmt=False
    )

    solver = Solver()
    converter = solver.converter
    phi = get_normalized(phi, converter)

    tddnnf = get_normalized(tddnnf_builder.phi_ddnnf, converter)

    p_atoms = set(phi.get_atoms())
    missing = set()
    for t_atom in tddnnf.get_atoms():
        if t_atom not in p_atoms:
            print("t_atom not in p_atoms:", t_atom)
            missing.add(t_atom)

    print("MISSING ATOMS:", missing)


    # USE YOUR t-d-DNNF
    # print("PHI:", phi)
    # print("d-DDNF PHI:", ddnnf.phi_ddnnf)

    # CHECK YOUR LOGGER
    print(logger)


if __name__ == "__main__":
    main()
