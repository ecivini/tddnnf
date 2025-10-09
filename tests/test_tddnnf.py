"""tests for T-dDNNF"""

import os
from theorydd.tddnnf.theory_ddnnf import TheoryDDNNF
import theorydd.formula as formula
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from pysmt.shortcuts import Or, LT, REAL, Symbol, And, Not, Equals, Real
from theorydd.constants import SAT
from pathlib import Path
import pytest

test_data = [
    (
        Or(  # SAT
            LT(Symbol("X", REAL), Symbol("Y", REAL)),
            LT(Symbol("Y", REAL), Symbol("Zr", REAL)),
            LT(Symbol("Zr", REAL), Symbol("X", REAL)),
            Equals(Symbol("X", REAL), Real(5))
        ),
        "./ddnnf_sat.smt",
    ),

    (
        And(  # UNSAT
            LT(Symbol("X", REAL), Symbol("Y", REAL)),
            LT(Symbol("Y", REAL), Symbol("Zr", REAL)),
            LT(Symbol("Zr", REAL), Symbol("X", REAL)),
        ),
        "./ddnnf_unsat.smt", # This should not be generated
    ),

    (
        Or(  # VALID
            LT(Symbol("X", REAL), Symbol("Y", REAL)),
            Not(LT(Symbol("X", REAL), Symbol("Y", REAL))),
        ),
        "./ddnnf_valid.smt",
    ),

    (
        formula.read_phi("./tests/items/rng.smt"),
        "./ddnnf_rng.smt",
    )
]


@pytest.mark.parametrize("phi,out", test_data)
def test_init_models_total(phi, out):
    total = MathSATTotalEnumerator()
    total.check_all_sat(phi, None)
    tddnnf = TheoryDDNNF(phi, solver=total, out_path=out)
    
    print("T-DDNNF result:", tddnnf.sat_result)
    print("T-DDNNF tlemmas:", tddnnf.tlemmas)

    if tddnnf.sat_result == SAT:
        print("T_DDNNF compiled:", tddnnf.phi_ddnnf)
        assert os.path.isfile(out)
        Path.unlink(out)
    else:
        assert not hasattr(tddnnf, "phi_ddnnf")
        assert os.path.isfile(out) == False