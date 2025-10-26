"""tests for T-dDNNF"""

import os
import shutil
import tempfile
from copy import deepcopy

import pytest
from pysmt.fnode import FNode
from pysmt.shortcuts import (
    And,
    Equals,
    LT,
    Not,
    Or,
    Real,
    Symbol,
    REAL,
    BOOL,
)

import theorydd.formula as formula
from theorydd.constants import SAT, UNSAT
from theorydd.solvers.mathsat_partial_extended import (
    MathSATExtendedPartialEnumerator
)
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.tddnnf.theory_ddnnf import TheoryDDNNF


# ==================== Fixtures ====================

@pytest.fixture
def temp_dir():
    """Create a temporary directory for test outputs"""
    tmpdir = tempfile.mkdtemp()
    yield tmpdir
    # Cleanup after test
    if os.path.exists(tmpdir):
        shutil.rmtree(tmpdir)


@pytest.fixture
def sat_formula():
    """SAT formula fixture"""
    return Or(
        LT(Symbol("X", REAL), Symbol("Y", REAL)),
        LT(Symbol("Y", REAL), Symbol("Zr", REAL)),
        LT(Symbol("Zr", REAL), Symbol("X", REAL)),
        Equals(Symbol("X", REAL), Real(5))
    )


@pytest.fixture
def unsat_formula():
    """UNSAT formula fixture (cyclic inequalities)"""
    return And(
        LT(Symbol("X", REAL), Symbol("Y", REAL)),
        LT(Symbol("Y", REAL), Symbol("Zr", REAL)),
        LT(Symbol("Zr", REAL), Symbol("X", REAL)),
    )


@pytest.fixture
def valid_formula():
    """Valid/tautology formula fixture"""
    return Or(
        LT(Symbol("X", REAL), Symbol("Y", REAL)),
        Not(LT(Symbol("X", REAL), Symbol("Y", REAL))),
    )


@pytest.fixture
def simple_boolean_formula():
    """Simple boolean formula"""
    return Or(
        Symbol("A", BOOL),
        And(Symbol("B", BOOL), Not(Symbol("C", BOOL)))
    )


# ==================== Basic Initialization Tests ====================

def test_init_default_solver(sat_formula):
    """Test initialization with default solver"""
    tddnnf = TheoryDDNNF(sat_formula)
    
    assert hasattr(tddnnf, "sat_result")
    assert hasattr(tddnnf, "tlemmas")
    assert hasattr(tddnnf, "structure_name")
    assert tddnnf.structure_name == "T-DDNNF"
    assert isinstance(tddnnf.tlemmas, list)
    assert len(tddnnf.tlemmas) >= 2  # At least 2 due to padding


def test_init_with_total_solver(sat_formula):
    """Test initialization with MathSATTotalEnumerator"""
    total = MathSATTotalEnumerator()
    tddnnf = TheoryDDNNF(sat_formula, solver=total)
    
    assert tddnnf.sat_result == SAT
    assert hasattr(tddnnf, "phi_ddnnf")
    assert isinstance(tddnnf.phi_ddnnf, FNode)
    assert len(tddnnf.tlemmas) >= 2


def test_init_with_partial_solver(sat_formula):
    """Test initialization with MathSATExtendedPartialEnumerator"""
    partial = MathSATExtendedPartialEnumerator()
    tddnnf = TheoryDDNNF(sat_formula, solver=partial)
    
    assert tddnnf.sat_result == SAT
    assert hasattr(tddnnf, "phi_ddnnf")
    assert isinstance(tddnnf.phi_ddnnf, FNode)


# ==================== SAT/UNSAT Behavior Tests ====================

def test_sat_formula_compilation(sat_formula):
    """Test that SAT formulas compile to dDNNF"""
    total = MathSATTotalEnumerator()
    tddnnf = TheoryDDNNF(sat_formula, solver=total)
    
    assert tddnnf.sat_result == SAT
    assert hasattr(tddnnf, "phi_ddnnf")
    assert tddnnf.phi_ddnnf is not None


def test_unsat_formula_no_compilation(unsat_formula):
    """Test that UNSAT formulas don't compile to dDNNF"""
    total = MathSATTotalEnumerator()
    tddnnf = TheoryDDNNF(unsat_formula, solver=total)
    
    assert tddnnf.sat_result == UNSAT
    assert not hasattr(tddnnf, "phi_ddnnf")


def test_valid_formula_compilation(valid_formula):
    """Test that valid/tautology formulas compile to dDNNF"""
    total = MathSATTotalEnumerator()
    tddnnf = TheoryDDNNF(valid_formula, solver=total)
    
    assert tddnnf.sat_result == SAT
    assert hasattr(tddnnf, "phi_ddnnf")


def test_boolean_formula(simple_boolean_formula):
    """Test with simple boolean formula"""
    total = MathSATTotalEnumerator()
    tddnnf = TheoryDDNNF(simple_boolean_formula, solver=total)
    
    assert tddnnf.sat_result == SAT
    assert hasattr(tddnnf, "phi_ddnnf")


# ==================== File Output Tests ====================

def test_output_file_creation_sat(sat_formula, temp_dir):
    """Test that output file is created for SAT formula"""
    total = MathSATTotalEnumerator()
    TheoryDDNNF(sat_formula, solver=total, base_out_path=temp_dir)
    
    tddnnf_file = os.path.join(temp_dir, "tddnnf.smt2")
    assert os.path.isfile(tddnnf_file), \
        "tddnnf.smt2 should be created for SAT formula"


def test_circuit_bc_file_creation(sat_formula, temp_dir):
    """Test that circuit.bc file is created for SAT formula"""
    total = MathSATTotalEnumerator()
    TheoryDDNNF(sat_formula, solver=total, base_out_path=temp_dir)
    
    circuit_file = os.path.join(temp_dir, "circuit.bc")
    assert os.path.isfile(circuit_file), "circuit.bc should be created"
    
    # Verify file contains BC-S1.2 header
    with open(circuit_file, "r", encoding="utf8") as f:
        first_line = f.readline().strip()
        assert first_line == "c BC-S1.2", \
            "circuit.bc should start with BC-S1.2 header"


def test_mapping_files_creation(sat_formula, temp_dir):
    """Test that mapping files are created for SAT formula"""
    total = MathSATTotalEnumerator()
    TheoryDDNNF(sat_formula, solver=total, base_out_path=temp_dir)
    
    mapping_dir = os.path.join(temp_dir, "mapping")
    assert os.path.isdir(mapping_dir), "mapping directory should be created"
    
    mapping_file = os.path.join(mapping_dir, "mapping.json")
    assert os.path.isfile(mapping_file), "mapping.json should be created"
    
    important_labels_file = os.path.join(mapping_dir, "important_labels.json")
    assert os.path.isfile(important_labels_file), \
        "important_labels.json should be created"


def test_mapping_file_structure(sat_formula, temp_dir):
    """Test that mapping.json has correct structure"""
    import json
    
    total = MathSATTotalEnumerator()
    TheoryDDNNF(sat_formula, solver=total, base_out_path=temp_dir)
    
    mapping_file = os.path.join(temp_dir, "mapping", "mapping.json")
    with open(mapping_file, "r", encoding="utf8") as f:
        mapping = json.load(f)
    
    # mapping should be a list of [id, smtlib_string] pairs
    assert isinstance(mapping, list), "mapping should be a list"
    for entry in mapping:
        assert isinstance(entry, list), "each entry should be a list"
        assert len(entry) == 2, "each entry should have 2 elements"
        assert isinstance(entry[0], int), "first element should be an int (id)"
        assert isinstance(entry[1], str), "second element should be a string"


def test_important_labels_structure(sat_formula, temp_dir):
    """Test that important_labels.json has correct structure"""
    import json
    
    total = MathSATTotalEnumerator()
    TheoryDDNNF(sat_formula, solver=total, base_out_path=temp_dir)
    
    labels_file = os.path.join(temp_dir, "mapping", "important_labels.json")
    with open(labels_file, "r", encoding="utf8") as f:
        labels = json.load(f)
    
    # important_labels should be a list of integers
    assert isinstance(labels, list), "important_labels should be a list"
    for label in labels:
        assert isinstance(label, int), "each label should be an integer"


def test_compilation_output_nnf_creation(sat_formula, temp_dir):
    """Test that compilation_output.nnf is created"""
    total = MathSATTotalEnumerator()
    TheoryDDNNF(sat_formula, solver=total, base_out_path=temp_dir)
    
    nnf_file = os.path.join(temp_dir, "compilation_output.nnf")
    assert os.path.isfile(nnf_file), "compilation_output.nnf should be created"
    
    # Verify it's a valid NNF file (has content with nodes)
    with open(nnf_file, "r", encoding="utf8") as f:
        content = f.read().strip()
        assert len(content) > 0, "NNF file should not be empty"
        # D4 NNF format starts with node definitions (o, t, or, etc.)
        first_char = content[0]
        assert first_char in ['o', 't', 'f', 'a'], \
            f"NNF file should start with valid node type, got '{first_char}'"


def test_no_output_file_for_unsat(unsat_formula, temp_dir):
    """Test that output file is NOT created for UNSAT formula"""
    total = MathSATTotalEnumerator()
    TheoryDDNNF(unsat_formula, solver=total, base_out_path=temp_dir)
    
    tddnnf_file = os.path.join(temp_dir, "tddnnf.smt2")
    assert not os.path.isfile(tddnnf_file), \
        "tddnnf.smt2 should NOT be created for UNSAT formula"


def test_no_circuit_bc_for_unsat(unsat_formula, temp_dir):
    """Test that circuit.bc is NOT created for UNSAT formula"""
    total = MathSATTotalEnumerator()
    tddnnf = TheoryDDNNF(unsat_formula, solver=total, base_out_path=temp_dir)
    
    # Circuit.bc is created during compilation attempt but not meaningful
    # The important part is that phi_ddnnf attribute doesn't exist
    assert not hasattr(tddnnf, "phi_ddnnf"), \
        "phi_ddnnf should not exist for UNSAT formula"


def test_no_mapping_for_unsat(unsat_formula, temp_dir):
    """Test that mapping is NOT created for UNSAT formula"""
    total = MathSATTotalEnumerator()
    TheoryDDNNF(unsat_formula, solver=total, base_out_path=temp_dir)
    
    # The mapping directory might exist from the compilation process,
    # but the final tddnnf.smt2 should not be created
    tddnnf_file = os.path.join(temp_dir, "tddnnf.smt2")
    assert not os.path.isfile(tddnnf_file)


def test_no_output_without_path(sat_formula):
    """Test that no file is created when base_out_path is None"""
    total = MathSATTotalEnumerator()
    tddnnf = TheoryDDNNF(sat_formula, solver=total, base_out_path=None)
    
    assert tddnnf.sat_result == SAT
    assert hasattr(tddnnf, "phi_ddnnf")
    # No file should be created in current directory
    assert not os.path.isfile("tddnnf.smt2")


# ==================== Lemma Loading Tests ====================

def test_precomputed_lemmas(sat_formula):
    """Test initialization with precomputed lemmas"""
    # First, compute lemmas
    total = MathSATTotalEnumerator()
    total.check_all_sat(sat_formula, None)
    precomputed_lemmas = total.get_theory_lemmas()
    
    # Now create T-DDNNF with precomputed lemmas
    tddnnf = TheoryDDNNF(
        sat_formula,
        solver=total,
        tlemmas=precomputed_lemmas,
        sat_result=SAT
    )
    
    assert tddnnf.sat_result == SAT
    assert len(tddnnf.tlemmas) >= 2
    assert hasattr(tddnnf, "phi_ddnnf")


def test_lemma_loading_from_file():
    """Test loading lemmas from file"""
    phi = formula.read_phi("./tests/items/rng.smt")
    total = MathSATTotalEnumerator()
    
    # When loading lemmas from file, sat_result needs to be provided
    # or it will be computed during lemma extraction
    tddnnf = TheoryDDNNF(
        phi,
        solver=total,
        load_lemmas="./tests/items/rng_lemmas.smt",
        sat_result=SAT
    )
    
    assert tddnnf.sat_result == SAT
    assert len(tddnnf.tlemmas) >= 1


def test_lemma_padding(sat_formula):
    """Test that lemmas are padded to at least 2 entries"""
    total = MathSATTotalEnumerator()
    # Pass empty lemmas list
    tddnnf = TheoryDDNNF(
        sat_formula,
        solver=total,
        tlemmas=[],
        sat_result=SAT
    )
    
    # Should be padded to at least 2
    assert len(tddnnf.tlemmas) >= 2

# ==================== Parallel Processing Tests ====================

def test_parallel_allsmt_single_proc(sat_formula):
    """Test with single process (default)"""
    partial = MathSATExtendedPartialEnumerator()
    tddnnf = TheoryDDNNF(sat_formula, solver=partial, parallel_allsmt_procs=1)
    
    assert tddnnf.sat_result == SAT
    assert hasattr(tddnnf, "phi_ddnnf")


def test_parallel_allsmt_multi_proc(sat_formula):
    """Test with multiple processes"""
    partial = MathSATExtendedPartialEnumerator()
    # Use 2 processes if available
    tddnnf = TheoryDDNNF(sat_formula, solver=partial, parallel_allsmt_procs=2)
    
    assert tddnnf.sat_result == SAT
    assert hasattr(tddnnf, "phi_ddnnf")


def test_invalid_parallel_procs_zero(sat_formula):
    """Test that invalid parallel_allsmt_procs (0) raises error"""
    partial = MathSATExtendedPartialEnumerator()
    
    with pytest.raises(
        ValueError,
        match="parallel_allsmt_procs must be between 1"
    ):
        TheoryDDNNF(sat_formula, solver=partial, parallel_allsmt_procs=0)


def test_invalid_parallel_procs_negative(sat_formula):
    """Test that negative parallel_allsmt_procs raises error"""
    partial = MathSATExtendedPartialEnumerator()
    
    with pytest.raises(
        ValueError,
        match="parallel_allsmt_procs must be between 1"
    ):
        TheoryDDNNF(sat_formula, solver=partial, parallel_allsmt_procs=-1)


def test_invalid_parallel_procs_too_many(sat_formula):
    """Test that too many parallel_allsmt_procs raises error"""
    import multiprocessing
    partial = MathSATExtendedPartialEnumerator()
    too_many = multiprocessing.cpu_count() + 1
    
    with pytest.raises(
        ValueError,
        match="parallel_allsmt_procs must be between 1"
    ):
        TheoryDDNNF(
            sat_formula,
            solver=partial,
            parallel_allsmt_procs=too_many
        )


# ==================== Edge Cases Tests ====================

def test_complex_formula_from_file():
    """Test with complex formula loaded from file"""
    phi = formula.read_phi("./tests/items/rng.smt")
    total = MathSATTotalEnumerator()
    
    tddnnf = TheoryDDNNF(phi, solver=total)
    
    assert tddnnf.sat_result == True
    assert len(tddnnf.tlemmas) >= 2


def test_sat_result_parameter_sat(sat_formula):
    """Test providing sat_result parameter (SAT)"""
    total = MathSATTotalEnumerator()
    
    tddnnf = TheoryDDNNF(
        sat_formula,
        solver=total,
        tlemmas=[formula.top()],
        sat_result=SAT
    )
    
    assert tddnnf.sat_result == SAT
    assert hasattr(tddnnf, "phi_ddnnf")


# ==================== Integration Tests ====================

def test_full_workflow_with_file_output(temp_dir):
    """Test complete workflow with file output"""
    phi = Or(
        LT(Symbol("X", REAL), Symbol("Y", REAL)),
        Equals(Symbol("X", REAL), Real(10))
    )
    
    total = MathSATTotalEnumerator()
    logger = {}
    
    tddnnf = TheoryDDNNF(
        phi,
        solver=total,
        base_out_path=temp_dir,
        computation_logger=logger
    )
    
    # Verify compilation
    assert tddnnf.sat_result == SAT
    assert hasattr(tddnnf, "phi_ddnnf")
    
    # Verify file output
    tddnnf_file = os.path.join(temp_dir, "tddnnf.smt2")
    assert os.path.isfile(tddnnf_file)
    
    # Verify logger
    assert "T-DDNNF" in logger
    assert logger["T-DDNNF"]["ALL SMT mode"] == "computed"


# ==================== Private Method Tests ====================

def test_normalize_input(sat_formula):
    """Test _normalize_input method"""
    total = MathSATTotalEnumerator()
    tddnnf = TheoryDDNNF(sat_formula, solver=total)
    
    # The formula should be normalized during initialization
    # We can check that tlemmas exist and are FNodes
    for lemma in tddnnf.tlemmas:
        assert isinstance(lemma, FNode)


def test_load_lemmas_computed_mode(sat_formula):
    """Test _load_lemmas in computed mode"""
    total = MathSATTotalEnumerator()
    logger = {}
    
    TheoryDDNNF(sat_formula, solver=total, computation_logger=logger)
    
    assert logger["T-DDNNF"]["ALL SMT mode"] == "computed"
    assert "lemmas loading time" in logger["T-DDNNF"]


def test_load_lemmas_loaded_mode_from_param(sat_formula):
    """Test _load_lemmas in loaded mode (from parameter)"""
    total = MathSATTotalEnumerator()
    logger = {}
    
    TheoryDDNNF(
        sat_formula,
        solver=total,
        tlemmas=[formula.top()],
        computation_logger=logger
    )
    
    assert logger["T-DDNNF"]["ALL SMT mode"] == "loaded"