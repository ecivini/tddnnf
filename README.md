# d-DNNF Modulo Theories

Implementation of the algorithms and procedures presented in the paper **"d-DNNF Modulo Theories: A General Framework for Polytime SMT Queries"**.

This package (`theorydd`) allows you to compile SMT formulas into Theory-consistent Decision Diagrams and Theory d-DNNF, enabling polytime SMT queries on the compiled structures.

> **Note:** This package requires **Python 3.12 or higher**

---

## Table of Contents

- [Installation](#installation)
- [Package Overview](#package-overview)
- [TheoryDDNNF](#theoryddnnf)
  - [What is a T-d-DNNF?](#what-is-a-t-d-dnnf)
  - [Constructor](#constructor)
  - [Methods](#methods)
  - [Basic Examples](#basic-examples)
- [Other Classes](#other-classes)
- [SMT Enumerators](#smt-enumerators)
- [Examples Folder](#examples-folder)
- [License](#license)

---

## Installation

It is recommended to use a virtual environment.

### Prerequisites

- Python 3.12 or higher
- GCC and build tools (for compiling MathSAT bindings)

### Step-by-step Installation

```bash
# 1. Install package dependencies
pip3 install .

# 2. Install MathSAT SMT solver
pysmt-install --msat

# 3. Install the d4v2 d-DNNF compiler
theorydd_install --d4
```

---

## Package Overview

The `theorydd` package provides tools to compile SMT formulas into compact knowledge representations that support polytime queries. The main compilation targets are:

- **T-BDD** (`TheoryBDD`): Theory-consistent Binary Decision Diagrams
- **T-SDD** (`TheorySDD`): Theory-consistent Sentential Decision Diagrams
- **T-d-DNNF** (`TheoryDDNNF`): Theory-consistent deterministic Decomposable Negation Normal Form

All of these representations guarantee theory consistency, meaning that every satisfying assignment of the compiled structure is also T-satisfiable (consistent with the underlying SMT theory).

The package uses [pysmt](https://pypi.org/project/PySMT/) for managing SMT formulas. All input formulas must be expressed as `FNode` objects via pysmt.

---

## TheoryDDNNF

### What is a T-d-DNNF?

A **Theory d-DNNF** (T-d-DNNF) is a d-DNNF formula that encodes exactly the T-satisfiable models of an SMT formula `φ`. It is built by:

1. Running AllSMT enumeration on `φ` to extract **theory lemmas** — clauses that rule out all T-inconsistent assignments.
2. Conjoining `φ` with those lemmas.
3. Compiling the resulting propositional formula into a d-DNNF using an external compiler (d4v2).

---

### Constructor

```python
from theorydd.ddnnf.theory_ddnnf import TheoryDDNNF
from enumerators.solvers.mathsat_total import MathSATTotalEnumerator

logger = {}

tddnnf = TheoryDDNNF(
    phi,
    computation_logger=logger,
    base_out_path=f"data/{EXAMPLE_CODE}",
    store_tlemmas=True,
    solver=MathSATTotalEnumerator(project_on_theory_atoms=False, computation_logger=logger),
    tddnnf_type=TheoryDNNFType.TReduced,
)
```

#### Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `phi` | `FNode` | *(required)* | The SMT formula to compile into a T-d-DNNF. |
| `solver` | `SMTEnumerator \| str` | `"total"` | The AllSMT solver used to extract theory lemmas. Accepts a string (`"total"`, `"partial"`, `"tabular_total"`, `"tabular_partial"`) or an `SMTEnumerator` instance. Also used for formula normalization. |
| `tlemmas` | `List[FNode] \| None` | `None` | If provided, skips AllSMT enumeration and uses these theory lemmas directly. |
| `load_lemmas` | `str \| None` | `None` | Path to a `.smt2` file containing pre-computed theory lemmas. Ignored if `tlemmas` is not `None`. |
| `sat_result` | `bool \| None` | `None` | Pass `SAT` or `UNSAT` (from `theorydd.constants`) if the satisfiability of `phi` is already known, to speed up compilation. |
| `folder_name` | `str \| None` | `None` | If provided, loads a previously saved T-d-DNNF from this folder path instead of recompiling. All other parameters except `solver` are ignored. |
| `computation_logger` | `Dict \| None` | `None` | A dictionary passed by reference. Timing and computation details will be written into it during construction. |
| `compiler` | `str` | `"d4"` | The d-DNNF compiler binary to use. Supported values: `"d4"`, `"c2d"`. |
| `store_tlemmas` | `bool` | `False` | Store the computed T-lemmas as artifacts. |
| `stop_after_allsmt` | `bool` | `False` | Stops after the enumeration of T-lemmas. |
| `tddnnf_type` | `TheoryDNNFType` | `TheoryDNNFType.TReduced` | Type of the T-d-DNNF to compute (T-Reduced or T-extended). |



### Basic Examples

#### Example 1: Compiling a simple LRA formula

```python
from pysmt.shortcuts import Symbol, And, Or, Not, GE, LE, Real, get_env
from pysmt.typing import REAL
from theorydd.ddnnf.theory_ddnnf import TheoryDDNNF

# Define real-valued variables
x = Symbol("x", REAL)
y = Symbol("y", REAL)

# Build an SMT formula: (x >= 0 AND y >= 0) OR (x <= -1)
phi = Or(
    And(GE(x, Real(0)), GE(y, Real(0))),
    LE(x, Real(-1))
)

# Compile to T-d-DNNF using the default total MathSAT enumerator and d4
tddnnf = TheoryDDNNF(phi)
```

## Examples Folder

Additional usage examples are available in the [`examples/`](./examples) folder of this repository.

## Querying

Queries can be performed on the propositional d-DNNF representation using any Boolean Knowledge Compilation tool. Some examples and scripts on how to do it can be found in [tddnnf-testbench](https://github.com/ecivini/tddnnf-testbench).

---

## License

This project is licensed under the [MIT License](./LICENSE).