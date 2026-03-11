# Implementation of the algorithms and procedures presented in the paper "d-DNNF Modulo Theories: A General Framework for Polytime SMT Queries"

## Installation

### Prerequisites

- Python 3.12 or higher
- GCC and build tools (for compiling MathSAT bindings)

### Installation procedure
It is recommended to use virtualenv environments.

```bash
# Install the dependencies
$ pip3 install .

# Install MathSAT
$ pysmt-install --msat

# Install d4v2
$ theorydd_install --d4
```

## Usage

You can see examples on how to use this package in the [examples folder](./examples).