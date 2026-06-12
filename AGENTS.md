# AGENTS.md

## Project Overview
`theorydd` — SMT-level BDD/SDD/d-DNNF compiler. Combines an SMT formula with
T-lemmas (from `tlemmas-enumeration`), builds the boolean abstraction, compiles
it with a propositional C/C++ compiler (d4/c2d), then answers queries via a
propositional d-DNNF reasoner (with theory-atom ↔ boolean-atom mapping).

## Workflow
- Base branch: `develop`. Never commit/push to it directly.
- Work on feature branches: `type/description` (e.g. `feat/refactor-solver`).
- PR → squash-merge to `develop`. No commits unless explicitly told.

## Dev Setup
- Python 3.12+, package source in `src/theorydd/`, tests in `tests/`.
- Formatter/linter: `ruff format` && `ruff check` (line-length = 120).
- Tests: `pytest` (runs with `--import-mode=importlib`).
- No type checker configured; consult before adding one.

## Current Status
The codebase needs significant refactoring. Keep changes aligned with existing
`src/theorydd/` layout; preserve the solver/walker split pattern.
