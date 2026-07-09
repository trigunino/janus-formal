# Janus

Janus is a research repository for cosmology and gravity formalization.
This README is the entry point for external readers (no deep prior knowledge required).

## What is inside
- `formal/lean/` : Lean sources for the formal gates and scaffolds.
- `formal/` : additional formalization support and references.
- `docs/` : scientific notes, branch status, and audit logs.
- `scripts/` : data and report generation pipelines.
- `src/` : Python implementation for numerical/science workflows.
- `tests/` : test suite.
- `data/` : local datasets and generated artifacts.
- `outputs/` : generated reports, intermediate tables, and diagnostics.

## Quick start
1) Install prerequisites:
- Python and Git
- Node is not required for the core pipeline
- [elan](https://github.com/leanprover/elan) for Lean

2) Install dependencies and check environment:
```bash
lake env lean --version
```

3) Build the Lean entry point:
```bash
lake build JanusFormal
```

4) Run a single-file Lean check (fast):
```bash
lake env lean formal\lean\JanusBasic.lean
```

## Main working targets
- `formal/lean/P0SPathNoGo.lean` : S-path gate scaffold + current no-go status.
- `formal/lean/P0OrbifoldNoGo.lean` : orbifold no-go summary.
- `formal/lean/P0OrbifoldClosure.lean` : closure bridge notes.
- `formal/lean/P0SolderLawAxioms.lean` : solder-law minimal closure structure.

## Status for non-owners
- The project has many in-progress branches and long-running hypotheses. For current global status use:
  - `docs/janus_current_global_lock.md`
  - `docs/janus_branch_registry.md`
  - `docs/janus_build_architecture.md`

## Typical external contributor flow
1. Read this README.
2. Read the relevant status doc.
3. Open `formal/lean/JanusBasic.lean` and one gate file.
4. Run the corresponding one-file Lean check.
5. Open or update the related document entry in `docs/`.

## Notes
- This repository is intentionally scaffold-oriented: many modules expose explicit blockers and non-promoted claims.
- If you are not running numerics, prefer Lean files and docs first.

## Contact and context files
- `docs/source_traceability.md` : mapping from source claims to formal/num artifacts.
- `formal/README.md` : quick Lean workspace pointers.
