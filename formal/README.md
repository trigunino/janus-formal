# Janus Formal Workspace

Purpose: keep the path from source text to proof and data explicit.

Workflow:

1. `axioms/janus_axioms.md`: natural-language axioms and assumptions.
2. `axioms/bao_observable_map.md`: BAO observable-map derivation target.
3. `axioms/sigma8_observable_map.md`: sigma8/S8 observable-map derivation target.
4. `axioms/lensing_tensor_derivation_target.md`: tensor lensing normalization gates.
5. `latex/janus_core_equations.tex`: canonical equation set.
6. `scripts/check_symbolic_formulas.py`: SymPy checks for algebraic identities.
7. `lean/`: Lean skeleton for later formal proof.
8. `src/janus_lab/`: numerical implementation.
9. `outputs/reports/`: data-facing validation reports.

Do not promote an equation into code or Lean unless it is listed in
`docs/verified_formula_register.md`.
