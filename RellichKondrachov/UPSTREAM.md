# Euclidean Rellich core

This directory vendors only the dependency closure of the Euclidean
fixed-support Rellich theorem from
<https://github.com/abenenson/rellich-kondrachov>.

- Upstream commit: `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`
- License: Apache-2.0; see `LICENSE`
- Local port: Lean/Mathlib `v4.31.0`

The local changes are compatibility edits for elaboration of function
eta-expansions, `Lp` coercions, operator norms, and non-inferable instance
arguments. The theorem and proof strategy are unchanged.
