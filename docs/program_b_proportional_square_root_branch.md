# Program B — proportional square-root branch

- Program: **B**
- Stable ID: `B-PROP-SQRT`
- Evidence: **T** (Lean theorem)
- Dependency: proportional branch `f = c² g`
- Lean target: `P0EFTJanusProportionalBimetricEquations.lean`

## Result

On the proportional branch, the mixed endomorphism is `g⁻¹f = c² I`. The
candidate `X = c I` squares exactly to this map. For `c > 0`, it is a positive
real square-root branch, and metric exchange sends its ratio to the positive
reciprocal `1/c`.

This closes matrix-square-root existence on the positive proportional branch.
It does not establish existence for arbitrary non-proportional Lorentzian
metric pairs, where real square roots and compatible null-cone structure remain
open.

## Failure criterion

Reject any extension leaving the proportional cone if `g⁻¹f` has no selected
real smooth square root or if the selected branch becomes discontinuous.
