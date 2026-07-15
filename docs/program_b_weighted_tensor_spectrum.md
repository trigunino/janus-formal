# Program B — weighted tensor spectrum

- Program: **B**
- Stable ID: `B-WEIGHTED-TENSOR-SPECTRUM`
- Evidence: **T** (Lean theorem)
- Dependency: positive bimetric linear spectrum
- Lean target: `P0EFTJanusPositiveBimetricLinearSpectrum.lean`

## Result

For distinct positive kinetic normalizations `M_+²` and `M_-²`, the diagonal
mode remains massless. The weighted relative eigenvector is

```text
(M_-² h, -M_+² h)
```

with generalized eigenvalue

```text
m_rel² (1/M_+² + 1/M_-²).
```

This eigenvalue is strictly positive when both kinetic coefficients and the
relative mass coefficient are positive. The safe tensor architecture therefore
does not require equal Planck normalizations.

## Remaining physical atom

This is a two-amplitude tensor reduction. Vector/scalar constraints,
spacetime-dependent coefficients and the nonlinear secondary constraint remain
open.
