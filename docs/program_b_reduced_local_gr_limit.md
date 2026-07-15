# Program B — reduced local-GR branch

- Program: **B**
- Stable ID: `B-REDUCED-LOCAL-GR`
- Evidence: **T** (Lean theorem)
- Dependencies: positive kinetic eigenmodes and PT-flat proportional potential
- Lean target: `P0EFTJanusReducedHamiltonianStability.lean`

## Result

On the equal-metric fluctuation branch

```text
c = 1,  h_plus = h_minus = h,
```

the relative mass term and proportional interaction vanish exactly. The
reduced Hamiltonian becomes

```text
H = 2 M_Pl² h²,
```

and is strictly positive for `M_Pl² > 0` and `h != 0`.

This closes the reduced homogeneous local-GR restriction. It does not yet prove
the full tensorial GR limit, the observed Newton constant, post-Newtonian
bounds, or decoupling of the massive mode in an inhomogeneous background.

## Failure criterion

Reject a nonlinear completion if its diagonal branch retains a relative mass
source, changes the massless kinetic sign, or fails to recover the Einstein
equations after the full constraints are imposed.
