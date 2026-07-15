# Program B — minisuperspace lapse constraint gate

- Program: **B**
- Stable ID: `B-LAPSE-PRIMARY`
- Evidence: **T** (Lean theorem)
- Dependencies: HR elementary-symmetric interaction and diagonal FLRW ansatz
- Lean target: `P0EFTJanusMinisuperspaceLapseConstraint.lean`

## Result

For square-root eigenvalues `(N_-/N_+, r, r, r)`, multiplication by the plus
volume lapse reorganizes the HR potential exactly as

```text
N_+ B(r) + N_- A(r).
```

The interaction is therefore affine in each lapse. Its lapse first variations
are constraint equations independent of the lapses, and the pure lapse Hessian
vanishes.

This closes the primary lapse-constraint structure in diagonal minisuperspace.
The executable SVT audit separately verifies that its encoded shift system is
solved algebraically and that boundary bending is eliminated after lapse
substitution. It now marks full-EH lapse compatibility, the secondary
Hamiltonian constraint and Boulware–Deser removal explicitly as open.

## Secondary-constraint boundary

A separate Lean theorem records that lapse linearity alone does not imply the
secondary constraint. Closing removal of the Boulware–Deser mode still requires
the ADM shift redefinition, canonical Poisson brackets and preservation of the
primary constraint under time evolution.

## Failure criterion

Reject an extension if its reduced interaction becomes nonlinear in a physical
lapse, or if preservation of the primary constraint fails to generate the
required independent secondary constraint.
