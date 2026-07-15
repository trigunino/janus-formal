# Program B — cosmological Bianchi gate

- Program: **B**
- Stable ID: `B-FLRW-BIANCHI`
- Evidence: **T** (Lean theorem)
- Dependencies: proportional HR potential and positive ratio branch
- Lean target: `P0EFTJanusProportionalBimetricEquations.lean`

## Result

The derivative of the plus-sector FLRW interaction density is exactly

```text
d rho_int / d r = 3 (beta1 + 2 beta2 r + beta3 r²).
```

Using `r_dot = r (H_- - H_+)`, its continuity residual factorizes as

```text
3 r (beta1 + 2 beta2 r + beta3 r²) (H_- - H_+).
```

For `r > 0` and nonzero Bianchi factor, covariant interaction continuity forces

```text
H_+ = H_-.
```

This closes the diagonal proportional FLRW Bianchi identity. It does not prove
the full spacetime tensor identity with inhomogeneous matter transport,
determinant weights and independent connections.

## Failure criterion

Reject a cosmological branch if its field equations do not reproduce this
factorization or if matter exchange violates the combined continuity identity.
