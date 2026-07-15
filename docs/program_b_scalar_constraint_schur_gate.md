# Program B — scalar constraint Schur gate

- Program: **B**
- Stable ID: `B-SCALAR-SCHUR`
- Evidence: **T** (Lean theorem)
- Dependencies: full scalar quadratic coefficients and a derived auxiliary constraint
- Lean target: `P0EFTJanusScalarConstraintSchurGate.lean`

## Result

For the two-scalar kinetic form

```text
K = a x² + 2 b x y + c y²,
```

the algebraic constraint `b x + c y = 0` gives

```text
y = -(b/c) x,
K_reduced = (a - b²/c) x².
```

The physical scalar is ghost-free when

```text
c > 0,
a c - b² > 0.
```

This is an exact conditional gate. It does not derive the required lapse or
boundary constraint from the full Janus action.

## Failure criterion

Reject a proposed scalar branch if the constraint is imposed by hand, if the
auxiliary coefficient vanishes, if the Schur determinant is nonpositive, or if
the reduced gradient term has the wrong sign.
