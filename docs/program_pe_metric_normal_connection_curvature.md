# Program P.E-R — Metric normal connection and derived Ricci equation

> Second-fundamental-form jet bridge: [`program_pe_second_fundamental_form_jet.md`](program_pe_second_fundamental_form_jet.md)  
> Structured-jet program: [`program_pe_structured_jet_reduction.md`](program_pe_structured_jet_reduction.md)  
> Current status: [`current_status.md`](current_status.md)

## Objective

The preceding formal layer had established:

```text
second fundamental form II
  -> Riesz shape operators A_xi
  -> algebraic shape commutator
  -> a formally reconstructed normal-curvature tensor.
```

That was not yet the geometric Ricci equation. The missing step was to introduce
an actual local normal-connection jet, compute its curvature, place it in the
adapted tangent/normal block connection, and derive the Ricci identity from the
curvature of that block connection.

This document records the exact local theorem now proved in Lean. It remains a
finite-dimensional pointwise jet theorem; it does not yet construct the normal
connection of the global Janus immersion bundle.

## 1. Metric normal-connection one-jet

Fix finite-dimensional real inner-product models

```text
T = tangent model,
N = normal model.
```

A local metric normal-connection one-jet in a commuting tangent coordinate
frame is represented by

```text
omega_x       : N -> N,
partial_x omega_y : N -> N,
```

with every coefficient and first derivative skew-adjoint:

```text
<omega_x xi,eta> = -<xi,omega_x eta>,
<partial_x omega_y xi,eta> = -<xi,partial_x omega_y eta>.
```

Lean structure:

```text
P0EFTJanusMetricNormalConnectionCurvature
  .MetricNormalConnectionOneJet
```

The skew-adjointness of the derivative is the differentiated metric-compatibility
identity in a fixed orthonormal normal frame.

## 2. Normal curvature

The curvature endomorphism is defined by

```text
R_perp(x,y)
  = partial_x omega_y
    - partial_y omega_x
    + [omega_x,omega_y].
```

Lean definition:

```text
normalConnectionCurvatureEndomorphism
```

### Theorem R1 — proved in Lean

```text
normalConnectionCurvatureEndomorphism_swap_tangent
```

proves

```text
R_perp(y,x) = -R_perp(x,y).
```

### Theorem R2 — proved in Lean

```text
normalConnectionCurvatureEndomorphism_skew
```

proves that every `R_perp(x,y)` is skew-adjoint. Consequently, the scalar tensor

```text
R_perp(x,y,xi,eta) = <R_perp(x,y)xi,eta>
```

is skew in both pairs:

```text
normalConnectionCurvatureScalar_swap_tangent
normalConnectionCurvatureScalar_swap_normal.
```

Thus the local metric connection produces an honest algebraic normal-curvature
tensor, not an arbitrary four-variable function.

## 3. Adapted ambient block connection

Let `II : T x T -> N` be a symmetric finite-dimensional second fundamental
form. The Riesz theorem already constructs the shape operators `A_xi` from

```text
<A_xi x,y> = <II(x,y),xi>.
```

On `T direct-sum N`, retain the off-diagonal and normal blocks of the ambient
connection:

```text
Omega_x(t,xi)
  = (-A_xi x,
     II(x,t) + omega_x xi).
```

Lean definition:

```text
splitAmbientConnectionAction
```

The tangential diagonal connection is omitted because it does not contribute to
the normal-normal block of the Ricci identity at the chosen commuting
coordinate point.

For a pure normal input, the normal component of the block curvature is
computed by

```text
partial_x Omega_y
  - partial_y Omega_x
  + [Omega_x,Omega_y].
```

Lean definition:

```text
splitAmbientMixedCurvatureAction
```

## 4. Block-curvature expansion

### Theorem R3 — proved in Lean

```text
splitAmbientMixedCurvatureAction_expansion
```

establishes

```text
R_ambient_mixed(x,y) xi
  = R_perp(x,y) xi
    - II(x,A_xi y)
    + II(y,A_xi x).
```

This is a direct expansion of the two block compositions. No Ricci equation is
assumed in this theorem.

### Theorem R4 — proved in Lean

```text
splitExtrinsicTerm_eq_neg_rieszCommutator
```

uses the Riesz–Weingarten identity and self-adjointness of every `A_xi` to prove

```text
<-II(x,A_xi y) + II(y,A_xi x), eta>
  = -<[A_xi,A_eta]x,y>.
```

This theorem fixes the sign convention. It was the nontrivial algebraic bridge
between the block computation and the previously defined shape commutator.

## 5. Derived Ricci equation

Write

```text
R_ambient_mixed(x,y,xi,eta)
  = <R_ambient_mixed(x,y)xi,eta>.
```

### Theorem R5 — proved in Lean

```text
metricNormalConnection_satisfies_Ricci
```

proves

```text
R_perp(x,y,xi,eta)
  = R_ambient_mixed(x,y,xi,eta)
    + <[A_xi,A_eta]x,y>.
```

The result is now derived from:

1. a metric normal-connection one-jet;
2. the Riesz construction of `A_xi` from `II`;
3. the adapted block connection;
4. the curvature commutator formula.

It is no longer a theorem true merely because the normal curvature was defined
as the right-hand side.

The ambient mixed block also has both expected skew symmetries:

```text
splitAmbientMixedCurvatureScalar_swap_tangent
splitAmbientMixedCurvatureScalar_swap_normal.
```

## 6. Exact executable audit

The repository contains an independent rational-matrix audit:

```text
python scripts/audit_janus_metric_normal_ricci.py
pytest -q tests/test_janus_metric_normal_ricci.py
```

It constructs exact matrices

```text
Omega_i = [[0, -B_i^T],
           [B_i, omega_i]],
```

computes

```text
R_ij = partial_i Omega_j - partial_j Omega_i + [Omega_i,Omega_j],
```

and verifies over `fractions.Fraction` that

```text
<R_perp_ij xi,eta>
  = <R_ij xi,eta> + <[A_xi,A_eta]e_i,e_j>
```

for basis normals and nontrivial rational linear combinations.

## 7. Evidence boundary

### Theorem demonstrated

Within fixed finite-dimensional Euclidean tangent and normal models:

- a metric normal-connection one-jet has a canonical curvature;
- the curvature has the two required skew symmetries;
- the adapted block connection has a computable mixed normal curvature;
- its extrinsic block equals the negative shape commutator;
- the Ricci normal equation follows as a derived identity;
- the fixed sign convention is independently audited exactly.

### Not yet demonstrated

The following remain open:

- extraction of `omega` and `partial omega` from the actual smooth normal frame
  and ambient Levi-Civita connection of a Janus immersion;
- proof that the resulting local jets satisfy the declared metric-compatibility
  hypotheses on every chart;
- the inhomogeneous gauge transformation law under a varying normal frame;
- the overlap/cocycle theorem for the connection coefficients and curvature;
- smooth dependence when the tangent metric and normal subspace vary over the
  structured-jet base;
- identification of the ambient mixed block with the curvature tensor of the
  genuine ambient Levi-Civita connection;
- global normal-bundle and SpinC determinant-line packaging.

Therefore the current result is a **proved local jet theorem**, not yet the full
manifold Ricci equation for the global Janus geometry.

## 8. Consequence for the structured jet program

The reduced local data can now be enlarged from

```text
(II,F)
```

to include a genuine connection-curvature sector:

```text
(II,
 omega, partial omega,
 R_perp,
 R_ambient_mixed,
 F, partial F,
 ...),
```

subject to the derived Ricci identity rather than an independently imposed
normal-curvature variable.

This removes one source of artificial freedom: once the adapted normal
connection and ambient block connection are fixed, the three quantities

```text
R_perp,
R_ambient_mixed,
[A,A]
```

cannot be chosen independently.

## 9. Next theorem queue

1. Extract the normal connection coefficients from a smooth adapted normal frame
   and the ambient Levi-Civita derivative.
2. Prove their skew-adjointness from orthonormality of the frame.
3. Differentiate once more and identify the resulting jet with
   `MetricNormalConnectionOneJet`.
4. Prove the varying-frame gauge law

   ```text
   omega' = g omega g^(-1) - dg g^(-1)
   ```

   with the repository's sign convention.
5. Prove curvature conjugacy on overlaps.
6. Identify the block ambient curvature with the actual ambient mixed curvature.
7. Package these data as equivariant bundles over the structured-jet groupoid.
8. Add the Ricci identity to the Gauss–Codazzi–Bianchi realizability locus.
9. Extend the Spencer/jet splitting by one order.

## 10. Lean correspondence

```text
JanusFormal/Branches/FundamentalGeometryPEJetUniversality/Gates/
  P0EFTJanusMetricNormalConnectionCurvature.lean
```

Validation on the focused P.E workflow:

```text
Program PE jet universality, run 29289354153
Lean focused head: success
Python exact audits/tests: success
```
