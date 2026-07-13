# Program P.E-FR — Normal connection extracted from an orthonormal frame jet

> Derived Ricci theorem: [`program_pe_metric_normal_connection_curvature.md`](program_pe_metric_normal_connection_curvature.md)  
> Smooth adapted frames: [`program_pe_smooth_adapted_frames.md`](program_pe_smooth_adapted_frames.md)  
> Structured-jet roadmap: [`program_pe_structured_jet_reduction.md`](program_pe_structured_jet_reduction.md)

## Objective

The preceding stage treated the metric normal-connection coefficients

```text
omega_x,
partial_x omega_y
```

as local jet data satisfying skew-adjointness assumptions. The next lock was to
show that these assumptions follow from an orthonormal normal frame, rather than
being inserted independently.

The result now proved is:

> **Local frame-jet theorem.** A two-jet of an orthonormal normal frame determines
> canonically a metric normal-connection one-jet. The first and second
> differentiated metric identities force respectively the connection
> coefficient and its first derivative to be skew-adjoint. Combining this
> construction with the adapted block-curvature theorem yields the Ricci normal
> equation.

The theorem is finite-dimensional and pointwise. The frame derivatives are
ordinary derivatives in a flat ambient coefficient model. Replacing them by the
ambient covariant derivatives of an actual smooth normal frame remains a
separate manifold theorem.

## 1. Orthonormal normal-frame two-jet

Fix real finite-dimensional inner-product models

```text
T = tangent model,
N = normal coordinate model,
A = ambient model.
```

A frame two-jet consists of

```text
E       : N -> A,
dE_x    : N -> A,
d2E_xy  : N -> A,
```

where `E` is a linear isometry. The structure stores the two differentiated
orthonormality identities.

### First metric identity

Differentiating

```text
<E xi,E eta> = <xi,eta>
```

once gives

```text
<dE_x xi,E eta> + <E xi,dE_x eta> = 0.
```

### Second metric identity

Differentiating again gives

```text
<d2E_xy xi,E eta>
+ <dE_y xi,dE_x eta>
+ <dE_x xi,dE_y eta>
+ <E xi,d2E_xy eta>
= 0.
```

Lean structure:

```text
P0EFTJanusNormalConnectionFromFrameJet
  .OrthonormalNormalFrameTwoJet
```

## 2. Extraction of the connection coefficient

For fixed `x`, define the bilinear scalar form

```text
b_x(xi,eta) = <dE_x xi,E eta>.
```

Finite-dimensional Riesz representation produces the unique continuous linear
operator `omega_x : N -> N` satisfying

```text
<omega_x xi,eta> = <dE_x xi,E eta>.
```

Lean definitions and characterization:

```text
frameConnectionCoefficientBilinear
frameNormalConnectionCoefficient
frameNormalConnectionCoefficient_inner
```

### Theorem FR1 — proved in Lean

```text
frameNormalConnectionCoefficient_skew
```

proves

```text
<omega_x xi,eta> = -<xi,omega_x eta>.
```

The proof uses only the first differentiated metric identity and symmetry of the
real inner product.

The repository also proves linearity in the tangent direction and packages

```text
x |-> omega_x
```

as a linear map into continuous normal endomorphisms.

## 3. Extraction of the derivative of the connection

The derivative of the coefficient is characterized by

```text
<partial_x omega_y xi,eta>
  = <d2E_xy xi,E eta>
    + <dE_y xi,dE_x eta>.
```

This is exactly the derivative of

```text
<omega_y xi,eta> = <dE_y xi,E eta>
```

when the normal coordinate vectors `xi,eta` are fixed.

Lean definitions:

```text
frameConnectionDerivativeBilinear
frameNormalConnectionDerivative
frameNormalConnectionDerivative_inner
```

### Theorem FR2 — proved in Lean

```text
frameNormalConnectionDerivative_skew
```

proves that every `partial_x omega_y` is skew-adjoint. The proof is the second
differentiated metric identity, rearranged by symmetry of the real inner
product.

The derivative is proved linear in both tangent directions and packaged as

```text
T -> Linear(T, End(N)).
```

## 4. Canonical metric normal-connection jet

### Theorem/Construction FR3 — proved in Lean

```text
metricNormalConnectionOneJetOfFrame
```

constructs the exact structure required by the curvature theorem:

```text
MetricNormalConnectionOneJet T N.
```

No skew-adjointness assumptions remain external at this stage; they have been
derived from orthonormality of the frame two-jet.

Characterization lemmas:

```text
metricNormalConnectionOneJetOfFrame_coefficient
metricNormalConnectionOneJetOfFrame_derivative
```

## 5. Ricci equation derived from the frame jet

### Theorem FR4 — proved in Lean

```text
normalFrameTwoJet_satisfies_Ricci
```

combines the frame-to-connection construction with the adapted block-curvature
theorem and proves

```text
<R_perp(x,y)xi,eta>
  = <R_ambient_mixed(x,y)xi,eta>
    + <[A_xi,A_eta]x,y>.
```

The logical chain is now

```text
orthonormal frame two-jet
  -> metric identities
  -> omega and partial omega by Riesz
  -> skew-adjoint metric connection jet
  -> R_perp = d omega + omega wedge omega
  -> adapted block curvature
  -> Ricci normal equation.
```

This removes another independent assumption from the structured-jet model.

## 6. Evidence boundary

### Theorem demonstrated

In a fixed finite-dimensional real inner-product coefficient model:

- the first derivative of an orthonormal normal frame determines the normal
  connection coefficient;
- its skew-adjointness follows from differentiated orthonormality;
- the frame second derivative determines the first derivative of the connection;
- its skew-adjointness follows from twice-differentiated orthonormality;
- both maps have the required tangent linearity;
- the resulting connection jet has a derived curvature and satisfies the Ricci
  equation with the Riesz shape operators.

### Not yet demonstrated

- construction of this two-jet from the smooth normal frame already produced by
  the Gram–Schmidt stage;
- replacement of ordinary frame derivatives by the ambient Levi-Civita
  covariant derivatives;
- inclusion of Christoffel and moving-coordinate terms in a curved ambient
  chart;
- the inhomogeneous transformation law under a varying normal-frame change;
- curvature conjugacy on overlaps;
- smooth dependence on varying tangent and normal subspaces;
- global packaging as a connection on the actual normal bundle;
- compatibility with the SpinC determinant-line connection.

Accordingly, FR4 is a **proved local frame-jet theorem**, not yet the global
manifold Ricci theorem for the Janus immersion.

## 7. Next theorem queue

1. Define a one-/two-jet of an orthogonal normal gauge transformation.
2. Prove, for one fixed convention, the inhomogeneous law

   ```text
   omega' = g omega g^(-1) - dg g^(-1)
   ```

   or its equivalent inverse-convention form.
3. Prove curvature conjugacy

   ```text
   R_perp' = g R_perp g^(-1).
   ```

4. Extract `E,dE,d2E` from the smooth normal frame on one chart.
5. Insert the ambient Levi-Civita covariant derivative.
6. Prove that chart-overlap connection jets agree by the gauge law.
7. Add the resulting connection data to the differentiable structured-jet
   groupoid.
8. Relate the normal and determinant-line connections in the precise SpinC
   fiber product.

## 8. Lean correspondence and validation

```text
JanusFormal/Branches/FundamentalGeometryPEJetUniversality/Gates/
  P0EFTJanusNormalConnectionFromFrameJet.lean
```

Focused validation:

```text
Program PE jet universality, run 29291044438
Lean focused head: success
Python exact audits/tests: success
```
