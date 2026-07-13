# Program P.E-S4 — Pointwise second fundamental form from structured jets

> First combined quotient: [`program_pe_low_order_structured_background.md`](program_pe_low_order_structured_background.md)  
> Structured-jet roadmap: [`program_pe_structured_jet_reduction.md`](program_pe_structured_jet_reduction.md)  
> Categorical theorem: [`program_pe_categorical_jet_equivalence.md`](program_pe_categorical_jet_equivalence.md)

## Objective

The low-order quotient theorem produced a normal quadratic tensor `B`, but this
was initially only a Taylor coefficient in an adapted algebraic model. Program
P.E-S4 asks whether that tensor is the actual pointwise second fundamental form

```text
II(X,Y) = (nabla^M_X di(Y))^perp
```

and how it transforms under the residual tangent and normal frame groups.

Mathlib does not currently provide a ready-made manifold Levi-Civita connection
or second-fundamental-form API. The present theorem therefore formalizes the
complete pointwise connection-coefficient calculation and states separately the
remaining manifold-level constructions.

## 1. Pointwise adapted orthogonal splitting

Let

```text
di : T -> Ambient
```

be a real linear isometry. The repository constructs:

```text
TangentRange = range(di),
NormalSpace  = TangentRange^perp,
Ambient ~=_isometry L2(TangentRange x NormalSpace).
```

Lean proves that in these adapted coordinates

```text
di(x) = (rangePoint(x), 0).
```

The main results are:

```text
P0EFTJanusAdaptedOrthogonalSplitting
  .adapted_derivative_fst
  .adapted_derivative_snd
  .adapted_derivative_is_standard_inclusion
  .tangent_range_finrank
  .tangent_plus_normal_finrank
```

Thus the first-order normalization used by the earlier second-jet quotient is
now justified pointwise for a linear isometric immersion derivative.

## 2. Connection-corrected second jet

A pointwise second-order coordinate model consists of

```text
rawSecond        : T x T -> Ambient,
ambientConnection: T x T -> Ambient,
sourceConnection : T x T -> T.
```

The connection-corrected second derivative is defined by

```text
D2_cov(x,y)
  = rawSecond(x,y)
  + ambientConnection(x,y)
  - di(sourceConnection(x,y)).
```

This is the coordinate formula

```text
D2 i + Gamma^M(di,di) - di(Gamma^Sigma).
```

The pointwise second fundamental form is

```text
II(x,y) = projection_Normal(D2_cov(x,y)).
```

Lean module:

```text
P0EFTJanusSecondFundamentalFormJet.lean
```

## 3. The source connection term disappears normally

### Theorem S4.1 — proved in Lean

```text
normalProjection_derivative_eq_zero
```

proves that every vector in the image of `di` has zero normal projection.
Consequently:

```text
secondFundamentalForm_eq_projected_raw_plus_ambient
```

proves

```text
II(x,y)
  = projection_Normal(rawSecond(x,y) + ambientConnection(x,y)).
```

The source Christoffel term is tangent-valued and therefore cannot affect the
second fundamental form.

## 4. Coordinate two-jet invariance

### Source-coordinate change

A quadratic source-coordinate correction `C : T x T -> T` changes

```text
rawSecond        -> rawSecond + di(C),
sourceConnection -> sourceConnection + C.
```

Lean proves the exact cancellation

```text
covariantSecondDerivative_sourceCoordinateChange
secondFundamentalForm_sourceCoordinateChange.
```

### Ambient-coordinate change

A quadratic ambient-coordinate correction `K : T x T -> Ambient` changes

```text
rawSecond        -> rawSecond + K,
ambientConnection-> ambientConnection - K.
```

Lean proves

```text
covariantSecondDerivative_ambientCoordinateChange
secondFundamentalForm_ambientCoordinateChange.
```

Therefore the pointwise connection-corrected tensor and its normal projection
are independent of the declared source and ambient coordinate two-jets.

## 5. Symmetry

If

```text
rawSecond,
ambientConnection,
sourceConnection
```

are symmetric in their two tangent arguments, then Lean proves

```text
covariantSecondDerivative_isSymmetric
secondFundamentalForm_isSymmetric.
```

This is the pointwise torsion-free symmetry theorem.

## 6. Normal component in adapted coordinates

Lean proves that the second coordinate of the canonical orthogonal splitting is
exactly the normal projection:

```text
adapted_snd_eq_normalProjection.
```

Hence

```text
adapted_snd_covariantSecondDerivative_eq_secondFundamentalForm
```

identifies `II` with the normal coordinate of the covariant second derivative.

## 7. Identification of the reduced tensor B

Given a split adapted two-jet

```text
(Q_tangent, Q_normal),
```

the repository reconstructs the ambient raw second derivative through the
inverse adapted isometry and sets both connection coefficients to zero.

### Theorem S4.2 — proved in Lean

```text
flat_secondFundamentalForm_eq_normalQuadratic
```

states

```text
II_flat = Q_normal.
```

Thus, in the flat adapted model used by the first quotient theorem, the reduced
normal quadratic tensor `B` is exactly the pointwise second fundamental form.
This is no longer only an analogy or a naming convention.

## 8. Residual orthogonal equivariance

The residual pointwise group is

```text
O(T) x O(N).
```

It acts on a normal-valued two-tensor by

```text
((a,b) . B)(x,y)
  = b(B(a^(-1)x, a^(-1)y)).
```

Lean module:

```text
P0EFTJanusSecondFundamentalResidualEquivariance.lean
```

The repository proves:

```text
actOnSecondFundamentalTensor_one
actOnSecondFundamentalTensor_mul
actOnSecondFundamentalTensor_preserves_symmetry
actOnAdaptedSplitJet_one
actOnAdaptedSplitJet_mul
flat_secondFundamentalForm_residual_equivariant.
```

Therefore the identity `B = II` is equivariant under the full pointwise
orthogonal residual group.

## 9. Exact evidence boundary

### Demonstrated in Lean

- orthogonal tangent/normal splitting of a linear isometric derivative;
- standard-inclusion first-order normal form;
- connection-corrected second derivative at one point;
- normal projection definition of `II`;
- independence from source and ambient coordinate two-jets;
- torsion-free symmetry;
- identification with the adapted normal coordinate;
- exact equality between the reduced tensor `B` and `II` in the flat adapted
  model;
- `O(T) x O(N)` action laws and equivariance.

### Not yet demonstrated

- construction of the source and ambient Levi-Civita connections as global or
  local smooth manifold objects in Lean;
- existence of a smooth local germ of adapted orthonormal frames;
- the full transformation law involving derivatives of a varying frame field;
- oriented reduction to `SO(T) x SO(N)`;
- the compatible Spin or SpinC central extension and its action on spinors;
- the determinant-line connection and its compatibility with the immersion
  splitting;
- a smooth finite-dimensional structured-jet base and differentiable groupoid.

The repository deliberately does not label those missing objects as proved.

## 10. Mathematical conclusion

The low-order local chain is now

```text
linear isometric first jet
  -> canonical pointwise tangent/normal splitting

connection-corrected second jet
  -> coordinate-independent covariant second derivative
  -> normal projection II

flat adapted quotient
  -> B = II

residual frames
  -> O(T) x O(N)-equivariance.
```

The next genuine geometric lock is no longer the algebraic identity `B = II`.
It is the construction of a smooth adapted frame germ and the oriented/SpinC
lift of its residual frame group.

## 11. Next theorem queue

1. Define a local smooth family of injective/isometric derivatives.
2. Construct a smooth orthogonal projector onto the tangent image and its normal
   complement.
3. Prove local smooth triviality of the tangent and normal image bundles.
4. Construct a smooth adapted orthonormal frame germ.
5. Compute the derivative-of-frame contribution and match it with the
   connection-corrected formula already proved pointwise.
6. Reduce the residual group to the required oriented subgroup.
7. Construct the exact SpinC fiber product and determinant-line action.
8. Add one covariant derivative of `II` and derive the first Codazzi constraint.

## 12. Lean correspondence

```text
JanusFormal/Branches/FundamentalGeometryPEJetUniversality/Gates/
  P0EFTJanusAdaptedOrthogonalSplitting.lean
  P0EFTJanusSecondFundamentalFormJet.lean
  P0EFTJanusSecondFundamentalResidualEquivariance.lean
```
