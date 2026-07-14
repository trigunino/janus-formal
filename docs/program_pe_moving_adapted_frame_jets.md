# Program P.E-S5.3 — Moving adapted-frame jets and normal transport

> Smooth adapted frames: [`program_pe_smooth_adapted_frames.md`](program_pe_smooth_adapted_frames.md)  
> Second fundamental form jet: [`program_pe_second_fundamental_form_jet.md`](program_pe_second_fundamental_form_jet.md)  
> Structured-jet roadmap: [`program_pe_structured_jet_reduction.md`](program_pe_structured_jet_reduction.md)

## Objective

Stages S5.1 and S5.2 constructed smooth tangent/normal projectors and a smooth
local adapted orthonormal frame in a finite-dimensional coordinate model. The
next question is whether a varying frame introduces uncontrolled terms into the
immersion two-jet.

It does introduce first derivatives of the frame into the raw Hessian. The
geometric statement to prove is that these terms are exactly cancelled by the
transformation of the ambient connection, so that the connection-corrected
second derivative and the second fundamental form transform tensorially.

## 1. Formal first jet of a moving ambient frame

The Lean structure

```text
MovingAmbientFrameOneJet
```

contains:

```text
R      : Ambient ≃ₗᵢ[ℝ] Ambient,
dR     : Tangent -> Ambient -> Ambient.
```

Here `R` is the orthogonal frame value at the base point and `dR` is its first
variation in source directions.

The transformed immersion derivative is

```text
di' = R ∘ di.
```

Lean:

```text
transformedDerivative
transformedDerivative_apply.
```

## 2. Product-rule correction in the raw Hessian

At an immersion base point translated to the ambient origin, the moving-frame
product rule contributes

```text
C_R(x,y) = dR(x)(di(y)) + dR(y)(di(x)).
```

Lean:

```text
frameDerivativeCorrection
frameDerivativeCorrection_isSymmetric
movingFrameRawSecond
movingFrameRawSecond_formula.
```

Thus the raw second coefficient transforms as

```text
D²i'(x,y) = R(D²i(x,y)) + C_R(x,y).
```

The zeroth-order `d²R · i` contribution is absent because the immersion value has
been translated to zero at the chosen point.

## 3. Ambient connection compensation

The transformed ambient connection coefficient is defined by

```text
Γ_M' = R Γ_M - C_R.
```

The raw Hessian and connection therefore contain opposite copies of the moving
frame correction.

Lean:

```text
movingAmbientFrameChange
movingAmbientFrameChange_rawSecond
movingAmbientFrameChange_ambientConnection.
```

### Theorem S5.3.1 — proved in Lean

```text
covariantSecondDerivative_movingAmbientFrameChange
```

proves

```text
∇di' = R(∇di).
```

All first derivatives of the moving frame cancel exactly.

## 4. Combined source-coordinate and ambient-frame law

A source two-jet change contributes the already formalized tangent correction

```text
di(C_source)
```

to the raw Hessian and the same `C_source` to the source connection. Combining
this with the moving ambient frame gives the explicit raw formula

```text
D²i' = R(D²i + di(C_source)) + C_R.
```

Lean:

```text
movingAdaptedFrameChange
movingAdaptedFrameChange_rawSecond_formula
covariantSecondDerivative_movingAdaptedFrameChange.
```

The final connection-corrected tensor still obeys

```text
∇di' = R(∇di).
```

This closes the formal two-jet transformation law under simultaneous source and
ambient adapted-frame changes.

## 5. Canonical transport of normal spaces

Because `R` is orthogonal, it sends the old tangent image to the transformed
tangent image and therefore sends the old normal space to the transformed normal
space.

Lean proves:

```text
map_normalSpace_eq.
```

This equality yields the canonical isometric map

```text
normalTransport : N_di ≃ₗᵢ[ℝ] N_(R∘di).
```

The construction is not a choice of bases; it is the restriction of the ambient
orthogonal transformation to the corresponding normal subspaces.

## 6. Naturality of orthogonal projection

### Theorem S5.3.2 — proved in Lean

```text
normalProjection_movingFrame
```

proves

```text
T_N(P_N(v)) = P_N'(R(v)).
```

The proof uses the intrinsic characterization of orthogonal projection:

1. the transported candidate belongs to the transformed normal subspace;
2. the difference from `R(v)` is orthogonal to that subspace;
3. the orthogonal projection is unique with these properties.

This proof deliberately avoids rewriting dependent projector instances across an
equality of submodules.

## 7. Moving-frame equivariance of the second fundamental form

The second fundamental form is

```text
II = P_N(∇di).
```

Combining tensoriality of `∇di` with naturality of `P_N` gives the main result.

### Theorem S5.3.3 — proved in Lean

```text
secondFundamentalForm_movingAmbientFrameChange
```

proves

```text
T_N(II) = II'.
```

The complete source-plus-ambient result is

```text
secondFundamentalForm_movingAdaptedFrameChange.
```

Hence source two-jet corrections, derivatives of the moving ambient frame and
connection corrections all disappear from the geometric normal tensor, except
for its canonical orthogonal transport between the old and new normal spaces.

## 8. Exact evidence boundary

### Demonstrated in Lean

- formal first jet of a moving ambient orthogonal frame;
- symmetric product-rule correction in the raw Hessian;
- exact ambient-connection compensation;
- complete source-plus-moving-frame two-jet law;
- tensorial transformation of the connection-corrected second derivative;
- identification of the transformed normal subspace;
- canonical isometric normal transport;
- naturality of normal projection;
- moving-frame equivariance of the second fundamental form.

### Still open

- extract `MovingAmbientFrameOneJet` from the actual smooth adapted frame by
  differentiating a smooth orthogonal-frame-valued map;
- package the pointwise normal transport as a smooth normal-bundle isometry;
- prove the cocycle law on overlaps of local adapted frames;
- construct the oriented reduction;
- lift the tangent/normal orthogonal transition functions to the relevant SpinC
  fiber product;
- include the determinant-line connection and its gauge transformations;
- assemble these data into the differentiable structured-jet groupoid.

## 9. Scientific consequence

The local extrinsic tensor chain is now

```text
smooth immersion frame
  -> smooth tangent/normal projectors
  -> smooth adapted orthonormal frame
  -> moving-frame two-jet product rule
  -> connection cancellation
  -> canonical normal transport
  -> T_N(II) = II'.
```

Thus the normal quadratic tensor used in the low-order quotient is no longer
merely a coordinate representative in one fixed adapted frame. In the declared
local model, its geometric incarnation as the second fundamental form is stable
under moving adapted orthogonal frames.

The next lock is the transition-function layer:

```text
local adapted frames
  -> overlap cocycle in O(T) x O(N)
  -> oriented reduction
  -> SpinC lift and determinant-line compatibility.
```

## 10. Lean correspondence

```text
JanusFormal/Branches/FundamentalGeometryPEJetUniversality/Gates/
  P0EFTJanusMovingAdaptedFrameSecondJet.lean
  P0EFTJanusMovingNormalTransport.lean
```

Validated through the focused target

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```
