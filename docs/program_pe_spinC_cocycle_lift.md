# Program P.E-S6 — Oriented overlaps, SpinC defect cancellation and the rank-two model

> Smooth adapted frames: [`program_pe_smooth_adapted_frames.md`](program_pe_smooth_adapted_frames.md)  
> Pointwise second fundamental form: [`program_pe_second_fundamental_form_jet.md`](program_pe_second_fundamental_form_jet.md)  
> Structured-jet roadmap: [`program_pe_structured_jet_reduction.md`](program_pe_structured_jet_reduction.md)

## Objective

After constructing a smooth local adapted orthonormal frame, the next geometric
problem is not another pointwise normal-form calculation. Local adapted frames
must be compared on overlaps, reduced to the correct oriented subgroup, lifted
through a central double cover, and combined with determinant-line phase data.

The exact staged problem is

```text
local adapted frames
  -> O(T) x O(N) overlap cocycle
  -> SO(T) x SO(N) oriented subcocycle
  -> chosen Spin lifts with a central ±1 triple defect
  -> local determinant square roots with a central ±1 triple defect
  -> diagonal cancellation in SpinC.
```

This document records the abstract theorem, the concrete circle two-torsion
instantiation, and the complete rank-two matrix model now proved in Lean.

## 1. Varying adapted frames and connection terms

Lean modules:

```text
P0EFTJanusMovingAdaptedFrameSecondJet.lean
P0EFTJanusMovingNormalTransport.lean
```

The moving-frame second-jet calculation proves that differentiating a varying
ambient frame produces exactly the expected derivative-of-frame correction.
When the ambient connection is transformed simultaneously, those terms cancel
and the connection-corrected second derivative transforms tensorially.

Principal results include:

```text
movingFrameRawSecond_formula
movingAmbientFrameChange_rawSecond
movingAmbientFrameChange_ambientConnection
covariantSecondDerivative_movingAmbientFrameChange
movingAdaptedFrameChange_rawSecond_formula
```

This closes the algebraic core of the previously open S5.3 varying-frame lemma.
It does not by itself package the calculation as a theorem about jets of smooth
maps between manifolds.

The normal-space theorem then constructs canonical transport between the normal
models defined by two adapted frames and proves the corresponding equivariance
of the second fundamental form.

## 2. Čech cocycle of adapted-frame transitions

Lean module:

```text
P0EFTJanusAdaptedFrameOverlapCocycle.lean
```

A local adapted frame choice consists of tangent and normal orthogonal gauges.
The transition from `first` to `second` is

```text
(first.tangentGauge⁻¹ * second.tangentGauge,
 first.normalGauge⁻¹  * second.normalGauge).
```

Lean proves:

```text
adaptedTransition_self
adaptedTransition_reverse
adaptedTransition_cocycle
adaptedTransition_mul.
```

Thus the residual tangent/normal changes satisfy the exact Čech identity

```text
g_23 * g_12 = g_13.
```

The module also introduces abstract orientation characters and proves that the
orientation-preserving transitions form a subcocycle:

```text
orientationPreserving_self
orientationPreserving_cocycle
orientationPreserving_reverse.
```

## 3. Determinant-one oriented reduction

Lean module:

```text
P0EFTJanusDeterminantOrientedReduction.lean
```

For a finite-dimensional real inner-product space, the orthogonal determinant is
bundled as a multiplicative character

```text
O(V) -> Rˣ.
```

Its kernel is the concrete special-orthogonal subgroup. For tangent and normal
models the residual oriented subgroup is

```text
SO(T) x SO(N) <= O(T) x O(N).
```

Principal results:

```text
orthogonalDeterminant
mem_specialOrthogonalSubgroup_iff
determinantOrientationCharacters
orientedResidualSubgroup
orientationPredicate_iff_mem_orientedResidualSubgroup
determinantOrientedTransition_cocycle
determinantOrientedTransition_reverse.
```

This is an exact determinant-one reduction. The theorem remains algebraic until
the transitions are extracted as smooth maps from actual oriented frame bundles.

## 4. Central double-cover obstruction

Lean module:

```text
P0EFTJanusCentralLiftCocycleObstruction.lean
```

Let

```text
1 -> {±1} -> Spin -> SO -> 1
```

be represented abstractly by a central double-cover homomorphism. Given an
`SO`-valued transition cocycle and arbitrary chosen local Spin lifts, define the
triple defect

```text
c_ijk = ŝ_jk * ŝ_ij * ŝ_ik⁻¹.
```

Lean proves that:

- the defect lies in the kernel of the projection;
- it is central;
- for a genuine double cover it is either `1` or the distinguished central
  element `-1`.

This isolates the exact obstruction to a Spin cocycle. Choosing pairwise lifts
does not by itself produce a principal Spin bundle; the triple defects must
vanish or be cancelled by additional central data.

## 5. SpinC diagonal cancellation

Lean module:

```text
P0EFTJanusSpinCDiagonalDefectCancellation.lean
```

A SpinC transition is represented by the diagonal quotient of

```text
Spin x U(1)
```

that kills `(-1,-1)`. The abstract theorem proves:

> If the Spin-lift triple defect and the phase triple defect represent the same
> central `±1` class, then their product is killed by the diagonal quotient and
> the resulting SpinC transitions satisfy the Čech cocycle law.

The principal theorem is the matching-defect SpinC cocycle result in that module.
It is a genuine algebraic cancellation theorem and makes the characteristic
class requirement explicit rather than hiding it inside a status flag.

## 6. Determinant-line square-root defect

Lean module:

```text
P0EFTJanusDeterminantSquareRootDefect.lean
```

Let `h_ij` be a determinant-line `U(1)` cocycle and choose local square roots
`r_ij` with

```text
r_ij² = h_ij.
```

The root transitions need not satisfy a cocycle. Their triple defect

```text
z_ijk = r_jk * r_ij * r_ik⁻¹
```

satisfies

```text
z_ijk² = 1.
```

Lean proves the two-torsion identity and then specializes the abstract SpinC
cancellation theorem to square-root defects. The remaining geometric theorem is
to prove that the determinant-root defect equals the Spin-lift defect for the
actual Janus tangent/normal data.

## 7. Circle two-torsion

Lean module:

```text
P0EFTJanusCirclePhaseTwoTorsion.lean
```

For the complex unit circle, Lean proves the concrete dichotomy

```text
z² = 1  <->  z = 1 or z = -1.
```

Consequently, every determinant square-root triple defect is literally one of
the two phases `±1`, not merely an unspecified element of a two-torsion kernel.
This supplies the phase-side central double-cover data used by the SpinC theorem.

## 8. Concrete rank-two circle double cover

Lean module:

```text
P0EFTJanusSpin2CircleModel.lean
```

Under the standard abstract identifications

```text
Spin(2) ≅ U(1),
SO(2)   ≅ U(1),
```

the Spin projection is circle squaring:

```text
z |-> z².
```

Lean now proves directly:

```text
circleSquaringProjection_surjective
circleSquaringProjection_eq_iff
spin2CircleDoubleCover_projection_surjective.
```

The kernel is exactly `{+1,-1}`, and the fiber theorem is

```text
z₁² = z₂²  <->  z₁ = z₂ or z₁ = -z₂.
```

The module also constructs:

- the diagonal subgroup generated by `(-1,-1)` in `U(1) x U(1)`;
- the exact quotient group;
- a concrete `SpinCDiagonalQuotientData` instance;
- a specialized theorem

```text
matching_spin2_circle_defects_implies_spinCCocycle.
```

Thus the rank-two circle model is not an interface: its double-cover and SpinC
cocycle algebra are fully instantiated.

## 9. Explicit matrix equivalence `U(1) ≃ SO(2)`

Lean module:

```text
P0EFTJanusCircleSO2Equivalence.lean
```

A circle phase `z=a+ib` is sent to the standard rotation matrix

```text
[ a  -b ]
[ b   a ].
```

Lean proves that this matrix is special orthogonal, constructs the inverse map
from the first matrix column, and obtains the group equivalence

```text
circleEquivMatrixSO2 : U(1) ≃* SO(2).
```

Principal results:

```text
circleRotationMatrix_mem_specialOrthogonal
circleToMatrixSO2_mul
matrixSO2Complex_norm
matrixSO2ToCircle_circleToMatrixSO2
circleToMatrixSO2_matrixSO2ToCircle
circleEquivMatrixSO2.
```

Composing this equivalence with circle squaring gives a matrix-valued projection

```text
Spin(2) -> SO(2)
```

with theorems

```text
spin2ToMatrixSO2Projection_surjective
spin2ToMatrixSO2Projection_eq_iff
spin2MatrixSO2DoubleCover.
```

Therefore the matrix definition of `SO(2)` is now connected explicitly to the
circle model. The current `main` stack also identifies the circle model with
Mathlib's even Clifford-algebra `spinGroup` definition and transports this
matrix projection to that Clifford model.

## 10. Exact evidence boundary

### Demonstrated in Lean

- varying-frame raw second-jet formula;
- cancellation of derivative-of-frame terms by the transformed connection;
- moving-frame equivariance of the second fundamental form;
- Čech cocycle of residual adapted-frame transitions;
- determinant-one reduction to `SO(T) x SO(N)`;
- central `±1` lift defect of a double cover;
- diagonal SpinC defect cancellation;
- two-torsion of determinant square-root defects;
- concrete circle dichotomy `z²=1 -> z=±1`;
- surjective circle-squaring double cover with exact kernel and fibers;
- explicit diagonal quotient in the rank-two model;
- explicit group equivalence `U(1) ≃ SO(2)`;
- matrix-valued rank-two Spin projection with exact two-sheeted fibers;
- explicit group equivalence between the circle model and Mathlib's rank-two
  Clifford `spinGroup`;
- transported Clifford Spin-to-`SO(2)` projection with exact fibers;
- conditional multi-chart pointwise SpinC Cech transition packaging from
  supplied oriented cocycles, chosen Spin lifts, phase transitions and matching
  defects, without transition continuity/smoothness or a bundle total space;
- conditional abelian connection affine overlap law and unique global smooth
  curvature descent when all supplied additive gauge shifts are curvature-flat.

### Still open

- prove the analogous Clifford Spin-to-SO projection in the required tangent and
  normal dimensions;
- extract the required smooth group-valued overlap maps from actual manifold
  frame bundles and prove their compatibility with the supplied Cech inputs;
- instantiate the conditional package to construct the actual oriented and
  SpinC principal bundles globally;
- prove equality of the Spin obstruction and determinant-root obstruction for the
  actual Janus data, equivalently the relevant characteristic-class matching;
- attach and glue the determinant-line connection;
- prove effective actions on all tensor, spinor, twist and ghost sectors;
- include global holonomy, square-root and `Z4` sectors without collapsing them
  into local jet data.

## 11. Validation

The matrix, Clifford rank-two SpinC and scoped PR 10 layers are imported by

```text
JanusFormal.Branches.FundamentalGeometryPEJetUniversality.
```

The current merged head is

```text
96e60eb4df1db049f8488858c5a6b1fdb717b224
```

The theorem head passed focused Lean/Python validation locally before merge;
no independent post-merge workflow is claimed here. The earlier matrix layer
was remotely validated by **Program PE jet universality**, run `29249977153`:

```text
Lean focused head       success
P-E executable audits   success
focused Python tests    success
```

The conditional multi-chart SpinC and abelian-connection descent gates belong
to the active follow-on branch; they do not change the merged-head claim above.

## 12. Next theorem queue

1. Identify the transported rank-two projection with Clifford conjugation on
   embedded vectors and the standard `SO(2)` rotation.
2. Generalize the concrete central double-cover data to the tangent and normal
   dimensions required by the Janus category.
3. Derive the conditional package's transition cocycles and smoothness from
   actual adapted frame bundles.
4. Prove the characteristic-class equality matching Spin and determinant-root
   defects.
5. Instantiate the conditional Cech packages to construct the actual global
   SpinC principal bundle and determinant-line connection.
6. Globalize the existing `nabla II`, `nabla F` and curvature gates over the
   actual bundles and prove the higher-order structured jet-isomorphism theorem.

## 13. Lean correspondence

```text
JanusFormal/Branches/FundamentalGeometryPEJetUniversality/Gates/
  P0EFTJanusMovingAdaptedFrameSecondJet.lean
  P0EFTJanusMovingNormalTransport.lean
  P0EFTJanusAdaptedFrameOverlapCocycle.lean
  P0EFTJanusDeterminantOrientedReduction.lean
  P0EFTJanusCentralLiftCocycleObstruction.lean
  P0EFTJanusSpinCDiagonalDefectCancellation.lean
  P0EFTJanusDeterminantSquareRootDefect.lean
  P0EFTJanusCirclePhaseTwoTorsion.lean
  P0EFTJanusSpin2CircleModel.lean
  P0EFTJanusCircleSO2Equivalence.lean
  P0EFTJanusCliffordSpin2Bridge.lean
  P0EFTJanusCliffordSpin2DoubleCover.lean
  P0EFTJanusEuclideanGlobalSpinCJetRealization.lean
  P0EFTJanusGlobalSpinCCechDescent.lean
  P0EFTJanusCechAbelianConnectionDescent.lean
```
