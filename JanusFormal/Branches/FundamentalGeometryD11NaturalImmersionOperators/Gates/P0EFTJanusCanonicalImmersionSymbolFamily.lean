import Mathlib

namespace JanusFormal
namespace P0EFTJanusCanonicalImmersionSymbolFamily

set_option autoImplicit false

/-- Cotangent fiber of the three-dimensional throat in an orthonormal frame. -/
@[ext] structure Covector3 where
  x : ℝ
  y : ℝ
  z : ℝ

/-- Zero covector. -/
def zeroCovector : Covector3 :=
  { x := 0, y := 0, z := 0 }

/-- Squared norm supplied by the induced Riemannian metric. -/
def normSquared (covector : Covector3) : ℝ :=
  covector.x ^ 2 + covector.y ^ 2 + covector.z ^ 2

/-- Every nonzero covector has positive squared norm. -/
theorem norm_squared_positive_of_nonzero
    (covector : Covector3)
    (hNonzero : covector ≠ zeroCovector) :
    0 < normSquared covector := by
  rcases covector with ⟨x, y, z⟩
  unfold normSquared
  by_contra hNotPositive
  have hNonpositive : x ^ 2 + y ^ 2 + z ^ 2 ≤ 0 :=
    le_of_not_gt hNotPositive
  have hx : x = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : y = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : z = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  apply hNonzero
  ext <;> simp [zeroCovector, hx, hy, hz]

/-- Finite coordinate fiber used for the local symbol audit. -/
abbrev CoordinateFiber (rank : ℕ) := Fin rank → ℝ

/-- Zero coordinate fiber. -/
def zeroFiber (rank : ℕ) : CoordinateFiber rank :=
  fun _ => 0

/-- Scalar principal symbol on a coordinate fiber. -/
def scaleFiber
    {rank : ℕ}
    (scalar : ℝ)
    (value : CoordinateFiber rank) : CoordinateFiber rank :=
  fun index => scalar * value index

/-- Multiplication by a nonzero scalar has trivial kernel. -/
theorem scale_fiber_kernel_trivial
    {rank : ℕ}
    (scalar : ℝ)
    (hScalar : scalar ≠ 0)
    (value : CoordinateFiber rank)
    (hKernel : scaleFiber scalar value = zeroFiber rank) :
    value = zeroFiber rank := by
  funext index
  have hCoordinate := congrFun hKernel index
  simp [scaleFiber, zeroFiber] at hCoordinate ⊢
  exact hCoordinate.resolve_left hScalar

/--
Gauge-fixed local fields naturally associated with an immersed SpinC throat.
The spinor entry is the real rank-four fiber of the squared rank-two complex
Dirac operator, so every block below is of Laplace type.
-/
@[ext] structure NaturalLaplaceField where
  normalMode : CoordinateFiber 1
  gaugeOneForm : CoordinateFiber 3
  symmetricMetric : CoordinateFiber 6
  squaredSpinor : CoordinateFiber 4
  u1Ghost : CoordinateFiber 1
  diffeomorphismGhost : CoordinateFiber 3

/-- Zero field. -/
def zeroNaturalLaplaceField : NaturalLaplaceField :=
  { normalMode := zeroFiber 1
    gaugeOneForm := zeroFiber 3
    symmetricMetric := zeroFiber 6
    squaredSpinor := zeroFiber 4
    u1Ghost := zeroFiber 1
    diffeomorphismGhost := zeroFiber 3 }

/--
Universal gauge-fixed principal symbol.  Every second-order block has symbol
`|ξ|² Id`; monopole, normal-root, curvature and mass data enter only in lower
order terms and domains.
-/
def canonicalPrincipalSymbol
    (covector : Covector3)
    (field : NaturalLaplaceField) : NaturalLaplaceField :=
  let weight := normSquared covector
  { normalMode := scaleFiber weight field.normalMode
    gaugeOneForm := scaleFiber weight field.gaugeOneForm
    symmetricMetric := scaleFiber weight field.symmetricMetric
    squaredSpinor := scaleFiber weight field.squaredSpinor
    u1Ghost := scaleFiber weight field.u1Ghost
    diffeomorphismGhost :=
      scaleFiber weight field.diffeomorphismGhost }

/-- The complete block symbol is elliptic at every nonzero covector. -/
theorem canonical_principal_symbol_kernel_trivial
    (covector : Covector3)
    (hCovector : covector ≠ zeroCovector)
    (field : NaturalLaplaceField)
    (hKernel :
      canonicalPrincipalSymbol covector field =
        zeroNaturalLaplaceField) :
    field = zeroNaturalLaplaceField := by
  have hWeight : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero covector hCovector)
  have hNormal := congrArg NaturalLaplaceField.normalMode hKernel
  have hGauge := congrArg NaturalLaplaceField.gaugeOneForm hKernel
  have hMetric := congrArg NaturalLaplaceField.symmetricMetric hKernel
  have hSpinor := congrArg NaturalLaplaceField.squaredSpinor hKernel
  have hU1 := congrArg NaturalLaplaceField.u1Ghost hKernel
  have hDiff := congrArg NaturalLaplaceField.diffeomorphismGhost hKernel
  exact NaturalLaplaceField.ext
    (scale_fiber_kernel_trivial
      (normSquared covector) hWeight field.normalMode hNormal)
    (scale_fiber_kernel_trivial
      (normSquared covector) hWeight field.gaugeOneForm hGauge)
    (scale_fiber_kernel_trivial
      (normSquared covector) hWeight field.symmetricMetric hMetric)
    (scale_fiber_kernel_trivial
      (normSquared covector) hWeight field.squaredSpinor hSpinor)
    (scale_fiber_kernel_trivial
      (normSquared covector) hWeight field.u1Ghost hU1)
    (scale_fiber_kernel_trivial
      (normSquared covector) hWeight field.diffeomorphismGhost hDiff)

/-- Raw local fiber rank of the displayed block package. -/
def canonicalRawFiberRank : ℕ :=
  1 + 3 + 6 + 4 + 1 + 3

@[simp] theorem canonical_raw_fiber_rank_is_eighteen :
    canonicalRawFiberRank = 18 := by
  norm_num [canonicalRawFiberRank]

/-- The rank-six metric block splits algebraically as trace plus traceless rank five. -/
theorem metric_rank_trace_traceless_split :
    (6 : ℕ) = 1 + 5 := by
  norm_num

/--
Geometric inputs needed to globalize this symbol family.  These are precisely
the data induced by a Riemannian immersion plus SpinC/gauge decoration; an
action is not yet needed at principal-symbol level.
-/
structure CanonicalSymbolGeometricStatus where
  compactThroatConstructed : Prop
  immersionConstructed : Prop
  inducedRiemannianMetricConstructed : Prop
  tangentNormalExactSequenceConstructed : Prop
  spinorBundleConstructed : Prop
  primitiveTwistingLineConstructed : Prop
  normalRootFlatLineConstructed : Prop
  gaugeBundleConstructed : Prop
  naturalTensorBundlesConstructed : Prop
  principalSymbolsIdentifiedWithCanonicalModel : Prop


def canonicalSymbolGeometricClosure
    (s : CanonicalSymbolGeometricStatus) : Prop :=
  s.compactThroatConstructed /\
  s.immersionConstructed /\
  s.inducedRiemannianMetricConstructed /\
  s.tangentNormalExactSequenceConstructed /\
  s.spinorBundleConstructed /\
  s.primitiveTwistingLineConstructed /\
  s.normalRootFlatLineConstructed /\
  s.gaugeBundleConstructed /\
  s.naturalTensorBundlesConstructed /\
  s.principalSymbolsIdentifiedWithCanonicalModel

end P0EFTJanusCanonicalImmersionSymbolFamily
end JanusFormal
