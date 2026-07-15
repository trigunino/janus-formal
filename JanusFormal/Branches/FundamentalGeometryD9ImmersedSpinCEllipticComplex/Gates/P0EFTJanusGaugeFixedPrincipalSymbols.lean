import Mathlib
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusImmersionFiberAlgebra

namespace JanusFormal
namespace P0EFTJanusGaugeFixedPrincipalSymbols

set_option autoImplicit false

open P0EFTJanusImmersionFiberAlgebra

/-- Zero tangent vector. -/
def zeroTangent : TangentVector3 :=
  { x := 0, y := 0, z := 0 }

/-- Tangent-vector addition. -/
def addTangent
    (first second : TangentVector3) : TangentVector3 :=
  { x := first.x + second.x
    y := first.y + second.y
    z := first.z + second.z }

/-- Tangent-vector subtraction. -/
def subTangent
    (first second : TangentVector3) : TangentVector3 :=
  { x := first.x - second.x
    y := first.y - second.y
    z := first.z - second.z }

/-- Scalar multiplication. -/
def scaleTangent
    (scalar : ℝ)
    (vector : TangentVector3) : TangentVector3 :=
  { x := scalar * vector.x
    y := scalar * vector.y
    z := scalar * vector.z }

/-- Euclidean dot product. -/
def tangentDot
    (first second : TangentVector3) : ℝ :=
  first.x * second.x +
    first.y * second.y +
    first.z * second.z

/-- Squared covector norm. -/
def normSquared (vector : TangentVector3) : ℝ :=
  tangentDot vector vector

/-- Cross product. -/
def crossProduct
    (first second : TangentVector3) : TangentVector3 :=
  { x := first.y * second.z - first.z * second.y
    y := first.z * second.x - first.x * second.z
    z := first.x * second.y - first.y * second.x }

@[simp] theorem scale_zero_tangent
    (scalar : ℝ) :
    scaleTangent scalar zeroTangent = zeroTangent := by
  ext <;> simp [scaleTangent, zeroTangent]

/-- Nonzero covectors have positive Euclidean norm squared. -/
theorem norm_squared_positive_of_nonzero
    (covector : TangentVector3)
    (hNonzero : covector ≠ zeroTangent) :
    0 < normSquared covector := by
  rcases covector with ⟨x, y, z⟩
  unfold normSquared tangentDot
  by_contra hNotPositive
  have hNonpositive : x * x + y * y + z * z ≤ 0 :=
    le_of_not_gt hNotPositive
  have hx : x = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : y = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : z = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  apply hNonzero
  ext <;> simp [zeroTangent, hx, hy, hz]

/-- Gradient symbol `φ ↦ φ ξ`. -/
def gradientSymbol
    (covector : TangentVector3)
    (scalar : ℝ) : TangentVector3 :=
  scaleTangent scalar covector

/-- Divergence symbol `A ↦ ξ·A`. -/
def divergenceSymbol
    (covector field : TangentVector3) : ℝ :=
  tangentDot covector field

/-- Gradient followed by divergence is the scalar Laplace symbol. -/
theorem divergence_gradient_symbol
    (covector : TangentVector3)
    (scalar : ℝ) :
    divergenceSymbol covector
        (gradientSymbol covector scalar) =
      normSquared covector * scalar := by
  unfold divergenceSymbol gradientSymbol
    tangentDot scaleTangent normSquared
  unfold tangentDot
  ring

/-- The de Rham symbol squares to zero at the first stage. -/
theorem cross_gradient_symbol_zero
    (covector : TangentVector3)
    (scalar : ℝ) :
    crossProduct covector
        (gradientSymbol covector scalar) = zeroTangent := by
  ext <;>
    simp [crossProduct, gradientSymbol,
      scaleTangent, zeroTangent] <;>
    ring

/-- The de Rham symbol squares to zero at the second stage. -/
theorem divergence_cross_symbol_zero
    (covector field : TangentVector3) :
    divergenceSymbol covector
        (crossProduct covector field) = 0 := by
  unfold divergenceSymbol tangentDot crossProduct
  ring

/-- Vector triple-product identity. -/
theorem cross_cross_identity
    (covector field : TangentVector3) :
    crossProduct covector
        (crossProduct covector field) =
      subTangent
        (scaleTangent (tangentDot covector field) covector)
        (scaleTangent (normSquared covector) field) := by
  ext <;>
    simp [crossProduct, subTangent, scaleTangent,
      tangentDot, normSquared] <;>
    ring

/-- Gauge-fixed Maxwell principal symbol. -/
def maxwellGaugeFixedSymbol
    (covector field : TangentVector3) : TangentVector3 :=
  subTangent
    (gradientSymbol covector
      (divergenceSymbol covector field))
    (crossProduct covector
      (crossProduct covector field))

/-- Gauge fixing converts Maxwell to the scalar Laplace symbol on each component. -/
theorem maxwell_gauge_fixed_symbol_is_laplacian
    (covector field : TangentVector3) :
    maxwellGaugeFixedSymbol covector field =
      scaleTangent (normSquared covector) field := by
  rw [maxwellGaugeFixedSymbol,
    cross_cross_identity]
  ext <;>
    simp [gradientSymbol, divergenceSymbol,
      subTangent, scaleTangent, tangentDot, normSquared]

/-- Symmetrized derivative/gauge symbol for metric perturbations. -/
def symGradientSymbol
    (covector vector : TangentVector3) : SymmetricTensor3 :=
  { xx := 2 * covector.x * vector.x
    yy := 2 * covector.y * vector.y
    zz := 2 * covector.z * vector.z
    xy := covector.x * vector.y + covector.y * vector.x
    xz := covector.x * vector.z + covector.z * vector.x
    yz := covector.y * vector.z + covector.z * vector.y }

/-- Trace of a symmetric tensor. -/
def symmetricTrace
    (tensor : SymmetricTensor3) : ℝ :=
  tensor.xx + tensor.yy + tensor.zz

/-- de Donder gauge symbol. -/
noncomputable def deDonderSymbol
    (covector : TangentVector3)
    (tensor : SymmetricTensor3) : TangentVector3 :=
  { x := covector.x * tensor.xx +
      covector.y * tensor.xy +
      covector.z * tensor.xz -
      (1 / 2) * covector.x * symmetricTrace tensor
    y := covector.x * tensor.xy +
      covector.y * tensor.yy +
      covector.z * tensor.yz -
      (1 / 2) * covector.y * symmetricTrace tensor
    z := covector.x * tensor.xz +
      covector.y * tensor.yz +
      covector.z * tensor.zz -
      (1 / 2) * covector.z * symmetricTrace tensor }

/-- de Donder composed with the diffeomorphism symbol is the ghost Laplacian. -/
theorem de_donder_sym_gradient
    (covector vector : TangentVector3) :
    deDonderSymbol covector
        (symGradientSymbol covector vector) =
      scaleTangent (normSquared covector) vector := by
  ext <;>
    simp [deDonderSymbol, symGradientSymbol,
      symmetricTrace, scaleTangent, normSquared,
      tangentDot] <;>
    ring

/-- Diffeomorphism-ghost principal symbol. -/
def ghostLaplacianSymbol
    (covector vector : TangentVector3) : TangentVector3 :=
  scaleTangent (normSquared covector) vector

/-- Scalar Jacobi/Laplace principal symbol of the normal immersion mode. -/
def normalJacobiSymbol
    (covector : TangentVector3)
    (normalScalar : ℝ) : ℝ :=
  normSquared covector * normalScalar

/-- Lichnerowicz principal symbol on metric perturbations. -/
def metricLaplacianSymbol
    (covector : TangentVector3)
    (tensor : SymmetricTensor3) : SymmetricTensor3 :=
  scaleSymmetric (normSquared covector) tensor

/-- Nonzero scalar multiplication is injective on tangent fibers. -/
theorem scale_tangent_eq_zero
    (scalar : ℝ)
    (hScalar : scalar ≠ 0)
    (vector : TangentVector3)
    (hZero : scaleTangent scalar vector = zeroTangent) :
    vector = zeroTangent := by
  have hx := congrArg TangentVector3.x hZero
  have hy := congrArg TangentVector3.y hZero
  have hz := congrArg TangentVector3.z hZero
  apply TangentVector3.ext <;>
    simp [scaleTangent, zeroTangent] at hx hy hz ⊢
  · exact hx.resolve_left hScalar
  · exact hy.resolve_left hScalar
  · exact hz.resolve_left hScalar

/-- Nonzero scalar multiplication is injective on symmetric tensors. -/
theorem scale_symmetric_eq_zero
    (scalar : ℝ)
    (hScalar : scalar ≠ 0)
    (tensor : SymmetricTensor3)
    (hZero : scaleSymmetric scalar tensor = zeroSymmetric) :
    tensor = zeroSymmetric := by
  have hxx := congrArg SymmetricTensor3.xx hZero
  have hyy := congrArg SymmetricTensor3.yy hZero
  have hzz := congrArg SymmetricTensor3.zz hZero
  have hxy := congrArg SymmetricTensor3.xy hZero
  have hxz := congrArg SymmetricTensor3.xz hZero
  have hyz := congrArg SymmetricTensor3.yz hZero
  apply SymmetricTensor3.ext <;>
    simp [scaleSymmetric, zeroSymmetric] at hxx hyy hzz hxy hxz hyz ⊢
  · exact hxx.resolve_left hScalar
  · exact hyy.resolve_left hScalar
  · exact hzz.resolve_left hScalar
  · exact hxy.resolve_left hScalar
  · exact hxz.resolve_left hScalar
  · exact hyz.resolve_left hScalar

/-- Maxwell is elliptic after gauge fixing. -/
theorem maxwell_symbol_kernel_trivial
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (field : TangentVector3)
    (hKernel : maxwellGaugeFixedSymbol covector field = zeroTangent) :
    field = zeroTangent := by
  rw [maxwell_gauge_fixed_symbol_is_laplacian] at hKernel
  exact scale_tangent_eq_zero
    (normSquared covector)
    (ne_of_gt (norm_squared_positive_of_nonzero covector hCovector))
    field hKernel

/-- The diffeomorphism ghost symbol is elliptic. -/
theorem ghost_symbol_kernel_trivial
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (ghost : TangentVector3)
    (hKernel : ghostLaplacianSymbol covector ghost = zeroTangent) :
    ghost = zeroTangent := by
  exact scale_tangent_eq_zero
    (normSquared covector)
    (ne_of_gt (norm_squared_positive_of_nonzero covector hCovector))
    ghost hKernel

/-- The gauge-fixed metric principal symbol is elliptic. -/
theorem metric_symbol_kernel_trivial
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (tensor : SymmetricTensor3)
    (hKernel : metricLaplacianSymbol covector tensor = zeroSymmetric) :
    tensor = zeroSymmetric := by
  exact scale_symmetric_eq_zero
    (normSquared covector)
    (ne_of_gt (norm_squared_positive_of_nonzero covector hCovector))
    tensor hKernel

/-- The normal Jacobi principal symbol is elliptic. -/
theorem normal_jacobi_kernel_trivial
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (normalScalar : ℝ)
    (hKernel : normalJacobiSymbol covector normalScalar = 0) :
    normalScalar = 0 := by
  unfold normalJacobiSymbol at hKernel
  exact (mul_eq_zero.mp hKernel).resolve_left
    (ne_of_gt (norm_squared_positive_of_nonzero covector hCovector))

/-- The induced-metric principal symbol alone cannot see a pure normal deformation. -/
def immersionMetricPrincipalSymbol
    (covector : TangentVector3)
    (deformation : TangentVector3 × ℝ) : SymmetricTensor3 :=
  symGradientSymbol covector deformation.1

/-- Every pure normal deformation lies in that principal-symbol kernel. -/
theorem pure_normal_deformation_in_metric_symbol_kernel
    (covector : TangentVector3)
    (normalScalar : ℝ) :
    immersionMetricPrincipalSymbol covector
        (zeroTangent, normalScalar) = zeroSymmetric := by
  ext <;>
    simp [immersionMetricPrincipalSymbol,
      symGradientSymbol, zeroTangent, zeroSymmetric]

/-- Adding the normal Jacobi block restores ellipticity of the immersion deformation system. -/
theorem gauge_fixed_immersion_symbol_kernel_trivial
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (deformation : TangentVector3 × ℝ)
    (hTangent :
      ghostLaplacianSymbol covector deformation.1 = zeroTangent)
    (hNormal :
      normalJacobiSymbol covector deformation.2 = 0) :
    deformation = (zeroTangent, 0) := by
  have hTangentZero :=
    ghost_symbol_kernel_trivial covector hCovector
      deformation.1 hTangent
  have hNormalZero :=
    normal_jacobi_kernel_trivial covector hCovector
      deformation.2 hNormal
  exact Prod.ext hTangentZero hNormalZero

/--
The complete principal-symbol picture is now explicit: de Rham/Maxwell, the
diffeomorphism ghost, the Lichnerowicz metric block and the normal Jacobi block
all reduce to multiplication by `|ξ|²` after gauge fixing. The induced metric
variation alone is not elliptic because normal deformations enter only at lower
order through the second fundamental form.
-/
structure GaugeFixedSymbolPhysicalStatus where
  throatMetricConstructed : Prop
  LeviCivitaConnectionConstructed : Prop
  immersionSecondFundamentalFormConstructed : Prop
  maxwellGaugeFixingDerived : Prop
  diffeomorphismGaugeFixingDerived : Prop
  ghostOperatorsDerived : Prop
  normalJacobiOperatorDerived : Prop
  lichnerowiczOperatorDerived : Prop
  lowerOrderCurvatureTermsComputed : Prop
  boundaryConditionsMatchedToNormalLift : Prop


def gaugeFixedSymbolPhysicalClosure
    (s : GaugeFixedSymbolPhysicalStatus) : Prop :=
  s.throatMetricConstructed /\
  s.LeviCivitaConnectionConstructed /\
  s.immersionSecondFundamentalFormConstructed /\
  s.maxwellGaugeFixingDerived /\
  s.diffeomorphismGaugeFixingDerived /\
  s.ghostOperatorsDerived /\
  s.normalJacobiOperatorDerived /\
  s.lichnerowiczOperatorDerived /\
  s.lowerOrderCurvatureTermsComputed /\
  s.boundaryConditionsMatchedToNormalLift

end P0EFTJanusGaugeFixedPrincipalSymbols
end JanusFormal
