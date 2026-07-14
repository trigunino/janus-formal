import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameConnectionGaugeLaw

namespace JanusFormal
namespace P0EFTJanusNormalConnectionCurvatureGaugeLaw

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusMetricNormalConnectionCurvature
open P0EFTJanusNormalFrameConnectionGaugeLaw

universe u v

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]

/-- Maurer--Cartan two-jet of an orthogonal normal gauge in the convention
`E' = E ∘ g`.

`logDerivative x` is `kappa_x = g⁻¹ d_x g`. The stored identity is

`d_x kappa_y - d_y kappa_x + [kappa_x,kappa_y] = 0`. -/
structure OrthogonalGaugeMaurerCartanTwoJet
    (Tangent : Type u) (Normal : Type v)
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal] where
  value : Normal ≃ₗᵢ[ℝ] Normal
  logDerivative : Tangent →ₗ[ℝ] Normal →L[ℝ] Normal
  derivative : Tangent →ₗ[ℝ] Tangent →ₗ[ℝ] Normal →L[ℝ] Normal
  logDerivative_skew : ∀ x,
    IsSkewAdjointOperator (logDerivative x)
  derivative_skew : ∀ x y,
    IsSkewAdjointOperator (derivative x y)
  maurerCartan : ∀ x y,
    derivative x y - derivative y x +
      operatorCommutator (logDerivative x) (logDerivative y) = 0

/-- Orthogonal conjugation preserves addition. -/
theorem orthogonalConjugate_add
    (gauge : Normal ≃ₗᵢ[ℝ] Normal)
    (first second : Normal →L[ℝ] Normal) :
    orthogonalConjugate gauge (first + second) =
      orthogonalConjugate gauge first +
        orthogonalConjugate gauge second := by
  apply ContinuousLinearMap.ext
  intro normal
  simp [orthogonalConjugate]

/-- Orthogonal conjugation preserves subtraction. -/
theorem orthogonalConjugate_sub
    (gauge : Normal ≃ₗᵢ[ℝ] Normal)
    (first second : Normal →L[ℝ] Normal) :
    orthogonalConjugate gauge (first - second) =
      orthogonalConjugate gauge first -
        orthogonalConjugate gauge second := by
  apply ContinuousLinearMap.ext
  intro normal
  simp [orthogonalConjugate]

/-- Orthogonal conjugation preserves operator commutators. -/
theorem orthogonalConjugate_commutator
    (gauge : Normal ≃ₗᵢ[ℝ] Normal)
    (first second : Normal →L[ℝ] Normal) :
    orthogonalConjugate gauge
        (operatorCommutator first second) =
      operatorCommutator
        (orthogonalConjugate gauge first)
        (orthogonalConjugate gauge second) := by
  apply ContinuousLinearMap.ext
  intro normal
  simp [orthogonalConjugate, operatorCommutator]

/-- The Maurer--Cartan curvature of the logarithmic derivative. -/
def gaugeMaurerCartanCurvature
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (x y : Tangent) : Normal →L[ℝ] Normal :=
  gauge.derivative x y - gauge.derivative y x +
    operatorCommutator (gauge.logDerivative x)
      (gauge.logDerivative y)

/-- The stored Maurer--Cartan equation says that this curvature vanishes. -/
theorem gaugeMaurerCartanCurvature_eq_zero
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (x y : Tangent) :
    gaugeMaurerCartanCurvature gauge x y = 0 :=
  gauge.maurerCartan x y

/-- Homogeneous conjugated part of the transformed connection coefficient. -/
def conjugatedConnectionCoefficient
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x : Tangent) : Normal →L[ℝ] Normal :=
  orthogonalConjugate gauge.value (jet.coefficient x)

/-- Gauge-transformed connection coefficient

`omega'_x = g⁻¹ omega_x g + kappa_x`. -/
def gaugeTransformedConnectionCoefficient
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x : Tangent) : Normal →L[ℝ] Normal :=
  conjugatedConnectionCoefficient gauge jet x +
    gauge.logDerivative x

/-- Derivative of the transformed coefficient:

`partial_x omega'_y
 = g⁻¹(partial_x omega_y)g
   + [g⁻¹ omega_y g,kappa_x]
   + partial_x kappa_y`. -/
def gaugeTransformedConnectionDerivative
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) : Normal →L[ℝ] Normal :=
  orthogonalConjugate gauge.value (jet.derivative x y) +
    operatorCommutator
      (conjugatedConnectionCoefficient gauge jet y)
      (gauge.logDerivative x) +
    gauge.derivative x y

/-- The transformed coefficient remains skew-adjoint. -/
theorem gaugeTransformedConnectionCoefficient_skew
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x : Tangent) :
    IsSkewAdjointOperator
      (gaugeTransformedConnectionCoefficient gauge jet x) :=
  skewAdjoint_add
    (orthogonalConjugate_skew gauge.value
      (jet.coefficient_skew x))
    (gauge.logDerivative_skew x)

/-- The transformed derivative remains skew-adjoint. -/
theorem gaugeTransformedConnectionDerivative_skew
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) :
    IsSkewAdjointOperator
      (gaugeTransformedConnectionDerivative gauge jet x y) :=
  skewAdjoint_add
    (skewAdjoint_add
      (orthogonalConjugate_skew gauge.value
        (jet.derivative_skew x y))
      (skewAdjoint_operatorCommutator
        (orthogonalConjugate_skew gauge.value
          (jet.coefficient_skew y))
        (gauge.logDerivative_skew x)))
    (gauge.derivative_skew x y)

/-- Curvature computed from the transformed coefficient and derivative. -/
def gaugeTransformedCurvatureEndomorphism
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) : Normal →L[ℝ] Normal :=
  gaugeTransformedConnectionDerivative gauge jet x y -
    gaugeTransformedConnectionDerivative gauge jet y x +
    operatorCommutator
      (gaugeTransformedConnectionCoefficient gauge jet x)
      (gaugeTransformedConnectionCoefficient gauge jet y)

/-- General curvature decomposition before imposing Maurer--Cartan:

`R' = g⁻¹ R g + d kappa + kappa wedge kappa`. -/
theorem gaugeTransformedCurvature_decomposition
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) :
    gaugeTransformedCurvatureEndomorphism gauge jet x y =
      orthogonalConjugate gauge.value
        (normalConnectionCurvatureEndomorphism jet x y) +
      gaugeMaurerCartanCurvature gauge x y := by
  apply ContinuousLinearMap.ext
  intro normal
  simp [gaugeTransformedCurvatureEndomorphism,
    gaugeTransformedConnectionDerivative,
    gaugeTransformedConnectionCoefficient,
    conjugatedConnectionCoefficient,
    gaugeMaurerCartanCurvature,
    normalConnectionCurvatureEndomorphism,
    orthogonalConjugate, operatorCommutator]
  abel

/-- Curvature transforms homogeneously under the orthogonal gauge. -/
theorem gaugeTransformedCurvature_eq_conjugate
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) :
    gaugeTransformedCurvatureEndomorphism gauge jet x y =
      orthogonalConjugate gauge.value
        (normalConnectionCurvatureEndomorphism jet x y) := by
  rw [gaugeTransformedCurvature_decomposition,
    gaugeMaurerCartanCurvature_eq_zero, add_zero]

/-- Scalar curvature covariance:

`<R' xi,eta> = <R(g xi),g eta>`. -/
theorem gaugeTransformedCurvatureScalar_eq
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    ⟪gaugeTransformedCurvatureEndomorphism gauge jet x y firstNormal,
      secondNormal⟫_ℝ =
      ⟪normalConnectionCurvatureEndomorphism jet x y
          (gauge.value firstNormal),
        gauge.value secondNormal⟫_ℝ := by
  rw [gaugeTransformedCurvature_eq_conjugate]
  calc
    ⟪gauge.value.symm
        (normalConnectionCurvatureEndomorphism jet x y
          (gauge.value firstNormal)), secondNormal⟫_ℝ =
      ⟪gauge.value
          (gauge.value.symm
            (normalConnectionCurvatureEndomorphism jet x y
              (gauge.value firstNormal))),
        gauge.value secondNormal⟫_ℝ :=
      (gauge.value.inner_map_map _ _).symm
    _ = _ := by rw [gauge.value.apply_symm_apply]

/-- The transformed curvature is skew-adjoint and therefore has the required
normal-pair antisymmetry. -/
theorem gaugeTransformedCurvature_skew
    (gauge : OrthogonalGaugeMaurerCartanTwoJet Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) :
    IsSkewAdjointOperator
      (gaugeTransformedCurvatureEndomorphism gauge jet x y) := by
  rw [gaugeTransformedCurvature_eq_conjugate]
  exact orthogonalConjugate_skew gauge.value
    (normalConnectionCurvatureEndomorphism_skew jet x y)

/-- Exact boundary after the local curvature gauge law. -/
structure NormalConnectionCurvatureGaugeLawStatus where
  maurerCartanGaugeTwoJetDefined : Prop
  transformedCoefficientDefined : Prop
  transformedDerivativeDefined : Prop
  transformedMetricCompatibilityProved : Prop
  curvatureDecompositionProved : Prop
  curvatureConjugacyProved : Prop
  scalarCurvatureCovarianceProved : Prop
  maurerCartanJetExtractedFromSmoothGauge : Prop
  frameGaugeJetCompatibilityProved : Prop
  manifoldOverlapCurvatureLawProved : Prop
  globalNormalConnectionDescended : Prop

/-- Closure of the global gauge-descent stage. -/
def normalConnectionCurvatureGaugeLawClosed
    (s : NormalConnectionCurvatureGaugeLawStatus) : Prop :=
  s.maurerCartanGaugeTwoJetDefined /\
  s.transformedCoefficientDefined /\
  s.transformedDerivativeDefined /\
  s.transformedMetricCompatibilityProved /\
  s.curvatureDecompositionProved /\
  s.curvatureConjugacyProved /\
  s.scalarCurvatureCovarianceProved /\
  s.maurerCartanJetExtractedFromSmoothGauge /\
  s.frameGaugeJetCompatibilityProved /\
  s.manifoldOverlapCurvatureLawProved /\
  s.globalNormalConnectionDescended

/-- Algebraic curvature covariance still has to be linked to the two-jet of the
actual smooth overlap gauge. -/
theorem missing_smooth_gauge_jet_blocks_global_descent
    (s : NormalConnectionCurvatureGaugeLawStatus)
    (hMissing : Not s.maurerCartanJetExtractedFromSmoothGauge) :
    Not (normalConnectionCurvatureGaugeLawClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusNormalConnectionCurvatureGaugeLaw
end JanusFormal
