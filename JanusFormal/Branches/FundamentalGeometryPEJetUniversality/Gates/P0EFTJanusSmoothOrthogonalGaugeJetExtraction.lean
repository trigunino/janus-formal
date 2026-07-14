import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothNormalFrameJetExtraction
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalConnectionCurvatureGaugeLaw

namespace JanusFormal
namespace P0EFTJanusSmoothOrthogonalGaugeJetExtraction

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusMetricNormalConnectionCurvature
open P0EFTJanusNormalConnectionFromFrameJet
open P0EFTJanusSmoothNormalFrameJetExtraction
open P0EFTJanusNormalFrameConnectionGaugeLaw
open P0EFTJanusNormalConnectionCurvatureGaugeLaw

universe u v

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]

/-- A twice Fréchet-differentiable orthogonal gauge field, together with an
explicit smooth inverse and symmetry of its second derivative.

The inherited frame field has ambient model equal to the normal model. Thus a
normal-coordinate gauge is treated as a moving orthonormal frame of `Normal`
itself. -/
structure SmoothOrthogonalGaugeTwoJetField
    (Tangent : Type u) (Normal : Type v)
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    extends SmoothOrthonormalNormalFrameTwoJetField
      Tangent Normal Normal where
  inverse : Tangent → Normal →L[ℝ] Normal
  inverse_value : ∀ base normal,
    inverse base (field base normal) = normal
  value_inverse : ∀ base normal,
    field base (inverse base normal) = normal
  second_symmetric : ∀ base x y,
    second base x y = second base y x

/-- The value of the smooth gauge at one base point is a linear isometric
equivalence. -/
def smoothGaugeValueAt
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base : Tangent) : Normal ≃ₗᵢ[ℝ] Normal :=
  LinearIsometryEquiv.ofLinearIsometry
    (frameValueAt
      gauge.toSmoothOrthonormalNormalFrameTwoJetField base)
    (gauge.inverse base).toLinearMap
    (by
      apply LinearMap.ext
      intro normal
      exact gauge.value_inverse base normal)
    (by
      apply LinearMap.ext
      intro normal
      exact gauge.inverse_value base normal)

@[simp]
theorem smoothGaugeValueAt_apply
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base : Tangent) (normal : Normal) :
    smoothGaugeValueAt gauge base normal = gauge.field base normal := by
  rfl

@[simp]
theorem smoothGaugeValueAt_symm_apply
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base : Tangent) (normal : Normal) :
    (smoothGaugeValueAt gauge base).symm normal =
      gauge.inverse base normal := by
  rfl

/-- Extraction of the first orthogonal gauge jet from the smooth field. -/
def orthogonalNormalGaugeOneJetAt
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base : Tangent) : OrthogonalNormalGaugeOneJet Tangent Normal where
  value := smoothGaugeValueAt gauge base
  derivative := (gauge.first base).toLinearMap
  derivative_metric := first_metric_identity
    gauge.toSmoothOrthonormalNormalFrameTwoJetField base

/-- Pointwise left Maurer--Cartan coefficient `g⁻¹ d_x g`. -/
def smoothGaugeLogDerivative
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base x : Tangent) : Normal →L[ℝ] Normal :=
  gaugeLogDerivative (orthogonalNormalGaugeOneJetAt gauge base) x

@[simp]
theorem smoothGaugeLogDerivative_apply
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base x : Tangent) (normal : Normal) :
    smoothGaugeLogDerivative gauge base x normal =
      gauge.inverse base (gauge.first base x normal) := by
  rfl

/-- The extracted Maurer--Cartan coefficient agrees with the normal connection
coefficient of the gauge field viewed as a moving orthonormal frame. -/
theorem smoothGaugeLogDerivative_eq_frameNormalConnectionCoefficient
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base x : Tangent) :
    smoothGaugeLogDerivative gauge base x =
      frameNormalConnectionCoefficient
        (orthonormalNormalFrameTwoJetAt
          gauge.toSmoothOrthonormalNormalFrameTwoJetField base) x := by
  apply ContinuousLinearMap.ext
  intro firstNormal
  apply ext_inner_right ℝ
  intro secondNormal
  rw [frameNormalConnectionCoefficient_inner]
  change
    ⟪(smoothGaugeValueAt gauge base).symm
        (gauge.first base x firstNormal), secondNormal⟫_ℝ =
      ⟪gauge.first base x firstNormal,
        smoothGaugeValueAt gauge base secondNormal⟫_ℝ
  calc
    ⟪(smoothGaugeValueAt gauge base).symm
          (gauge.first base x firstNormal), secondNormal⟫_ℝ =
      ⟪smoothGaugeValueAt gauge base
          ((smoothGaugeValueAt gauge base).symm
            (gauge.first base x firstNormal)),
        smoothGaugeValueAt gauge base secondNormal⟫_ℝ :=
      ((smoothGaugeValueAt gauge base).inner_map_map _ _).symm
    _ = _ := by rw [(smoothGaugeValueAt gauge base).apply_symm_apply]

/-- Applying the gauge value to its logarithmic derivative recovers the ordinary
first derivative of the smooth gauge. -/
theorem smoothGaugeValue_logDerivative
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base x : Tangent) (normal : Normal) :
    smoothGaugeValueAt gauge base
        (smoothGaugeLogDerivative gauge base x normal) =
      gauge.first base x normal := by
  change gauge.field base
      (gauge.inverse base (gauge.first base x normal)) = _
  exact gauge.value_inverse base (gauge.first base x normal)

/-- Explicit derivative of the Maurer--Cartan coefficient:

`d_x kappa_y = g⁻¹ d_x d_y g - kappa_x kappa_y`. -/
def smoothGaugeLogDerivativeDerivative
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base x y : Tangent) : Normal →L[ℝ] Normal :=
  (smoothGaugeValueAt gauge base).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (gauge.second base x y) -
    (smoothGaugeLogDerivative gauge base x).comp
      (smoothGaugeLogDerivative gauge base y)

/-- The derivative formula above agrees with the derivative of the connection
coefficient extracted from the orthonormal gauge frame. -/
theorem smoothGaugeLogDerivativeDerivative_eq_frameNormalConnectionDerivative
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base x y : Tangent) :
    smoothGaugeLogDerivativeDerivative gauge base x y =
      frameNormalConnectionDerivative
        (orthonormalNormalFrameTwoJetAt
          gauge.toSmoothOrthonormalNormalFrameTwoJetField base) x y := by
  apply ContinuousLinearMap.ext
  intro firstNormal
  apply ext_inner_right ℝ
  intro secondNormal
  rw [frameNormalConnectionDerivative_inner]
  have hFirstTerm :
      ⟪(smoothGaugeValueAt gauge base).symm
          (gauge.second base x y firstNormal), secondNormal⟫_ℝ =
        ⟪gauge.second base x y firstNormal,
          smoothGaugeValueAt gauge base secondNormal⟫_ℝ := by
    calc
      ⟪(smoothGaugeValueAt gauge base).symm
            (gauge.second base x y firstNormal), secondNormal⟫_ℝ =
        ⟪smoothGaugeValueAt gauge base
            ((smoothGaugeValueAt gauge base).symm
              (gauge.second base x y firstNormal)),
          smoothGaugeValueAt gauge base secondNormal⟫_ℝ :=
        ((smoothGaugeValueAt gauge base).inner_map_map _ _).symm
      _ = _ := by rw [(smoothGaugeValueAt gauge base).apply_symm_apply]
  have hProduct :=
    gaugeLogDerivative_skew
      (orthogonalNormalGaugeOneJetAt gauge base) x
      (smoothGaugeLogDerivative gauge base y firstNormal)
      secondNormal
  have hProduct' :
      ⟪smoothGaugeLogDerivative gauge base x
          (smoothGaugeLogDerivative gauge base y firstNormal),
        secondNormal⟫_ℝ =
        -⟪smoothGaugeLogDerivative gauge base y firstNormal,
          smoothGaugeLogDerivative gauge base x secondNormal⟫_ℝ := by
    exact hProduct
  have hCross :
      ⟪smoothGaugeLogDerivative gauge base y firstNormal,
          smoothGaugeLogDerivative gauge base x secondNormal⟫_ℝ =
        ⟪gauge.first base y firstNormal,
          gauge.first base x secondNormal⟫_ℝ := by
    calc
      ⟪smoothGaugeLogDerivative gauge base y firstNormal,
          smoothGaugeLogDerivative gauge base x secondNormal⟫_ℝ =
        ⟪smoothGaugeValueAt gauge base
            (smoothGaugeLogDerivative gauge base y firstNormal),
          smoothGaugeValueAt gauge base
            (smoothGaugeLogDerivative gauge base x secondNormal)⟫_ℝ :=
        ((smoothGaugeValueAt gauge base).inner_map_map _ _).symm
      _ = _ := by
        rw [smoothGaugeValue_logDerivative,
          smoothGaugeValue_logDerivative]
  change
    ⟪(smoothGaugeValueAt gauge base).symm
          (gauge.second base x y firstNormal) -
        smoothGaugeLogDerivative gauge base x
          (smoothGaugeLogDerivative gauge base y firstNormal),
      secondNormal⟫_ℝ = _
  rw [inner_sub_left, hFirstTerm, hProduct', hCross, sub_neg_eq_add]
  change
    ⟪gauge.second base x y firstNormal,
        smoothGaugeValueAt gauge base secondNormal⟫_ℝ +
      ⟪gauge.first base y firstNormal,
        gauge.first base x secondNormal⟫_ℝ =
    ⟪gauge.second base x y firstNormal,
        smoothGaugeValueAt gauge base secondNormal⟫_ℝ +
      ⟪gauge.first base y firstNormal,
        gauge.first base x secondNormal⟫_ℝ
  rfl

/-- Maurer--Cartan identity derived from symmetry of the ordinary second
Fréchet derivative. -/
theorem smoothGauge_maurerCartan
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base x y : Tangent) :
    frameNormalConnectionDerivative
          (orthonormalNormalFrameTwoJetAt
            gauge.toSmoothOrthonormalNormalFrameTwoJetField base) x y -
        frameNormalConnectionDerivative
          (orthonormalNormalFrameTwoJetAt
            gauge.toSmoothOrthonormalNormalFrameTwoJetField base) y x +
        operatorCommutator
          (frameNormalConnectionCoefficient
            (orthonormalNormalFrameTwoJetAt
              gauge.toSmoothOrthonormalNormalFrameTwoJetField base) x)
          (frameNormalConnectionCoefficient
            (orthonormalNormalFrameTwoJetAt
              gauge.toSmoothOrthonormalNormalFrameTwoJetField base) y) = 0 := by
  rw [← smoothGaugeLogDerivativeDerivative_eq_frameNormalConnectionDerivative,
    ← smoothGaugeLogDerivativeDerivative_eq_frameNormalConnectionDerivative,
    ← smoothGaugeLogDerivative_eq_frameNormalConnectionCoefficient,
    ← smoothGaugeLogDerivative_eq_frameNormalConnectionCoefficient]
  apply ContinuousLinearMap.ext
  intro normal
  simp [smoothGaugeLogDerivativeDerivative, operatorCommutator]
  rw [gauge.second_symmetric base x y]
  abel

/-- The smooth orthogonal gauge field canonically produces the exact
Maurer--Cartan two-jet required by the curvature gauge law. -/
def orthogonalGaugeMaurerCartanTwoJetAt
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base : Tangent) :
    OrthogonalGaugeMaurerCartanTwoJet Tangent Normal where
  value := smoothGaugeValueAt gauge base
  logDerivative := frameNormalConnectionCoefficientLinear
    (orthonormalNormalFrameTwoJetAt
      gauge.toSmoothOrthonormalNormalFrameTwoJetField base)
  derivative := frameNormalConnectionDerivativeLinear
    (orthonormalNormalFrameTwoJetAt
      gauge.toSmoothOrthonormalNormalFrameTwoJetField base)
  logDerivative_skew := frameNormalConnectionCoefficient_skew
    (orthonormalNormalFrameTwoJetAt
      gauge.toSmoothOrthonormalNormalFrameTwoJetField base)
  derivative_skew := frameNormalConnectionDerivative_skew
    (orthonormalNormalFrameTwoJetAt
      gauge.toSmoothOrthonormalNormalFrameTwoJetField base)
  maurerCartan := smoothGauge_maurerCartan gauge base

/-- Curvature covariance now applies directly to a smooth orthogonal overlap
gauge through its extracted Maurer--Cartan two-jet. -/
theorem curvature_covariance_of_smoothOrthogonalGauge
    (gauge : SmoothOrthogonalGaugeTwoJetField Tangent Normal)
    (base : Tangent)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) :
    gaugeTransformedCurvatureEndomorphism
        (orthogonalGaugeMaurerCartanTwoJetAt gauge base) jet x y =
      orthogonalConjugate (smoothGaugeValueAt gauge base)
        (normalConnectionCurvatureEndomorphism jet x y) :=
  gaugeTransformedCurvature_eq_conjugate
    (orthogonalGaugeMaurerCartanTwoJetAt gauge base) jet x y

/-- Exact boundary after extracting the Maurer--Cartan jet from smooth gauge data. -/
structure SmoothOrthogonalGaugeJetExtractionStatus where
  smoothOrthogonalGaugeFieldDefined : Prop
  inverseFieldStored : Prop
  firstFrechetDerivativeWitnessed : Prop
  secondFrechetDerivativeWitnessed : Prop
  secondDerivativeSymmetryStored : Prop
  gaugeOneJetExtracted : Prop
  logarithmicDerivativeIdentified : Prop
  logarithmicDerivativeDerivativeIdentified : Prop
  maurerCartanEquationDerived : Prop
  maurerCartanTwoJetExtracted : Prop
  curvatureCovarianceApplied : Prop
  overlapGaugeDerivedFromTwoFrameTrivializations : Prop
  variableOverlapCocycleCompatibilityProved : Prop
  globalNormalConnectionDescended : Prop

/-- Closure of smooth orthogonal gauge descent. -/
def smoothOrthogonalGaugeJetExtractionClosed
    (s : SmoothOrthogonalGaugeJetExtractionStatus) : Prop :=
  s.smoothOrthogonalGaugeFieldDefined /\
  s.inverseFieldStored /\
  s.firstFrechetDerivativeWitnessed /\
  s.secondFrechetDerivativeWitnessed /\
  s.secondDerivativeSymmetryStored /\
  s.gaugeOneJetExtracted /\
  s.logarithmicDerivativeIdentified /\
  s.logarithmicDerivativeDerivativeIdentified /\
  s.maurerCartanEquationDerived /\
  s.maurerCartanTwoJetExtracted /\
  s.curvatureCovarianceApplied /\
  s.overlapGaugeDerivedFromTwoFrameTrivializations /\
  s.variableOverlapCocycleCompatibilityProved /\
  s.globalNormalConnectionDescended

/-- A smooth gauge jet is not yet a global descent theorem until it is shown to
be the actual transition map between the local normal-frame trivializations. -/
theorem missing_overlap_realization_blocks_global_normal_connection
    (s : SmoothOrthogonalGaugeJetExtractionStatus)
    (hMissing : Not s.overlapGaugeDerivedFromTwoFrameTrivializations) :
    Not (smoothOrthogonalGaugeJetExtractionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusSmoothOrthogonalGaugeJetExtraction
end JanusFormal
