import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFourDimensionalDensityLieDerivativeNoether
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricCoupledScalarMatterJetVariation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInverseRelativeRootFrechet

/-!
# Metric-induced scalar stress variation in four dimensions

This gate removes the independent measure and inverse-metric slots of the
earlier scalar first-jet model.  A single symmetric metric `g` supplies both
`sqrt |det g|` and the exact inverse of the affine curve `g + t delta-g`.
The curve is based in an open component where a chosen determinant sign is
fixed.  Its actual first variation is identified with a pointwise symmetric
stress tensor.

The scalar value and coordinate covector `p_mu` are fixed in this gate.  This
is a pointwise four-dimensional calculation; no spacetime integration,
covariant derivative, field equation, conservation law, or global signature
theorem is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMetricInducedScalarStressVariation4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInverseRelativeRootFrechet

abbrev Index4 := Fin 4
abbrev Vector4 := Index4 -> Real
abbrev Matrix4 := Matrix Index4 Index4 Real

/-- Matrix-valued derivative with the Frobenius norm fixed explicitly. -/
def FrobeniusMatrixHasDerivAt
    (function : Real -> Matrix4) (derivative : Matrix4) (point : Real) : Prop :=
  @HasFDerivAt Real DenselyNormedField.toNontriviallyNormedField Real
    NormedField.toNormedCommRing.toAddCommGroup
    Semiring.toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Matrix4
    Matrix.frobeniusNormedAddCommGroup.toAddCommGroup
    Matrix.frobeniusNormedSpace.toModule
    Matrix.frobeniusNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    function (ContinuousLinearMap.toSpanSingleton Real derivative) point

/-- Scalar derivative with the instances produced by Frobenius composition. -/
def FrobeniusScalarHasDerivAt
    (function : Real -> Real) (derivative point : Real) : Prop :=
  @HasFDerivAt Real DenselyNormedField.toNontriviallyNormedField Real
    NormedField.toNormedCommRing.toAddCommGroup
    Semiring.toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Real
    Real.normedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace Real Real).toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    function (ContinuousLinearMap.toSpanSingleton Real derivative) point

/-- Open matrix domain on which `orientation * det g` is positive. -/
def fixedDeterminantSignDomain (orientation : Real) : Set Matrix4 :=
  {metric | 0 < orientation * Matrix.det metric}

theorem fixedDeterminantSignDomain_isOpen (orientation : Real) :
    IsOpen (fixedDeterminantSignDomain orientation) := by
  rw [show fixedDeterminantSignDomain orientation =
      (fun metric : Matrix4 => orientation * Matrix.det metric) ⁻¹' Set.Ioi 0 by
        rfl]
  exact isOpen_Ioi.preimage
    (continuous_const.mul (continuous_id.matrix_det))

/-- A symmetric metric based in one open determinant-sign component. -/
structure FixedSignMetric4 where
  metric : Matrix4
  orientation : Real
  orientation_ne_zero : orientation ≠ 0
  metric_symmetric : metric.transpose = metric
  metric_mem_domain : metric ∈ fixedDeterminantSignDomain orientation

theorem FixedSignMetric4.det_ne_zero (data : FixedSignMetric4) :
    Matrix.det data.metric ≠ 0 := by
  intro hZero
  have hPositive := data.metric_mem_domain
  simp [fixedDeterminantSignDomain, hZero] at hPositive

theorem FixedSignMetric4.metric_isUnit (data : FixedSignMetric4) :
    IsUnit data.metric := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr data.det_ne_zero

theorem FixedSignMetric4.inverse_symmetric (data : FixedSignMetric4) :
    data.metric⁻¹.transpose = data.metric⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, data.metric_symmetric]

/-- A symmetric covariant metric direction. -/
structure SymmetricMetricVariation4 where
  tensor : Matrix4
  tensor_symmetric : tensor.transpose = tensor

/-- Genuine affine curve in the covariant metric. -/
def metricCurve
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (t : Real) : Matrix4 :=
  data.metric + t • variation.tensor

@[simp]
theorem metricCurve_zero
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4) :
    metricCurve data variation 0 = data.metric := by
  simp [metricCurve]

theorem metricCurve_hasDerivAt
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4) :
    FrobeniusMatrixHasDerivAt (metricCurve data variation)
      variation.tensor 0 := by
  unfold FrobeniusMatrixHasDerivAt
  have hDerivative :=
    ((hasDerivAt_id (0 : Real)).smul_const variation.tensor).const_add
      data.metric
  exact (hDerivative.congr_deriv (one_smul Real variation.tensor)).hasFDerivAt

/-- The metric curve remains in the same fixed-sign open component locally. -/
theorem eventually_metricCurve_mem_domain
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4) :
    ∀ᶠ t in nhds (0 : Real),
      metricCurve data variation t ∈
        fixedDeterminantSignDomain data.orientation := by
  have hNeighbourhood :
      fixedDeterminantSignDomain data.orientation ∈ nhds data.metric :=
    (fixedDeterminantSignDomain_isOpen data.orientation).mem_nhds
      data.metric_mem_domain
  rw [← metricCurve_zero data variation] at hNeighbourhood
  exact (metricCurve_hasDerivAt data variation).continuousAt hNeighbourhood

/-- Actual inverse of the same covariant metric curve. -/
def exactInverseMetricCurve
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (t : Real) : Matrix4 :=
  (metricCurve data variation t)⁻¹

@[simp]
theorem exactInverseMetricCurve_zero
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4) :
    exactInverseMetricCurve data variation 0 = data.metric⁻¹ := by
  simp [exactInverseMetricCurve]

theorem exactInverseMetricCurve_hasDerivAt
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4) :
    FrobeniusMatrixHasDerivAt (exactInverseMetricCurve data variation)
      (-(data.metric⁻¹ * variation.tensor * data.metric⁻¹)) 0 := by
  unfold FrobeniusMatrixHasDerivAt
  have hComposite :=
    (matrixInverse_hasFDerivAt data.metric data.metric_isUnit).comp_hasDerivAt_of_eq 0
      (metricCurve_hasDerivAt data variation).hasDerivAt (by simp)
  have hDerivative :
      matrixInverseDerivative data.metric
          ((ContinuousLinearMap.toSpanSingleton Real variation.tensor) 1) =
        -(data.metric⁻¹ * variation.tensor * data.metric⁻¹) := by
    simp [matrixInverseDerivative_apply]
  have hCorrect := hComposite.congr_deriv hDerivative
  change HasFDerivAt
    (fun t : Real => (metricCurve data variation t)⁻¹)
    (ContinuousLinearMap.toSpanSingleton Real
      (-(data.metric⁻¹ * variation.tensor * data.metric⁻¹))) 0
  exact hCorrect.hasFDerivAt

/-- Relative covariant metric tangent `g⁻¹ delta-g`. -/
def relativeMetricVariation
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4) : Matrix4 :=
  data.metric⁻¹ * variation.tensor

theorem metricCurve_factor
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (t : Real) :
    metricCurve data variation t =
      data.metric * (1 + t • relativeMetricVariation data variation) := by
  rw [metricCurve, relativeMetricVariation, Matrix.mul_add, Matrix.mul_one,
    Matrix.mul_smul, ← Matrix.mul_assoc]
  have hDet : IsUnit (Matrix.det data.metric) :=
    (Matrix.isUnit_iff_isUnit_det _).mp data.metric_isUnit
  rw [Matrix.mul_nonsing_inv data.metric hDet, Matrix.one_mul]

/-- Jacobi formula for the determinant of the genuine `4 x 4` metric curve. -/
theorem metricDeterminantCurve_hasDerivAt
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4) :
    HasDerivAt (fun t : Real => Matrix.det (metricCurve data variation t))
      (Matrix.det data.metric *
        Matrix.trace (relativeMetricVariation data variation)) 0 := by
  have hReduced :=
    (P0EFTJanusFourDimensionalDensityLieDerivativeNoether.jacobianDeterminant_hasDerivAt
      (relativeMetricVariation data variation)).const_mul
        (Matrix.det data.metric)
  exact hReduced.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by
      change Matrix.det (metricCurve data variation t) =
        Matrix.det data.metric *
          Matrix.det (1 + t • relativeMetricVariation data variation)
      rw [metricCurve_factor, Matrix.det_mul])

/-- Actual derivative of the metric-induced volume density. -/
theorem metricMeasureCurve_hasDerivAt
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4) :
    HasDerivAt
      (fun t : Real => Real.sqrt |Matrix.det (metricCurve data variation t)|)
      ((Real.sqrt |Matrix.det data.metric| / 2) *
        Matrix.trace (relativeMetricVariation data variation)) 0 := by
  have hDet := metricDeterminantCurve_hasDerivAt data variation
  have hBase : Matrix.det (metricCurve data variation 0) ≠ 0 := by
    simpa using data.det_ne_zero
  have hAbs := (hasDerivAt_abs hBase).comp 0 hDet
  have hAbsCorrect : HasDerivAt
      (fun t : Real => |Matrix.det (metricCurve data variation t)|)
      (|Matrix.det data.metric| *
        Matrix.trace (relativeMetricVariation data variation)) 0 := by
    refine hAbs.congr_deriv ?_
    simp only [metricCurve_zero]
    rw [← mul_assoc, sign_mul_self]
  have hAbsNe : |Matrix.det data.metric| ≠ 0 :=
    abs_ne_zero.mpr data.det_ne_zero
  have hSqrt := hAbsCorrect.sqrt (by simpa using hAbsNe)
  have hSqrtNe : Real.sqrt |Matrix.det data.metric| ≠ 0 :=
    (Real.sqrt_ne_zero (abs_nonneg _)).mpr hAbsNe
  have hCoefficient :
      (|Matrix.det data.metric| *
          Matrix.trace (relativeMetricVariation data variation)) /
          (2 * Real.sqrt |Matrix.det (metricCurve data variation 0)|) =
        (Real.sqrt |Matrix.det data.metric| / 2) *
          Matrix.trace (relativeMetricVariation data variation) := by
    simp only [metricCurve_zero]
    nth_rewrite 1 [← Real.mul_self_sqrt
      (abs_nonneg (Matrix.det data.metric))]
    field_simp
  exact hSqrt.congr_deriv hCoefficient

/-- Kinetic dependence on an inverse metric as a continuous covector. -/
def inverseMetricKineticCovector (gradient : Vector4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun inverseMetric => scalarKinetic inverseMetric gradient
      map_add' := by
        intro first second
        simp [scalarKinetic, Matrix.add_apply, add_mul,
          Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro scalar inverseMetric
        simp [scalarKinetic, Matrix.smul_apply, Finset.mul_sum]
        ring }

@[simp]
theorem inverseMetricKineticCovector_apply
    (gradient : Vector4) (inverseMetric : Matrix4) :
    inverseMetricKineticCovector gradient inverseMetric =
      scalarKinetic inverseMetric gradient := by
  rfl

/-- The scalar Lagrangian follows the exact inverse of the metric curve. -/
theorem scalarLagrangian_exactInverseCurve_hasDerivAt
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (massSquared source : Real) (jet : ScalarMatterJet) :
    FrobeniusScalarHasDerivAt
      (fun t => scalarMatterLagrangian massSquared source
        (exactInverseMetricCurve data variation t) jet)
      (scalarKinetic (-(data.metric⁻¹ * variation.tensor * data.metric⁻¹))
        jet.gradient) 0 := by
  unfold FrobeniusScalarHasDerivAt
  have hInverse := exactInverseMetricCurve_hasDerivAt data variation
  unfold FrobeniusMatrixHasDerivAt at hInverse
  have hInverseDeriv : HasDerivAt (exactInverseMetricCurve data variation)
      (-(data.metric⁻¹ * variation.tensor * data.metric⁻¹)) 0 :=
    hInverse.hasDerivAt.congr_deriv (by simp)
  have hKinetic :=
    (inverseMetricKineticCovector jet.gradient).hasFDerivAt.comp_hasDerivAt 0
      hInverseDeriv
  have hSum := hKinetic.const_add
    (massSquared / 2 * jet.field ^ 2 + source * jet.field)
  have hDerivative :
      inverseMetricKineticCovector jet.gradient
          (-(data.metric⁻¹ * variation.tensor * data.metric⁻¹)) =
        scalarKinetic
          (-(data.metric⁻¹ * variation.tensor * data.metric⁻¹))
          jet.gradient := rfl
  have hCorrect := hSum.congr_deriv hDerivative
  exact (hCorrect.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by
      simp [scalarMatterLagrangian, Function.comp_apply]
      ring)).hasFDerivAt

/-- The density in which measure and inverse come from the same metric. -/
def metricInducedScalarDensityCurve
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (massSquared source : Real) (jet : ScalarMatterJet) (t : Real) : Real :=
  Real.sqrt |Matrix.det (metricCurve data variation t)| *
    scalarMatterLagrangian massSquared source
      (exactInverseMetricCurve data variation t) jet

/-- Derived metric variation coefficient, with no independent measure or
inverse-metric tangent. -/
def metricInducedScalarDensityFirstVariation
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (massSquared source : Real) (jet : ScalarMatterJet) : Real :=
  (Real.sqrt |Matrix.det data.metric| / 2) *
      Matrix.trace (data.metric⁻¹ * variation.tensor) *
      scalarMatterLagrangian massSquared source data.metric⁻¹ jet +
    Real.sqrt |Matrix.det data.metric| *
      scalarKinetic (-(data.metric⁻¹ * variation.tensor * data.metric⁻¹))
        jet.gradient

/-- Genuine constrained metric derivative of the scalar density. -/
theorem metricInducedScalarDensityCurve_hasDerivAt
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (massSquared source : Real) (jet : ScalarMatterJet) :
    FrobeniusScalarHasDerivAt
      (metricInducedScalarDensityCurve data variation massSquared source jet)
      (metricInducedScalarDensityFirstVariation data variation
        massSquared source jet) 0 := by
  unfold FrobeniusScalarHasDerivAt
  have hMeasure := metricMeasureCurve_hasDerivAt data variation
  have hMatter := scalarLagrangian_exactInverseCurve_hasDerivAt
    data variation massSquared source jet
  unfold FrobeniusScalarHasDerivAt at hMatter
  have hMatterDeriv : HasDerivAt
      (fun t => scalarMatterLagrangian massSquared source
        (exactInverseMetricCurve data variation t) jet)
      (scalarKinetic (-(data.metric⁻¹ * variation.tensor * data.metric⁻¹))
        jet.gradient) 0 := hMatter.hasDerivAt.congr_deriv (by simp)
  have hProduct := hMeasure.mul hMatterDeriv
  have hDerivative :
      (Real.sqrt |Matrix.det data.metric| / 2 *
            Matrix.trace (relativeMetricVariation data variation)) *
          scalarMatterLagrangian massSquared source
            (exactInverseMetricCurve data variation 0) jet +
        Real.sqrt |Matrix.det (metricCurve data variation 0)| *
          scalarKinetic
            (-(data.metric⁻¹ * variation.tensor * data.metric⁻¹))
            jet.gradient =
        metricInducedScalarDensityFirstVariation data variation
          massSquared source jet := by
    simp [metricInducedScalarDensityFirstVariation, relativeMetricVariation]
  have hCorrect := hProduct.congr_deriv hDerivative
  exact (hCorrect.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by
      simp [metricInducedScalarDensityCurve])).hasFDerivAt

/-- Covector obtained by raising the fixed scalar gradient. -/
def raisedGradient (data : FixedSignMetric4) (gradient : Vector4) : Vector4 :=
  Matrix.mulVec data.metric⁻¹ gradient

/-- Standard contravariant scalar stress tensor for the sign convention of
`scalarMatterLagrangian`. -/
def pointwiseScalarStressTensor
    (data : FixedSignMetric4) (massSquared source : Real)
    (jet : ScalarMatterJet) : Matrix4 :=
  fun first second =>
    raisedGradient data jet.gradient first *
        raisedGradient data jet.gradient second -
      (data.metric⁻¹) first second *
        scalarMatterLagrangian massSquared source data.metric⁻¹ jet

theorem pointwiseScalarStressTensor_symmetric
    (data : FixedSignMetric4) (massSquared source : Real)
    (jet : ScalarMatterJet) :
    (pointwiseScalarStressTensor data massSquared source jet).transpose =
      pointwiseScalarStressTensor data massSquared source jet := by
  ext first second
  have hEntry := congrArg (fun matrix : Matrix4 => matrix first second)
    data.inverse_symmetric
  simp only [Matrix.transpose_apply] at hEntry
  simp [pointwiseScalarStressTensor, hEntry]
  ring

/-- Pair a contravariant tensor with a covariant metric variation. -/
def tensorMetricPairing (tensor variation : Matrix4) : Real :=
  ∑ first : Index4, ∑ second : Index4,
    tensor first second * variation first second

private theorem trace_mul_eq_metric_pairing
    (inverseMetric variation : Matrix4) :
    Matrix.trace (inverseMetric * variation) =
      ∑ first : Index4, ∑ second : Index4,
        inverseMetric first second * variation second first := by
  simp [Matrix.trace, Matrix.mul_apply]

private theorem scalarKinetic_eq_dotProduct
    (inverseMetric : Matrix4) (gradient : Vector4) :
    scalarKinetic inverseMetric gradient =
      (1 / 2 : Real) *
        dotProduct gradient (Matrix.mulVec inverseMetric gradient) := by
  rw [Matrix.dot_mulVec_eq_sum_sum]
  unfold scalarKinetic
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

private theorem scalarKinetic_inverse_product_eq_raised_pairing
    (data : FixedSignMetric4) (variation : Matrix4) (gradient : Vector4) :
    scalarKinetic (data.metric⁻¹ * variation * data.metric⁻¹) gradient =
      (1 / 2 : Real) *
        ∑ first : Index4, ∑ second : Index4,
          raisedGradient data gradient first *
            raisedGradient data gradient second * variation first second := by
  have hInverseSymmetric := data.inverse_symmetric
  have hVecMul : Matrix.vecMul gradient data.metric⁻¹ =
      Matrix.mulVec data.metric⁻¹ gradient := by
    calc
      Matrix.vecMul gradient data.metric⁻¹ =
          Matrix.vecMul gradient data.metric⁻¹.transpose := by
            rw [hInverseSymmetric]
      _ = Matrix.mulVec data.metric⁻¹ gradient :=
        Matrix.vecMul_transpose data.metric⁻¹ gradient
  have hQuadratic :
      dotProduct gradient
          (Matrix.mulVec (data.metric⁻¹ * variation * data.metric⁻¹) gradient) =
        dotProduct (raisedGradient data gradient)
          (Matrix.mulVec variation (raisedGradient data gradient)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, hVecMul]
    rfl
  have hSum :
      (∑ second : Index4, ∑ first : Index4,
        raisedGradient data gradient first * variation first second *
          raisedGradient data gradient second) =
        ∑ first : Index4, ∑ second : Index4,
          raisedGradient data gradient first *
            raisedGradient data gradient second * variation first second := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    ring
  rw [scalarKinetic_eq_dotProduct, hQuadratic,
    Matrix.dot_mulVec_eq_sum_sum, hSum]

private theorem stress_tensor_pairing_expansion
    (data : FixedSignMetric4) (massSquared source : Real)
    (jet : ScalarMatterJet) (variation : Matrix4) :
    tensorMetricPairing
        (pointwiseScalarStressTensor data massSquared source jet) variation =
      (∑ first : Index4, ∑ second : Index4,
        raisedGradient data jet.gradient first *
          raisedGradient data jet.gradient second * variation first second) -
      scalarMatterLagrangian massSquared source data.metric⁻¹ jet *
        (∑ first : Index4, ∑ second : Index4,
          (data.metric⁻¹) first second * variation first second) := by
  let lagrangian :=
    scalarMatterLagrangian massSquared source data.metric⁻¹ jet
  have hPotential :
      (∑ first : Index4, ∑ second : Index4,
        (data.metric⁻¹) first second * lagrangian * variation first second) =
      lagrangian *
        (∑ first : Index4, ∑ second : Index4,
          (data.metric⁻¹) first second * variation first second) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro second _
    ring
  unfold tensorMetricPairing pointwiseScalarStressTensor
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hPotential]

/-- The derivative is exactly minus one half the metric pairing with the
pointwise stress tensor. -/
theorem metricInducedScalarDensityFirstVariation_eq_stress_pairing
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (massSquared source : Real) (jet : ScalarMatterJet) :
    metricInducedScalarDensityFirstVariation data variation
        massSquared source jet =
      -(Real.sqrt |Matrix.det data.metric| / 2) *
        tensorMetricPairing
          (pointwiseScalarStressTensor data massSquared source jet)
          variation.tensor := by
  rw [metricInducedScalarDensityFirstVariation]
  have hKinetic := scalarKinetic_inverse_product_eq_raised_pairing
    data variation.tensor jet.gradient
  have hTrace := trace_mul_eq_metric_pairing data.metric⁻¹ variation.tensor
  have hNeg : scalarKinetic
      (-(data.metric⁻¹ * variation.tensor * data.metric⁻¹)) jet.gradient =
        -scalarKinetic
          (data.metric⁻¹ * variation.tensor * data.metric⁻¹) jet.gradient := by
    simp [scalarKinetic]
  have hVariationEntry : ∀ first second : Index4,
      variation.tensor second first = variation.tensor first second := by
    intro first second
    have h := congrArg (fun matrix : Matrix4 => matrix first second)
      variation.tensor_symmetric
    simpa using h
  have hTraceSymmetric :
      Matrix.trace (data.metric⁻¹ * variation.tensor) =
        ∑ first : Index4, ∑ second : Index4,
          (data.metric⁻¹) first second * variation.tensor first second := by
    rw [hTrace]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    rw [hVariationEntry]
  have hPairing := stress_tensor_pairing_expansion data massSquared source
    jet variation.tensor
  rw [hNeg, hTraceSymmetric, hKinetic, hPairing]
  ring

/-- Final stress-form derivative along the exact metric curve. -/
theorem metricInducedScalarDensityCurve_stress_hasDerivAt
    (data : FixedSignMetric4) (variation : SymmetricMetricVariation4)
    (massSquared source : Real) (jet : ScalarMatterJet) :
    FrobeniusScalarHasDerivAt
      (metricInducedScalarDensityCurve data variation massSquared source jet)
      (-(Real.sqrt |Matrix.det data.metric| / 2) *
        tensorMetricPairing
          (pointwiseScalarStressTensor data massSquared source jet)
          variation.tensor) 0 := by
  have hDerivative := metricInducedScalarDensityCurve_hasDerivAt
    data variation massSquared source jet
  unfold FrobeniusScalarHasDerivAt at hDerivative ⊢
  have hScalar := hDerivative.hasDerivAt.congr_deriv
    (by
      simpa using
        (metricInducedScalarDensityFirstVariation_eq_stress_pairing
          data variation massSquared source jet))
  exact (hScalar.congr_deriv (by ring)).hasFDerivAt

end

end P0EFTJanusMetricInducedScalarStressVariation4D
end JanusFormal
