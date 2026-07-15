import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanMetricKoszulConnection

namespace JanusFormal
namespace P0EFTJanusEuclideanKoszulConnectionExistence

set_option autoImplicit false

noncomputable section

open Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusEuclideanMetricKoszulConnection

universe u

variable {Model : Type u}
variable [NormedAddCommGroup Model] [InnerProductSpace ℝ Model]
variable [FiniteDimensional ℝ Model]

/-- The real Riesz inverse as an ordinary continuous linear map. -/
def realRieszInverseLinearMap : (Model →L[ℝ] ℝ) →ₗ[ℝ] Model where
  toFun := fun functional => (InnerProductSpace.toDual ℝ Model).symm functional
  map_add' := by
    intro first second
    exact (InnerProductSpace.toDual ℝ Model).symm.map_add first second
  map_smul' := by
    intro scalar functional
    simpa using (InnerProductSpace.toDual ℝ Model).symm.map_smul scalar functional

/-- Continuous version of the real Riesz inverse. -/
def realRieszInverseCLM : (Model →L[ℝ] ℝ) →L[ℝ] Model :=
  realRieszInverseLinearMap.mkContinuous 1 (by
    intro functional
    change ‖(InnerProductSpace.toDual ℝ Model).symm functional‖ ≤
      1 * ‖functional‖
    simpa only [(InnerProductSpace.toDual ℝ Model).symm.norm_map, one_mul] using
      (le_refl ‖functional‖))

local instance functionalNormedAddCommGroup :
    NormedAddCommGroup (Model →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance functionalNormedSpace : NormedSpace ℝ (Model →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance metricTensorNormedAddCommGroup :
    NormedAddCommGroup (ContinuousMetricTensor Model) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance metricTensorNormedSpace :
    NormedSpace ℝ (ContinuousMetricTensor Model) :=
  ContinuousLinearMap.toNormedSpace

/-- The first derivative of a Euclidean metric coefficient. -/
abbrev ContinuousMetricDerivativeTensor
    (Model : Type u)
    [NormedAddCommGroup Model] [NormedSpace ℝ Model] :=
  Model →L[ℝ] ContinuousMetricTensor Model

local instance metricDerivativeTensorNormedAddCommGroup :
    NormedAddCommGroup (ContinuousMetricDerivativeTensor Model) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance metricDerivativeTensorNormedSpace :
    NormedSpace ℝ (ContinuousMetricDerivativeTensor Model) :=
  ContinuousLinearMap.toNormedSpace

local instance tangentialQuadraticNormedAddCommGroup :
    NormedAddCommGroup (ContinuousTangentialQuadratic Model) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tangentialQuadraticNormedSpace :
    NormedSpace ℝ (ContinuousTangentialQuadratic Model) :=
  ContinuousLinearMap.toNormedSpace

/-- A smooth positive-definite Euclidean metric.  Symmetry of its derivative is
recorded as the differentiated form of metric symmetry. -/
structure SmoothPositiveDefiniteEuclideanMetric where
  metric : Model → ContinuousMetricTensor Model
  metric_contDiff : ContDiff ℝ ∞ metric
  metric_symmetric :
    ∀ base first second,
      metric base first second = metric base second first
  metricDerivative_symmetric :
    ∀ base direction first second,
      fderiv ℝ metric base direction first second =
        fderiv ℝ metric base direction second first
  metric_positive :
    ∀ base vector, vector ≠ 0 → 0 < metric base vector vector

/-- Continuous Riesz conversion in the last covariant slot. -/
def rieszLastCLM :
    ContinuousMetricDerivativeTensor (Model := Model) →L[ℝ]
      ContinuousTangentialQuadratic Model :=
  (ContinuousLinearMap.compL ℝ Model
      (Model →L[ℝ] Model →L[ℝ] ℝ) (Model →L[ℝ] Model))
    ((ContinuousLinearMap.compL ℝ Model (Model →L[ℝ] ℝ) Model)
      realRieszInverseCLM)

/-- Swap the first two slots of a covariant three-tensor. -/
def swapFirstSecondCLM :
    ContinuousMetricDerivativeTensor (Model := Model) →L[ℝ]
      ContinuousMetricDerivativeTensor (Model := Model) :=
  (LinearIsometryEquiv.toLinearIsometry
    (ContinuousLinearMap.flipₗᵢ ℝ Model Model
      (Model →L[ℝ] ℝ))).toContinuousLinearMap

/-- Swap the last two slots of a covariant three-tensor. -/
def swapSecondThirdCLM :
    ContinuousMetricDerivativeTensor (Model := Model) →L[ℝ]
      ContinuousMetricDerivativeTensor (Model := Model) :=
  (ContinuousLinearMap.compL ℝ Model
      (Model →L[ℝ] Model →L[ℝ] ℝ)
      (Model →L[ℝ] Model →L[ℝ] ℝ))
    ((LinearIsometryEquiv.toLinearIsometry
      (ContinuousLinearMap.flipₗᵢ ℝ Model Model ℝ)).toContinuousLinearMap)

/-- Linear Koszul combination
`D(first,second,test) + D(second,first,test) - D(test,first,second)`. -/
def metricKoszulCovariantCLM :
    ContinuousMetricDerivativeTensor (Model := Model) →L[ℝ]
      ContinuousMetricDerivativeTensor (Model := Model) :=
  ContinuousLinearMap.id ℝ (ContinuousMetricDerivativeTensor Model) +
    swapFirstSecondCLM (Model := Model) -
      (swapSecondThirdCLM (Model := Model)).comp
        (swapFirstSecondCLM (Model := Model))

/-- Background-inner-product representative of the Koszul covector. -/
def metricKoszulNumeratorCLM :
    ContinuousMetricDerivativeTensor (Model := Model) →L[ℝ]
      ContinuousTangentialQuadratic Model :=
  (rieszLastCLM (Model := Model)).comp
    (metricKoszulCovariantCLM (Model := Model))

/-- The metric Riesz operator, bundled continuously in the metric tensor. -/
def metricRieszOperatorCLM :
    ContinuousMetricTensor Model →L[ℝ] Model →L[ℝ] Model :=
  (ContinuousLinearMap.compL ℝ Model (Model →L[ℝ] ℝ) Model)
    realRieszInverseCLM

/-- Apply an endomorphism to the value of a continuous bilinear map. -/
def postcomposeQuadraticCLM :
    (Model →L[ℝ] Model) →L[ℝ]
      ContinuousTangentialQuadratic Model →L[ℝ]
        ContinuousTangentialQuadratic Model :=
  (ContinuousLinearMap.compL ℝ Model
      (Model →L[ℝ] Model) (Model →L[ℝ] Model)).comp
    (ContinuousLinearMap.compL ℝ Model Model Model)

@[simp]
theorem metricRieszOperatorCLM_inner
    (metric : ContinuousMetricTensor Model) (first second : Model) :
    ⟪metricRieszOperatorCLM metric first, second⟫_ℝ = metric first second := by
  exact InnerProductSpace.toDual_symm_apply

@[simp]
theorem metricKoszulCovariantCLM_apply
    (derivative : ContinuousMetricDerivativeTensor (Model := Model))
    (first second test : Model) :
    metricKoszulCovariantCLM derivative first second test =
      derivative first second test + derivative second first test -
        derivative test first second := by
  rfl

@[simp]
theorem metricKoszulNumeratorCLM_inner
    (derivative : ContinuousMetricDerivativeTensor (Model := Model))
    (first second test : Model) :
    ⟪metricKoszulNumeratorCLM derivative first second, test⟫_ℝ =
      derivative first second test + derivative second first test -
        derivative test first second := by
  exact InnerProductSpace.toDual_symm_apply

@[simp]
theorem postcomposeQuadraticCLM_apply
    (operator : Model →L[ℝ] Model)
    (quadratic : ContinuousTangentialQuadratic Model)
    (first second : Model) :
    postcomposeQuadraticCLM operator quadratic first second =
      operator (quadratic first second) := by
  rfl

/-- Pointwise metric Riesz operator. -/
def SmoothPositiveDefiniteEuclideanMetric.metricRieszOperator
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model))
    (base : Model) : Model →L[ℝ] Model :=
  metricRieszOperatorCLM (data.metric base)

theorem SmoothPositiveDefiniteEuclideanMetric.metricRieszOperator_contDiff
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model)) :
    ContDiff ℝ ∞ data.metricRieszOperator := by
  change ContDiff ℝ ∞ (fun base =>
    metricRieszOperatorCLM (Model := Model) (data.metric base))
  exact (metricRieszOperatorCLM (Model := Model)).contDiff.comp
    data.metric_contDiff

theorem SmoothPositiveDefiniteEuclideanMetric.metricRieszOperator_injective
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model))
    (base : Model) : Function.Injective (data.metricRieszOperator base) := by
  intro first second hEqual
  by_contra hNe
  have hVectorNe : first - second ≠ 0 := sub_ne_zero.mpr hNe
  have hPositive := data.metric_positive base (first - second) hVectorNe
  have hOperatorZero :
      data.metricRieszOperator base (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hPairing : data.metric base (first - second) (first - second) = 0 := by
    rw [← metricRieszOperatorCLM_inner]
    change ⟪data.metricRieszOperator base (first - second), first - second⟫_ℝ = 0
    rw [hOperatorZero]
    simp
  linarith

/-- Positivity supplies a continuous linear equivalence at every base point. -/
def SmoothPositiveDefiniteEuclideanMetric.metricRieszEquiv
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model))
    (base : Model) : Model ≃L[ℝ] Model :=
  (LinearEquiv.ofInjectiveEndo
      (data.metricRieszOperator base).toLinearMap
      (data.metricRieszOperator_injective base)).toContinuousLinearEquiv

@[simp]
theorem SmoothPositiveDefiniteEuclideanMetric.coe_metricRieszEquiv
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model))
    (base : Model) :
    (data.metricRieszEquiv base : Model →L[ℝ] Model) =
      data.metricRieszOperator base := by
  ext vector
  rfl

theorem SmoothPositiveDefiniteEuclideanMetric.metricRieszOperator_isInvertible
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model))
    (base : Model) :
    (data.metricRieszOperator base).IsInvertible := by
  exact ⟨data.metricRieszEquiv base, data.coe_metricRieszEquiv base⟩

/-- Smooth inverse metric Riesz operator. -/
def SmoothPositiveDefiniteEuclideanMetric.inverseMetricRieszOperator
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model))
    (base : Model) : Model →L[ℝ] Model :=
  ContinuousLinearMap.inverse (data.metricRieszOperator base)

theorem SmoothPositiveDefiniteEuclideanMetric.inverseMetricRieszOperator_contDiff
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model)) :
    ContDiff ℝ ∞ data.inverseMetricRieszOperator := by
  rw [contDiff_iff_contDiffAt]
  intro base
  exact (data.metricRieszOperator_isInvertible base).contDiffAt_map_inverse.comp
    base data.metricRieszOperator_contDiff.contDiffAt

/-- The Levi-Civita coefficient constructed from the metric and its first
derivative by the Euclidean Koszul formula. -/
def SmoothPositiveDefiniteEuclideanMetric.connection
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model))
  (base : Model) : ContinuousTangentialQuadratic Model :=
  (2 : ℝ)⁻¹ •
    postcomposeQuadraticCLM (Model := Model)
      (data.inverseMetricRieszOperator base)
      (metricKoszulNumeratorCLM (Model := Model)
        (fderiv ℝ data.metric base))

theorem SmoothPositiveDefiniteEuclideanMetric.connection_contDiff
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model)) :
    ContDiff ℝ ∞ data.connection := by
  have hDerivative : ContDiff ℝ ∞ (fderiv ℝ data.metric) :=
    data.metric_contDiff.fderiv_right (m := ∞) (by simp)
  have hNumerator : ContDiff ℝ ∞
      (fun base => metricKoszulNumeratorCLM (Model := Model)
        (fderiv ℝ data.metric base)) :=
    (metricKoszulNumeratorCLM (Model := Model)).contDiff.comp hDerivative
  have hPostcompose : ContDiff ℝ ∞
      (fun base => postcomposeQuadraticCLM (Model := Model)
        (data.inverseMetricRieszOperator base)
        (metricKoszulNumeratorCLM (fderiv ℝ data.metric base))) :=
    ((postcomposeQuadraticCLM (Model := Model)).contDiff.comp
      data.inverseMetricRieszOperator_contDiff).clm_apply hNumerator
  exact hPostcompose.const_smul (2 : ℝ)⁻¹

theorem SmoothPositiveDefiniteEuclideanMetric.metric_nondegenerate
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model)) :
    ∀ base left right,
      (∀ test, data.metric base left test = data.metric base right test) →
        left = right := by
  intro base left right hPairing
  by_contra hNe
  have hVectorNe : left - right ≠ 0 := sub_ne_zero.mpr hNe
  have hPositive := data.metric_positive base (left - right) hVectorNe
  have hZero : data.metric base (left - right) (left - right) = 0 := by
    calc
      data.metric base (left - right) (left - right) =
          data.metric base left (left - right) -
            data.metric base right (left - right) := by
        exact congrArg (fun covector => covector (left - right))
          ((data.metric base).map_sub left right)
      _ = 0 := by rw [hPairing (left - right), sub_self]
  linarith

theorem SmoothPositiveDefiniteEuclideanMetric.connection_koszul
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model)) :
    ∀ base first second test,
      2 * data.metric base (data.connection base first second) test =
        metricKoszulRhs data.metric base first second test := by
  intro base first second test
  have hInverse := (data.metricRieszOperator_isInvertible base).self_apply_inverse
    (metricKoszulNumeratorCLM (fderiv ℝ data.metric base) first second)
  rw [← metricRieszOperatorCLM_inner]
  change 2 * ⟪data.metricRieszOperator base
    (data.connection base first second), test⟫_ℝ = _
  simp only [SmoothPositiveDefiniteEuclideanMetric.connection,
    SmoothPositiveDefiniteEuclideanMetric.inverseMetricRieszOperator,
    postcomposeQuadraticCLM_apply, ContinuousLinearMap.smul_apply]
  rw [(data.metricRieszOperator base).map_smul, inner_smul_left]
  rw [hInverse, metricKoszulNumeratorCLM_inner]
  simp [metricKoszulRhs]

/-- A smooth positive-definite metric canonically produces the complete
Euclidean Koszul connection package; no connection coefficient is supplied. -/
def SmoothPositiveDefiniteEuclideanMetric.toKoszulConnectionData
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model)) :
    SmoothEuclideanKoszulConnectionData Model where
  metric := data.metric
  connection := data.connection
  metric_contDiff := data.metric_contDiff
  connection_contDiff := data.connection_contDiff
  metric_symmetric := data.metric_symmetric
  metricDerivative_symmetric := data.metricDerivative_symmetric
  metric_nondegenerate := data.metric_nondegenerate
  connection_koszul := data.connection_koszul

/-- Existence, not merely uniqueness, of the smooth Euclidean Levi-Civita
coefficient associated to a smooth positive-definite metric. -/
theorem smoothEuclideanKoszulConnection_exists
    (data : SmoothPositiveDefiniteEuclideanMetric (Model := Model)) :
    ∃ connection : Model → ContinuousTangentialQuadratic Model,
      ContDiff ℝ ∞ connection ∧
      ∀ base first second test,
        2 * data.metric base (connection base first second) test =
          metricKoszulRhs data.metric base first second test := by
  exact ⟨data.connection, data.connection_contDiff, data.connection_koszul⟩

end

end P0EFTJanusEuclideanKoszulConnectionExistence
end JanusFormal
