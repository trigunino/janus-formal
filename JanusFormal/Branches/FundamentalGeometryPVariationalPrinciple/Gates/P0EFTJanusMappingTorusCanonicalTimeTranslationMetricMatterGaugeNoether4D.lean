import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTimeTranslationMetricMatterGaugeNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzMetricTimeTranslationIsometry4D

/-!
# Canonical intrinsic time-translation Noether specialization

The lightweight time-translation Noether block remains valid for arbitrary
metric pairs.  This downstream gate proves that the canonical intrinsic
metric is fixed by the complete time flow and discharges its metric contract.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTimeTranslationMetricMatterGaugeNoether4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusCovariantTensorDiffeomorphismGenerator4D
open P0EFTJanusMappingTorusMatterGaugeNoetherOperator4D
open P0EFTJanusMappingTorusMetricMatterGaugeNoetherOperator4D
open P0EFTJanusMappingTorusMetricMatterGaugeActionNoetherBridge4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusTimeTranslationMetricMatterGaugeNoether4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev QuotientCovariantTwoTensorFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point →L[Real]
    (TangentSpace coverModelWithCorners point →L[Real] Real)

private instance quotientCovariantTwoTensorFiberNormedAddCommGroup
    (point : EffectiveQuotient period hPeriod) :
    NormedAddCommGroup
      (QuotientCovariantTwoTensorFiber period hPeriod point) :=
  inferInstanceAs (NormedAddCommGroup
    (CoverCoordinates →L[Real] (CoverCoordinates →L[Real] Real)))

private instance quotientCovariantTwoTensorFiberNormedSpace
    (point : EffectiveQuotient period hPeriod) :
    NormedSpace Real (QuotientCovariantTwoTensorFiber period hPeriod point) :=
  inferInstanceAs (NormedSpace Real
    (CoverCoordinates →L[Real] (CoverCoordinates →L[Real] Real)))

private theorem quotientTensor_deriv_const
    (point : EffectiveQuotient period hPeriod)
    (value : QuotientCovariantTwoTensorFiber period hPeriod point) :
    deriv (fun _ : Real => value) 0 = 0 :=
  @deriv_const Real inferInstance
    (QuotientCovariantTwoTensorFiber period hPeriod point)
    (quotientCovariantTwoTensorFiberNormedAddCommGroup period hPeriod point)
    (quotientCovariantTwoTensorFiberNormedSpace period hPeriod point)
    (0 : Real) value

/-- The quotient projection derivative commutes with cover and quotient time
translation. -/
theorem quotientProjectionDerivative_timeTranslation_natural
    (shift : Real) (point : EffectiveCover period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    mfderiv coverModelWithCorners coverModelWithCorners
        (effectiveTimeFlow period hPeriod shift)
        (mappingTorusMk (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point vector) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod))
        (coverTimeTranslation (sphereData period hPeriod) shift point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (coverTimeTranslation (sphereData period hPeriod) shift)
          point vector) := by
  have hProjection :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
  have hTranslation :=
    effectiveCoverTimeTranslation_contMDiff period hPeriod shift
  have hFlow := effectiveTimeFlow_contMDiff period hPeriod shift
  have hMaps :
      effectiveTimeFlow period hPeriod shift ∘
          mappingTorusMk (sphereData period hPeriod) =
        mappingTorusMk (sphereData period hPeriod) ∘
          coverTimeTranslation (sphereData period hPeriod) shift := by
    funext current
    rfl
  have hLeft := mfderiv_comp_apply point
    (hFlow.mdifferentiable (by simp)
      (mappingTorusMk (sphereData period hPeriod) point))
    (hProjection.mdifferentiable (by simp) point) vector
  have hRight := mfderiv_comp_apply point
    (hProjection.mdifferentiable (by simp)
      (coverTimeTranslation (sphereData period hPeriod) shift point))
    (hTranslation.mdifferentiable (by simp) point) vector
  rw [hMaps] at hLeft
  exact hLeft.symm.trans hRight

private theorem
    quotientProjectionDerivative_timeTranslation_natural_diffeomorph_local
    (shift : Real) (point : EffectiveCover period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    mfderiv coverModelWithCorners coverModelWithCorners
        (⇑(effectiveTimeFlowDiffeomorph period hPeriod shift))
        (mappingTorusMk (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point vector) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod))
        (coverTimeTranslation (sphereData period hPeriod) shift point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (coverTimeTranslation (sphereData period hPeriod) shift)
          point vector) := by
  convert quotientProjectionDerivative_timeTranslation_natural period hPeriod
    shift point vector using 1 <;> rfl

@[simp]
private theorem effectiveTimeFlowDiffeomorph_mk_local
    (shift : Real) (point : EffectiveCover period hPeriod) :
    effectiveTimeFlowDiffeomorph period hPeriod shift
        (mappingTorusMk (sphereData period hPeriod) point) =
      mappingTorusMk (sphereData period hPeriod)
        (coverTimeTranslation (sphereData period hPeriod) shift point) := by
  convert effectiveTimeFlow_mk period hPeriod shift point using 1 <;> rfl

private theorem intrinsicCoverLorentzTensor_timeTranslation_isometry_local
    (shift : Real) (point : EffectiveCover period hPeriod)
    (first second : TangentSpace coverModelWithCorners point) :
    intrinsicCoverLorentzTensor period hPeriod
        (coverTimeTranslation (sphereData period hPeriod) shift point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (coverTimeTranslation (sphereData period hPeriod) shift)
          point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (coverTimeTranslation (sphereData period hPeriod) shift)
          point second) =
      intrinsicCoverLorentzTensor period hPeriod point first second := by
  convert intrinsicCoverLorentzTensor_timeTranslation_isometry period hPeriod
    shift point first second using 1 <;> rfl

@[simp]
private theorem smoothDiffeomorphismTensorPullback_apply_local
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentSpace coverModelWithCorners point) :
    (smoothDiffeomorphismTensorPullback period hPeriod diffeomorphism tensor).tensor
        point first second =
      tensor.tensor (diffeomorphism point)
        (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism
          point first)
        (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism
          point second) :=
  rfl

/-- Pulling the canonical quotient tensor by a finite time translation gives
another descent of the same intrinsic cover tensor. -/
def intrinsicTimeTranslationPulledTensorDescent (shift : Real) :
    IntrinsicTensorQuotientDescent period hPeriod where
  tensor :=
    (smoothDiffeomorphismTensorPullback period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod shift)
      (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor).tensor
  pullback := by
    intro point first second
    rw [smoothDiffeomorphismTensorPullback_apply_local,
      quotientProjectionDerivative_timeTranslation_natural_diffeomorph_local,
      quotientProjectionDerivative_timeTranslation_natural_diffeomorph_local,
      effectiveTimeFlowDiffeomorph_mk_local]
    change (intrinsicTensorQuotientDescent period hPeriod).tensor
        (mappingTorusMk (sphereData period hPeriod)
          (coverTimeTranslation (sphereData period hPeriod) shift point))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (coverTimeTranslation (sphereData period hPeriod) shift point)
          (mfderiv coverModelWithCorners coverModelWithCorners
            (coverTimeTranslation (sphereData period hPeriod) shift)
            point first))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (coverTimeTranslation (sphereData period hPeriod) shift point)
          (mfderiv coverModelWithCorners coverModelWithCorners
            (coverTimeTranslation (sphereData period hPeriod) shift)
            point second)) = _
    rw [(intrinsicTensorQuotientDescent period hPeriod).pullback]
    exact intrinsicCoverLorentzTensor_timeTranslation_isometry_local period
      hPeriod shift point first second

/-- The canonical smooth quotient tensor is fixed by every finite slice of
the complete time flow. -/
theorem intrinsicSmoothTensor_timeTranslation_fixed (shift : Real) :
    smoothDiffeomorphismTensorPullback period hPeriod
        (effectiveTimeFlowDiffeomorph period hPeriod shift)
        (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor =
      (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  change (intrinsicTimeTranslationPulledTensorDescent period hPeriod shift).tensor =
    (intrinsicTensorQuotientDescent period hPeriod).tensor
  exact IntrinsicTensorQuotientDescent.tensor_unique period hPeriod
    (intrinsicTimeTranslationPulledTensorDescent period hPeriod shift)
    (intrinsicTensorQuotientDescent period hPeriod)

/-- The complete intrinsic Lorentz metric is fixed by finite time
translation. -/
@[simp]
theorem intrinsicSmoothGeneralLorentzMetric_timeTranslation_fixed
    (shift : Real) :
    smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
        (effectiveTimeFlowDiffeomorph period hPeriod shift)
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) =
      intrinsicSmoothGeneralLorentzMetric period hPeriod := by
  apply smoothGeneralLorentzMetric_ext period hPeriod
  exact intrinsicSmoothTensor_timeTranslation_fixed period hPeriod shift

/-- The infinitesimal pullback generator of the canonical intrinsic tensor
vanishes pointwise. -/
theorem intrinsicSmoothTensor_timeTranslation_generator_zero
    (point : EffectiveQuotient period hPeriod) :
    covariantTensorDiffeomorphismGeneratorAt period hPeriod
        (effectiveTimeFlowDiffeomorph period hPeriod)
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor.toTensorField
        point = 0 := by
  have hCurve :
      tensorPullbackCurveValue period hPeriod
          (effectiveTimeFlowDiffeomorph period hPeriod)
          (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor.toTensorField
          point =
        fun _ : Real =>
          (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point := by
    funext shift
    have hFixed := congrArg
      (fun tensor : SmoothSymmetricCovariantTwoTensor period hPeriod =>
        tensor.tensor point)
      (intrinsicSmoothTensor_timeTranslation_fixed period hPeriod shift)
    exact hFixed
  unfold covariantTensorDiffeomorphismGeneratorAt
  rw [hCurve]
  change deriv (fun _ : Real =>
      ((intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point :
        QuotientCovariantTwoTensorFiber period hPeriod point)) 0 = 0
  exact quotientTensor_deriv_const period hPeriod point _

/-- The canonical intrinsic metric pair needs no residual regularity input:
finite time-translation isometry makes both infinitesimal metric variations
the zero smooth symmetric tensor. -/
def intrinsicTimeTranslationMetricPairContract :
    TimeTranslationMetricPairContract period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor where
  plusVariation := 0
  minusVariation := 0
  plus_realizes := by
    intro point
    exact (intrinsicSmoothTensor_timeTranslation_generator_zero period hPeriod
      point).symm
  minus_realizes := by
    intro point
    exact (intrinsicSmoothTensor_timeTranslation_generator_zero period hPeriod
      point).symm
  plus_symmetric := by
    intro point first second
    rfl
  minus_symmetric := by
    intro point first second
    rfl

@[simp]
theorem intrinsicTimeTranslationMetricPairContract_plusVariation :
    (intrinsicTimeTranslationMetricPairContract period hPeriod).plusVariation =
      0 :=
  rfl

@[simp]
theorem intrinsicTimeTranslationMetricPairContract_minusVariation :
    (intrinsicTimeTranslationMetricPairContract period hPeriod).minusVariation =
      0 :=
  rfl

/-- Contract-free restricted variation for the canonical intrinsic metric
pair. -/
def intrinsicTimeTranslationMetricMatterGaugeLinearizedVariation
    (fields : IndependentFields period hPeriod) :
    TimeTranslationMatterGaugeParameterSpace period hPeriod →ₗ[Real]
      MetricMatterGaugeVariationSpace period hPeriod :=
  timeTranslationMetricMatterGaugeLinearizedVariation period hPeriod fields
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor
    (intrinsicTimeTranslationMetricPairContract period hPeriod)

/-- Time translation has identically zero metric component on the canonical
intrinsic pair. -/
@[simp]
theorem intrinsicTimeTranslationMetricMatterGaugeLinearizedVariation_metric
    (fields : IndependentFields period hPeriod)
    (parameters : TimeTranslationMatterGaugeParameterSpace period hPeriod) :
    (intrinsicTimeTranslationMetricMatterGaugeLinearizedVariation period
      hPeriod fields parameters).1 = 0 := by
  rw [intrinsicTimeTranslationMetricMatterGaugeLinearizedVariation,
    timeTranslationMetricMatterGaugeLinearizedVariation_metric]
  apply Prod.ext
  · change parameters.1 •
      (intrinsicTimeTranslationMetricPairContract period hPeriod).plusVariation = 0
    rw [intrinsicTimeTranslationMetricPairContract_plusVariation]
    apply ContMDiffSection.ext
    intro point
    simp only [ContMDiffSection.coe_smul, ContMDiffSection.coe_zero,
      Pi.smul_apply, Pi.zero_apply, smul_zero]
  · change parameters.1 •
      (intrinsicTimeTranslationMetricPairContract period hPeriod).minusVariation = 0
    rw [intrinsicTimeTranslationMetricPairContract_minusVariation]
    apply ContMDiffSection.ext
    intro point
    simp only [ContMDiffSection.coe_smul, ContMDiffSection.coe_zero,
      Pi.smul_apply, Pi.zero_apply, smul_zero]

/-- Contract-free Noether operator for the canonical intrinsic metric pair. -/
def intrinsicTimeTranslationMetricMatterGaugeNoetherOperator
    (fields : IndependentFields period hPeriod)
    (euler : MetricMatterGaugeVariationSpace period hPeriod →ₗ[Real] Real) :
    TimeTranslationMatterGaugeParameterSpace period hPeriod →ₗ[Real] Real :=
  euler.comp
    (intrinsicTimeTranslationMetricMatterGaugeLinearizedVariation period
      hPeriod fields)

@[simp]
theorem intrinsicTimeTranslationMetricMatterGaugeNoetherOperator_apply
    (fields : IndependentFields period hPeriod)
    (euler : MetricMatterGaugeVariationSpace period hPeriod →ₗ[Real] Real)
    (parameters : TimeTranslationMatterGaugeParameterSpace period hPeriod) :
    intrinsicTimeTranslationMetricMatterGaugeNoetherOperator period hPeriod
        fields euler parameters =
      euler (intrinsicTimeTranslationMetricMatterGaugeLinearizedVariation
        period hPeriod fields parameters) :=
  rfl

/-- Pure-time line invariance specialized to the canonical intrinsic pair;
no metric-regularity contract appears in this public condition. -/
def IntrinsicPureTimeTranslationLineInvariantAtZero
    (fields : IndependentFields period hPeriod)
    (action : MetricMatterGaugeVariationSpace period hPeriod → Real) : Prop :=
  ∀ lineParameter : Real,
    action (lineParameter •
      intrinsicTimeTranslationMetricMatterGaugeLinearizedVariation period
        hPeriod fields (unitTimeTranslationParameter period hPeriod)) =
      action 0

/-- The canonical intrinsic pair has an unconditional metric input to the
time Noether identity.  Only first variation and action invariance remain. -/
theorem intrinsicTimeTranslationNoether_identity
    (fields : IndependentFields period hPeriod)
    (action : MetricMatterGaugeVariationSpace period hPeriod → Real)
    (euler : MetricMatterGaugeVariationSpace period hPeriod →ₗ[Real] Real)
    (hFirstVariation :
      HasMetricMatterGaugeDirectionalFirstVariationAtZero period hPeriod
        action euler)
    (hInvariant :
      IntrinsicPureTimeTranslationLineInvariantAtZero period hPeriod fields
        action) :
    intrinsicTimeTranslationMetricMatterGaugeNoetherOperator period hPeriod
        fields euler (unitTimeTranslationParameter period hPeriod) = 0 := by
  change timeTranslationMetricMatterGaugeNoetherOperator period hPeriod fields
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor
      (intrinsicTimeTranslationMetricPairContract period hPeriod) euler
      (unitTimeTranslationParameter period hPeriod) = 0
  apply timeTranslationNoether_identity period hPeriod fields
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor
    (intrinsicTimeTranslationMetricPairContract period hPeriod) action euler
    hFirstVariation
  intro lineParameter
  exact hInvariant lineParameter

end

end P0EFTJanusMappingTorusCanonicalTimeTranslationMetricMatterGaugeNoether4D
end JanusFormal
