import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedD8GeneralLorentzMetricFunctor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeTimeTranslationInvariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTimeTranslationMetricMatterGaugeNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCovariantTensorDiffeomorphismGenerator4D

/-!
# Time-translation skewness for the bulk metric pairing

This gate only treats the genuine complete time-translation subgroup. Tensor
orbits are the actual smooth pullbacks. The pointwise orbit-generator/action
bridge remains explicit; it does not by itself differentiate the integrated
pairing and therefore does not assert skew-adjointness.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeneralMetricTimeTranslationSkew4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
open P0EFTJanusFixedD8GeneralLorentzMetricFunctor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeTimeTranslationInvariance4D
open P0EFTJanusMappingTorusTimeTranslationMetricMatterGaugeNoether4D
open P0EFTJanusMappingTorusCanonicalTimeTranslationMetricMatterGaugeNoether4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
open P0EFTJanusMappingTorusCovariantTensorDiffeomorphismGenerator4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev MetricPair :=
  SmoothGeneralMetricTensorPair period hPeriod

private abbrev BackgroundPair :=
  SmoothGeneralLorentzMetric period hPeriod ×
    SmoothGeneralLorentzMetric period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The actual complete time-translation ghost in the common `C∞` interface. -/
def effectiveTimeTranslationCInfinityGhost :
    CInfinityDiffeomorphismGhost period hPeriod :=
  smoothGhostToCInfinity period hPeriod
    (effectiveTimeTranslationGhost period hPeriod)

/-- Pull back both tensor sectors by one genuine finite time translation. -/
def generalMetricTimeTranslationTensorOrbit
    (parameter : Real)
    (field : MetricPair period hPeriod) :
    MetricPair period hPeriod :=
  (smoothDiffeomorphismTensorPullback period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod parameter) field.1,
    smoothDiffeomorphismTensorPullback period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod parameter) field.2)

/-- Transport both background metrics along the same genuine time slice. -/
def generalMetricTimeTranslationBackgroundOrbit
    (parameter : Real)
    (metrics : BackgroundPair period hPeriod) :
    BackgroundPair period hPeriod :=
  (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod parameter) metrics.1,
    smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod parameter) metrics.2)

private theorem effectiveTimeFlowDiffeomorph_zero :
    effectiveTimeFlowDiffeomorph period hPeriod 0 =
      Diffeomorph.refl coverModelWithCorners
        (EffectiveQuotient period hPeriod) ω := by
  ext point
  exact effectiveTimeFlow_zero period hPeriod point

@[simp]
theorem generalMetricTimeTranslationTensorOrbit_zero
    (field : MetricPair period hPeriod) :
    generalMetricTimeTranslationTensorOrbit
        period hPeriod 0 field = field := by
  unfold generalMetricTimeTranslationTensorOrbit
  rw [effectiveTimeFlowDiffeomorph_zero]
  exact Prod.ext
    (smoothDiffeomorphismTensorPullback_refl
      period hPeriod field.1)
    (smoothDiffeomorphismTensorPullback_refl
      period hPeriod field.2)

@[simp]
theorem generalMetricTimeTranslationBackgroundOrbit_zero
    (metrics : BackgroundPair period hPeriod) :
    generalMetricTimeTranslationBackgroundOrbit
        period hPeriod 0 metrics = metrics := by
  unfold generalMetricTimeTranslationBackgroundOrbit
  rw [effectiveTimeFlowDiffeomorph_zero]
  exact Prod.ext
    (smoothGeneralLorentzMetricDiffeomorphismPullback_refl
      period hPeriod metrics.1)
    (smoothGeneralLorentzMetricDiffeomorphismPullback_refl
      period hPeriod metrics.2)

/-- The canonical intrinsic two-background pair is fixed by every finite
time translation. -/
theorem intrinsicGeneralLorentzMetricPair_timeTranslation_fixed
    (parameter : Real) :
    generalMetricTimeTranslationBackgroundOrbit period hPeriod parameter
        (intrinsicGeneralLorentzMetricPair period hPeriod) =
      intrinsicGeneralLorentzMetricPair period hPeriod := by
  apply Prod.ext
  · exact intrinsicSmoothGeneralLorentzMetric_timeTranslation_fixed
      period hPeriod parameter
  · exact intrinsicSmoothGeneralLorentzMetric_timeTranslation_fixed
      period hPeriod parameter

/-- Scalar integrals are invariant under the genuine time-translation flow. -/
theorem effectiveTimeFlow_integral_invariant
    (parameter : Real)
    (density : EffectiveQuotient period hPeriod → Real) :
    (∫ point,
        density (effectiveTimeFlow period hPeriod parameter point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, density point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  by
    simpa only using
      (intrinsicCanonicalLorentzVolumeMeasure_timeTranslation_measurePreserving
        period hPeriod parameter).integral_comp
          (effectiveTimeFlowDiffeomorph
            period hPeriod parameter).toHomeomorph.measurableEmbedding
          density

/-- Exact pointwise bridge still required between the derivative of the
genuine tensor pullback orbit and a supplied infinitesimal action. The
regularity field excludes the default value of `deriv` on a
non-differentiable curve. No differentiation under the spacetime integral,
and hence no skew-adjointness conclusion, is included. -/
structure GeneralMetricTimeTranslationOrbitGeneratorBridge
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (MetricPair period hPeriod)) : Prop where
  pullback_regular :
    TensorPullbackCurveDifferentiability period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod)
  action_first_at :
    ∀ field point,
      (representation.action
          (effectiveTimeTranslationCInfinityGhost period hPeriod)
          field).1.tensor point =
        covariantTensorDiffeomorphismGeneratorAt period hPeriod
          (effectiveTimeFlowDiffeomorph period hPeriod)
          field.1.tensor.toTensorField point
  action_second_at :
    ∀ field point,
      (representation.action
          (effectiveTimeTranslationCInfinityGhost period hPeriod)
          field).2.tensor point =
        covariantTensorDiffeomorphismGeneratorAt period hPeriod
          (effectiveTimeFlowDiffeomorph period hPeriod)
          field.2.tensor.toTensorField point

end
end P0EFTJanusProgramPGeneralMetricTimeTranslationSkew4D
end JanusFormal
