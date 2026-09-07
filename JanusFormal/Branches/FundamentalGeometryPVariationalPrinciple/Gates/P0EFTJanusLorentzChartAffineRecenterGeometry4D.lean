import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartVariationTransport4D

/-! # Exact affine metric geometry and local domains for action recentering -/

namespace JanusFormal
namespace P0EFTJanusLorentzChartAffineRecenterGeometry4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  GeneralMetricTangentFiber period hPeriod point

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The musical inverse is determined by the covariant tensor. -/
theorem smoothGeneralLorentzMetric_eq_of_tensor_eq
    (first second : SmoothGeneralLorentzMetric period hPeriod)
    (hTensor : first.tensor = second.tensor) : first = second := by
  cases first with
  | mk firstTensor firstMusical firstEq firstLorentz =>
    cases second with
    | mk secondTensor secondMusical secondEq secondLorentz =>
      change firstTensor = secondTensor at hTensor
      cases hTensor
      have hMusical : firstMusical = secondMusical := by
        funext point
        apply ContinuousLinearEquiv.coe_injective
        exact (firstEq point).trans (secondEq point).symm
      cases hMusical
      rfl

/-- A zero perturbation preserves the genuine metric, independently of frame choices. -/
theorem lorentzChart_zero_metric
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric 0
      (regularGeneralMetricSmoothC2Variation_zero_mem_lorentzChartDomain period hPeriod metric)).metric =
      metric.metric := by
  apply smoothGeneralLorentzMetric_eq_of_tensor_eq period hPeriod
  change metric.metric.tensor + 0 = metric.metric.tensor
  exact add_zero _

/-- Both presentations of g+h+k have exactly the same musical metric. -/
theorem lorentzChartRecenter_metric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift increment : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hTotal : regularGeneralMetricSmoothC2Variation period hPeriod metric (shift + increment) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hIncrement : regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift) increment ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)) :
    (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
      increment hIncrement).metric =
    (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric (shift + increment) hTotal).metric := by
  apply smoothGeneralLorentzMetric_eq_of_tensor_eq period hPeriod
  change (metric.metric.tensor + shift) + increment = metric.metric.tensor + (shift + increment)
  exact add_assoc _ _ _

/-- The fixed density of the original action is preserved by every reconstruction. -/
theorem lorentzChart_stored_volume
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift).volume =
      metric.volume := rfl

/-- Smooth tensor lines embed as the actual affine lines of the completed chart. -/
theorem regularGeneralMetricSmoothC2Variation_affine_line
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod) (t : Real) :
    regularGeneralMetricSmoothC2Variation period hPeriod metric (shift + t • direction) =
      regularGeneralMetricSmoothC2Variation period hPeriod metric shift +
        t • regularGeneralMetricSmoothC2Variation period hPeriod metric direction := by
  unfold regularGeneralMetricSmoothC2Variation
  rw [map_add, map_smul]

/-- Admissibility persists near any admissible smooth point, not only at zero. -/
theorem lorentzChart_affine_line_eventually_admissible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    ∀ᶠ t : Real in 𝓝 0, regularGeneralMetricSmoothC2Variation period hPeriod metric
      (shift + t • direction) ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod metric := by
  have hContinuous : Continuous (fun t : Real =>
      regularGeneralMetricSmoothC2Variation period hPeriod metric shift +
        t • regularGeneralMetricSmoothC2Variation period hPeriod metric direction) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hAt : regularGeneralMetricSmoothC2Variation period hPeriod metric shift +
      (0 : Real) • regularGeneralMetricSmoothC2Variation period hPeriod metric direction ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric := by
    simpa only [zero_smul, add_zero] using hShift
  have hEvent := hContinuous.continuousAt.eventually
    ((regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod metric).mem_nhds hAt)
  filter_upwards [hEvent] with t ht
  rw [regularGeneralMetricSmoothC2Variation_affine_line]
  exact ht

/-- Both original and recentered chart domains hold along the same tensor line near zero. -/
theorem lorentzChartRecenter_line_eventually_admissible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    ∀ᶠ t : Real in 𝓝 0,
      regularGeneralMetricSmoothC2Variation period hPeriod metric (shift + t • direction) ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod metric ∧
      regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
        (t • direction) ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift) := by
  have hOriginal := lorentzChart_affine_line_eventually_admissible period hPeriod metric shift direction hShift
  have hNew := lorentzChart_affine_line_eventually_admissible period hPeriod
    (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift) 0 direction
    (regularGeneralMetricSmoothC2Variation_zero_mem_lorentzChartDomain period hPeriod _)
  simpa only [zero_add] using hOriginal.and hNew

end
end P0EFTJanusLorentzChartAffineRecenterGeometry4D
end JanusFormal
