import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwell4D

/-! # Fixed-volume Maxwell action bridge -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2FixedVolumeMaxwellActionBridge4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwell4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Maxwell density with the base volume held fixed. -/
def regularGeneralMetricC0FixedVolumeMaxwellDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod metric.volume *
    ((-(1 / 4 : Real)) •
      regularGeneralMetricC0MaxwellPairing period hPeriod metric first second
        variation)

theorem regularGeneralMetricC0FixedVolumeMaxwellDensity_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC0FixedVolumeMaxwellDensity period hPeriod metric
        first second)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  unfold regularGeneralMetricC0FixedVolumeMaxwellDensity
  exact contDiffOn_const.mul
    ((regularGeneralMetricC0MaxwellPairing_contDiffOn_two period hPeriod metric
      first second).const_smul _)

/-- Smooth density represented by the fixed base volume and genuine pairing. -/
def regularGeneralMetricFixedVolumeSmoothMaxwellDensity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := fun point => metric.volume point *
    (-(1 / 4 : Real) *
      globalMaxwellPairing period hPeriod variedMetric first second point)
  contMDiff_toFun := metric.volume.contMDiff_toFun.mul
    (contMDiff_const.mul
      (globalSmoothMaxwellPairing period hPeriod variedMetric first second
        ).contMDiff_toFun)

theorem regularGeneralMetricC0FixedVolumeMaxwellDensity_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor ∈ regularGeneralMetricC2Domain period hPeriod metric)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC0FixedVolumeMaxwellDensity period hPeriod metric
        first second
          (smoothToGeneralMetricRelativeC2Core period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularGeneralMetricFixedVolumeSmoothMaxwellDensity period hPeriod
          metric variedMetric first second) := by
  have hPairing := regularGeneralMetricC0MaxwellPairing_smooth period hPeriod
    metric tensor variedMetric hVaried hVariation first second
  unfold regularGeneralMetricC0FixedVolumeMaxwellDensity
  rw [hPairing]
  apply ContinuousMap.ext
  intro point
  rfl

/-- Integrated fixed-volume Maxwell pairing. -/
def regularGeneralMetricC0FixedVolumeMaxwellAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) : Real :=
  regularGeneralMetricC0IntegralCLM period hPeriod measure
    (regularGeneralMetricC0FixedVolumeMaxwellDensity period hPeriod metric
      first second variation)

theorem regularGeneralMetricC0FixedVolumeMaxwellAction_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC0FixedVolumeMaxwellAction period hPeriod metric
        measure first second)
      (regularGeneralMetricC2Domain period hPeriod metric) :=
  (regularGeneralMetricC0IntegralCLM period hPeriod measure).contDiff.contDiffOn
    |>.comp
      (regularGeneralMetricC0FixedVolumeMaxwellDensity_contDiffOn_two period
        hPeriod metric first second) (fun _ _ => mem_univ _)

/-- Exact agreement with the intrinsic Maxwell action on a smooth Lorentz
chart variation. -/
theorem regularGeneralMetricC0FixedVolumeMaxwellAction_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : regularGeneralMetricSmoothC2Variation period hPeriod metric
        tensor ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC0FixedVolumeMaxwellAction period hPeriod metric measure
        first second
          (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) =
      intrinsicMaxwellAction period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          tensor hLorentz)
        (globalSmoothMaxwellPairing period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
            tensor hLorentz).metric first second) measure := by
  let varied := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    metric tensor hLorentz
  have hVaried : varied.metric.tensor = metric.metric.tensor + tensor :=
    regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod metric tensor
      hLorentz
  have hDensity :
      regularGeneralMetricC0FixedVolumeMaxwellDensity period hPeriod metric
          first second
            (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) =
        smoothToCanonicalPhysicalContinuousScalar period hPeriod
          (regularGeneralMetricFixedVolumeSmoothMaxwellDensity period hPeriod
            metric varied.metric first second) := by
    simpa only [regularGeneralMetricSmoothC2Variation] using
      (regularGeneralMetricC0FixedVolumeMaxwellDensity_smooth period hPeriod
        metric tensor varied.metric hVaried hLorentz.1 first second)
  unfold regularGeneralMetricC0FixedVolumeMaxwellAction
  rw [hDensity, regularGeneralMetricC0IntegralCLM_apply period hPeriod measure]
  rfl

/-- Gate marker for the fixed-potential, fixed-volume Maxwell action. -/
theorem regular_general_metric_c2_fixed_volume_maxwell_action_bridge_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : regularGeneralMetricSmoothC2Variation period hPeriod metric
        tensor ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC0FixedVolumeMaxwellAction period hPeriod metric measure
        potential potential
          (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) =
      intrinsicMaxwellAction period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
          tensor hLorentz)
        (globalSmoothMaxwellPairing period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric
            tensor hLorentz).metric potential potential) measure := by
  exact regularGeneralMetricC0FixedVolumeMaxwellAction_smooth period hPeriod
    metric tensor hLorentz measure potential potential

end
end P0EFTJanusProgramPRegularGeneralMetricC2FixedVolumeMaxwellActionBridge4D
end JanusFormal
