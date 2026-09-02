import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

/-!
# Einstein--Maxwell actions on the Lorentz C² chart

The existing Einstein--Hilbert and Maxwell families are restricted to the
open chart on which every genuine smooth metric variation is now known to
remain Lorentzian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartActions4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

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

local instance regularGeneralMetricC2CoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (RegularGeneralMetricC2Core period hPeriod metric) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric).normedAddCommGroup

local instance regularGeneralMetricC2CoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (RegularGeneralMetricC2Core period hPeriod metric) :=
  Submodule.normedSpace
    (generalMetricRelativeC2CoreSubmodule period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric)

/-- The Einstein--Hilbert action is `C²` on the genuine Lorentz chart. -/
theorem regularGeneralMetricC0EinsteinHilbertAction_contDiffOn_two_lorentzChart
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    ContDiffOn Real 2
      (regularGeneralMetricC0EinsteinHilbertAction period hPeriod metric
        measure couplings)
      (regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :=
  (regularGeneralMetricC0EinsteinHilbertAction_contDiffOn_two period hPeriod
    metric measure couplings).mono (fun _ hVariation => hVariation.1)

/-- The integrated Maxwell pairing is `C²` on the same Lorentz chart. -/
theorem regularGeneralMetricC2IntegratedMaxwellPairing_contDiffOn_two_lorentzChart
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2IntegratedMaxwellPairing period hPeriod metric
        measure first second)
      (regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :=
  (regularGeneralMetricC2IntegratedMaxwellPairing_contDiffOn_two period hPeriod
    metric measure first second).mono (fun _ hVariation => hVariation.1)

/-- The local Einstein--Maxwell action on the unified Lorentz chart. -/
def regularGeneralMetricC2LorentzEinsteinMaxwellAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) : Real :=
  regularGeneralMetricC0EinsteinHilbertAction period hPeriod metric measure
      couplings variation +
    regularGeneralMetricC2IntegratedMaxwellPairing period hPeriod metric
      measure first second variation

theorem regularGeneralMetricC2LorentzEinsteinMaxwellAction_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2LorentzEinsteinMaxwellAction period hPeriod metric
        measure couplings first second)
      (regularGeneralMetricC2LorentzChartDomain period hPeriod metric) := by
  exact
    (regularGeneralMetricC0EinsteinHilbertAction_contDiffOn_two_lorentzChart
      period hPeriod metric measure couplings).add
    (regularGeneralMetricC2IntegratedMaxwellPairing_contDiffOn_two_lorentzChart
      period hPeriod metric measure first second)

theorem regularGeneralMetricC2LorentzEinsteinMaxwellAction_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC2LorentzEinsteinMaxwellAction period hPeriod metric
        measure couplings first second 0 =
      intrinsicEinsteinHilbertAction period hPeriod couplings
          (JanusFormal.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D.RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
            period hPeriod metric)
          measure +
        ∫ point, metric.volume point *
          globalMaxwellPairing period hPeriod metric.metric first second point
          ∂measure := by
  rw [regularGeneralMetricC2LorentzEinsteinMaxwellAction,
    regularGeneralMetricC0EinsteinHilbertAction_zero,
    regularGeneralMetricC2IntegratedMaxwellPairing_zero]

/-- Gate marker: the actual Lorentz chart now carries both bulk metric action
families, their sum, and the genuine smooth metric represented by each smooth
chart point. -/
theorem regular_general_metric_c2_lorentz_chart_actions_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    IsOpen (regularGeneralMetricC2LorentzChartDomain period hPeriod metric) ∧
      (0 : RegularGeneralMetricC2Core period hPeriod metric) ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod metric ∧
      ContDiffOn Real 2
        (regularGeneralMetricC2LorentzEinsteinMaxwellAction period hPeriod
          metric measure couplings first second)
        (regularGeneralMetricC2LorentzChartDomain period hPeriod metric) ∧
      ∀ (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
        (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod
          metric tensor ∈
            regularGeneralMetricC2LorentzChartDomain period hPeriod metric),
        (regularGeneralMetricC2LorentzChartMetric period hPeriod metric tensor
          hVariation).tensor = metric.metric.tensor + tensor := by
  exact ⟨regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod metric,
    zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod metric,
    regularGeneralMetricC2LorentzEinsteinMaxwellAction_contDiffOn_two
      period hPeriod metric measure couplings first second,
    fun tensor hVariation =>
      regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod metric
        tensor hVariation⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartActions4D
end JanusFormal
