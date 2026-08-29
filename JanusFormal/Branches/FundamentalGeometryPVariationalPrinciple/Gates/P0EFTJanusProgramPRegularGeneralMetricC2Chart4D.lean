import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D

/-!
# C² chart attached to an actual regular general Lorentz metric

The genuine four-frame already stored in `RegularGeneralLorentzMetric` is a
`SmoothD8Frame`.  It therefore instantiates the general relative C² metric
core and its open positive-volume domain without an auxiliary frame or a
special metric ansatz.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D

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

/-- The true smooth frame stored by a regular metric, viewed through the
existing finite-generator interface. -/
def regularGeneralLorentzMetricSmoothD8Frame
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothD8Frame period hPeriod where
  count := 4
  vectorAt point index := metric.frame index point
  spansAt point := by
    apply top_unique
    intro vector _
    obtain ⟨coordinates, rfl⟩ := (metric.frameEquiv point).surjective vector
    rw [← (Pi.basisFun Real (Fin 4)).sum_repr coordinates, map_sum]
    apply Submodule.sum_mem
    intro index _
    rw [map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨index, ?_⟩
    exact RegularGeneralLorentzMetric.frame_eq_basisFun
      period hPeriod metric point index
  contMDiff_vector index := (metric.frame index).contMDiff_toFun

@[simp]
theorem regularGeneralLorentzMetricSmoothD8Frame_count
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (regularGeneralLorentzMetricSmoothD8Frame
      period hPeriod metric).count = 4 :=
  rfl

@[simp]
theorem regularGeneralLorentzMetricSmoothD8Frame_vectorAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    (regularGeneralLorentzMetricSmoothD8Frame
      period hPeriod metric).vectorAt point index =
      metric.frame index point :=
  rfl

/-- Complete general-metric tangent based at the supplied regular metric. -/
abbrev RegularGeneralMetricC2Core
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  GeneralMetricRelativeC2Core period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) metric.metric

/-- Genuine admissible open set carrying inverse metric and positive volume. -/
def regularGeneralMetricC2Domain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (RegularGeneralMetricC2Core period hPeriod metric) :=
  generalMetricRelativeC2VolumeDomain period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) metric.metric

theorem regularGeneralMetricC2Domain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2Domain period hPeriod metric) :=
  generalMetricRelativeC2VolumeDomain_isOpen period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) metric.metric

theorem zero_mem_regularGeneralMetricC2Domain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (0 : RegularGeneralMetricC2Core period hPeriod metric) ∈
      regularGeneralMetricC2Domain period hPeriod metric :=
  zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) metric.metric

/-- Actual local C² volume density of the supplied regular metric. -/
def regularGeneralMetricC2Volume
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :=
  generalMetricC2VolumeDensity period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric metric.volume variation

theorem regularGeneralMetricC2Volume_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2Volume period hPeriod metric)
      (regularGeneralMetricC2Domain period hPeriod metric) :=
  generalMetricC2VolumeDensity_contDiffOn_two period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric metric.volume

theorem regularGeneralMetricC2Volume_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    regularGeneralMetricC2Volume period hPeriod metric 0 =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod metric.volume :=
  generalMetricC2VolumeDensity_zero period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric metric.volume

/-- Dense faithful inclusion of every genuine smooth symmetric metric
variation into the actual regular-metric chart. -/
theorem regularGeneralMetric_smoothCore_faithful_dense
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Function.Injective
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric) ∧
      DenseRange
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric) :=
  ⟨smoothToGeneralMetricRelativeC2Core_injective period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric,
    smoothToGeneralMetricRelativeC2Core_denseRange period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric⟩

/-- Summary gate for the actual regular general-metric local chart. -/
theorem regular_general_metric_c2_chart_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2Domain period hPeriod metric) ∧
      (0 : RegularGeneralMetricC2Core period hPeriod metric) ∈
        regularGeneralMetricC2Domain period hPeriod metric ∧
      ContDiffOn Real 2
        (regularGeneralMetricC2Volume period hPeriod metric)
        (regularGeneralMetricC2Domain period hPeriod metric) ∧
      regularGeneralMetricC2Volume period hPeriod metric 0 =
        smoothToCanonicalPhysicalScalarC2JetCore
          period hPeriod metric.volume ∧
      Function.Injective
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric) ∧
      DenseRange
        (smoothToGeneralMetricRelativeC2Core period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric) := by
  exact ⟨regularGeneralMetricC2Domain_isOpen period hPeriod metric,
    zero_mem_regularGeneralMetricC2Domain period hPeriod metric,
    regularGeneralMetricC2Volume_contDiffOn_two period hPeriod metric,
    regularGeneralMetricC2Volume_zero period hPeriod metric,
    (regularGeneralMetric_smoothCore_faithful_dense
      period hPeriod metric).1,
    (regularGeneralMetric_smoothCore_faithful_dense
      period hPeriod metric).2⟩

end


end P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
end JanusFormal
