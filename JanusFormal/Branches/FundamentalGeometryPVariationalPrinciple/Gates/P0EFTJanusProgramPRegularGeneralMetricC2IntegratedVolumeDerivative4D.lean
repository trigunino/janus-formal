import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D

/-! # Exact first derivative of integrated regular-metric C² volume -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2IntegratedVolumeDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminantDerivative4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D

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

/-- Continuous integral of the exact C² volume-density derivative. -/
def regularGeneralMetricC2IntegratedVolumeDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real] Real :=
  (canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure).comp
    (regularGeneralMetricC2VolumeDerivativeAtZero period hPeriod metric)

theorem regularGeneralMetricC2IntegratedVolume_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    HasFDerivAt
      (regularGeneralMetricC2IntegratedVolume
        period hPeriod metric measure)
      (regularGeneralMetricC2IntegratedVolumeDerivativeAtZero
        period hPeriod metric measure) 0 := by
  have hInner := regularGeneralMetricC2Volume_hasFDerivAt_zero
    period hPeriod metric
  have hOuter : HasFDerivAt
      (fun field => canonicalPhysicalC2ScalarIntegralCLM
        period hPeriod measure field)
      (canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure)
      (regularGeneralMetricC2Volume period hPeriod metric 0) :=
    (canonicalPhysicalC2ScalarIntegralCLM
      period hPeriod measure).hasFDerivAt
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

theorem regularGeneralMetricC2IntegratedVolumeDerivativeAtZero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC2IntegratedVolumeDerivativeAtZero
        period hPeriod metric measure direction =
      ∫ point,
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (regularGeneralMetricC2VolumeDerivativeAtZero
            period hPeriod metric direction) point ∂measure := by
  exact canonicalPhysicalC2ScalarIntegralCLM_apply period hPeriod measure
    (regularGeneralMetricC2VolumeDerivativeAtZero
      period hPeriod metric direction)

private theorem regularGeneralMetricC2VolumeDerivative_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (regularGeneralMetricC2VolumeDerivativeAtZero
          period hPeriod metric direction) point =
      (1 / 2 : Real) * metric.volume point *
        ∑ index : Fin 4,
          canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (direction.1 index index) point := by
  rw [regularGeneralMetricC2VolumeDerivativeAtZero]
  rw [generalMetricC2VolumeDensityDerivativeAtZero_apply]
  rw [map_smul]
  change (1 / 2 : Real) *
      (metric.volume point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (c2FiniteMatrixTrace period hPeriod 4 direction.1) point) = _
  rw [c2FiniteMatrixTrace_apply]
  have hSum :
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (∑ index : Fin 4, direction.1 index index) point =
        ∑ index : Fin 4,
          canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (direction.1 index index) point := by
    exact map_sum
      ((ContinuousMap.evalCLM Real point).comp
        (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod))
      (fun index : Fin 4 => direction.1 index index) Finset.univ
  rw [hSum]
  ring

/-- Integrated half-trace formula for the metric-volume variation. -/
theorem regularGeneralMetricC2IntegratedVolumeDerivative_halfTrace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC2IntegratedVolumeDerivativeAtZero
        period hPeriod metric measure direction =
      ∫ point,
        (1 / 2 : Real) * metric.volume point *
          ∑ index : Fin 4,
            canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
              (direction.1 index index) point ∂measure := by
  rw [regularGeneralMetricC2IntegratedVolumeDerivativeAtZero_apply]
  apply integral_congr_ae
  filter_upwards [] with point
  exact regularGeneralMetricC2VolumeDerivative_valueAt
    period hPeriod metric direction point

/-- Gate marker for the exact integrated metric-volume derivative. -/
theorem regular_general_metric_c2_integrated_volume_derivative_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    HasFDerivAt
        (regularGeneralMetricC2IntegratedVolume
          period hPeriod metric measure)
        (regularGeneralMetricC2IntegratedVolumeDerivativeAtZero
          period hPeriod metric measure) 0 ∧
      ∀ direction,
        regularGeneralMetricC2IntegratedVolumeDerivativeAtZero
            period hPeriod metric measure direction =
          ∫ point,
            (1 / 2 : Real) * metric.volume point *
              ∑ index : Fin 4,
                canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
                  (direction.1 index index) point ∂measure :=
  ⟨regularGeneralMetricC2IntegratedVolume_hasFDerivAt_zero
      period hPeriod metric measure,
    regularGeneralMetricC2IntegratedVolumeDerivative_halfTrace
      period hPeriod metric measure⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2IntegratedVolumeDerivative4D
end JanusFormal
