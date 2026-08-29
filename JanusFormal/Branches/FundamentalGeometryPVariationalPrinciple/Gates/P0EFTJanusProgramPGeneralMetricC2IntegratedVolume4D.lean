import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.L1

/-!
# Finite-measure integration on the genuine general-metric C² chart

The value projection of the canonical C² jet core is continuous.  It therefore
integrates continuously against every finite common measure.  Applying this
functional to the already constructed general-metric volume density gives the
actual local integrated volume without an intermediate Sobolev hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

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

/-- Continuous integration of the value represented by a canonical C² jet. -/
def canonicalPhysicalC2ScalarIntegralCLM
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    C2Scalar period hPeriod →L[Real] Real :=
  (L1.integralCLM
      (α := EffectiveQuotient period hPeriod)
      (E := Real) (μ := measure)).comp
    ((ContinuousMap.toLp (1 : ENNReal) measure Real).comp
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod))

theorem canonicalPhysicalC2ScalarIntegralCLM_apply
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (field : C2Scalar period hPeriod) :
    canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure field =
      ∫ point,
        canonicalPhysicalScalarC2JetCoreToContinuous
          period hPeriod field point ∂measure := by
  let continuousField :=
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod field
  let l1Field : Lp Real (1 : ENNReal) measure :=
    ContinuousMap.toLp (1 : ENNReal) measure Real continuousField
  change L1.integralCLM l1Field =
    ∫ point, continuousField point ∂measure
  calc
    L1.integralCLM l1Field = L1.integral l1Field :=
      (L1.integral_eq l1Field).symm
    _ = ∫ point,
          (l1Field : EffectiveQuotient period hPeriod → Real) point
          ∂measure := L1.integral_eq_integral l1Field
    _ = ∫ point, continuousField point ∂measure := by
      exact integral_congr_ae
        (ContinuousMap.coeFn_toLp
          (p := (1 : ENNReal)) (μ := measure) (𝕜 := Real)
          continuousField)

/-- The integrated volume of the actual regular general-metric C² chart. -/
def regularGeneralMetricC2IntegratedVolume
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (variation : RegularGeneralMetricC2Core period hPeriod metric) : Real :=
  canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure
    (regularGeneralMetricC2Volume period hPeriod metric variation)

theorem regularGeneralMetricC2IntegratedVolume_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    ContDiffOn Real 2
      (regularGeneralMetricC2IntegratedVolume
        period hPeriod metric measure)
      (regularGeneralMetricC2Domain period hPeriod metric) := by
  exact
    (canonicalPhysicalC2ScalarIntegralCLM
      period hPeriod measure).contDiff.contDiffOn.comp
        (regularGeneralMetricC2Volume_contDiffOn_two
          period hPeriod metric)
        (fun _ _ => mem_univ _)

theorem regularGeneralMetricC2IntegratedVolume_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    regularGeneralMetricC2IntegratedVolume
        period hPeriod metric measure 0 =
      ∫ point, metric.volume point ∂measure := by
  rw [regularGeneralMetricC2IntegratedVolume,
    regularGeneralMetricC2Volume_zero,
    canonicalPhysicalC2ScalarIntegralCLM_apply,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  rfl

/-- Summary gate for the genuinely integrated local volume family. -/
theorem regular_general_metric_c2_integrated_volume_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    ContDiffOn Real 2
        (regularGeneralMetricC2IntegratedVolume
          period hPeriod metric measure)
        (regularGeneralMetricC2Domain period hPeriod metric) ∧
      regularGeneralMetricC2IntegratedVolume
          period hPeriod metric measure 0 =
        ∫ point, metric.volume point ∂measure :=
  ⟨regularGeneralMetricC2IntegratedVolume_contDiffOn_two
      period hPeriod metric measure,
    regularGeneralMetricC2IntegratedVolume_zero
      period hPeriod metric measure⟩

end

end P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D
end JanusFormal
