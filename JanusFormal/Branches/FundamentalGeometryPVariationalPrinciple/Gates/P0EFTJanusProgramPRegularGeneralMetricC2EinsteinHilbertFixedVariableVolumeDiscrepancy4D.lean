import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D

/-!
# Exact fixed/variable-volume Einstein--Hilbert discrepancy

The transported-frame paired chart keeps the legacy `volume` field fixed.
The unrestricted metric chart instead varies the genuine metric volume.  This
file computes their exact first-order difference.  The missing term is the
Einstein--Hilbert scalar Lagrangian times the half-trace volume variation; it
is not a boundary term and therefore cannot be discarded by Stokes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar :=
  C(EffectiveQuotient period hPeriod, Real)

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

/-- Fréchet derivative of the transported-frame, fixed-volume EH density. -/
def regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C0Scalar period hPeriod :=
  fderiv Real
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity
      period hPeriod metric couplings) 0

theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    HasFDerivAt
      (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity
        period hPeriod metric couplings)
      (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings) 0 := by
  exact (((regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_contDiffOn_two
    period hPeriod metric couplings).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
        (zero_mem_regularGeneralMetricC2Domain period hPeriod metric)))
    |>.differentiableAt (by norm_num)).hasFDerivAt

@[simp]
theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings direction =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod metric.volume •
        ((1 / (2 * couplings.gravitationalCoupling)) •
          regularGeneralMetricC0ScalarCurvatureDerivativeAtZero
            period hPeriod metric direction) := by
  have hVolume : HasFDerivAt
      (fun _ : RegularGeneralMetricC2Core period hPeriod metric =>
        smoothToCanonicalPhysicalContinuousScalar period hPeriod metric.volume)
      (0 : RegularGeneralMetricC2Core period hPeriod metric →L[Real]
        C0Scalar period hPeriod)
      (0 : RegularGeneralMetricC2Core period hPeriod metric) :=
    hasFDerivAt_const (x :=
      (0 : RegularGeneralMetricC2Core period hPeriod metric))
      (c := smoothToCanonicalPhysicalContinuousScalar
        period hPeriod metric.volume)
  have hCurvature :=
    regularGeneralMetricC0ScalarCurvature_hasFDerivAt_zero
      period hPeriod metric
  have hScaled :=
    (hCurvature.sub_const
      (regularGeneralMetricC0Constant period hPeriod
        (2 * couplings.cosmologicalConstant))).const_smul
          (1 / (2 * couplings.gravitationalCoupling))
  have hProduct := hVolume.mul hScaled
  have hUnique :=
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_hasFDerivAt_zero
      period hPeriod metric couplings).unique hProduct
  have hApply := congrArg (fun derivative => derivative direction) hUnique
  simpa only [regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero,
    add_apply, add_zero, zero_apply, smul_apply, smul_zero,
    Pi.smul_apply, Pi.sub_apply] using hApply

/-- The variable-volume derivative is the fixed-volume derivative plus the
exact missing volume contribution. -/
theorem regularGeneralMetricC0EinsteinHilbertDensityDerivative_fixedVolume_discrepancy
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings direction =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero
          period hPeriod metric couplings direction +
        ((1 / (2 * couplings.gravitationalCoupling)) •
          (regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 -
            regularGeneralMetricC0Constant period hPeriod
              (2 * couplings.cosmologicalConstant))) •
          regularGeneralMetricC0VolumeDerivativeAtZero
            period hPeriod metric direction := by
  rw [regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero_apply,
    regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero_apply,
    regularGeneralMetricC0Volume_zero]

/-- Fréchet derivative of the integrated fixed-volume EH family. -/
def regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real] Real :=
  (regularGeneralMetricC0IntegralCLM period hPeriod measure).comp
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero
      period hPeriod metric couplings)

theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    HasFDerivAt
      (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
        period hPeriod metric measure couplings)
      (regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod metric measure couplings) 0 := by
  have hInner :=
    regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity_hasFDerivAt_zero
      period hPeriod metric couplings
  have hOuter : HasFDerivAt
      (fun field => regularGeneralMetricC0IntegralCLM
        period hPeriod measure field)
      (regularGeneralMetricC0IntegralCLM period hPeriod measure)
      (regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity
        period hPeriod metric couplings 0) :=
    (regularGeneralMetricC0IntegralCLM period hPeriod measure).hasFDerivAt
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Integrated form of the exact volume discrepancy. -/
theorem regularGeneralMetricC0EinsteinHilbertActionDerivative_fixedVolume_discrepancy
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric measure couplings direction =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
          period hPeriod metric measure couplings direction +
        ∫ point,
          (((1 / (2 * couplings.gravitationalCoupling)) •
            (regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 -
              regularGeneralMetricC0Constant period hPeriod
                (2 * couplings.cosmologicalConstant))) •
            regularGeneralMetricC0VolumeDerivativeAtZero
              period hPeriod metric direction) point ∂measure := by
  unfold regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
    regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    regularGeneralMetricC0EinsteinHilbertDensityDerivative_fixedVolume_discrepancy,
    map_add, regularGeneralMetricC0IntegralCLM_apply,
    regularGeneralMetricC0IntegralCLM_apply]

/-- Gate marker: fixed volume is now formally separated from the genuine
metric-volume variation at density and action levels. -/
theorem regular_general_metric_c2_einstein_hilbert_fixed_variable_volume_discrepancy_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings direction =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero
          period hPeriod metric couplings direction +
        ((1 / (2 * couplings.gravitationalCoupling)) •
          (regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 -
            regularGeneralMetricC0Constant period hPeriod
              (2 * couplings.cosmologicalConstant))) •
          regularGeneralMetricC0VolumeDerivativeAtZero
            period hPeriod metric direction ∧
      regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
          period hPeriod metric measure couplings direction =
        regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
            period hPeriod metric measure couplings direction +
          ∫ point,
            (((1 / (2 * couplings.gravitationalCoupling)) •
              (regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 -
                regularGeneralMetricC0Constant period hPeriod
                  (2 * couplings.cosmologicalConstant))) •
              regularGeneralMetricC0VolumeDerivativeAtZero
                period hPeriod metric direction) point ∂measure := by
  exact ⟨
    regularGeneralMetricC0EinsteinHilbertDensityDerivative_fixedVolume_discrepancy
      period hPeriod metric couplings direction,
    regularGeneralMetricC0EinsteinHilbertActionDerivative_fixedVolume_discrepancy
      period hPeriod metric measure couplings direction⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
end JanusFormal
