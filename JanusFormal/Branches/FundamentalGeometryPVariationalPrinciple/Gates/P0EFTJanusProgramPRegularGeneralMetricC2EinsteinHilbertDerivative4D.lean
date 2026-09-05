import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IntegratedVolumeDerivative4D

/-! # Exact Einstein--Hilbert derivatives on the regular general-metric C² chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D

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

/-- The exact C⁰-valued half-trace derivative of the varied volume. -/
def regularGeneralMetricC0VolumeDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C0Scalar period hPeriod :=
  (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
    (regularGeneralMetricC2VolumeDerivativeAtZero period hPeriod metric)

theorem regularGeneralMetricC0Volume_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    HasFDerivAt
      (regularGeneralMetricC0Volume period hPeriod metric)
      (regularGeneralMetricC0VolumeDerivativeAtZero period hPeriod metric) 0 := by
  have hInner := regularGeneralMetricC2Volume_hasFDerivAt_zero
    period hPeriod metric
  have hOuter : HasFDerivAt
      (fun field => canonicalPhysicalScalarC2JetCoreToContinuous
        period hPeriod field)
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod)
      (regularGeneralMetricC2Volume period hPeriod metric 0) :=
    (canonicalPhysicalScalarC2JetCoreToContinuous
      period hPeriod).hasFDerivAt
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Exact C⁰-valued derivative of the intrinsic scalar curvature family. -/
def regularGeneralMetricC0ScalarCurvatureDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C0Scalar period hPeriod :=
  fderiv Real
    (regularGeneralMetricC0ScalarCurvature period hPeriod metric) 0

theorem regularGeneralMetricC0ScalarCurvature_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    HasFDerivAt
      (regularGeneralMetricC0ScalarCurvature period hPeriod metric)
      (regularGeneralMetricC0ScalarCurvatureDerivativeAtZero
        period hPeriod metric) 0 := by
  exact (((regularGeneralMetricC0ScalarCurvature_contDiffOn_two
    period hPeriod metric).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
        (zero_mem_regularGeneralMetricC2Domain period hPeriod metric)))
    |>.differentiableAt (by norm_num)).hasFDerivAt

/-- Product-rule derivative of the genuine variable-volume EH density. -/
def regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C0Scalar period hPeriod :=
  fderiv Real
    (regularGeneralMetricC0EinsteinHilbertDensity
      period hPeriod metric couplings) 0

theorem regularGeneralMetricC0EinsteinHilbertDensity_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    HasFDerivAt
      (regularGeneralMetricC0EinsteinHilbertDensity
        period hPeriod metric couplings)
      (regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings) 0 := by
  have hVolume := regularGeneralMetricC0Volume_hasFDerivAt_zero
    period hPeriod metric
  have hCurvature :=
    regularGeneralMetricC0ScalarCurvature_hasFDerivAt_zero
      period hPeriod metric
  have hScaled :=
    (hCurvature.sub_const
      (regularGeneralMetricC0Constant period hPeriod
        (2 * couplings.cosmologicalConstant))).const_smul
          (1 / (2 * couplings.gravitationalCoupling))
  have hProduct := hVolume.mul hScaled
  have hDifferentiable : DifferentiableAt Real
      (regularGeneralMetricC0EinsteinHilbertDensity
        period hPeriod metric couplings) 0 := by
    apply DifferentiableAt.congr_of_eventuallyEq hProduct.differentiableAt
    exact Filter.Eventually.of_forall fun _ => rfl
  exact hDifferentiable.hasFDerivAt

@[simp]
theorem regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings direction =
      regularGeneralMetricC0Volume period hPeriod metric 0 •
          ((1 / (2 * couplings.gravitationalCoupling)) •
            regularGeneralMetricC0ScalarCurvatureDerivativeAtZero
              period hPeriod metric direction) +
        ((1 / (2 * couplings.gravitationalCoupling)) •
          (regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 -
            regularGeneralMetricC0Constant period hPeriod
              (2 * couplings.cosmologicalConstant))) •
          regularGeneralMetricC0VolumeDerivativeAtZero
            period hPeriod metric direction := by
  have hVolume := regularGeneralMetricC0Volume_hasFDerivAt_zero
    period hPeriod metric
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
    (regularGeneralMetricC0EinsteinHilbertDensity_hasFDerivAt_zero
      period hPeriod metric couplings).unique hProduct
  have hApply := congrArg (fun derivative => derivative direction) hUnique
  simpa only [regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero,
    add_apply, smul_apply, Pi.smul_apply, Pi.sub_apply] using hApply

/-- Integrated exact EH derivative on the same C² chart. -/
def regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real] Real :=
  (regularGeneralMetricC0IntegralCLM period hPeriod measure).comp
    (regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
      period hPeriod metric couplings)

theorem regularGeneralMetricC0EinsteinHilbertAction_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    HasFDerivAt
      (regularGeneralMetricC0EinsteinHilbertAction
        period hPeriod metric measure couplings)
      (regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric measure couplings) 0 := by
  have hInner :=
    regularGeneralMetricC0EinsteinHilbertDensity_hasFDerivAt_zero
      period hPeriod metric couplings
  have hOuter : HasFDerivAt
      (fun field => regularGeneralMetricC0IntegralCLM
        period hPeriod measure field)
      (regularGeneralMetricC0IntegralCLM period hPeriod measure)
      (regularGeneralMetricC0EinsteinHilbertDensity
        period hPeriod metric couplings 0) :=
    (regularGeneralMetricC0IntegralCLM period hPeriod measure).hasFDerivAt
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

theorem regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric measure couplings direction =
      ∫ point,
        regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
          period hPeriod metric couplings direction point ∂measure := by
  unfold regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
  rw [ContinuousLinearMap.comp_apply,
    regularGeneralMetricC0IntegralCLM_apply]

/-- Gate marker: the unrestricted EH density and action now have exact
Fréchet derivatives on the physical C² metric chart. -/
theorem regular_general_metric_c2_einstein_hilbert_derivative_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    HasFDerivAt
        (regularGeneralMetricC0EinsteinHilbertDensity
          period hPeriod metric couplings)
        (regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
          period hPeriod metric couplings) 0 ∧
      HasFDerivAt
        (regularGeneralMetricC0EinsteinHilbertAction
          period hPeriod metric measure couplings)
        (regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
          period hPeriod metric measure couplings) 0 :=
  ⟨regularGeneralMetricC0EinsteinHilbertDensity_hasFDerivAt_zero
      period hPeriod metric couplings,
    regularGeneralMetricC0EinsteinHilbertAction_hasFDerivAt_zero
      period hPeriod metric measure couplings⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
end JanusFormal
