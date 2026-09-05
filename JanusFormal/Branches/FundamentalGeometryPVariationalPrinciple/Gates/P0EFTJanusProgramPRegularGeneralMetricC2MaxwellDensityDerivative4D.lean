import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MaxwellPairingDerivative4D

/-! # Exact variable-volume C² Maxwell density derivative -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellPairingDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

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

/-- Product-rule derivative of `volume × Maxwell pairing`. -/
def regularGeneralMetricC2MaxwellDensityDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C2Scalar period hPeriod :=
  fderiv Real
    (regularGeneralMetricC2MaxwellDensity
      period hPeriod metric first second) 0

theorem regularGeneralMetricC2MaxwellDensity_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    HasFDerivAt
      (regularGeneralMetricC2MaxwellDensity
        period hPeriod metric first second)
      (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
        period hPeriod metric first second) 0 := by
  let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
  have hVolume := regularGeneralMetricC2Volume_hasFDerivAt_zero
    period hPeriod metric
  have hPairing := regularGeneralMetricC2MaxwellPairing_hasFDerivAt_zero
    period hPeriod metric first second
  have hProduct := (product.hasFDerivAt.comp 0 hVolume).clm_apply hPairing
  have hDifferentiable : DifferentiableAt Real
      (regularGeneralMetricC2MaxwellDensity
        period hPeriod metric first second) 0 := by
    apply DifferentiableAt.congr_of_eventuallyEq hProduct.differentiableAt
    exact Filter.Eventually.of_forall fun _ => rfl
  exact hDifferentiable.hasFDerivAt

@[simp]
theorem regularGeneralMetricC2MaxwellDensityDerivativeAtZero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC2MaxwellDensityDerivativeAtZero
        period hPeriod metric first second direction =
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (regularGeneralMetricC2Volume period hPeriod metric 0)
          (regularGeneralMetricC2MaxwellPairingDerivativeAtZero
            period hPeriod metric first second direction) +
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (regularGeneralMetricC2VolumeDerivativeAtZero
            period hPeriod metric direction)
          (regularGeneralMetricC2MaxwellPairing
            period hPeriod metric first second 0) := by
  let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
  have hVolume := regularGeneralMetricC2Volume_hasFDerivAt_zero
    period hPeriod metric
  have hPairing := regularGeneralMetricC2MaxwellPairing_hasFDerivAt_zero
    period hPeriod metric first second
  have hProduct := (product.hasFDerivAt.comp 0 hVolume).clm_apply hPairing
  have hUnique :=
    (regularGeneralMetricC2MaxwellDensity_hasFDerivAt_zero
      period hPeriod metric first second).unique hProduct
  have hApply := congrArg (fun derivative => derivative direction) hUnique
  simpa only [regularGeneralMetricC2MaxwellDensityDerivativeAtZero,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    Function.comp_apply, product] using hApply

/-- The same derivative with both base fields identified with their smooth
physical values. -/
theorem regularGeneralMetricC2MaxwellDensityDerivativeAtZero_smoothBase
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC2MaxwellDensityDerivativeAtZero
        period hPeriod metric first second direction =
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (smoothToCanonicalPhysicalScalarC2JetCore
            period hPeriod metric.volume)
          (regularGeneralMetricC2MaxwellPairingDerivativeAtZero
            period hPeriod metric first second direction) +
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (regularGeneralMetricC2VolumeDerivativeAtZero
            period hPeriod metric direction)
          (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
            (globalSmoothMaxwellPairing
              period hPeriod metric.metric first second)) := by
  rw [regularGeneralMetricC2MaxwellDensityDerivativeAtZero_apply,
    regularGeneralMetricC2Volume_zero,
    regularGeneralMetricC2MaxwellPairing_zero]

/-- Continuous integral of the exact variable-volume Maxwell derivative. -/
def regularGeneralMetricC2IntegratedMaxwellPairingDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real] Real :=
  (canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure).comp
    (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
      period hPeriod metric first second)

theorem regularGeneralMetricC2IntegratedMaxwellPairing_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    HasFDerivAt
      (regularGeneralMetricC2IntegratedMaxwellPairing
        period hPeriod metric measure first second)
      (regularGeneralMetricC2IntegratedMaxwellPairingDerivativeAtZero
        period hPeriod metric measure first second) 0 := by
  have hInner := regularGeneralMetricC2MaxwellDensity_hasFDerivAt_zero
    period hPeriod metric first second
  have hOuter : HasFDerivAt
      (fun field => canonicalPhysicalC2ScalarIntegralCLM
        period hPeriod measure field)
      (canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure)
      (regularGeneralMetricC2MaxwellDensity
        period hPeriod metric first second 0) :=
    (canonicalPhysicalC2ScalarIntegralCLM
      period hPeriod measure).hasFDerivAt
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

theorem regularGeneralMetricC2IntegratedMaxwellPairingDerivativeAtZero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC2IntegratedMaxwellPairingDerivativeAtZero
        period hPeriod metric measure first second direction =
      ∫ point,
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
            period hPeriod metric first second direction) point ∂measure := by
  exact canonicalPhysicalC2ScalarIntegralCLM_apply period hPeriod measure
    (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
      period hPeriod metric first second direction)

/-- Gate marker for the actual variable-volume integrated Maxwell derivative. -/
theorem regular_general_metric_c2_maxwell_density_derivative_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    HasFDerivAt
        (regularGeneralMetricC2MaxwellDensity
          period hPeriod metric first second)
        (regularGeneralMetricC2MaxwellDensityDerivativeAtZero
          period hPeriod metric first second) 0 ∧
      HasFDerivAt
        (regularGeneralMetricC2IntegratedMaxwellPairing
          period hPeriod metric measure first second)
        (regularGeneralMetricC2IntegratedMaxwellPairingDerivativeAtZero
          period hPeriod metric measure first second) 0 :=
  ⟨regularGeneralMetricC2MaxwellDensity_hasFDerivAt_zero
      period hPeriod metric first second,
    regularGeneralMetricC2IntegratedMaxwellPairing_hasFDerivAt_zero
      period hPeriod metric measure first second⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityDerivative4D
end JanusFormal
