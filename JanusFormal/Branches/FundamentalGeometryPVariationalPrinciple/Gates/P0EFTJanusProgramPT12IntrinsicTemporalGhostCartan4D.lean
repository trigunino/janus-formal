import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicTemporalGradient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowRadialGenerator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGhostCEClosure4D
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! A genuine periodic non-Killing ghost for the intrinsic Lorentz metric.
This identifies a metric direction produced by BRST from a pure ghost; it
does not rule out reductions that also retain or quotient metric directions. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalGhostCartan4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalVolumePreservingFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowRadialGenerator4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusScalarGhostCEClosure4D
open P0EFTJanusMappingTorusMetricCartanFiberCore4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPT12IntrinsicTemporalGradient4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Cover := MappingTorusCover (reflectedSphereData period hPeriod)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Ambient := ModelProd EuclideanR4 Real
local instance : NormedAddCommGroup Ambient := inferInstanceAs (NormedAddCommGroup (EuclideanR4 × Real))
local instance : NormedSpace Real Ambient := inferInstanceAs (NormedSpace Real (EuclideanR4 × Real))
local instance : ChartedSpace CoverModel (Cover period hPeriod) := reflectedSphereCoverChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Cover period hPeriod) := reflectedSphereCover_isManifold period hPeriod
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod

/-- The actual generator of time translation on the reflected quotient. -/
def intrinsicTimeVector : CInfinityDiffeomorphismGhost period hPeriod where
  toFun := canonicalFlowGenerator period hPeriod (canonicalTimeVolumePreservingFlow period hPeriod)
  contMDiff_toFun := canonicalFlowGenerator_contMDiff period hPeriod
    (canonicalTimeVolumePreservingFlow period hPeriod)

private theorem timeFlow_ambient_derivative (point : Cover period hPeriod) :
    coverAmbientDerivative period hPeriod point
      (canonicalCoverFlowValue period hPeriod .time point) = (0, 1) := by
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := coverModelWithCorners) (I'' := 𝓘(Real, Ambient))
    (f := canonicalCoverFlowCurve period hPeriod .time point)
    (g := coverAmbientMap period hPeriod) (x := (0 : Real)) (y := point)
    ((coverAmbientMap_contMDiff period hPeriod).mdifferentiableAt (by simp))
    ((canonicalCoverFlowCurve_contMDiff period hPeriod .time point).mdifferentiableAt (by simp))
    (canonicalCoverFlow_zero period hPeriod .time point) (1 : Real)
  have hMap : coverAmbientMap period hPeriod ∘ canonicalCoverFlowCurve period hPeriod .time point =
      fun parameter : Real => (sphereAmbientMap point.fiber, point.time + parameter) := rfl
  have hDerivative : HasDerivAt
      (fun parameter : Real => (sphereAmbientMap point.fiber, point.time + parameter))
      (0, 1) 0 :=
    (hasDerivAt_const 0 (sphereAmbientMap point.fiber)).prodMk
      ((hasDerivAt_id 0).const_add point.time)
  change mfderiv coverModelWithCorners 𝓘(Real, Ambient) (coverAmbientMap period hPeriod) point
    (canonicalCoverFlowValue period hPeriod .time point) = _
  calc
    _ = mfderiv 𝓘(Real, Real) 𝓘(Real, Ambient)
        (coverAmbientMap period hPeriod ∘ canonicalCoverFlowCurve period hPeriod .time point) 0 1 := hComp.symm
    _ = _ := by
      rw [hMap, mfderiv_eq_fderiv]
      exact hDerivative.deriv

theorem intrinsicTimeVector_metric (point : Q period hPeriod) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point
      (intrinsicTimeVector period hPeriod point) (intrinsicTimeVector period hPeriod point) = -1 := by
  obtain ⟨point, rfl⟩ := mappingTorusMk_surjective (reflectedSphereData period hPeriod) point
  have hVelocity := canonicalProjectionDerivativeEquiv_flowValue period hPeriod .time point
  change intrinsicQuotientTensorField period hPeriod (mappingTorusMk (reflectedSphereData period hPeriod) point)
    (canonicalFlowGenerator period hPeriod (canonicalVolumePreservingFlow period hPeriod .time) _)
    (canonicalFlowGenerator period hPeriod (canonicalVolumePreservingFlow period hPeriod .time) _) = -1
  rw [← hVelocity]
  change intrinsicQuotientTensorField period hPeriod (mappingTorusMk (reflectedSphereData period hPeriod) point)
    (mfderiv coverModelWithCorners coverModelWithCorners (mappingTorusMk (reflectedSphereData period hPeriod)) point
      (canonicalCoverFlowValue period hPeriod .time point))
    (mfderiv coverModelWithCorners coverModelWithCorners (mappingTorusMk (reflectedSphereData period hPeriod)) point
      (canonicalCoverFlowValue period hPeriod .time point)) = -1
  rw [intrinsicQuotientTensorField_pullback, intrinsicCoverLorentzTensor_apply,
    timeFlow_ambient_derivative]
  norm_num

def periodicTemporalDiffeomorphismGhost (profile : Real → Real)
    (hSmooth : ContDiff Real ∞ profile) (hPeriodic : Function.Periodic profile period) :
    GlobalDiffeomorphismGhostField period hPeriod :=
  ⟨cInfinityScalarSmulGhost period hPeriod
    (analyticScalarToCInfinity period hPeriod (periodicTemporalScalar period hPeriod profile hSmooth hPeriodic))
    (intrinsicTimeVector period hPeriod)⟩

theorem intrinsicTimeVector_periodicTemporalScalar (profile : Real → Real)
    (hSmooth : ContDiff Real ∞ profile) (hPeriodic : Function.Periodic profile period)
    (point : Cover period hPeriod) :
    scalarDifferential period hPeriod (periodicTemporalScalar period hPeriod profile hSmooth hPeriodic)
      (mappingTorusMk (reflectedSphereData period hPeriod) point)
      (intrinsicTimeVector period hPeriod (mappingTorusMk (reflectedSphereData period hPeriod) point)) =
      deriv profile point.time := by
  have hFlow := smoothQuotientField_flow_hasDerivAt_zero period hPeriod Real
    (canonicalTimeVolumePreservingFlow period hPeriod)
    (periodicTemporalScalar period hPeriod profile hSmooth hPeriodic)
    (mappingTorusMk (reflectedSphereData period hPeriod) point)
  have hFunction : (fun parameter : Real =>
      periodicTemporalScalar period hPeriod profile hSmooth hPeriodic
        ((canonicalTimeVolumePreservingFlow period hPeriod).flow parameter
          (mappingTorusMk (reflectedSphereData period hPeriod) point))) =
      fun parameter : Real => profile (point.time + parameter) := by
    funext parameter
    change periodicTemporalScalar period hPeriod profile hSmooth hPeriodic
      (effectiveTimeFlow period hPeriod parameter (mappingTorusMk (reflectedSphereData period hPeriod) point)) = _
    rw [effectiveTimeFlow_mk]
    rfl
  rw [hFunction] at hFlow
  have hProfile : HasDerivAt (fun parameter : Real => profile (point.time + parameter))
      (deriv profile point.time) 0 := by
    have hOuter : HasDerivAt profile (deriv profile point.time) (point.time + (0 : Real)) := by
      simpa only [add_zero] using (hSmooth.differentiable (by simp) point.time).hasDerivAt
    have hInner : HasDerivAt (fun parameter : Real => point.time + parameter) 1 0 :=
      (hasDerivAt_id 0).const_add point.time
    simpa only [Function.comp_def, mul_one] using hOuter.comp 0 hInner
  exact hFlow.unique hProfile

theorem periodicTemporalDiffeomorphismGhost_cartan_time (profile : Real → Real)
    (hSmooth : ContDiff Real ∞ profile) (hPeriodic : Function.Periodic profile period)
    (point : Cover period hPeriod) :
    (smoothMetricCartanAction period hPeriod
      (periodicTemporalDiffeomorphismGhost period hPeriod profile hSmooth hPeriodic).field
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor).tensor
      (mappingTorusMk (reflectedSphereData period hPeriod) point)
      (intrinsicTimeVector period hPeriod (mappingTorusMk (reflectedSphereData period hPeriod) point))
      (intrinsicTimeVector period hPeriod (mappingTorusMk (reflectedSphereData period hPeriod) point)) =
      -2 * deriv profile point.time := by
  let scalar := periodicTemporalScalar period hPeriod profile hSmooth hPeriodic
  let time := intrinsicTimeVector period hPeriod
  let location := mappingTorusMk (reflectedSphereData period hPeriod) point
  have hBracket : VectorField.mlieBracket coverModelWithCorners
      (periodicTemporalDiffeomorphismGhost period hPeriod profile hSmooth hPeriodic).field time location =
      (-deriv profile point.time) • time location := by
    have h := VectorField.mlieBracket_smul_left (I := coverModelWithCorners)
      (V := time) (W := time) (f := scalar) (x := location)
      (scalar.contMDiff_toFun.mdifferentiableAt (by simp))
      (time.contMDiff.mdifferentiableAt (by simp))
    simp only [VectorField.mlieBracket_self, Pi.zero_apply, smul_zero, add_zero] at h
    change VectorField.mlieBracket coverModelWithCorners
      (periodicTemporalDiffeomorphismGhost period hPeriod profile hSmooth hPeriodic).field time location =
      (-scalarDifferential period hPeriod scalar location (time location)) • time location at h
    exact h.trans (congrArg (fun value : Real => (-value) • time location)
      (intrinsicTimeVector_periodicTemporalScalar period hPeriod profile hSmooth hPeriodic point))
  have hMetric : (fun current : Q period hPeriod =>
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor current (time current) (time current)) =
      fun _ => (-1 : Real) := funext (intrinsicTimeVector_metric period hPeriod)
  rw [smoothMetricCartanAction_apply]
  unfold metricCartanResidualAt
  rw [hMetric, mvfderiv_const]
  change 0 - (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor location
      (VectorField.mlieBracket coverModelWithCorners
        (periodicTemporalDiffeomorphismGhost period hPeriod profile hSmooth hPeriodic).field time location) (time location) -
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor location (time location)
      (VectorField.mlieBracket coverModelWithCorners
        (periodicTemporalDiffeomorphismGhost period hPeriod profile hSmooth hPeriodic).field time location) = _
  rw [hBracket]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [congrFun hMetric location]
  ring

def intrinsicTemporalSineProfile (time : Real) : Real := Real.sin ((2 * Real.pi / period) * time)

theorem intrinsicTemporalSineProfile_contDiff : ContDiff Real ∞ (intrinsicTemporalSineProfile period) :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

include hPeriod in
theorem intrinsicTemporalSineProfile_periodic : Function.Periodic (intrinsicTemporalSineProfile period) period := by
  intro time
  unfold intrinsicTemporalSineProfile
  rw [mul_add, div_mul_cancel₀ _ hPeriod]
  exact Real.sin_add_two_pi _

theorem intrinsicTemporalSineProfile_deriv_zero : deriv (intrinsicTemporalSineProfile period) 0 = 2 * Real.pi / period := by
  change deriv (fun time : Real => Real.sin ((2 * Real.pi / period) * time)) 0 = 2 * Real.pi / period
  simpa only [id_eq, mul_zero, Real.cos_zero, one_mul, mul_one] using
    (((hasDerivAt_id 0).const_mul (2 * Real.pi / period)).sin).deriv

def intrinsicTemporalSineGhost : GlobalDiffeomorphismGhostField period hPeriod :=
  periodicTemporalDiffeomorphismGhost period hPeriod (intrinsicTemporalSineProfile period)
    (intrinsicTemporalSineProfile_contDiff period) (intrinsicTemporalSineProfile_periodic period hPeriod)

theorem intrinsicTemporalSineGhost_cartan_ne_zero :
    smoothMetricCartanAction period hPeriod (intrinsicTemporalSineGhost period hPeriod).field
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor ≠ 0 := by
  let fiber : UnitThreeSphere := ⟨fun index => if index = 0 then 1 else 0, by
    norm_num [OnUnitThreeSphere, radiusSquared, Fin.sum_univ_four]⟩
  let point : Cover period hPeriod := ⟨fiber, 0⟩
  intro hZero
  have hValue := periodicTemporalDiffeomorphismGhost_cartan_time period hPeriod
    (intrinsicTemporalSineProfile period) (intrinsicTemporalSineProfile_contDiff period)
    (intrinsicTemporalSineProfile_periodic period hPeriod) point
  change (smoothMetricCartanAction period hPeriod (intrinsicTemporalSineGhost period hPeriod).field
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor).tensor _ _ _ = _ at hValue
  rw [hZero] at hValue
  change 0 = -2 * deriv (intrinsicTemporalSineProfile period) 0 at hValue
  rw [intrinsicTemporalSineProfile_deriv_zero] at hValue
  exact (mul_ne_zero (by norm_num : (-2 : Real) ≠ 0)
    (div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hPeriod)) hValue.symm

theorem intrinsicTemporalSineGhost_generator_ne_zero :
    globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) (intrinsicTemporalSineGhost period hPeriod) ≠ 0 :=
  intrinsicTemporalSineGhost_cartan_ne_zero period hPeriod

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalGhostCartan4D
