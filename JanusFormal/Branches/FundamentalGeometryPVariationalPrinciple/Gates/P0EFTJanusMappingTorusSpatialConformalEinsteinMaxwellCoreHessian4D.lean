import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalEinsteinHilbertHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D

/-!
# Spatial-conformal Einstein--Maxwell core Hessian

This gate assembles the already proved Einstein--Hilbert Hessian in arbitrary
logarithmic spatial-conformal directions with the frame-free Maxwell Hessian
in arbitrary potential directions.  Four-dimensional conformal invariance
makes both Maxwell blocks containing a conformal metric direction vanish.

The result is a genuine symmetric bilinear form on the restricted product
core.  It is not a Hessian in arbitrary Lorentz-metric directions and does
not introduce a field-space chart or an analytic regularity contract.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSpatialConformalEinsteinMaxwellCoreHessian4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusGlobalSmoothScalarWave4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusFrameFreeMaxwellGaugeOrbitHessian4D
open P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D
open P0EFTJanusMappingTorusSpatialConformalEinsteinHilbertHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

private theorem gradientPairing_add_left
    (first second third : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalGlobalScalarGradientPairing period hPeriod
        (first + second) third point =
      canonicalGlobalScalarGradientPairing period hPeriod first third point +
        canonicalGlobalScalarGradientPairing period hPeriod second third point := by
  have hMul :
      smoothScalarFieldMul period hPeriod (first + second) third =
        smoothScalarFieldMul period hPeriod first third +
          smoothScalarFieldMul period hPeriod second third := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro input
    change (first input + second input) * third input =
      first input * third input + second input * third input
    ring
  have hWaveMul :
      canonicalGlobalSmoothScalarWave period hPeriod
          (smoothScalarFieldMul period hPeriod (first + second) third) point =
        canonicalGlobalSmoothScalarWave period hPeriod
            (smoothScalarFieldMul period hPeriod first third) point +
          canonicalGlobalSmoothScalarWave period hPeriod
            (smoothScalarFieldMul period hPeriod second third) point := by
    rw [hMul, canonicalGlobalSmoothScalarWave_add]
    rfl
  have hWaveAdd :
      canonicalGlobalSmoothScalarWave period hPeriod (first + second) point =
        canonicalGlobalSmoothScalarWave period hPeriod first point +
          canonicalGlobalSmoothScalarWave period hPeriod second point := by
    rw [canonicalGlobalSmoothScalarWave_add]
    rfl
  unfold canonicalGlobalScalarGradientPairing
  change
    (2 : Real)⁻¹ *
        (canonicalGlobalSmoothScalarWave period hPeriod
              (smoothScalarFieldMul period hPeriod (first + second) third) point -
          (first point + second point) *
            canonicalGlobalSmoothScalarWave period hPeriod third point -
          third point * canonicalGlobalSmoothScalarWave period hPeriod
            (first + second) point) = _
  rw [hWaveMul, hWaveAdd]
  ring

private theorem gradientPairing_smul_left
    (scalar : Real)
    (first second : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalGlobalScalarGradientPairing period hPeriod
        (scalar • first) second point =
      scalar * canonicalGlobalScalarGradientPairing
        period hPeriod first second point := by
  have hMul :
      smoothScalarFieldMul period hPeriod (scalar • first) second =
        scalar • smoothScalarFieldMul period hPeriod first second := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro input
    change (scalar * first input) * second input =
      scalar * (first input * second input)
    ring
  have hWaveMul :
      canonicalGlobalSmoothScalarWave period hPeriod
          (smoothScalarFieldMul period hPeriod (scalar • first) second) point =
        scalar * canonicalGlobalSmoothScalarWave period hPeriod
          (smoothScalarFieldMul period hPeriod first second) point := by
    rw [hMul, canonicalGlobalSmoothScalarWave_smul]
    rfl
  have hWaveSmul :
      canonicalGlobalSmoothScalarWave period hPeriod (scalar • first) point =
        scalar * canonicalGlobalSmoothScalarWave period hPeriod first point := by
    rw [canonicalGlobalSmoothScalarWave_smul]
    rfl
  unfold canonicalGlobalScalarGradientPairing
  change
    (2 : Real)⁻¹ *
        (canonicalGlobalSmoothScalarWave period hPeriod
              (smoothScalarFieldMul period hPeriod (scalar • first) second) point -
          scalar * first point *
            canonicalGlobalSmoothScalarWave period hPeriod second point -
          second point * canonicalGlobalSmoothScalarWave period hPeriod
            (scalar • first) point) = _
  rw [hWaveMul, hWaveSmul]
  ring

private theorem spatialConformalEHHessianDensity_integrable
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothScalarField period hPeriod) :
    Integrable
      (spatialConformalEHHessianDensity period hPeriod couplings first second)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  letI := intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  have hContinuous : Continuous
      (spatialConformalEHHessianDensity period hPeriod couplings first second) := by
    have hCurvature :=
      (globalSmoothScalarCurvature period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod))
        |>.contMDiff_toFun.continuous
    have hWaveFirst :=
      (canonicalGlobalSmoothScalarWave period hPeriod first)
        |>.contMDiff_toFun.continuous
    have hWaveSecond :=
      (canonicalGlobalSmoothScalarWave period hPeriod second)
        |>.contMDiff_toFun.continuous
    have hPairing :=
      (canonicalGlobalScalarGradientPairing period hPeriod first second)
        |>.contMDiff_toFun.continuous
    have hFirst := first.contMDiff_toFun.continuous
    have hSecond := second.contMDiff_toFun.continuous
    unfold spatialConformalEHHessianDensity
    continuity
  exact hContinuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem spatialConformalEHHessian_add_left
    (couplings : EinsteinHilbertCouplings)
    (first second third : SmoothScalarField period hPeriod) :
    spatialConformalEHHessian period hPeriod couplings (first + second) third =
      spatialConformalEHHessian period hPeriod couplings first third +
        spatialConformalEHHessian period hPeriod couplings second third := by
  unfold spatialConformalEHHessian
  rw [show
    spatialConformalEHHessianDensity period hPeriod couplings
        (first + second) third =
      fun point =>
        spatialConformalEHHessianDensity period hPeriod couplings first third point +
          spatialConformalEHHessianDensity period hPeriod couplings second third point by
    funext point
    unfold spatialConformalEHHessianDensity
    rw [canonicalGlobalSmoothScalarWave_add,
      gradientPairing_add_left period hPeriod]
    change
      (1 / (2 * couplings.gravitationalCoupling)) *
          ((4 * _ - 32 * couplings.cosmologicalConstant) *
              (first point + second point) * third point -
            12 * ((first point + second point) * _ +
              third point * (_ + _)) -
            12 * (_ + _)) = _
    ring]
  exact integral_add
    (spatialConformalEHHessianDensity_integrable
      period hPeriod couplings first third)
    (spatialConformalEHHessianDensity_integrable
      period hPeriod couplings second third)

private theorem spatialConformalEHHessian_smul_left
    (couplings : EinsteinHilbertCouplings)
    (scalar : Real)
    (first second : SmoothScalarField period hPeriod) :
    spatialConformalEHHessian period hPeriod couplings (scalar • first) second =
      scalar * spatialConformalEHHessian period hPeriod couplings first second := by
  unfold spatialConformalEHHessian
  rw [show
    spatialConformalEHHessianDensity period hPeriod couplings
        (scalar • first) second =
      fun point => scalar *
        spatialConformalEHHessianDensity period hPeriod couplings first second point by
    funext point
    unfold spatialConformalEHHessianDensity
    rw [canonicalGlobalSmoothScalarWave_smul,
      gradientPairing_smul_left period hPeriod]
    change
      (1 / (2 * couplings.gravitationalCoupling)) *
          ((4 * _ - 32 * couplings.cosmologicalConstant) *
              (scalar * first point) * second point -
            12 * (scalar * first point * _ +
              second point * (scalar * _)) -
            12 * (scalar * _)) =
        scalar * _
    ring]
  rw [integral_const_mul]

/-- The existing spatial-conformal Einstein--Hilbert Hessian, now packaged
as an actual bilinear form. -/
def spatialConformalEHHessianBilinForm
    (couplings : EinsteinHilbertCouplings) :
    LinearMap.BilinForm Real (SmoothScalarField period hPeriod) :=
  LinearMap.mk₂ Real
    (spatialConformalEHHessian period hPeriod couplings)
    (spatialConformalEHHessian_add_left period hPeriod couplings)
    (fun scalar first second => by
      simpa only [smul_eq_mul] using
        spatialConformalEHHessian_smul_left period hPeriod couplings
          scalar first second)
    (fun first second third => by
      rw [spatialConformalEHHessian_symmetric period hPeriod couplings
          first (second + third),
        spatialConformalEHHessian_add_left period hPeriod couplings,
        spatialConformalEHHessian_symmetric period hPeriod couplings second first,
        spatialConformalEHHessian_symmetric period hPeriod couplings third first])
    (fun scalar first second => by
      rw [spatialConformalEHHessian_symmetric period hPeriod couplings
          first (scalar • second),
        spatialConformalEHHessian_smul_left period hPeriod couplings,
        spatialConformalEHHessian_symmetric period hPeriod couplings second first]
      simp only [smul_eq_mul])

@[simp]
theorem spatialConformalEHHessianBilinForm_apply
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothScalarField period hPeriod) :
    spatialConformalEHHessianBilinForm period hPeriod couplings first second =
      spatialConformalEHHessian period hPeriod couplings first second :=
  rfl

/-- Tangent core consisting of a logarithmic spatial-conformal metric
direction and an arbitrary Abelian potential direction. -/
abbrev SpatialConformalEinsteinMaxwellDirection :=
  SmoothScalarField period hPeriod × SmoothAbelianGaugePotential period hPeriod

/-- Exact block Hessian on the spatial-conformal Einstein--Maxwell core. -/
def spatialConformalEinsteinMaxwellCoreHessian
    (couplings : EinsteinHilbertCouplings)
    (_potential : SmoothAbelianGaugePotential period hPeriod) :
    LinearMap.BilinForm Real
      (SpatialConformalEinsteinMaxwellDirection period hPeriod) :=
  LinearMap.mk₂ Real
    (fun first second =>
      spatialConformalEHHessianBilinForm period hPeriod couplings
          first.1 second.1 +
        frameFreeMaxwellPotentialHessian period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          first.2 second.2)
    (by
      intros
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      abel)
    (by intros; simp [mul_add])
    (by
      intros
      simp only [Prod.fst_add, Prod.snd_add, map_add]
      abel)
    (by intros; simp [mul_add])

@[simp]
theorem spatialConformalEinsteinMaxwellCoreHessian_apply
    (couplings : EinsteinHilbertCouplings)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : SpatialConformalEinsteinMaxwellDirection period hPeriod) :
    spatialConformalEinsteinMaxwellCoreHessian period hPeriod couplings potential
        first second =
      spatialConformalEHHessian period hPeriod couplings first.1 second.1 +
        frameFreeMaxwellPotentialHessian period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          first.2 second.2 :=
  rfl

theorem spatialConformalEinsteinMaxwellCoreHessian_symmetric
    (couplings : EinsteinHilbertCouplings)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : SpatialConformalEinsteinMaxwellDirection period hPeriod) :
    spatialConformalEinsteinMaxwellCoreHessian period hPeriod couplings potential
        first second =
      spatialConformalEinsteinMaxwellCoreHessian period hPeriod couplings potential
        second first := by
  rw [spatialConformalEinsteinMaxwellCoreHessian_apply,
    spatialConformalEinsteinMaxwellCoreHessian_apply,
    spatialConformalEHHessian_symmetric,
    frameFreeMaxwellPotentialHessian_symmetric]

/-- The cross block is the already proved same-action logarithmic-conformal
Maxwell mixed Hessian. -/
theorem spatialConformalEinsteinMaxwellCoreHessian_metric_potential_eq_mixed
    (couplings : EinsteinHilbertCouplings)
    (potential direction : SmoothAbelianGaugePotential period hPeriod)
    (conformalDirection : SmoothScalarField period hPeriod) :
    spatialConformalEinsteinMaxwellCoreHessian period hPeriod couplings potential
        (conformalDirection, 0) (0, direction) =
      conformalPotentialFrameFreeMaxwellMixedHessian period hPeriod potential
        conformalDirection direction := by
  rw [conformalPotentialFrameFreeMaxwellMixedHessian_eq_zero]
  change
    spatialConformalEHHessianBilinForm period hPeriod couplings
        conformalDirection 0 +
      frameFreeMaxwellPotentialHessian period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) 0 direction = 0
  simp only [map_zero, LinearMap.zero_apply, zero_add]

@[simp]
theorem spatialConformalEinsteinMaxwellCoreHessian_metric_potential
    (couplings : EinsteinHilbertCouplings)
    (potential direction : SmoothAbelianGaugePotential period hPeriod)
    (conformalDirection : SmoothScalarField period hPeriod) :
    spatialConformalEinsteinMaxwellCoreHessian period hPeriod couplings potential
        (conformalDirection, 0) (0, direction) = 0 := by
  rw [spatialConformalEinsteinMaxwellCoreHessian_metric_potential_eq_mixed,
    conformalPotentialFrameFreeMaxwellMixedHessian_eq_zero]

end

end P0EFTJanusMappingTorusSpatialConformalEinsteinMaxwellCoreHessian4D
end JanusFormal
