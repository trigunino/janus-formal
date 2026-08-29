import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalMetricJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeIntrinsicEinsteinHilbertAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompactParametricIntegralC2

/-!
# Spatial conformal Einstein--Hilbert Hessian

This gate evaluates the four-dimensional conformal Einstein--Hilbert density
on `g(t) = exp(2 t u) g₀`, differentiates it twice under the canonical compact
volume integral, and polarizes the result.  The separate identification of the
conformal curvature formula with the raw coordinate Ricci construction is
proved by the companion curvature and Einstein--Hilbert closure gates.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSpatialConformalEinsteinHilbertHessian4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusGlobalSmoothScalarWave4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusCompactParametricIntegralC2

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

private def referenceCurvature :
    SmoothScalarField period hPeriod :=
  globalSmoothScalarCurvature period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)

def spatialConformalEHDensityCurve
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  (1 / (2 * couplings.gravitationalCoupling)) *
    (Real.exp (2 * parameter * direction point) *
        (referenceCurvature period hPeriod point -
          6 * parameter *
            canonicalGlobalSmoothScalarWave period hPeriod direction point -
          6 * parameter ^ 2 *
            canonicalGlobalScalarGradientPairing
              period hPeriod direction direction point) -
      2 * couplings.cosmologicalConstant *
        Real.exp (4 * parameter * direction point))

def spatialConformalEHFirstDensity
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  let curvature := referenceCurvature period hPeriod point
  let wave := canonicalGlobalSmoothScalarWave period hPeriod direction point
  let gradientSquare :=
    canonicalGlobalScalarGradientPairing period hPeriod direction direction point
  let exponential := Real.exp (2 * parameter * direction point)
  (1 / (2 * couplings.gravitationalCoupling)) *
    (exponential *
        (2 * direction point *
            (curvature - 6 * parameter * wave -
              6 * parameter ^ 2 * gradientSquare) -
          6 * wave - 12 * parameter * gradientSquare) -
      8 * couplings.cosmologicalConstant * direction point *
        Real.exp (4 * parameter * direction point))

def spatialConformalEHSecondDensity
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  let curvature := referenceCurvature period hPeriod point
  let wave := canonicalGlobalSmoothScalarWave period hPeriod direction point
  let gradientSquare :=
    canonicalGlobalScalarGradientPairing period hPeriod direction direction point
  let value := direction point
  (1 / (2 * couplings.gravitationalCoupling)) *
    (Real.exp (2 * parameter * value) *
        (4 * value ^ 2 *
            (curvature - 6 * parameter * wave -
              6 * parameter ^ 2 * gradientSquare) +
          4 * value * (-6 * wave - 12 * parameter * gradientSquare) -
          12 * gradientSquare) -
      32 * couplings.cosmologicalConstant * value ^ 2 *
        Real.exp (4 * parameter * value))

theorem spatialConformalEHDensityCurve_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        spatialConformalEHDensityCurve period hPeriod couplings direction
          varied point)
      (spatialConformalEHFirstDensity period hPeriod couplings direction
        parameter point) parameter := by
  unfold spatialConformalEHDensityCurve spatialConformalEHFirstDensity
  dsimp only
  have hExponential :=
    (((hasDerivAt_const parameter 2).mul (hasDerivAt_id parameter)).mul
      (hasDerivAt_const parameter (direction point))).exp
  have hBracket :=
    ((hasDerivAt_const parameter (referenceCurvature period hPeriod point)).sub
      (((hasDerivAt_const parameter 6).mul (hasDerivAt_id parameter)).mul
        (hasDerivAt_const parameter
          (canonicalGlobalSmoothScalarWave period hPeriod direction point)))).sub
      (((hasDerivAt_const parameter 6).mul ((hasDerivAt_id parameter).pow 2)).mul
        (hasDerivAt_const parameter (canonicalGlobalScalarGradientPairing
          period hPeriod direction direction point)))
  have hCosmological :=
    (((hasDerivAt_const parameter 4).mul (hasDerivAt_id parameter)).mul
      (hasDerivAt_const parameter (direction point))).exp
  have hDerivative :=
    (hasDerivAt_const parameter (1 / (2 * couplings.gravitationalCoupling))).mul
      ((hExponential.mul hBracket).sub
        (((hasDerivAt_const parameter 2).mul
          (hasDerivAt_const parameter couplings.cosmologicalConstant)).mul
            hCosmological))
  refine (hDerivative.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun varied => by
      simp [id_eq]
  · simp [id_eq]
    try ring_nf
    all_goals exact Or.inl trivial

theorem spatialConformalEHFirstDensity_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        spatialConformalEHFirstDensity period hPeriod couplings direction
          varied point)
      (spatialConformalEHSecondDensity period hPeriod couplings direction
        parameter point) parameter := by
  unfold spatialConformalEHFirstDensity spatialConformalEHSecondDensity
  dsimp only
  have hExponential :=
    (((hasDerivAt_const parameter 2).mul (hasDerivAt_id parameter)).mul
      (hasDerivAt_const parameter (direction point))).exp
  have hBracket :=
    ((hasDerivAt_const parameter (referenceCurvature period hPeriod point)).sub
      (((hasDerivAt_const parameter 6).mul (hasDerivAt_id parameter)).mul
        (hasDerivAt_const parameter
          (canonicalGlobalSmoothScalarWave period hPeriod direction point)))).sub
      (((hasDerivAt_const parameter 6).mul ((hasDerivAt_id parameter).pow 2)).mul
        (hasDerivAt_const parameter (canonicalGlobalScalarGradientPairing
          period hPeriod direction direction point)))
  have hInner :=
    ((((hasDerivAt_const parameter 2).mul
      (hasDerivAt_const parameter (direction point))).mul hBracket).sub
      ((hasDerivAt_const parameter 6).mul (hasDerivAt_const parameter
        (canonicalGlobalSmoothScalarWave period hPeriod direction point)))).sub
      (((hasDerivAt_const parameter 12).mul (hasDerivAt_id parameter)).mul
        (hasDerivAt_const parameter (canonicalGlobalScalarGradientPairing
          period hPeriod direction direction point)))
  have hCosmological :=
    (((hasDerivAt_const parameter 4).mul (hasDerivAt_id parameter)).mul
      (hasDerivAt_const parameter (direction point))).exp
  have hDerivative :=
    (hasDerivAt_const parameter (1 / (2 * couplings.gravitationalCoupling))).mul
      ((hExponential.mul hInner).sub
        (((((hasDerivAt_const parameter 8).mul
          (hasDerivAt_const parameter couplings.cosmologicalConstant)).mul
            (hasDerivAt_const parameter (direction point))).mul hCosmological)))
  refine (hDerivative.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun varied => by
      simp [id_eq]
  · simp [id_eq]
    try ring_nf
    all_goals exact Or.inl trivial

def spatialConformalEHActionCurve
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) : Real :=
  ∫ point,
    spatialConformalEHDensityCurve period hPeriod couplings direction
      parameter point
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

def spatialConformalEHActionFirstDerivative
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) : Real :=
  ∫ point,
    spatialConformalEHFirstDensity period hPeriod couplings direction
      parameter point
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

def spatialConformalEHActionSecondDerivative
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) : Real :=
  ∫ point,
    spatialConformalEHSecondDensity period hPeriod couplings direction
      parameter point
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

theorem spatialConformalEHActionCurve_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) :
    HasDerivAt
      (spatialConformalEHActionCurve period hPeriod couplings direction)
      (spatialConformalEHActionFirstDerivative
        period hPeriod couplings direction parameter) parameter := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  apply hasDerivAt_integral_of_jointContinuous_compact
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (spatialConformalEHDensityCurve period hPeriod couplings direction)
    (spatialConformalEHFirstDensity period hPeriod couplings direction)
  · have hSnd : Continuous
        (fun input : Real × EffectiveQuotient period hPeriod => input.2) :=
      continuous_snd
    have hDirection : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        direction input.2) := direction.contMDiff_toFun.continuous.comp hSnd
    have hCurvature : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        referenceCurvature period hPeriod input.2) :=
      (referenceCurvature period hPeriod).contMDiff_toFun.continuous.comp hSnd
    have hWave : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        canonicalGlobalSmoothScalarWave period hPeriod direction input.2) :=
      (canonicalGlobalSmoothScalarWave period hPeriod direction)
        |>.contMDiff_toFun.continuous.comp hSnd
    have hPairing : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        canonicalGlobalScalarGradientPairing period hPeriod direction direction input.2) :=
      (canonicalGlobalScalarGradientPairing period hPeriod direction direction)
        |>.contMDiff_toFun.continuous.comp hSnd
    change Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
      spatialConformalEHDensityCurve period hPeriod couplings direction input.1 input.2)
    unfold spatialConformalEHDensityCurve
    continuity
  · have hSnd : Continuous
        (fun input : Real × EffectiveQuotient period hPeriod => input.2) :=
      continuous_snd
    have hDirection : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        direction input.2) := direction.contMDiff_toFun.continuous.comp hSnd
    have hCurvature : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        referenceCurvature period hPeriod input.2) :=
      (referenceCurvature period hPeriod).contMDiff_toFun.continuous.comp hSnd
    have hWave : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        canonicalGlobalSmoothScalarWave period hPeriod direction input.2) :=
      (canonicalGlobalSmoothScalarWave period hPeriod direction)
        |>.contMDiff_toFun.continuous.comp hSnd
    have hPairing : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        canonicalGlobalScalarGradientPairing period hPeriod direction direction input.2) :=
      (canonicalGlobalScalarGradientPairing period hPeriod direction direction)
        |>.contMDiff_toFun.continuous.comp hSnd
    change Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
      spatialConformalEHFirstDensity period hPeriod couplings direction input.1 input.2)
    unfold spatialConformalEHFirstDensity
    dsimp only [Function.uncurry]
    continuity
  · exact spatialConformalEHDensityCurve_hasDerivAt
      period hPeriod couplings direction

theorem spatialConformalEHActionFirstDerivative_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) :
    HasDerivAt
      (spatialConformalEHActionFirstDerivative
        period hPeriod couplings direction)
      (spatialConformalEHActionSecondDerivative
        period hPeriod couplings direction parameter) parameter := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  apply hasDerivAt_integral_of_jointContinuous_compact
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (spatialConformalEHFirstDensity period hPeriod couplings direction)
    (spatialConformalEHSecondDensity period hPeriod couplings direction)
  · have hSnd : Continuous
        (fun input : Real × EffectiveQuotient period hPeriod => input.2) :=
      continuous_snd
    have hDirection : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        direction input.2) := direction.contMDiff_toFun.continuous.comp hSnd
    have hCurvature : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        referenceCurvature period hPeriod input.2) :=
      (referenceCurvature period hPeriod).contMDiff_toFun.continuous.comp hSnd
    have hWave : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        canonicalGlobalSmoothScalarWave period hPeriod direction input.2) :=
      (canonicalGlobalSmoothScalarWave period hPeriod direction)
        |>.contMDiff_toFun.continuous.comp hSnd
    have hPairing : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        canonicalGlobalScalarGradientPairing period hPeriod direction direction input.2) :=
      (canonicalGlobalScalarGradientPairing period hPeriod direction direction)
        |>.contMDiff_toFun.continuous.comp hSnd
    change Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
      spatialConformalEHFirstDensity period hPeriod couplings direction input.1 input.2)
    unfold spatialConformalEHFirstDensity
    dsimp only [Function.uncurry]
    continuity
  · have hSnd : Continuous
        (fun input : Real × EffectiveQuotient period hPeriod => input.2) :=
      continuous_snd
    have hDirection : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        direction input.2) := direction.contMDiff_toFun.continuous.comp hSnd
    have hCurvature : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        referenceCurvature period hPeriod input.2) :=
      (referenceCurvature period hPeriod).contMDiff_toFun.continuous.comp hSnd
    have hWave : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        canonicalGlobalSmoothScalarWave period hPeriod direction input.2) :=
      (canonicalGlobalSmoothScalarWave period hPeriod direction)
        |>.contMDiff_toFun.continuous.comp hSnd
    have hPairing : Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
        canonicalGlobalScalarGradientPairing period hPeriod direction direction input.2) :=
      (canonicalGlobalScalarGradientPairing period hPeriod direction direction)
        |>.contMDiff_toFun.continuous.comp hSnd
    change Continuous (fun input : Real × EffectiveQuotient period hPeriod =>
      spatialConformalEHSecondDensity period hPeriod couplings direction input.1 input.2)
    unfold spatialConformalEHSecondDensity
    dsimp only [Function.uncurry]
    continuity
  · exact spatialConformalEHFirstDensity_hasDerivAt
      period hPeriod couplings direction

def spatialConformalEHHessianDensity
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  (1 / (2 * couplings.gravitationalCoupling)) *
    ((4 * referenceCurvature period hPeriod point -
        32 * couplings.cosmologicalConstant) *
          first point * second point -
      12 * (first point *
          canonicalGlobalSmoothScalarWave period hPeriod second point +
        second point *
          canonicalGlobalSmoothScalarWave period hPeriod first point) -
      12 * canonicalGlobalScalarGradientPairing
        period hPeriod first second point)

def spatialConformalEHHessian
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothScalarField period hPeriod) : Real :=
  ∫ point,
    spatialConformalEHHessianDensity
      period hPeriod couplings first second point
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

theorem spatialConformalEHHessian_symmetric
    (couplings : EinsteinHilbertCouplings)
    (first second : SmoothScalarField period hPeriod) :
    spatialConformalEHHessian period hPeriod couplings first second =
      spatialConformalEHHessian period hPeriod couplings second first := by
  apply integral_congr_ae
  filter_upwards with point
  unfold spatialConformalEHHessianDensity
  rw [canonicalGlobalScalarGradientPairing_symmetric]
  ring

theorem spatialConformalEHActionSecondDerivative_zero_eq_hessian
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod) :
    spatialConformalEHActionSecondDerivative
        period hPeriod couplings direction 0 =
      spatialConformalEHHessian
        period hPeriod couplings direction direction := by
  apply integral_congr_ae
  filter_upwards with point
  unfold spatialConformalEHSecondDensity spatialConformalEHHessianDensity
  dsimp only
  simp only [Real.exp_zero, zero_mul, one_mul, mul_zero, sub_zero]
  ring

theorem spatialConformalEHActionFirstDerivative_hasSecondDerivAt_zero
    (couplings : EinsteinHilbertCouplings)
    (direction : SmoothScalarField period hPeriod) :
    HasDerivAt
      (spatialConformalEHActionFirstDerivative
        period hPeriod couplings direction)
      (spatialConformalEHHessian
        period hPeriod couplings direction direction) 0 := by
  rw [← spatialConformalEHActionSecondDerivative_zero_eq_hessian]
  exact spatialConformalEHActionFirstDerivative_hasDerivAt
    period hPeriod couplings direction 0

end

end P0EFTJanusMappingTorusSpatialConformalEinsteinHilbertHessian4D
end JanusFormal
