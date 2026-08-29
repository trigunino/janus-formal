import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalMetricJet4D

/-!
# Spatial conformal exponential specialization

Independent linearity lemmas used when the logarithmic conformal factor is a
constant multiple of a smooth scalar direction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSpatialConformalExponentialBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarWave4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSpatialConformalMetricJet4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev ScalarIndex4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The positive conformal scale `s_t = exp (2 t u)`. -/
def spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) : SmoothScalarField period hPeriod where
  toFun := fun point =>
    Real.exp (2 * parameter * direction point)
  contMDiff_toFun :=
    Real.contDiff_exp.contMDiff.comp
      (contMDiff_const.mul direction.contMDiff_toFun)

@[simp]
theorem spatialConformalExponentialScale_apply
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) (point) :
    spatialConformalExponentialScale
        period hPeriod direction parameter point =
      Real.exp (2 * parameter * direction point) :=
  rfl

theorem spatialConformalExponentialScale_pos
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real) (point) :
    0 < spatialConformalExponentialScale
      period hPeriod direction parameter point :=
  Real.exp_pos _

@[simp]
theorem localScalarRepresentative_spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarRepresentative period hPeriod
        (spatialConformalExponentialScale
          period hPeriod direction parameter) patch coordinate =
      Real.exp (2 * parameter *
        localScalarRepresentative
          period hPeriod direction patch coordinate) :=
  rfl

theorem localScalarGradient_spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (index : ScalarIndex4) :
    localScalarGradient period hPeriod
        (spatialConformalExponentialScale
          period hPeriod direction parameter) patch coordinate index =
      2 * parameter *
        localScalarRepresentative period hPeriod
          (spatialConformalExponentialScale
            period hPeriod direction parameter) patch coordinate *
        localScalarGradient period hPeriod
          direction patch coordinate index := by
  have hDirection : DifferentiableAt Real
      (localScalarRepresentative period hPeriod direction patch) coordinate :=
    ((localScalarRepresentative_contDiff
      period hPeriod direction patch).differentiable (by simp)).differentiableAt
  have hInner : DifferentiableAt Real
      (fun current =>
        (2 * parameter) *
          localScalarRepresentative period hPeriod direction patch current)
      coordinate :=
    hDirection.const_mul _
  unfold localScalarGradient
  change
    (fderiv Real
      (fun current =>
        Real.exp ((2 * parameter) *
          localScalarRepresentative period hPeriod direction patch current))
      coordinate) _ =
    2 * parameter *
      Real.exp (2 * parameter *
        localScalarRepresentative period hPeriod direction patch coordinate) *
      (fderiv Real
        (localScalarRepresentative period hPeriod direction patch)
        coordinate) _
  rw [fderiv_exp hInner, fderiv_const_mul hDirection]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem localConformalLogGradient_spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (index : ScalarIndex4) :
    localConformalLogGradient period hPeriod
        (spatialConformalExponentialScale
          period hPeriod direction parameter) patch coordinate index =
      parameter *
        localScalarGradient period hPeriod
          direction patch coordinate index := by
  unfold localConformalLogGradient
  rw [localScalarGradient_spatialConformalExponentialScale,
    localScalarRepresentative_spatialConformalExponentialScale]
  have hExponential :
      Real.exp (2 * parameter *
        localScalarRepresentative
          period hPeriod direction patch coordinate) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  field_simp [hExponential]

theorem localConformalRaisedLogGradient_spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper : ScalarIndex4) :
    localConformalRaisedLogGradient period hPeriod
        (spatialConformalExponentialScale
          period hPeriod direction parameter) patch coordinate upper =
      parameter *
        localSmoothScalarRaisedGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch direction coordinate upper := by
  unfold localConformalRaisedLogGradient localSmoothScalarRaisedGradient
    covariantScalarJetRaisedGradient localFixedSignMetric
    localCovariantScalarJet coordinateScalarJetNormalForm
    localCoordinateScalarJet Matrix.mulVec dotProduct
  simp_rw [localConformalLogGradient_spatialConformalExponentialScale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro contracted _
  ring

private theorem smoothScalarFieldMul_smul_smul
    (firstScalar secondScalar : Real)
    (first second : SmoothScalarField period hPeriod) :
    smoothScalarFieldMul period hPeriod
        (firstScalar • first) (secondScalar • second) =
      (firstScalar * secondScalar) •
        smoothScalarFieldMul period hPeriod first second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [smoothScalarFieldMul_apply, smoothQuotientField_smul_apply,
    smul_eq_mul]
  ring

@[simp]
theorem canonicalGlobalSmoothScalarWave_smul_apply
    (scalar : Real)
    (field : SmoothScalarField period hPeriod)
    (point) :
    canonicalGlobalSmoothScalarWave period hPeriod (scalar • field) point =
      scalar *
        canonicalGlobalSmoothScalarWave period hPeriod field point := by
  rw [canonicalGlobalSmoothScalarWave_smul]
  rfl

theorem canonicalGlobalScalarGradientPairing_smul_smul
    (firstScalar secondScalar : Real)
    (first second : SmoothScalarField period hPeriod) :
    canonicalGlobalScalarGradientPairing period hPeriod
        (firstScalar • first) (secondScalar • second) =
      (firstScalar * secondScalar) •
        canonicalGlobalScalarGradientPairing period hPeriod first second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hProductWave :
      canonicalGlobalSmoothScalarWave period hPeriod
          (smoothScalarFieldMul period hPeriod
            (firstScalar • first) (secondScalar • second)) point =
        (firstScalar * secondScalar) *
          canonicalGlobalSmoothScalarWave period hPeriod
            (smoothScalarFieldMul period hPeriod first second) point := by
    rw [smoothScalarFieldMul_smul_smul,
      canonicalGlobalSmoothScalarWave_smul_apply]
  change (2 : Real)⁻¹ *
      (canonicalGlobalSmoothScalarWave period hPeriod
            (smoothScalarFieldMul period hPeriod
              (firstScalar • first) (secondScalar • second)) point -
        firstScalar * first point *
          canonicalGlobalSmoothScalarWave period hPeriod
            (secondScalar • second) point -
        secondScalar * second point *
          canonicalGlobalSmoothScalarWave period hPeriod
            (firstScalar • first) point) =
    (firstScalar * secondScalar) * ((2 : Real)⁻¹ *
      (canonicalGlobalSmoothScalarWave period hPeriod
            (smoothScalarFieldMul period hPeriod first second) point -
        first point *
          canonicalGlobalSmoothScalarWave period hPeriod second point -
        second point *
          canonicalGlobalSmoothScalarWave period hPeriod first point))
  rw [hProductWave, canonicalGlobalSmoothScalarWave_smul_apply,
    canonicalGlobalSmoothScalarWave_smul_apply]
  ring

@[simp]
theorem canonicalGlobalScalarGradientPairing_smul_smul_apply
    (firstScalar secondScalar : Real)
    (first second : SmoothScalarField period hPeriod)
    (point) :
    canonicalGlobalScalarGradientPairing period hPeriod
        (firstScalar • first) (secondScalar • second) point =
      (firstScalar * secondScalar) *
        canonicalGlobalScalarGradientPairing period hPeriod first second point := by
  rw [canonicalGlobalScalarGradientPairing_smul_smul]
  rfl

@[simp]
theorem canonicalGlobalScalarGradientPairing_smul_self_apply
    (scalar : Real)
    (field : SmoothScalarField period hPeriod)
    (point) :
    canonicalGlobalScalarGradientPairing period hPeriod
        (scalar • field) (scalar • field) point =
      scalar ^ 2 *
        canonicalGlobalScalarGradientPairing period hPeriod field field point := by
  rw [canonicalGlobalScalarGradientPairing_smul_smul_apply]
  ring

end

end P0EFTJanusMappingTorusSpatialConformalExponentialBridge4D
end JanusFormal
