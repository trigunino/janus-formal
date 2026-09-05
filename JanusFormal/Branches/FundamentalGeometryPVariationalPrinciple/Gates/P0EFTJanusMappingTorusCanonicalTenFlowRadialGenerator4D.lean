import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowEuclideanSpan4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostBracketNaturality4D

/-! # Radial coordinates for the ten canonical flow generators -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowRadialGenerator4D

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set Bundle
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusJointAnalyticTimeAction4D
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D
open P0EFTJanusMappingTorusD8NonabelianGhostBracketNaturality4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationQuotient4D
open P0EFTJanusMappingTorusCanonicalSpatialRotationQuotient4D
open P0EFTJanusMappingTorusCanonicalVolumePreservingFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowEuclideanSpan4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Uniform lift of the ten quotient flows to the sphere-times-real cover. -/
def canonicalCoverFlow (index : CanonicalFlowIndex)
    (input : Real × EffectiveCover period hPeriod) :
    EffectiveCover period hPeriod :=
  match index with
  | .time => coverTimeTranslation (sphereData period hPeriod) input.1 input.2
  | .spatial axis =>
      coverSpatialRotationFlow period hPeriod axis input
  | .phasedNormal axis phase =>
      coverPhasedNormalRotationFlow period hPeriod axis phase input

theorem canonicalCoverFlow_contMDiff (index : CanonicalFlowIndex) :
    ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞ (canonicalCoverFlow period hPeriod index) := by
  cases index with
  | time =>
      change ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
        coverModelWithCorners ∞
        (fun input : Real × EffectiveCover period hPeriod => coverTimeTranslation
          (sphereData period hPeriod) input.1 input.2)
      convert (effectiveCoverJointTimeTranslation_contMDiff period hPeriod).of_le
        (by simp) using 1
  | spatial axis =>
      exact coverSpatialRotationFlow_contMDiff period hPeriod axis
  | phasedNormal axis phase =>
      exact coverPhasedNormalRotationFlow_contMDiff period hPeriod axis phase

@[simp]
theorem canonicalCoverFlow_zero (index : CanonicalFlowIndex)
    (point : EffectiveCover period hPeriod) :
    canonicalCoverFlow period hPeriod index (0, point) = point := by
  cases index with
  | time =>
      change coverTimeTranslation (sphereData period hPeriod) 0 point = point
      exact coverTimeTranslation_zero (sphereData period hPeriod) point
  | spatial axis => exact coverSpatialRotationFlow_zero period hPeriod axis point
  | phasedNormal axis phase =>
      exact coverPhasedNormalRotationFlow_zero period hPeriod axis phase point

theorem canonicalCoverFlow_projection (index : CanonicalFlowIndex)
    (parameter : Real) (point : EffectiveCover period hPeriod) :
    (canonicalVolumePreservingFlow period hPeriod index).flow parameter
        (mappingTorusMk (sphereData period hPeriod) point) =
      mappingTorusMk (sphereData period hPeriod)
        (canonicalCoverFlow period hPeriod index (parameter, point)) := by
  cases index with
  | time => exact effectiveTimeFlow_mk period hPeriod parameter point
  | spatial axis => exact spatialRotationFlow_mk period hPeriod axis parameter point
  | phasedNormal axis phase =>
      exact phasedNormalRotationFlow_mk period hPeriod axis phase parameter point

/-- Orbit curve of one lifted canonical flow. -/
def canonicalCoverFlowCurve (index : CanonicalFlowIndex)
    (point : EffectiveCover period hPeriod) (parameter : Real) :
    EffectiveCover period hPeriod :=
  canonicalCoverFlow period hPeriod index (parameter, point)

theorem canonicalCoverFlowCurve_contMDiff (index : CanonicalFlowIndex)
    (point : EffectiveCover period hPeriod) :
    ContMDiff 𝓘(Real, Real) coverModelWithCorners ∞
      (canonicalCoverFlowCurve period hPeriod index point) :=
  (canonicalCoverFlow_contMDiff period hPeriod index).comp
    (contMDiff_id.prodMk contMDiff_const)

/-- Tangent velocity of one lifted canonical flow. -/
def canonicalCoverFlowValue (index : CanonicalFlowIndex)
    (point : EffectiveCover period hPeriod) :
    TangentSpace coverModelWithCorners point :=
  mfderiv 𝓘(Real, Real) coverModelWithCorners
    (canonicalCoverFlowCurve period hPeriod index point) 0 1

/-- Differential of the quotient projection at a chosen cover anchor. -/
def canonicalProjectionDerivativeEquiv
    (point : EffectiveCover period hPeriod) :
    TangentSpace coverModelWithCorners point ≃L[Real]
      TangentSpace coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod) point) :=
  (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
    |>.mfderivToContinuousLinearEquiv (by simp) point

@[simp]
theorem canonicalProjectionDerivativeEquiv_coe
    (point : EffectiveCover period hPeriod) :
    (canonicalProjectionDerivativeEquiv period hPeriod point :
      TangentSpace coverModelWithCorners point →L[Real]
        TangentSpace coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod) point)) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod)) point :=
  IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
      (by simp) point

/-- Differential of global polar coordinates on the cover. -/
def canonicalRadialDerivativeEquiv
    (point : EffectiveCover period hPeriod) :
    TangentSpace coverModelWithCorners point ≃L[Real] EuclideanR4 :=
  (coverRadialMap_isLocalDiffeomorph period hPeriod)
    |>.mfderivToContinuousLinearEquiv (by simp) point

@[simp]
theorem canonicalRadialDerivativeEquiv_coe
    (point : EffectiveCover period hPeriod) :
    (canonicalRadialDerivativeEquiv period hPeriod point :
      TangentSpace coverModelWithCorners point →L[Real] EuclideanR4) =
      mfderiv coverModelWithCorners 𝓘(Real, EuclideanR4)
        (coverRadialMap period hPeriod) point :=
  IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (coverRadialMap_isLocalDiffeomorph period hPeriod) (by simp) point

/-- Radial coordinates on a quotient tangent fiber, using one cover anchor. -/
def canonicalQuotientRadialDerivativeEquiv
    (point : EffectiveCover period hPeriod) :
    TangentSpace coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod) point) ≃L[Real]
      EuclideanR4 :=
  (canonicalProjectionDerivativeEquiv period hPeriod point).symm.trans
    (canonicalRadialDerivativeEquiv period hPeriod point)

theorem canonicalQuotientRadialDerivativeEquiv_projection
    (point : EffectiveCover period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    canonicalQuotientRadialDerivativeEquiv period hPeriod point
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point vector) =
      mfderiv coverModelWithCorners 𝓘(Real, EuclideanR4)
        (coverRadialMap period hPeriod) point vector := by
  change canonicalRadialDerivativeEquiv period hPeriod point
      ((canonicalProjectionDerivativeEquiv period hPeriod point).symm
        (canonicalProjectionDerivativeEquiv period hPeriod point vector)) =
    canonicalRadialDerivativeEquiv period hPeriod point vector
  simp

/-- Projection carries each lifted velocity to its intrinsic quotient
generator. -/
theorem canonicalProjectionDerivativeEquiv_flowValue
    (index : CanonicalFlowIndex) (point : EffectiveCover period hPeriod) :
    canonicalProjectionDerivativeEquiv period hPeriod point
        (canonicalCoverFlowValue period hPeriod index point) =
      canonicalFlowGenerator period hPeriod
        (canonicalVolumePreservingFlow period hPeriod index)
        (mappingTorusMk (sphereData period hPeriod) point) := by
  have hProjectionAt : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners (mappingTorusMk (sphereData period hPeriod)) point :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod point)
      |>.mdifferentiableAt (by simp)
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real) coverModelWithCorners
      (canonicalCoverFlowCurve period hPeriod index point) 0 :=
    (canonicalCoverFlowCurve_contMDiff period hPeriod index point)
      |>.mdifferentiableAt (by simp)
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := coverModelWithCorners)
    (I'' := coverModelWithCorners)
    (f := canonicalCoverFlowCurve period hPeriod index point)
    (g := mappingTorusMk (sphereData period hPeriod))
    (x := (0 : Real)) (y := point) hProjectionAt hCurveAt
    (canonicalCoverFlow_zero period hPeriod index point) (1 : Real)
  have hCurveEq :
      (mappingTorusMk (sphereData period hPeriod)) ∘
          canonicalCoverFlowCurve period hPeriod index point =
        fun parameter =>
          (canonicalVolumePreservingFlow period hPeriod index).flow parameter
            (mappingTorusMk (sphereData period hPeriod) point) := by
    funext parameter
    exact (canonicalCoverFlow_projection period hPeriod index parameter point).symm
  rw [hCurveEq] at hComp
  have hVelocity := canonicalFlowGenerator_eq_curve_mfderiv period hPeriod
    (canonicalVolumePreservingFlow period hPeriod index)
    (mappingTorusMk (sphereData period hPeriod) point)
  change canonicalFlowGenerator period hPeriod
      (canonicalVolumePreservingFlow period hPeriod index)
      (mappingTorusMk (sphereData period hPeriod) point) =
    mfderiv 𝓘(Real, Real) coverModelWithCorners
      (fun parameter =>
        (canonicalVolumePreservingFlow period hPeriod index).flow parameter
          (mappingTorusMk (sphereData period hPeriod) point)) 0 1 at hVelocity
  change (canonicalProjectionDerivativeEquiv period hPeriod point :
      TangentSpace coverModelWithCorners point →L[Real]
        TangentSpace coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod) point))
      (canonicalCoverFlowValue period hPeriod index point) = _
  rw [canonicalProjectionDerivativeEquiv_coe]
  change mfderiv coverModelWithCorners coverModelWithCorners
      (mappingTorusMk (sphereData period hPeriod)) point
        (mfderiv 𝓘(Real, Real) coverModelWithCorners
          (canonicalCoverFlowCurve period hPeriod index point) 0 1) = _
  convert hComp.symm using 1
  · rfl
  · exact HEq.rfl
  · exact heq_of_eq hVelocity

theorem euclideanSpatialRotation_eq_flowGenerator
    (axis : Fin 3) (point : EuclideanR4) :
    euclideanSpatialRotation axis point =
      euclideanSpatialFlowGenerator axis point := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  fin_cases axis <;> ext index <;> fin_cases index <;>
    simp [euclideanSpatialRotation, euclideanSpatialFlowGenerator,
      ambientSpatialRotation_apply]

/-- Ambient normal generator transported to Euclidean four-space. -/
def euclideanNormalRotation (axis : Fin 3) :
    EuclideanR4 →L[Real] EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap.comp
    ((ambientNormalRotation axis).comp
      (EuclideanSpace.equiv (Fin 4) Real).toContinuousLinearMap)

theorem euclideanNormalRotation_symm_apply
    (axis : Fin 3) (point : R4Point) :
    euclideanNormalRotation axis
        ((EuclideanSpace.equiv (Fin 4) Real).symm point) =
      (EuclideanSpace.equiv (Fin 4) Real).symm
        (ambientNormalRotation axis point) := by
  change (EuclideanSpace.equiv (Fin 4) Real).symm
      (ambientNormalRotation axis
        ((EuclideanSpace.equiv (Fin 4) Real)
          ((EuclideanSpace.equiv (Fin 4) Real).symm point))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem euclideanNormalRotation_eq_flowGenerator
    (axis : Fin 3) (point : EuclideanR4) :
    euclideanNormalRotation axis point =
      euclideanNormalFlowGenerator axis point := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  fin_cases axis <;> ext index <;> fin_cases index <;>
    simp [euclideanNormalRotation, euclideanNormalFlowGenerator,
      ambientNormalRotation_apply]

theorem canonicalRadialDerivativeEquiv_timeFlowValue
    (point : EffectiveCover period hPeriod) :
    canonicalRadialDerivativeEquiv period hPeriod point
        (canonicalCoverFlowValue period hPeriod CanonicalFlowIndex.time point) =
      coverRadialMap period hPeriod point := by
  have hRadialAt : MDifferentiableAt coverModelWithCorners
      𝓘(Real, EuclideanR4) (coverRadialMap period hPeriod) point :=
    (coverRadialMap_isLocalDiffeomorph period hPeriod point)
      |>.mdifferentiableAt (by simp)
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real) coverModelWithCorners
      (canonicalCoverFlowCurve period hPeriod CanonicalFlowIndex.time point) 0 :=
    (canonicalCoverFlowCurve_contMDiff period hPeriod
      CanonicalFlowIndex.time point).mdifferentiableAt (by simp)
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := coverModelWithCorners)
    (I'' := 𝓘(Real, EuclideanR4))
    (f := canonicalCoverFlowCurve period hPeriod CanonicalFlowIndex.time point)
    (g := coverRadialMap period hPeriod)
    (x := (0 : Real)) (y := point) hRadialAt hCurveAt
    (canonicalCoverFlow_zero period hPeriod CanonicalFlowIndex.time point)
    (1 : Real)
  have hMap : coverRadialMap period hPeriod ∘
        canonicalCoverFlowCurve period hPeriod CanonicalFlowIndex.time point =
      fun parameter : Real => Real.exp parameter •
        coverRadialMap period hPeriod point := by
    funext parameter
    rw [Function.comp_apply, coverRadialMap_apply, coverRadialMap_apply]
    simp [canonicalCoverFlowCurve, canonicalCoverFlow, coverTimeTranslation,
      Real.exp_add, smul_smul, mul_comm]
  have hDerivative : HasDerivAt
      (fun parameter : Real => Real.exp parameter •
        coverRadialMap period hPeriod point)
      (coverRadialMap period hPeriod point) 0 := by
    simpa using (Real.hasDerivAt_exp 0).smul_const
      (coverRadialMap period hPeriod point)
  change (canonicalRadialDerivativeEquiv period hPeriod point :
      TangentSpace coverModelWithCorners point →L[Real] EuclideanR4)
        (canonicalCoverFlowValue period hPeriod CanonicalFlowIndex.time point) = _
  rw [canonicalRadialDerivativeEquiv_coe]
  calc
    _ = mfderiv 𝓘(Real, Real) 𝓘(Real, EuclideanR4)
        (coverRadialMap period hPeriod ∘
          canonicalCoverFlowCurve period hPeriod CanonicalFlowIndex.time point)
        0 1 := hComp.symm
    _ = _ := by
      rw [hMap, mfderiv_eq_fderiv]
      exact hDerivative.deriv

theorem canonicalRadialDerivativeEquiv_spatialFlowValue
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    canonicalRadialDerivativeEquiv period hPeriod point
        (canonicalCoverFlowValue period hPeriod
          (CanonicalFlowIndex.spatial axis) point) =
      euclideanSpatialFlowGenerator axis
        (coverRadialMap period hPeriod point) := by
  have hValue : canonicalCoverFlowValue period hPeriod
      (CanonicalFlowIndex.spatial axis) point =
        coverSpatialRotationValue period hPeriod axis point := by
    change mfderiv 𝓘(Real, Real) coverModelWithCorners
        (coverSpatialRotationCurve period hPeriod axis point) 0 1 = _
    exact (coverSpatialRotationValue_eq_curve_mfderiv
      period hPeriod axis point).symm
  change (canonicalRadialDerivativeEquiv period hPeriod point :
      TangentSpace coverModelWithCorners point →L[Real] EuclideanR4)
        (canonicalCoverFlowValue period hPeriod
          (CanonicalFlowIndex.spatial axis) point) = _
  rw [canonicalRadialDerivativeEquiv_coe, hValue]
  convert (coverRadialMap_mfderiv_rotation period hPeriod axis point).trans
    (euclideanSpatialRotation_eq_flowGenerator axis
      (coverRadialMap period hPeriod point)) using 1
  · rfl
  · exact HEq.rfl
  · exact HEq.rfl

theorem canonicalRadialDerivativeEquiv_phasedNormalFlowValue
    (axis : Fin 3) (phase : Fin 2)
    (point : EffectiveCover period hPeriod) :
    canonicalRadialDerivativeEquiv period hPeriod point
        (canonicalCoverFlowValue period hPeriod
          (CanonicalFlowIndex.phasedNormal axis phase) point) =
      canonicalNormalRotationPhase period phase point.time •
        euclideanNormalFlowGenerator axis
          (coverRadialMap period hPeriod point) := by
  let phaseValue := canonicalNormalRotationPhase period phase point.time
  have hRadialAt : MDifferentiableAt coverModelWithCorners
      𝓘(Real, EuclideanR4) (coverRadialMap period hPeriod) point :=
    (coverRadialMap_isLocalDiffeomorph period hPeriod point)
      |>.mdifferentiableAt (by simp)
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real) coverModelWithCorners
      (canonicalCoverFlowCurve period hPeriod
        (CanonicalFlowIndex.phasedNormal axis phase) point) 0 :=
    (canonicalCoverFlowCurve_contMDiff period hPeriod
      (CanonicalFlowIndex.phasedNormal axis phase) point)
      |>.mdifferentiableAt (by simp)
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := coverModelWithCorners)
    (I'' := 𝓘(Real, EuclideanR4))
    (f := canonicalCoverFlowCurve period hPeriod
      (CanonicalFlowIndex.phasedNormal axis phase) point)
    (g := coverRadialMap period hPeriod)
    (x := (0 : Real)) (y := point) hRadialAt hCurveAt
    (canonicalCoverFlow_zero period hPeriod
      (CanonicalFlowIndex.phasedNormal axis phase) point) (1 : Real)
  have hMap : coverRadialMap period hPeriod ∘
        canonicalCoverFlowCurve period hPeriod
          (CanonicalFlowIndex.phasedNormal axis phase) point =
      fun parameter : Real => Real.exp point.time •
        (EuclideanSpace.equiv (Fin 4) Real).symm
          (ambientNormalRotationFlow axis
            (parameter * phaseValue, point.fiber.1)) := by
    funext parameter
    rw [Function.comp_apply, coverRadialMap_apply]
    simp only [canonicalCoverFlowCurve, canonicalCoverFlow,
      coverPhasedNormalRotationFlow]
    rw [sphereNormalRotationFlow_coe]
  have hAngle : HasDerivAt
      (fun parameter : Real => parameter * phaseValue) phaseValue 0 := by
    simpa using (hasDerivAt_id (0 : Real)).mul_const phaseValue
  have hAmbient : HasDerivAt
      (fun parameter : Real => ambientNormalRotationFlow axis
        (parameter * phaseValue, point.fiber.1))
      (phaseValue • ambientNormalRotation axis point.fiber.1) 0 := by
    have h := (ambientNormalRotationFlow_hasDerivAt_zero axis point.fiber.1)
      |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 hAngle (by simp)
    convert h using 1 <;> rfl
  have hEuclidean : HasDerivAt
      (fun parameter : Real => (EuclideanSpace.equiv (Fin 4) Real).symm
        (ambientNormalRotationFlow axis
          (parameter * phaseValue, point.fiber.1)))
      ((EuclideanSpace.equiv (Fin 4) Real).symm
        (phaseValue • ambientNormalRotation axis point.fiber.1)) 0 := by
    have h := (EuclideanSpace.equiv (Fin 4) Real).symm.hasFDerivAt
      |>.comp_hasDerivAt 0 hAmbient
    convert h using 1 <;> rfl
  have hDerivative : HasDerivAt
      (fun parameter : Real => Real.exp point.time •
        (EuclideanSpace.equiv (Fin 4) Real).symm
          (ambientNormalRotationFlow axis
            (parameter * phaseValue, point.fiber.1)))
      (Real.exp point.time • (EuclideanSpace.equiv (Fin 4) Real).symm
        (phaseValue • ambientNormalRotation axis point.fiber.1)) 0 :=
    hEuclidean.const_smul (Real.exp point.time)
  change (canonicalRadialDerivativeEquiv period hPeriod point :
      TangentSpace coverModelWithCorners point →L[Real] EuclideanR4)
        (canonicalCoverFlowValue period hPeriod
          (CanonicalFlowIndex.phasedNormal axis phase) point) = _
  rw [canonicalRadialDerivativeEquiv_coe]
  calc
    _ = mfderiv 𝓘(Real, Real) 𝓘(Real, EuclideanR4)
        (coverRadialMap period hPeriod ∘
          canonicalCoverFlowCurve period hPeriod
            (CanonicalFlowIndex.phasedNormal axis phase) point) 0 1 := hComp.symm
    _ = Real.exp point.time • (EuclideanSpace.equiv (Fin 4) Real).symm
        (phaseValue • ambientNormalRotation axis point.fiber.1) := by
      rw [hMap, mfderiv_eq_fderiv]
      exact hDerivative.deriv
    _ = canonicalNormalRotationPhase period phase point.time •
        euclideanNormalFlowGenerator axis
          (coverRadialMap period hPeriod point) := by
      rw [← euclideanNormalRotation_eq_flowGenerator,
        coverRadialMap_apply, map_smul, map_smul,
        euclideanNormalRotation_symm_apply]
      simp [phaseValue, smul_smul, mul_comm]

theorem canonicalRadialDerivativeEquiv_flowValue
    (index : CanonicalFlowIndex) (point : EffectiveCover period hPeriod) :
    canonicalRadialDerivativeEquiv period hPeriod point
        (canonicalCoverFlowValue period hPeriod index point) =
      canonicalEuclideanFlowGenerator period point.time
        (coverRadialMap period hPeriod point) index := by
  cases index with
  | time =>
      simpa [canonicalEuclideanFlowGenerator] using
        canonicalRadialDerivativeEquiv_timeFlowValue period hPeriod point
  | spatial axis =>
      simpa [canonicalEuclideanFlowGenerator] using
        canonicalRadialDerivativeEquiv_spatialFlowValue
          period hPeriod axis point
  | phasedNormal axis phase =>
      simpa [canonicalEuclideanFlowGenerator] using
        canonicalRadialDerivativeEquiv_phasedNormalFlowValue
          period hPeriod axis phase point

/-- Every intrinsic quotient generator has exactly the advertised ambient
radial-coordinate vector. -/
theorem canonicalQuotientRadialDerivativeEquiv_generator
    (index : CanonicalFlowIndex) (point : EffectiveCover period hPeriod) :
    canonicalQuotientRadialDerivativeEquiv period hPeriod point
        (canonicalFlowGenerator period hPeriod
          (canonicalVolumePreservingFlow period hPeriod index)
          (mappingTorusMk (sphereData period hPeriod) point)) =
      canonicalEuclideanFlowGenerator period point.time
        (coverRadialMap period hPeriod point) index := by
  rw [← canonicalProjectionDerivativeEquiv_flowValue
    period hPeriod index point]
  change canonicalRadialDerivativeEquiv period hPeriod point
      ((canonicalProjectionDerivativeEquiv period hPeriod point).symm
        (canonicalProjectionDerivativeEquiv period hPeriod point
          (canonicalCoverFlowValue period hPeriod index point))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact canonicalRadialDerivativeEquiv_flowValue period hPeriod index point

theorem coverRadialMap_ne_zero (point : EffectiveCover period hPeriod) :
    coverRadialMap period hPeriod point ≠ 0 := by
  rw [coverRadialMap_apply]
  refine smul_ne_zero (Real.exp_ne_zero point.time) ?_
  exact ne_zero_of_mem_unit_sphere (unitThreeSphereHomeomorph point.fiber)

/-- Gate marker: the ten intrinsic quotient generators are the ten explicit
Euclidean radial generators at every cover anchor. -/
theorem canonical_ten_flow_radial_generator_gate :
    ∀ (index : CanonicalFlowIndex) (point : EffectiveCover period hPeriod),
      canonicalQuotientRadialDerivativeEquiv period hPeriod point
          (canonicalFlowGenerator period hPeriod
            (canonicalVolumePreservingFlow period hPeriod index)
            (mappingTorusMk (sphereData period hPeriod) point)) =
        canonicalEuclideanFlowGenerator period point.time
          (coverRadialMap period hPeriod point) index :=
  canonicalQuotientRadialDerivativeEquiv_generator period hPeriod

end
end P0EFTJanusMappingTorusCanonicalTenFlowRadialGenerator4D
end JanusFormal
