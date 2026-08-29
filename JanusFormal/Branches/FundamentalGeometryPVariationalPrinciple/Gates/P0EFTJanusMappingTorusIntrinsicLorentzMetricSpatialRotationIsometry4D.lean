import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialRotationAmbientLorentzIsometry4D

/-!
# Spatial-rotation isometry of the intrinsic cover Lorentz tensor

The explicit finite cover rotations intertwine the cover immersion with the
ambient finite Lorentz isometries.  Differentiating this identity proves that
the intrinsic ambient-pullback Lorentz tensor is rotation invariant.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicLorentzMetricSpatialRotationIsometry4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusSpatialRotationAmbientLorentzIsometry4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

/-- The sphere immersion intertwines its finite rotation with the ambient
Euclidean rotation. -/
theorem sphereAmbientMap_spatialRotation
    (axis : Fin 3) (angle : Real) (point : UnitThreeSphere) :
    sphereAmbientMap (sphereSpatialRotationFlow axis (angle, point)) =
      euclideanR4FiniteSpatialRotation axis angle
        (sphereAmbientMap point) := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  rw [euclideanR4FiniteSpatialRotation_coordinates]
  change (sphereSpatialRotationFlow axis (angle, point)).1 =
    ambientSpatialRotationFlow axis (angle, point.1)
  exact sphereSpatialRotationFlow_coe axis (angle, point)

/-- The cover immersion intertwines finite cover rotation with the ambient
finite Lorentz isometry. -/
theorem coverAmbientMap_spatialRotation
    (axis : Fin 3) (angle : Real)
    (point : EffectiveCover period hPeriod) :
    coverAmbientMap period hPeriod
        (coverSpatialRotationFlow period hPeriod axis (angle, point)) =
      ambientFiniteSpatialRotation axis angle
        (coverAmbientMap period hPeriod point) := by
  apply Prod.ext
  · exact sphereAmbientMap_spatialRotation axis angle point.fiber
  · rfl

@[simp]
private theorem ambientFiniteSpatialRotation_mfderiv
    (axis : Fin 3) (angle : Real) (point : EuclideanR4 × Real) :
    mfderiv 𝓘(Real, EuclideanR4 × Real)
        𝓘(Real, EuclideanR4 × Real)
        (ambientFiniteSpatialRotation axis angle) point =
      ambientFiniteSpatialRotation axis angle := by
  rw [mfderiv_eq_fderiv]
  exact (ambientFiniteSpatialRotation axis angle).hasFDerivAt.fderiv

/-- Naturality of the cover immersion derivative under finite spatial
rotation. -/
theorem coverAmbientDerivative_spatialRotation_natural
    (axis : Fin 3) (angle : Real)
    (point : EffectiveCover period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    coverAmbientDerivative period hPeriod
        (coverSpatialRotationFlow period hPeriod axis (angle, point))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (fun current =>
            coverSpatialRotationFlow period hPeriod axis (angle, current))
          point vector) =
      ambientFiniteSpatialRotation axis angle
        (coverAmbientDerivative period hPeriod point vector) := by
  have hRotation :
      ContMDiff coverModelWithCorners coverModelWithCorners ∞
        (fun current : EffectiveCover period hPeriod =>
          coverSpatialRotationFlow period hPeriod axis (angle, current)) :=
    (coverSpatialRotationFlow_contMDiff period hPeriod axis).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hCover := coverAmbientMap_contMDiff period hPeriod
  have hAmbient :
      ContMDiff 𝓘(Real, EuclideanR4 × Real)
        𝓘(Real, EuclideanR4 × Real) ∞
        (ambientFiniteSpatialRotation axis angle) :=
    (ambientFiniteSpatialRotation axis angle).contDiff.contMDiff
  have hMaps :
      coverAmbientMap period hPeriod ∘
          (fun current : EffectiveCover period hPeriod =>
            coverSpatialRotationFlow period hPeriod axis (angle, current)) =
        ambientFiniteSpatialRotation axis angle ∘
          coverAmbientMap period hPeriod := by
    funext current
    exact coverAmbientMap_spatialRotation period hPeriod axis angle current
  have hLeft := mfderiv_comp_apply point
    (hCover.mdifferentiable (by simp)
      (coverSpatialRotationFlow period hPeriod axis (angle, point)))
    (hRotation.mdifferentiable (by simp) point) vector
  have hRight := mfderiv_comp_apply point
    (hAmbient.mdifferentiable (by simp)
      (coverAmbientMap period hPeriod point))
    (hCover.mdifferentiable (by simp) point) vector
  rw [hMaps] at hLeft
  have hNatural := hLeft.symm.trans hRight
  change
    coverAmbientDerivative period hPeriod
        (coverSpatialRotationFlow period hPeriod axis (angle, point))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (fun current =>
            coverSpatialRotationFlow period hPeriod axis (angle, current))
          point vector) =
      mfderiv 𝓘(Real, EuclideanR4 × Real)
        𝓘(Real, EuclideanR4 × Real)
        (ambientFiniteSpatialRotation axis angle)
        (coverAmbientMap period hPeriod point)
        (coverAmbientDerivative period hPeriod point vector) at hNatural
  rw [ambientFiniteSpatialRotation_mfderiv] at hNatural
  exact hNatural

/-- Every finite cover spatial rotation is an exact isometry of the
intrinsic ambient-pullback Lorentz tensor. -/
theorem intrinsicCoverLorentzTensor_spatialRotation_isometry
    (axis : Fin 3) (angle : Real)
    (point : EffectiveCover period hPeriod)
    (first second : TangentSpace coverModelWithCorners point) :
    intrinsicCoverLorentzTensor period hPeriod
        (coverSpatialRotationFlow period hPeriod axis (angle, point))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (fun current =>
            coverSpatialRotationFlow period hPeriod axis (angle, current))
          point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (fun current =>
            coverSpatialRotationFlow period hPeriod axis (angle, current))
          point second) =
      intrinsicCoverLorentzTensor period hPeriod point first second := by
  rw [intrinsicCoverLorentzTensor_apply,
    intrinsicCoverLorentzTensor_apply,
    coverAmbientDerivative_spatialRotation_natural,
    coverAmbientDerivative_spatialRotation_natural]
  exact ambientFiniteSpatialRotation_preserves_minkowski axis angle
    (coverAmbientDerivative period hPeriod point first)
    (coverAmbientDerivative period hPeriod point second)

end

end P0EFTJanusMappingTorusIntrinsicLorentzMetricSpatialRotationIsometry4D
end JanusFormal
