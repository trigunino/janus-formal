import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricRestrictedGhostSkew4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostBracketNaturality4D

/-!
# Exact throat restriction of the D8 rotation ghosts

The three unconditional bulk rotation ghosts are tangent to the fixed throat.
Their restrictions are the already constructed throat rotation ghosts,
related by the differential of the canonical throat inclusion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD8RotationGhostThroatRestriction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostBracketNaturality4D
open P0EFTJanusProgramPThroatMetricRestrictedGhostSkew4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

local instance effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Spatial rotation commutes exactly with the fixed-throat cover inclusion. -/
theorem fixedThroatCoverInclusion_spatialRotationFlow
    (axis : Fin 3) (angle : Real)
    (point : EffectiveThroatCover period hPeriod) :
    fixedThroatCoverInclusion period hPeriod
        (throatCoverSpatialRotationFlow period hPeriod axis (angle, point)) =
      coverSpatialRotationFlow period hPeriod axis
        (angle, fixedThroatCoverInclusion period hPeriod point) := by
  apply MappingTorusCover.ext
  case fiber =>
    change equatorialSphereInclusion
        (equatorialSpatialRotationFlow axis (angle, point.fiber)) =
      sphereSpatialRotationFlow axis
        (angle, equatorialSphereInclusion point.fiber)
    apply Subtype.ext
    change (equatorialSpatialRotationFlow axis (angle, point.fiber)).1 =
      (sphereSpatialRotationFlow axis
        (angle, equatorialSphereInclusion point.fiber)).1
    rw [sphereSpatialRotationFlow_coe,
      equatorialSpatialRotationFlow_coe]
    rfl
  case time => rfl

/-- Infinitesimal cover rotations are related by the differential of the
fixed-throat cover inclusion. -/
theorem mfderiv_fixedThroatCoverInclusion_spatialRotationValue
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatCoverInclusion period hPeriod) point
        (throatCoverSpatialRotationValue period hPeriod axis point) =
      coverSpatialRotationValue period hPeriod axis
        (fixedThroatCoverInclusion period hPeriod point) := by
  rw [throatCoverSpatialRotationValue_eq_curve_mfderiv,
    coverSpatialRotationValue_eq_curve_mfderiv]
  have hCurve : MDifferentiableAt 𝓘(Real, Real)
      throatCoverModelWithCorners
      (throatCoverSpatialRotationCurve period hPeriod axis point) 0 :=
    (throatCoverSpatialRotationCurve_contMDiff period hPeriod axis point)
      |>.mdifferentiableAt (by simp)
  have hInclusion : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatCoverInclusion period hPeriod)
      (throatCoverSpatialRotationCurve period hPeriod axis point 0) :=
    (fixedThroatCoverInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hComp := mfderiv_comp_apply 0 hInclusion hCurve (1 : Real)
  rw [show throatCoverSpatialRotationCurve period hPeriod axis point 0 = point by
      exact throatCoverSpatialRotationFlow_zero
        period hPeriod axis point] at hComp
  rw [show (fixedThroatCoverInclusion period hPeriod) ∘
        throatCoverSpatialRotationCurve period hPeriod axis point =
      coverSpatialRotationCurve period hPeriod axis
        (fixedThroatCoverInclusion period hPeriod point) by
      funext parameter
      exact fixedThroatCoverInclusion_spatialRotationFlow
        period hPeriod axis parameter point] at hComp
  exact hComp.symm

private theorem descendedThroatCoverGhost_mk_eq_mfderiv
    (ghost : SmoothDeckEquivariantThroatCoverGhost period hPeriod)
    (point : EffectiveThroatCover period hPeriod) :
    descendSmoothDeckEquivariantThroatCoverGhost period hPeriod ghost
        (mappingTorusMk (fixedEquatorData period hPeriod) point) =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (mappingTorusMk (fixedEquatorData period hPeriod)) point
        (ghost.field point) := by
  rw [descendSmoothDeckEquivariantThroatCoverGhost_mk]
  rfl

private theorem descendedCoverGhost_mk_eq_mfderiv
    (ghost : SmoothDeckEquivariantCoverGhost period hPeriod)
    (point : EffectiveCover period hPeriod) :
    descendSmoothDeckEquivariantCoverGhost period hPeriod ghost
        (mappingTorusMk (reflectedSphereData period hPeriod) point) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (reflectedSphereData period hPeriod)) point
        (ghost.field point) := by
  rw [descendSmoothDeckEquivariantCoverGhost_mk]
  rfl

/-- Each unconditional bulk rotation ghost restricts exactly to its throat
rotation ghost through the differential of the quotient inclusion. -/
theorem unconditionalD8SpatialRotationGhost_inclusion_related
    (axis : Fin 3) (point : EffectiveThroat period hPeriod) :
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod) point
        (throatSpatialRotationGhost period hPeriod axis point) =
      (unconditionalD8SpatialRotationGhostRealization period hPeriod).ghosts axis
        (fixedThroatQuotientInclusion period hPeriod point) := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (fixedEquatorData period hPeriod) point
  change mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod)
      (mappingTorusMk (fixedEquatorData period hPeriod) anchor)
      (descendSmoothDeckEquivariantThroatCoverGhost period hPeriod
        (smoothDeckEquivariantThroatCoverSpatialRotation period hPeriod axis)
        (mappingTorusMk (fixedEquatorData period hPeriod) anchor)) =
    descendSmoothDeckEquivariantCoverGhost period hPeriod
      (smoothDeckEquivariantCoverSpatialRotation period hPeriod axis)
      (fixedThroatQuotientInclusion period hPeriod
        (mappingTorusMk (fixedEquatorData period hPeriod) anchor))
  rw [descendedThroatCoverGhost_mk_eq_mfderiv,
    fixedThroatQuotientInclusion_mk,
    descendedCoverGhost_mk_eq_mfderiv]
  change mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod)
      (mappingTorusMk (fixedEquatorData period hPeriod) anchor)
      (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (mappingTorusMk (fixedEquatorData period hPeriod)) anchor
        (throatCoverSpatialRotationValue period hPeriod axis anchor)) =
    mfderiv coverModelWithCorners coverModelWithCorners
      (mappingTorusMk (reflectedSphereData period hPeriod))
      (fixedThroatCoverInclusion period hPeriod anchor)
      (coverSpatialRotationValue period hPeriod axis
        (fixedThroatCoverInclusion period hPeriod anchor))
  rw [show coverSpatialRotationValue period hPeriod axis
        (fixedThroatCoverInclusion period hPeriod anchor) =
      mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatCoverInclusion period hPeriod) anchor
        (throatCoverSpatialRotationValue period hPeriod axis anchor) by
      exact (mfderiv_fixedThroatCoverInclusion_spatialRotationValue
        period hPeriod axis anchor).symm]
  have hSource : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners
      (mappingTorusMk (fixedEquatorData period hPeriod)) anchor :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.contMDiff.mdifferentiableAt (by simp)
  have hQuotient : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatQuotientInclusion period hPeriod)
      (mappingTorusMk (fixedEquatorData period hPeriod) anchor) :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hCover : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatCoverInclusion period hPeriod) anchor :=
    (fixedThroatCoverInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hTarget : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (mappingTorusMk (reflectedSphereData period hPeriod))
      (fixedThroatCoverInclusion period hPeriod anchor) :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
      |>.contMDiff.mdifferentiableAt (by simp)
  have hLeft := mfderiv_comp_apply anchor hQuotient hSource
    (throatCoverSpatialRotationValue period hPeriod axis anchor)
  have hRight := mfderiv_comp_apply anchor hTarget hCover
    (throatCoverSpatialRotationValue period hPeriod axis anchor)
  rw [show (fixedThroatQuotientInclusion period hPeriod) ∘
        mappingTorusMk (fixedEquatorData period hPeriod) =
      (mappingTorusMk (reflectedSphereData period hPeriod)) ∘
        fixedThroatCoverInclusion period hPeriod by
      funext current
      exact fixedThroatQuotientInclusion_mk
        period hPeriod current] at hLeft
  exact hLeft.symm.trans hRight

/-- Reusable restriction certificate, indexed by the three rotation axes. -/
def unconditionalD8SpatialRotationBulkGhostThroatRestriction
    (axis : Fin 3) :
    BulkGhostThroatRestrictionData period hPeriod
      ((unconditionalD8SpatialRotationGhostRealization
        period hPeriod).ghosts axis) where
  throatGhost := throatSpatialRotationGhost period hPeriod axis
  inclusion_related :=
    unconditionalD8SpatialRotationGhost_inclusion_related
      period hPeriod axis

/-- The exact inclusion relation holds for all three rotation ghosts. -/
theorem unconditionalD8SpatialRotationGhosts_inclusion_related :
    ∀ axis : Fin 3, ∀ point : EffectiveThroat period hPeriod,
      mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point
          (throatSpatialRotationGhost period hPeriod axis point) =
        (unconditionalD8SpatialRotationGhostRealization
          period hPeriod).ghosts axis
          (fixedThroatQuotientInclusion period hPeriod point) :=
  unconditionalD8SpatialRotationGhost_inclusion_related period hPeriod

end

end P0EFTJanusProgramPD8RotationGhostThroatRestriction4D
end JanusFormal
