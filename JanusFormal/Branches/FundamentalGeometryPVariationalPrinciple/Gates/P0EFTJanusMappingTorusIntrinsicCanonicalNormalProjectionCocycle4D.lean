import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionWinding4D

/-!
# Canonical intrinsic normal cocycle

This gate identifies the pushed canonical cover normal with the tangent of
the quotient latitude curve.  The scalar-action cocycle and global gluing are
kept as separate residuals.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionCocycle4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionDeck4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionTransportBridge4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionWinding4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev ThroatBase := MappingTorus (throatData period hPeriod)

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

private local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem eqMp_heq {α β : Sort _} (h : α = β) (x : α) :
    HEq (Eq.mp h x) x := by
  cases h
  rfl

private theorem eqMpr_heq {α β : Sort _} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

private theorem dependentApply_heq
    {α : Sort _} {β γ : α → Sort _}
    (f : (point : α) → β point → γ point)
    {source target : α} (h : source = target) (x : β source) :
    HEq (f target (Eq.mp (congrArg β h) x)) (f source x) := by
  cases h
  rfl

/-- The canonical pushed cover normal is exactly the derivative of the
quotient latitude curve, modulo the named base-point transports. -/
theorem canonicalQuotientLatitudeNormal_heq_quotientLatitudeNormalVectorAtCover
    (anchor : EffectiveThroatCover period hPeriod) :
    HEq (canonicalQuotientLatitudeNormal period hPeriod anchor)
      (quotientLatitudeNormalVectorAtCover period hPeriod anchor) := by
  have hOuter : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (mappingTorusMk (sphereData period hPeriod))
      (normalLatitudeCover period hPeriod anchor 0) :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (by simp)
  have hInner : MDifferentiableAt (modelWithCornersSelf Real Real)
      coverModelWithCorners (normalLatitudeCover period hPeriod anchor) 0 :=
    (normalLatitudeCover_contMDiff period hPeriod anchor).mdifferentiableAt
      (by simp)
  have hComp := mfderiv_comp_apply 0 hOuter hInner 1
  change mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
      (fun normal => mappingTorusMk (sphereData period hPeriod)
        (normalLatitudeCover period hPeriod anchor normal)) 0 1 = _ at hComp
  have hCanonical : HEq
      (canonicalQuotientLatitudeNormal period hPeriod anchor)
      (mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod))
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor)) := by
    unfold canonicalQuotientLatitudeNormal
    dsimp only [id]
    exact eqMpr_heq _ _
  have hProjection : HEq
      (mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod))
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor))
      (mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod))
        (normalLatitudeCover period hPeriod anchor 0)
        (mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
          (normalLatitudeCover period hPeriod anchor) 0 1)) := by
    unfold coverLatitudeNormalVector
    exact dependentApply_heq
      (fun point vector =>
        mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point vector)
      (normalLatitudeCover_zero period hPeriod anchor)
      (mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        (normalLatitudeCover period hPeriod anchor) 0 1)
  unfold quotientLatitudeNormalVectorAtCover quotientNormalLatitude
  exact hCanonical.trans (hProjection.trans hComp.symm.heq)

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionCocycle4D
end JanusFormal
