import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionDeck4D

/-!
# Transport bridge for the explicit intrinsic normal projection

This gate removes the dependent casts hidden by the named zero-latitude and
quotient-inclusion equalities.  The result connects the pushed canonical cover
normal to the derivative of the quotient latitude curve.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionTransportBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace
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

/-- The named cover latitude normal differs from its raw derivative only by
transport along `normalLatitudeCover_zero`. -/
theorem coverLatitudeNormalVector_heq_rawDerivative
    (anchor : EffectiveThroatCover period hPeriod) :
    HEq (coverLatitudeNormalVector period hPeriod anchor)
      (mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        (normalLatitudeCover period hPeriod anchor) 0 1) := by
  unfold coverLatitudeNormalVector
  exact eqMp_heq _ _

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionTransportBridge4D
end JanusFormal
