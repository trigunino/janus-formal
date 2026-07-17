import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionCocycle4D

/-!
# Scalar cocycle for the canonical intrinsic normal

The dependent tangent fibers are first identified by the equality of their
base points.  Scalar multiplication is then performed in one fixed fiber,
which avoids transporting unrelated `SMul` instances through `HEq`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionScalarCocycle4D

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
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionCocycle4D

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

private theorem tangentTransport_smul
    {source target : EffectiveQuotient period hPeriod}
    (h : source = target) (scalar : Real)
    (vector : TangentSpace coverModelWithCorners source) :
    Eq.mp (congrArg (TangentSpace coverModelWithCorners) h)
        (scalar • vector) =
      scalar • Eq.mp (congrArg (TangentSpace coverModelWithCorners) h)
        vector := by
  cases h
  rfl

/-- After the named zero-latitude base transport, the quotient derivative is
the canonical pushed normal as an ordinary equality in one tangent fiber. -/
theorem quotientLatitudeNormalVectorAtCanonicalBase_eq
    (anchor : EffectiveThroatCover period hPeriod) :
    Eq.mp
        (congrArg (TangentSpace coverModelWithCorners)
          (quotientNormalLatitude_zero period hPeriod anchor))
        (quotientLatitudeNormalVectorAtCover period hPeriod anchor) =
      canonicalQuotientLatitudeNormal period hPeriod anchor := by
  apply eq_of_heq
  exact (eqMp_heq _ _).trans
    (canonicalQuotientLatitudeNormal_heq_quotientLatitudeNormalVectorAtCover
      period hPeriod anchor).symm

/-- The all-winding tangent law as an equality after explicit base transport. -/
theorem quotientLatitudeNormalVectorAtCover_deck_winding_transport
    (winding : Int) (anchor : EffectiveThroatCover period hPeriod) :
    let hBase :
        quotientNormalLatitude period hPeriod (winding +ᵥ anchor) 0 =
          quotientNormalLatitude period hPeriod anchor 0 := by
      simpa using
        quotientNormalLatitude_deck_winding period hPeriod winding anchor 0
    Eq.mp (congrArg (TangentSpace coverModelWithCorners) hBase)
        (quotientLatitudeNormalVectorAtCover period hPeriod
          (winding +ᵥ anchor)) =
      (normalSignRepresentation winding : Real) •
        quotientLatitudeNormalVectorAtCover period hPeriod anchor := by
  dsimp only
  apply eq_of_heq
  exact (eqMp_heq _ _).trans
    (quotientLatitudeNormalVectorAtCover_deck_winding
      period hPeriod winding anchor)

/-- Scalar multiplication respects the canonical/quotient tangent bridge
without transporting an independently synthesized scalar-action instance. -/
theorem canonicalQuotientLatitudeNormal_smul_heq
    (anchor : EffectiveThroatCover period hPeriod) (scalar : Real) :
    HEq
      (scalar • canonicalQuotientLatitudeNormal period hPeriod anchor)
      (scalar • quotientLatitudeNormalVectorAtCover period hPeriod anchor) := by
  let hBase := quotientNormalLatitude_zero period hPeriod anchor
  let hTangent := congrArg (TangentSpace coverModelWithCorners) hBase
  have hCanonical :
      Eq.mp hTangent
          (quotientLatitudeNormalVectorAtCover period hPeriod anchor) =
        canonicalQuotientLatitudeNormal period hPeriod anchor := by
    exact quotientLatitudeNormalVectorAtCanonicalBase_eq
      period hPeriod anchor
  exact
    (congrArg (fun current => scalar • current) hCanonical.symm).heq |>.trans
      ((tangentTransport_smul period hPeriod hBase scalar
        (quotientLatitudeNormalVectorAtCover period hPeriod anchor)).symm.heq
        |>.trans
          (eqMp_heq hTangent
            (scalar • quotientLatitudeNormalVectorAtCover
              period hPeriod anchor)))

/-- Every deck winding acts on the canonical intrinsic normal by the normal
sign character.  `HEq` records only the unavoidable dependent base transport. -/
theorem canonicalQuotientLatitudeNormal_deck_winding
    (winding : Int) (anchor : EffectiveThroatCover period hPeriod) :
    HEq
      (canonicalQuotientLatitudeNormal period hPeriod (winding +ᵥ anchor))
      ((normalSignRepresentation winding : Real) •
        canonicalQuotientLatitudeNormal period hPeriod anchor) := by
  exact
    (canonicalQuotientLatitudeNormal_heq_quotientLatitudeNormalVectorAtCover
      period hPeriod (winding +ᵥ anchor)).trans
      ((quotientLatitudeNormalVectorAtCover_deck_winding
        period hPeriod winding anchor).trans
        (canonicalQuotientLatitudeNormal_smul_heq period hPeriod anchor
          (normalSignRepresentation winding : Real)).symm)

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionScalarCocycle4D
end JanusFormal
