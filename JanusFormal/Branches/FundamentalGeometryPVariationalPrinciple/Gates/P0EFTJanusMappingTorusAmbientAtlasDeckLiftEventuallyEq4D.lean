import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D

/-!
# Ambient atlas lifts realize the deck winding locally

On the genuine source of an ambient atlas transition, the two cover-chart
lifts differ locally by the actual integer deck index of that transition.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientAtlasDeckLiftEventuallyEq4D

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

private local instance ambientCoverChartedSpace :
    ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private abbrev ambientProjectionIsLocalHomeomorph :
    IsLocalHomeomorph (mappingTorusMk (AmbientData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap (AmbientData period hPeriod)).isLocalHomeomorph

/-- At a point of a genuine ambient overlap, the two cover-chart lifts are
related by the actual deck winding selected by the covering sections. -/
theorem ambientTransitionWinding_realizes_transition
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    (chartAt CoverModel second).symm
        (ambientAtlasTransition period hPeriod first second coordinate) =
      ambientTransitionWinding period hPeriod first second coordinate +ᵥ
        (chartAt CoverModel first).symm coordinate := by
  let projection := ambientProjectionIsLocalHomeomorph period hPeriod
  let firstSection := projection.localInverseAt first
  let secondSection := projection.localInverseAt second
  let firstChart := chartAt CoverModel first
  let secondChart := chartAt CoverModel second
  have hCoordinate' := hCoordinate
  simp only [ambientAtlasTransition, ambientQuotientLocalChart, projection,
    firstSection, secondSection, firstChart, secondChart, mfld_simps]
      at hCoordinate'
  have hDeck := ambientTransitionWinding_vadd period hPeriod
    first second coordinate hCoordinate
  change ambientTransitionWinding period hPeriod first second coordinate +ᵥ
      firstSection (firstSection.symm (firstChart.symm coordinate)) =
    secondSection (firstSection.symm (firstChart.symm coordinate)) at hDeck
  rw [firstSection.right_inv hCoordinate'.1.2] at hDeck
  simp only [ambientAtlasTransition, ambientQuotientLocalChart,
    Function.comp_apply, mfld_simps]
  rw [secondChart.left_inv hCoordinate'.2.2]
  exact hDeck.symm

/-- The pointwise deck law above holds with the winding frozen at the base
coordinate throughout a neighborhood of every genuine ambient overlap. -/
theorem ambientTransitionWinding_realizes_transition_eventuallyEq
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    Filter.EventuallyEq (nhds coordinate)
      (fun nearby ↦ (chartAt CoverModel second).symm
        (ambientAtlasTransition period hPeriod first second nearby))
      (fun nearby ↦
        ambientTransitionWinding period hPeriod first second coordinate +ᵥ
          (chartAt CoverModel first).symm nearby) := by
  let projection := ambientProjectionIsLocalHomeomorph period hPeriod
  let firstSection := projection.localInverseAt first
  let secondSection := projection.localInverseAt second
  let firstChart := chartAt CoverModel first
  let secondChart := chartAt CoverModel second
  let quotientFirst := firstSection.trans firstChart
  let base := quotientFirst.symm coordinate
  let winding := ambientTransitionWinding period hPeriod first second coordinate
  have hCoordinate' := hCoordinate
  simp only [ambientAtlasTransition, ambientQuotientLocalChart, projection,
    firstSection, secondSection, firstChart, secondChart, mfld_simps]
      at hCoordinate'
  have hFirstTarget : coordinate ∈ quotientFirst.target := by
    simpa only [quotientFirst, mfld_simps] using hCoordinate'.1
  have hFirstSource : base ∈ firstSection.source := by
    exact firstSection.symm.map_source hCoordinate'.1.2
  have hSecondSource : base ∈ secondSection.source := by
    exact hCoordinate'.2.1
  have hDeck := ambientTransitionWinding_vadd period hPeriod
    first second coordinate hCoordinate
  change winding +ᵥ firstSection base = secondSection base at hDeck
  have hSections := localInverseAt_eventuallyEq_vadd_of_mem
    (AmbientData period hPeriod) first second base hFirstSource hSecondSource
      winding hDeck
  have hInverseContinuous : ContinuousAt quotientFirst.symm coordinate :=
    quotientFirst.symm.continuousAt hFirstTarget
  have hSectionsCoordinate := hSections.comp_tendsto hInverseContinuous
  have hOverlap :
      (ambientAtlasTransition period hPeriod first second).source ∈
        nhds coordinate :=
    (ambientAtlasTransition period hPeriod first second).open_source.mem_nhds
      hCoordinate
  filter_upwards [hSectionsCoordinate, hOverlap]
    with nearby hSectionsNearby hNearby
  have hNearbyWinding :
      ambientTransitionWinding period hPeriod first second nearby = winding := by
    apply IsCancelVAdd.right_cancel _ _ (firstSection (quotientFirst.symm nearby))
    have hNearbyDeck := ambientTransitionWinding_vadd period hPeriod
      first second nearby hNearby
    change ambientTransitionWinding period hPeriod first second nearby +ᵥ
        firstSection (quotientFirst.symm nearby) =
      secondSection (quotientFirst.symm nearby) at hNearbyDeck
    exact hNearbyDeck.trans hSectionsNearby
  simpa only [winding, hNearbyWinding] using
    (ambientTransitionWinding_realizes_transition period hPeriod
      first second nearby hNearby)

end

end P0EFTJanusMappingTorusAmbientAtlasDeckLiftEventuallyEq4D
end JanusFormal
