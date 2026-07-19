import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientAtlasDeckLiftEventuallyEq4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGenuineStableRadialTangentTrivialization4D

/-!
# Radial form of the genuine ambient atlas tangent transition

The locally constant deck winding relating two genuine cover-chart lifts is
differentiated.  After applying the genuine radial tangent equivalences on the
two cover fibers, the actual ambient atlas Jacobian is the corresponding
integer power of the spatial reflection.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientAtlasRadialTangentTransition4D

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientAtlasDeckLiftEventuallyEq4D
open P0EFTJanusMappingTorusGenuineStableRadialTangentTrivialization4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

private local instance ambientCoverChartedSpace :
    ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance ambientCoverIsManifold :
    IsManifold coverModelWithCorners ω (AmbientCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private theorem coordinate_mem_firstCoverChart_target
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    coordinate ∈ (chartAt CoverModel first).target := by
  have hCoordinate' := hCoordinate
  simp only [ambientAtlasTransition, ambientQuotientLocalChart, mfld_simps]
      at hCoordinate'
  exact hCoordinate'.1.1

private theorem transition_mem_secondCoverChart_target
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ambientAtlasTransition period hPeriod first second coordinate ∈
      (chartAt CoverModel second).target := by
  have hTarget :=
    (ambientAtlasTransition period hPeriod first second).map_source hCoordinate
  change ambientAtlasTransition period hPeriod first second coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).target at hTarget
  rw [OpenPartialHomeomorph.trans_target] at hTarget
  have hSecondTarget := hTarget.1
  simp only [ambientQuotientLocalChart, mfld_simps] at hSecondTarget
  exact hSecondTarget.1

private theorem radialEquiv_transport
    {firstPoint secondPoint : AmbientCover period hPeriod}
    (hPoint : firstPoint = secondPoint)
    (vector : TangentSpace coverModelWithCorners firstPoint) :
    genuineStableRadialTangentEquiv period hPeriod firstPoint vector =
      genuineStableRadialTangentEquiv period hPeriod secondPoint
        (hPoint ▸ vector) := by
  subst secondPoint
  rfl

private theorem tangent_transport_eq_of_heq
    {firstPoint secondPoint : AmbientCover period hPeriod}
    (hPoint : firstPoint = secondPoint)
    (firstVector : TangentSpace coverModelWithCorners firstPoint)
    (secondVector : TangentSpace coverModelWithCorners secondPoint)
    (hVector : HEq firstVector secondVector) :
    hPoint ▸ firstVector = secondVector := by
  subst secondPoint
  exact eq_of_heq hVector

/-- Differentiating the genuine local equality of the two cover-chart lifts
gives equality of their manifold derivatives. -/
theorem ambientTransitionWinding_realizes_transition_mfderiv
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    mfderiv coverModelWithCorners coverModelWithCorners
        (fun nearby ↦ (chartAt CoverModel second).symm
          (ambientAtlasTransition period hPeriod first second nearby))
        coordinate =
      mfderiv coverModelWithCorners coverModelWithCorners
        (fun nearby ↦
          ambientTransitionWinding period hPeriod first second coordinate +ᵥ
            (chartAt CoverModel first).symm nearby)
        coordinate :=
  Filter.EventuallyEq.mfderiv_eq
    (I := coverModelWithCorners) (I' := coverModelWithCorners)
    (ambientTransitionWinding_realizes_transition_eventuallyEq
      period hPeriod first second coordinate hCoordinate)

/-- In the genuine radial frames of the two lifted cover points, the actual
ambient atlas tangent transition is exactly the radial deck operator selected
by the integer transition winding. -/
theorem ambientAtlasTangentTransition_radialDeckOperator
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (vector : TangentSpace coverModelWithCorners coordinate) :
    genuineStableRadialTangentEquiv period hPeriod
        ((chartAt CoverModel second).symm
          (ambientAtlasTransition period hPeriod first second coordinate))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (chartAt CoverModel second).symm
          (ambientAtlasTransition period hPeriod first second coordinate)
          (mfderiv coverModelWithCorners coverModelWithCorners
            (ambientAtlasTransition period hPeriod first second)
            coordinate vector)) =
      genuineStableRadialDeckOperator
          (ambientTransitionWinding period hPeriod first second coordinate)
        (genuineStableRadialTangentEquiv period hPeriod
          ((chartAt CoverModel first).symm coordinate)
          (mfderiv coverModelWithCorners coverModelWithCorners
            (chartAt CoverModel first).symm coordinate vector)) := by
  let winding := ambientTransitionWinding period hPeriod first second coordinate
  let firstPoint := (chartAt CoverModel first).symm coordinate
  let transformed := ambientAtlasTransition period hPeriod first second coordinate
  have hFirstTarget := coordinate_mem_firstCoverChart_target period hPeriod
    first second coordinate hCoordinate
  have hSecondTarget := transition_mem_secondCoverChart_target period hPeriod
    first second coordinate hCoordinate
  have hFirstInverse :
      MDifferentiableAt coverModelWithCorners coverModelWithCorners
        (chartAt CoverModel first).symm coordinate :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) hFirstTarget
  have hSecondInverse :
      MDifferentiableAt coverModelWithCorners coverModelWithCorners
        (chartAt CoverModel second).symm transformed :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) hSecondTarget
  have hTransition :
      MDifferentiableAt coverModelWithCorners coverModelWithCorners
        (ambientAtlasTransition period hPeriod first second) coordinate :=
    ((ambientAtlasPartialDiffeomorph period hPeriod first second)
      |>.isLocalDiffeomorphAt
        (I := coverModelWithCorners) (J := coverModelWithCorners) (n := ω)
        hCoordinate).mdifferentiableAt (by simp)
  have hDeck :
      MDifferentiableAt coverModelWithCorners coverModelWithCorners
        (winding +ᵥ · : AmbientCover period hPeriod → AmbientCover period hPeriod)
        firstPoint :=
    (reflectedSphereCover_deck_contMDiff period hPeriod winding)
      |>.mdifferentiableAt (by simp)
  have hDerivative := congrArg (fun derivative ↦ derivative vector)
    (ambientTransitionWinding_realizes_transition_mfderiv period hPeriod
      first second coordinate hCoordinate)
  change
      mfderiv coverModelWithCorners coverModelWithCorners
          ((chartAt CoverModel second).symm ∘
            ambientAtlasTransition period hPeriod first second)
          coordinate vector =
        mfderiv coverModelWithCorners coverModelWithCorners
          ((winding +ᵥ ·) ∘ (chartAt CoverModel first).symm)
          coordinate vector at hDerivative
  rw [mfderiv_comp_apply coordinate hSecondInverse hTransition vector,
    mfderiv_comp_apply coordinate hDeck hFirstInverse vector] at hDerivative
  have hLiftedPoint :=
    ambientTransitionWinding_realizes_transition period hPeriod
      first second coordinate hCoordinate
  change genuineStableRadialTangentEquiv period hPeriod
      ((chartAt CoverModel second).symm transformed)
      (mfderiv coverModelWithCorners coverModelWithCorners
        (chartAt CoverModel second).symm transformed
        (mfderiv coverModelWithCorners coverModelWithCorners
          (ambientAtlasTransition period hPeriod first second)
          coordinate vector)) = _
  have hTransportedDerivative := tangent_transport_eq_of_heq period hPeriod
    hLiftedPoint
    (mfderiv coverModelWithCorners coverModelWithCorners
      (chartAt CoverModel second).symm transformed
      (mfderiv coverModelWithCorners coverModelWithCorners
        (ambientAtlasTransition period hPeriod first second)
        coordinate vector))
    (mfderiv coverModelWithCorners coverModelWithCorners
      (winding +ᵥ · : AmbientCover period hPeriod → AmbientCover period hPeriod)
      firstPoint
      (mfderiv coverModelWithCorners coverModelWithCorners
        (chartAt CoverModel first).symm coordinate vector))
    (heq_of_eq hDerivative)
  calc
    _ = genuineStableRadialTangentEquiv period hPeriod
        (winding +ᵥ firstPoint)
        (hLiftedPoint ▸
          mfderiv coverModelWithCorners coverModelWithCorners
            (chartAt CoverModel second).symm transformed
            (mfderiv coverModelWithCorners coverModelWithCorners
              (ambientAtlasTransition period hPeriod first second)
              coordinate vector)) :=
      radialEquiv_transport period hPeriod hLiftedPoint _
    _ = genuineStableRadialTangentEquiv period hPeriod
        (winding +ᵥ firstPoint)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (winding +ᵥ · : AmbientCover period hPeriod → AmbientCover period hPeriod)
          firstPoint
          (mfderiv coverModelWithCorners coverModelWithCorners
            (chartAt CoverModel first).symm coordinate vector)) := by
      rw [hTransportedDerivative]
    _ = _ := genuineStableRadialTangentEquiv_deckWinding period hPeriod
      winding firstPoint
        (mfderiv coverModelWithCorners coverModelWithCorners
          (chartAt CoverModel first).symm coordinate vector)

end

end P0EFTJanusMappingTorusAmbientAtlasRadialTangentTransition4D
end JanusFormal
