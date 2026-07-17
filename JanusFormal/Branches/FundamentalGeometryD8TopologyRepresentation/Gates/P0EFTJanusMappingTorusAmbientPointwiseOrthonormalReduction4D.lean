import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinAtlasObstruction

/-!
# Pointwise ambient orthonormal reduction

The existing reduction record has no continuity field.  It is therefore
inhabited pointwise: choose one genuine quotient chart over every base point
and transport the Euclidean form through the actual atlas derivatives.  The
strict tangent cocycle proves compatibility.  This choice does not trivialize
the tangent bundle continuously.

Continuous and smooth refinements are recorded separately below.  No claim is
made that the pointwise choice satisfies either refinement.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPointwiseOrthonormalReduction4D

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinAtlasObstruction

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod

private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

private abbrev AmbientBase := MappingTorus (AmbientData period hPeriod)

private local instance ambientCoverChartedSpace :
    ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance ambientCoverIsManifold :
    IsManifold coverModelWithCorners ω (AmbientCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance ambientBaseChartedSpace :
    ChartedSpace CoverModel (AmbientBase period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance ambientBaseIsManifold :
    IsManifold coverModelWithCorners ω (AmbientBase period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- One actual cover representative of every quotient point.  No regularity
of this choice is asserted. -/
private def referenceLift (point : AmbientBase period hPeriod) :
    AmbientCover period hPeriod :=
  Classical.choose
    (mappingTorusMk_surjective (AmbientData period hPeriod) point)

@[simp]
private theorem referenceLift_mk (point : AmbientBase period hPeriod) :
    mappingTorusMk (AmbientData period hPeriod)
        (referenceLift period hPeriod point) = point :=
  Classical.choose_spec
    (mappingTorusMk_surjective (AmbientData period hPeriod) point)

private theorem ambientQuotientLocalChart_mk_mem_source
    (anchor : AmbientCover period hPeriod) :
    mappingTorusMk (AmbientData period hPeriod) anchor ∈
      (ambientQuotientLocalChart period hPeriod anchor).source := by
  let projection :=
    (mappingTorusMk_isCoveringMap
      (AmbientData period hPeriod)).isLocalHomeomorph
  change mappingTorusMk (AmbientData period hPeriod) anchor ∈
    ((projection.localInverseAt anchor).trans
      (chartAt CoverModel anchor)).source
  rw [OpenPartialHomeomorph.trans_source]
  refine ⟨projection.apply_self_mem_localInverseAt_source, ?_⟩
  change projection.localInverseAt anchor
      (mappingTorusMk (AmbientData period hPeriod) anchor) ∈
    (chartAt CoverModel anchor).source
  rw [projection.localInverseAt_apply_self]
  exact mem_chart_source CoverModel anchor

private theorem referencePoint_mem_chart_source
    (point : AmbientBase period hPeriod) :
    point ∈
      (ambientQuotientLocalChart period hPeriod
        (referenceLift period hPeriod point)).source := by
  simpa only [referenceLift_mk] using
    (ambientQuotientLocalChart_mk_mem_source period hPeriod
      (referenceLift period hPeriod point))

private def ambientChartBasePoint
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    AmbientBase period hPeriod :=
  (ambientQuotientLocalChart period hPeriod anchor).symm coordinate

private theorem coordinate_mem_referenceTransition_source
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    coordinate ∈
      (ambientAtlasTransition period hPeriod anchor
        (referenceLift period hPeriod
          (ambientChartBasePoint period hPeriod anchor coordinate))).source := by
  rw [ambientAtlasTransition, OpenPartialHomeomorph.trans_source]
  exact ⟨hCoordinate,
    referencePoint_mem_chart_source period hPeriod
      (ambientChartBasePoint period hPeriod anchor coordinate)⟩

/-- The true tangent transition from a chart to the selected reference chart
over the same quotient point. -/
private def ambientReferenceFrame
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    CoverCoordinates ≃L[Real] CoverCoordinates :=
  ambientAtlasTangentTransition period hPeriod anchor
    (referenceLift period hPeriod
      (ambientChartBasePoint period hPeriod anchor coordinate))
    coordinate
    (coordinate_mem_referenceTransition_source period hPeriod
      anchor coordinate hCoordinate)

/-- Total pointwise frame.  Values outside a chart target are irrelevant to
all atlas transition laws and are totalized by the identity. -/
def ambientPointwiseAtlasFrame
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    CoverCoordinates ≃L[Real] CoverCoordinates := by
  classical
  exact if hCoordinate : coordinate ∈
        (ambientQuotientLocalChart period hPeriod anchor).target then
      ambientReferenceFrame period hPeriod anchor coordinate hCoordinate
    else
      ContinuousLinearEquiv.refl Real CoverCoordinates

/-- Euclidean form transported to the selected reference chart. -/
def ambientPointwiseAtlasForm
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    QuadraticForm Real CoverCoordinates :=
  ambientCoverEuclideanQuadraticForm.comp
    (ambientPointwiseAtlasFrame period hPeriod anchor coordinate).toContinuousLinearMap.toLinearMap

theorem ambientPointwiseAtlasForm_posDef
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    (ambientPointwiseAtlasForm period hPeriod anchor coordinate).PosDef := by
  intro tangent hTangent
  change 0 < ambientCoverEuclideanQuadraticForm
    (ambientPointwiseAtlasFrame period hPeriod anchor coordinate tangent)
  apply ambientCoverEuclideanQuadraticForm_posDef
  intro hZero
  apply hTangent
  apply (ambientPointwiseAtlasFrame period hPeriod anchor coordinate).injective
  simpa using hZero

private def ambientPointwiseAtlasOrthonormalFrame
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    ambientCoverEuclideanQuadraticForm.IsometryEquiv
      (ambientPointwiseAtlasForm period hPeriod anchor coordinate) where
  __ :=
    (ambientPointwiseAtlasFrame period hPeriod anchor coordinate).symm.toLinearEquiv
  map_app' tangent := by
    simp [ambientPointwiseAtlasForm]

private theorem ambientAtlasTransition_basePoint
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ambientChartBasePoint period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate) =
      ambientChartBasePoint period hPeriod first coordinate := by
  change coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).source at hCoordinate
  rw [OpenPartialHomeomorph.trans_source] at hCoordinate
  change
    (ambientQuotientLocalChart period hPeriod second).symm
        ((ambientQuotientLocalChart period hPeriod second)
          ((ambientQuotientLocalChart period hPeriod first).symm coordinate)) =
      (ambientQuotientLocalChart period hPeriod first).symm coordinate
  exact (ambientQuotientLocalChart period hPeriod second).left_inv hCoordinate.2

private theorem coordinate_mem_firstChart_target
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    coordinate ∈
      (ambientQuotientLocalChart period hPeriod first).target := by
  change coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).source at hCoordinate
  rw [OpenPartialHomeomorph.trans_source] at hCoordinate
  exact hCoordinate.1

private theorem transition_mem_secondChart_target
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ambientAtlasTransition period hPeriod first second coordinate ∈
      (ambientQuotientLocalChart period hPeriod second).target := by
  have hTarget :=
    (ambientAtlasTransition period hPeriod first second).map_source hCoordinate
  change ambientAtlasTransition period hPeriod first second coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).target at hTarget
  rw [OpenPartialHomeomorph.trans_target] at hTarget
  exact hTarget.1

private theorem ambientPointwiseAtlasFrame_transition
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    (ambientPointwiseAtlasFrame period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate)).toLinearEquiv *
        (ambientAtlasTangentTransition period hPeriod first second
          coordinate hCoordinate).toLinearEquiv =
      (ambientPointwiseAtlasFrame period hPeriod first coordinate).toLinearEquiv := by
  let transformed :=
    ambientAtlasTransition period hPeriod first second coordinate
  have hFirstTarget := coordinate_mem_firstChart_target period hPeriod
    first second coordinate hCoordinate
  have hSecondTarget := transition_mem_secondChart_target period hPeriod
    first second coordinate hCoordinate
  have hBase := ambientAtlasTransition_basePoint period hPeriod
    first second coordinate hCoordinate
  have hSecondReference :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second
          (referenceLift period hPeriod
            (ambientChartBasePoint period hPeriod first coordinate))).source := by
    simpa only [transformed, hBase] using
      (coordinate_mem_referenceTransition_source period hPeriod second
        transformed hSecondTarget)
  simp only [ambientPointwiseAtlasFrame, dif_pos hFirstTarget,
    dif_pos hSecondTarget]
  unfold ambientReferenceFrame
  simp only [hBase]
  exact ambientAtlasTangentTransition_cocycle period hPeriod first second
    (referenceLift period hPeriod
      (ambientChartBasePoint period hPeriod first coordinate))
    coordinate hCoordinate
    hSecondReference
    (coordinate_mem_referenceTransition_source period hPeriod first
      coordinate hFirstTarget)

private theorem ambientPointwiseAtlasFrame_transition_apply
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (tangent : CoverCoordinates) :
    ambientPointwiseAtlasFrame period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate)
        (ambientAtlasTangentTransition period hPeriod first second
          coordinate hCoordinate tangent) =
      ambientPointwiseAtlasFrame period hPeriod first coordinate tangent := by
  have hFrames := congrArg
    (fun frame : CoverCoordinates ≃ₗ[Real] CoverCoordinates => frame tangent)
    (ambientPointwiseAtlasFrame_transition period hPeriod
      first second coordinate hCoordinate)
  simpa using hFrames

private def ambientPointwiseAtlasTransition
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    (ambientPointwiseAtlasForm period hPeriod first coordinate).IsometryEquiv
      (ambientPointwiseAtlasForm period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate)) where
  __ := (ambientAtlasTangentTransition period hPeriod first second
    coordinate hCoordinate).toLinearEquiv
  map_app' tangent := by
    change ambientCoverEuclideanQuadraticForm
        (ambientPointwiseAtlasFrame period hPeriod second
          (ambientAtlasTransition period hPeriod first second coordinate)
          (ambientAtlasTangentTransition period hPeriod first second
            coordinate hCoordinate tangent)) =
      ambientCoverEuclideanQuadraticForm
        (ambientPointwiseAtlasFrame period hPeriod first coordinate tangent)
    rw [ambientPointwiseAtlasFrame_transition_apply period hPeriod
      first second coordinate hCoordinate tangent]

/-- The actual quotient atlas has an unconditional pointwise orthonormal
reduction.  This theorem carries no continuity assertion. -/
def ambientPointwiseOrthonormalAtlasReduction :
    AmbientOrthonormalAtlasReduction period hPeriod where
  form := ambientPointwiseAtlasForm period hPeriod
  positiveDefinite := ambientPointwiseAtlasForm_posDef period hPeriod
  orthonormalFrame := ambientPointwiseAtlasOrthonormalFrame period hPeriod
  transition := ambientPointwiseAtlasTransition period hPeriod
  transition_coe := by
    intro first second coordinate hCoordinate
    rfl

theorem ambientOrthonormalAtlasReduction_nonempty :
    Nonempty (AmbientOrthonormalAtlasReduction period hPeriod) :=
  ⟨ambientPointwiseOrthonormalAtlasReduction period hPeriod⟩

/-! ## Honest regularity refinements -/

def chartTangentDomain
    (anchor : AmbientCover period hPeriod) :
    Set (CoverModel × CoverCoordinates) :=
  (ambientQuotientLocalChart period hPeriod anchor).target ×ˢ Set.univ

def transitionTangentDomain
    (first second : AmbientCover period hPeriod) :
    Set (CoverModel × CoverCoordinates) :=
  (ambientAtlasTransition period hPeriod first second).source ×ˢ Set.univ

def reductionFormApplication
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : Real :=
  reduction.form anchor input.1 input.2

def reductionFrameApplication
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : CoverCoordinates :=
  reduction.orthonormalFrame anchor input.1 input.2

def reductionOrthogonalTransitionApplication
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : CoverCoordinates := by
  classical
  exact if hCoordinate : input.1 ∈
        (ambientAtlasTransition period hPeriod first second).source then
      reduction.orthogonalTransition period hPeriod first second input.1
        hCoordinate input.2
    else
      0

/-- A continuous orthonormal reduction is a pointwise reduction whose metric,
frames and orthogonal overlap maps vary continuously on their genuine chart
domains. -/
structure AmbientContinuousOrthonormalAtlasReduction where
  toPointwise : AmbientOrthonormalAtlasReduction period hPeriod
  form_continuousOn : ∀ anchor,
    ContinuousOn (reductionFormApplication period hPeriod toPointwise anchor)
      (chartTangentDomain period hPeriod anchor)
  frame_continuousOn : ∀ anchor,
    ContinuousOn (reductionFrameApplication period hPeriod toPointwise anchor)
      (chartTangentDomain period hPeriod anchor)
  transition_continuousOn : ∀ first second,
    ContinuousOn
      (reductionOrthogonalTransitionApplication period hPeriod toPointwise
        first second)
      (transitionTangentDomain period hPeriod first second)

/-- A smooth orthonormal reduction records the analogous joint `C∞`
regularity.  It remains a separate construction problem. -/
structure AmbientContMDiffOrthonormalAtlasReduction where
  toPointwise : AmbientOrthonormalAtlasReduction period hPeriod
  form_contMDiffOn : ∀ anchor,
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, Real) ω
      (reductionFormApplication period hPeriod toPointwise anchor)
      (chartTangentDomain period hPeriod anchor)
  frame_contMDiffOn : ∀ anchor,
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ω
      (reductionFrameApplication period hPeriod toPointwise anchor)
      (chartTangentDomain period hPeriod anchor)
  transition_contMDiffOn : ∀ first second,
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ω
      (reductionOrthogonalTransitionApplication period hPeriod toPointwise
        first second)
      (transitionTangentDomain period hPeriod first second)

def continuousReduction_implies_pointwise
    (reduction : AmbientContinuousOrthonormalAtlasReduction period hPeriod) :
    AmbientOrthonormalAtlasReduction period hPeriod :=
  reduction.toPointwise

def contMDiffReduction_implies_pointwise
    (reduction : AmbientContMDiffOrthonormalAtlasReduction period hPeriod) :
    AmbientOrthonormalAtlasReduction period hPeriod :=
  reduction.toPointwise

theorem continuousReduction_nonempty_implies_pointwise_nonempty
    (hReduction :
      Nonempty (AmbientContinuousOrthonormalAtlasReduction period hPeriod)) :
    Nonempty (AmbientOrthonormalAtlasReduction period hPeriod) := by
  rcases hReduction with ⟨reduction⟩
  exact ⟨reduction.toPointwise⟩

theorem contMDiffReduction_nonempty_implies_pointwise_nonempty
    (hReduction :
      Nonempty (AmbientContMDiffOrthonormalAtlasReduction period hPeriod)) :
    Nonempty (AmbientOrthonormalAtlasReduction period hPeriod) := by
  rcases hReduction with ⟨reduction⟩
  exact ⟨reduction.toPointwise⟩

end

end P0EFTJanusMappingTorusAmbientPointwiseOrthonormalReduction4D
end JanusFormal
