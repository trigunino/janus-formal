import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientAtlasRadialReferenceTransition4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSmoothOrthonormalReduction4D

/-!
# Pointwise radial reference reduction of the ambient atlas

The genuine radial coordinate frames pull back the reference Euclidean form.
Their actual overlap transition is the canonical orthogonal phase selected by
the true winding.  Smooth dependence is deliberately left to the subsequent
analytic gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientRadialReferencePointwiseReduction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPointwiseOrthonormalReduction4D
open P0EFTJanusMappingTorusAmbientSmoothOrthonormalReduction4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceOrthogonalCocycle4D
open P0EFTJanusMappingTorusAmbientAtlasRadialReferenceTransition4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

private local instance ambientCoverChartedSpace :
    ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance ambientCoverIsManifold :
    IsManifold coverModelWithCorners ω (AmbientCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private theorem quotientChart_target_mem_coverChart_target
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    coordinate ∈ (chartAt CoverModel anchor).target := by
  simp only [ambientQuotientLocalChart, mfld_simps] at hCoordinate
  exact hCoordinate.1

/-- Totalized genuine radial coordinate frame. -/
def ambientRadialReferenceAtlasFrame
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    CoverCoordinates ≃L[Real] CoverCoordinates := by
  classical
  exact if hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target then
    ambientRadialReferenceCoordinateFrame period hPeriod anchor coordinate
      (quotientChart_target_mem_coverChart_target period hPeriod
        anchor coordinate hCoordinate)
  else
    ContinuousLinearEquiv.refl Real CoverCoordinates

/-- Euclidean form pulled back by the genuine radial coordinate frame. -/
def ambientRadialReferenceAtlasForm
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    QuadraticForm Real CoverCoordinates :=
  ambientCoverEuclideanQuadraticForm.comp
    (ambientRadialReferenceAtlasFrame period hPeriod anchor coordinate).toLinearMap

theorem ambientRadialReferenceAtlasForm_posDef
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    (ambientRadialReferenceAtlasForm period hPeriod anchor coordinate).PosDef := by
  intro tangent hTangent
  change 0 < ambientCoverEuclideanQuadraticForm
    (ambientRadialReferenceAtlasFrame period hPeriod anchor coordinate tangent)
  apply ambientCoverEuclideanQuadraticForm_posDef
  intro hZero
  apply hTangent
  apply (ambientRadialReferenceAtlasFrame period hPeriod anchor coordinate).injective
  simpa using hZero

private def ambientRadialReferenceAtlasOrthonormalFrame
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    ambientCoverEuclideanQuadraticForm.IsometryEquiv
      (ambientRadialReferenceAtlasForm period hPeriod anchor coordinate) where
  __ := (ambientRadialReferenceAtlasFrame period hPeriod anchor coordinate).symm.toLinearEquiv
  map_app' tangent := by simp [ambientRadialReferenceAtlasForm]

private theorem coordinate_mem_firstChart_target
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    coordinate ∈ (ambientQuotientLocalChart period hPeriod first).target := by
  change coordinate ∈ ((ambientQuotientLocalChart period hPeriod first).symm.trans
    (ambientQuotientLocalChart period hPeriod second)).source at hCoordinate
  rw [OpenPartialHomeomorph.trans_source] at hCoordinate
  exact hCoordinate.1

private theorem transition_mem_secondChart_target
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
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

theorem ambientRadialReferenceAtlasFrame_transition_apply
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (tangent : CoverCoordinates) :
    ambientRadialReferenceAtlasFrame period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate)
        (ambientAtlasTangentTransition period hPeriod first second
          coordinate hCoordinate tangent) =
      (canonicalAmbientReferenceOrthogonalTransition period hPeriod
        first second coordinate).toLinearEquiv
        (ambientRadialReferenceAtlasFrame period hPeriod first coordinate tangent) := by
  have hFirst := coordinate_mem_firstChart_target period hPeriod
    first second coordinate hCoordinate
  have hSecond := transition_mem_secondChart_target period hPeriod
    first second coordinate hCoordinate
  simp only [ambientRadialReferenceAtlasFrame, dif_pos hFirst, dif_pos hSecond]
  exact ambientAtlasTangentTransition_radialReferencePhase period hPeriod
    first second coordinate hCoordinate tangent

private def ambientRadialReferenceAtlasTransition
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    (ambientRadialReferenceAtlasForm period hPeriod first coordinate).IsometryEquiv
      (ambientRadialReferenceAtlasForm period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate)) where
  __ := (ambientAtlasTangentTransition period hPeriod first second
    coordinate hCoordinate).toLinearEquiv
  map_app' tangent := by
    change ambientCoverEuclideanQuadraticForm
        (ambientRadialReferenceAtlasFrame period hPeriod second
          (ambientAtlasTransition period hPeriod first second coordinate)
          (ambientAtlasTangentTransition period hPeriod first second
            coordinate hCoordinate tangent)) =
      ambientCoverEuclideanQuadraticForm
        (ambientRadialReferenceAtlasFrame period hPeriod first coordinate tangent)
    rw [ambientRadialReferenceAtlasFrame_transition_apply period hPeriod]
    exact (canonicalAmbientReferenceOrthogonalTransition period hPeriod
      first second coordinate).map_app _

/-- Pointwise radial orthonormal reduction of the actual atlas. -/
def ambientRadialReferenceOrthonormalAtlasReduction :
    AmbientOrthonormalAtlasReduction period hPeriod where
  form := ambientRadialReferenceAtlasForm period hPeriod
  positiveDefinite := ambientRadialReferenceAtlasForm_posDef period hPeriod
  orthonormalFrame := ambientRadialReferenceAtlasOrthonormalFrame period hPeriod
  transition := ambientRadialReferenceAtlasTransition period hPeriod
  transition_coe := by intros; rfl

/-- Its reduced overlap is exactly the canonical orthogonal winding phase. -/
theorem ambientRadialReferenceOrthogonalTransition_eq_canonical
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    (ambientRadialReferenceOrthonormalAtlasReduction period hPeriod
      |>.orthogonalTransition period hPeriod first second coordinate hCoordinate).toLinearEquiv =
      (canonicalAmbientReferenceOrthogonalTransition period hPeriod
        first second coordinate).toLinearEquiv := by
  apply LinearEquiv.ext
  intro tangent
  change ambientRadialReferenceAtlasFrame period hPeriod second
      (ambientAtlasTransition period hPeriod first second coordinate)
      (ambientAtlasTangentTransition period hPeriod first second coordinate
        hCoordinate
        ((ambientRadialReferenceAtlasFrame period hPeriod first coordinate).symm tangent)) =
    (canonicalAmbientReferenceOrthogonalTransition period hPeriod
      first second coordinate).toLinearEquiv tangent
  rw [ambientRadialReferenceAtlasFrame_transition_apply period hPeriod]
  simp

end

end P0EFTJanusMappingTorusAmbientRadialReferencePointwiseReduction4D
end JanusFormal
