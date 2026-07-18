import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeNormalAtlasFrame4D

/-!
# Vertex-gauge transformation of an ambient orthonormal atlas reduction

This upgrades the abstract group-level vertex-gauge algebra to the actual
`AmbientOrthonormalAtlasReduction` structure.  Postcomposing every Euclidean
source frame by a local orthogonal gauge preserves the metric and changes each
reduced transition by the exact source/target vertex-gauge formula.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientOrthonormalVertexGaugeTransform4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

/-- Change every local orthonormal frame by an `O(4)`-valued vertex gauge. -/
def ambientOrthonormalAtlasGaugeTransform
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (gauge : AmbientCover period hPeriod → CoverModel →
      AmbientOrthogonalIsometry) :
    AmbientOrthonormalAtlasReduction period hPeriod where
  form := reduction.form
  positiveDefinite := reduction.positiveDefinite
  orthonormalFrame anchor coordinate :=
    (gauge anchor coordinate).trans
      (reduction.orthonormalFrame anchor coordinate)
  transition := reduction.transition
  transition_coe := reduction.transition_coe

/-- The transformed reduced transition is exactly the abstract
source/target vertex-gauged transition. -/
theorem ambientOrthonormalAtlasGaugeTransform_orthogonalTransition
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (gauge : AmbientCover period hPeriod → CoverModel →
      AmbientOrthogonalIsometry)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ((ambientOrthonormalAtlasGaugeTransform period hPeriod reduction gauge)
      |>.orthogonalTransition period hPeriod first second coordinate
        hCoordinate).toLinearEquiv =
      vertexGaugedTransition
        (reduction.orthogonalTransition period hPeriod first second coordinate
          hCoordinate).toLinearEquiv
        (gauge first coordinate).toLinearEquiv
        (gauge second
          (ambientAtlasTransition period hPeriod first second coordinate)
        ).toLinearEquiv := by
  apply LinearEquiv.ext
  intro vector
  rfl

/-- Therefore any exact vertex-gauge realization of a target transition is
literally the transition of the transformed atlas reduction. -/
theorem ambientOrthonormalAtlasGaugeTransform_reaches_target
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (gauge : AmbientCover period hPeriod → CoverModel →
      AmbientOrthogonalIsometry)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (target : CoverCoordinates ≃ₗ[Real] CoverCoordinates)
    (hTarget :
      vertexGaugedTransition
        (reduction.orthogonalTransition period hPeriod first second coordinate
          hCoordinate).toLinearEquiv
        (gauge first coordinate).toLinearEquiv
        (gauge second
          (ambientAtlasTransition period hPeriod first second coordinate)
        ).toLinearEquiv = target) :
    ((ambientOrthonormalAtlasGaugeTransform period hPeriod reduction gauge)
      |>.orthogonalTransition period hPeriod first second coordinate
        hCoordinate).toLinearEquiv = target := by
  rw [ambientOrthonormalAtlasGaugeTransform_orthogonalTransition]
  exact hTarget

end

end P0EFTJanusMappingTorusAmbientOrthonormalVertexGaugeTransform4D
end JanusFormal
