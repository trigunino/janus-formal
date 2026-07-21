import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCoverLorentzGramRotationKernel4D

/-!
# Smooth cover field in the Lorentz Gram rotation kernel

For a fixed one of the already constructed spatial rotation generators, this
gate packages `A ∘ dι` as a smooth bundle-hom section on the genuine
mapping-torus cover.  Its scalar Lorentz Gram linearization is the zero
function.  The section also satisfies the exact naturality relation for the
deck generator.

Only generator-level deck naturality is asserted here.  No all-winding
descent, quotient complex, or global D8 statement is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCoverLorentzGramRotationSection4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open Bundle
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusCoverLorentzGramFrechet4D
open P0EFTJanusMappingTorusCoverLorentzGramRotationKernel4D
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

/-- `A_axis ∘ dι` varies smoothly as a genuine bundle-hom section. -/
def smoothCoverLorentzGramRotationHom (axis : Fin 3) :=
  postcomposeCoverAmbientDerivativeSection period hPeriod
    (coverAmbientSpatialRotation axis)

@[simp]
theorem smoothCoverLorentzGramRotationHom_apply
    (axis : Fin 3) (point : EffectiveCover period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    smoothCoverLorentzGramRotationHom period hPeriod axis point vector =
      coverAmbientSpatialRotation axis
        (coverAmbientDerivative period hPeriod point vector) := by
  rfl

/-- The scalar Gram linearization of the true cover derivative along the
smooth rotation section, written in the fixed one-jet coordinates. -/
def actualCoverLorentzGramRotationLinearizationField
    (axis : Fin 3) (first second : CoverCoordinates) :
    EffectiveCover period hPeriod → Real :=
  fun point =>
    coverLorentzGramComponentLinearization first second
      (coverAmbientDerivativeCoordinates period hPeriod point)
      (coverLorentzGramRotationDirection axis
        (coverAmbientDerivativeCoordinates period hPeriod point))

/-- Field-level form of `J(dι)(A_axis ∘ dι) = 0` on the genuine
cover. -/
theorem actualCoverLorentzGramRotationLinearizationField_eq_zero
    (axis : Fin 3) (first second : CoverCoordinates) :
    actualCoverLorentzGramRotationLinearizationField period hPeriod axis
        first second = 0 := by
  funext point
  exact actualCoverLorentzGramLinearization_rotation_zero
    period hPeriod axis point first second

/-- The resulting zero scalar field is smooth on the genuine cover. -/
theorem actualCoverLorentzGramRotationLinearizationField_contMDiff
    (axis : Fin 3) (first second : CoverCoordinates) :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (actualCoverLorentzGramRotationLinearizationField period hPeriod axis
        first second) := by
  rw [actualCoverLorentzGramRotationLinearizationField_eq_zero]
  exact contMDiff_const

/-- The lifted spatial rotation commutes with the Euclidean reflection in
the deck generator. -/
theorem euclideanAmbientSpatialRotation_reflection_commutes
    (axis : Fin 3) (point : EuclideanR4) :
    euclideanReflection (euclideanAmbientSpatialRotation axis point) =
      euclideanAmbientSpatialRotation axis (euclideanReflection point) := by
  have hReflection (current : EuclideanR4) :
      WithLp.ofLp (euclideanReflection current) =
        reflectPoint (WithLp.ofLp current) := by
    funext coordinate
    simp [euclideanReflection_apply, reflectPoint]
  apply WithLp.ofLp_injective 2
  rw [hReflection]
  simp only [euclideanAmbientSpatialRotation_apply,
    WithLp.ofLp_toLp]
  rw [hReflection]
  exact ambientSpatialRotation_reflection_commutes axis
    (WithLp.ofLp point)

/-- Consequently the ambient rotation commutes with the full linear part of
the deck generator. -/
theorem coverAmbientSpatialRotation_deckGenerator_commutes
    (axis : Fin 3) (point : CoverAmbientCoordinates) :
    coverAmbientSpatialRotation axis
        (coverAmbientDeckGeneratorLinear point) =
      coverAmbientDeckGeneratorLinear
        (coverAmbientSpatialRotation axis point) := by
  apply Prod.ext
  · exact (euclideanAmbientSpatialRotation_reflection_commutes
      axis point.1).symm
  · rfl

/-- Exact equivariance of the smooth kernel section under the genuine deck
generator.  This is the generator cocycle needed before an all-winding
quotient descent. -/
theorem smoothCoverLorentzGramRotationHom_deckGenerator_natural
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    (smoothCoverLorentzGramRotationHom period hPeriod axis
        ((1 : Int) +ᵥ point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point) =
      coverAmbientDeckGeneratorLinear.comp
        (smoothCoverLorentzGramRotationHom period hPeriod axis point) := by
  apply postcomposeCoverAmbientDerivativeSection_deckGenerator_natural
  apply ContinuousLinearMap.ext
  intro ambientPoint
  exact coverAmbientSpatialRotation_deckGenerator_commutes
    axis ambientPoint

/-- The zero scalar linearization field is invariant under the deck
generator. -/
theorem actualCoverLorentzGramRotationLinearizationField_deckGenerator
    (axis : Fin 3) (first second : CoverCoordinates)
    (point : EffectiveCover period hPeriod) :
    actualCoverLorentzGramRotationLinearizationField period hPeriod axis
        first second ((1 : Int) +ᵥ point) =
      actualCoverLorentzGramRotationLinearizationField period hPeriod axis
        first second point := by
  simp only [actualCoverLorentzGramRotationLinearizationField]
  rw [actualCoverLorentzGramLinearization_rotation_zero,
    actualCoverLorentzGramLinearization_rotation_zero]

end

end P0EFTJanusMappingTorusCoverLorentzGramRotationSection4D
end JanusFormal
