import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LiftedFrameContinuity4D

/-! Genuine deck equivariance of lifted quotient fields and their radial coordinates. -/
namespace JanusFormal.P0EFTJanusProgramPT12LiftedFrameDeck4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusGenuineStableRadialTangentTrivialization4D
open P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D
open P0EFTJanusProgramPT12LiftedFrameContinuity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveCover := MappingTorusCover (reflectedSphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem quotientProjectionDerivative_deckGenerator
    (point : EffectiveCover period hPeriod) (vector : TangentSpace coverModelWithCorners point) :
    mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (reflectedSphereData period hPeriod)) ((1 : Int) +ᵥ point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          ((1 : Int) +ᵥ ·) point vector) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (reflectedSphereData period hPeriod)) point vector := by
  have hProjection : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (mappingTorusMk (reflectedSphereData period hPeriod)) ((1 : Int) +ᵥ point) :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff.mdifferentiableAt (by simp)
  have hDeck : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      ((1 : Int) +ᵥ ·) point :=
    (reflectedSphereCover_deck_contMDiff period hPeriod 1).mdifferentiableAt (by simp)
  have hComposite := mfderiv_comp point hProjection hDeck
  have hMap : (mappingTorusMk (reflectedSphereData period hPeriod)) ∘ ((1 : Int) +ᵥ ·) =
      mappingTorusMk (reflectedSphereData period hPeriod) := by
    funext current
    exact (mappingTorusMk_eq_iff_exists_vadd (reflectedSphereData period hPeriod) _ _).2 ⟨1, rfl⟩
  calc
    _ = mfderiv coverModelWithCorners coverModelWithCorners
        ((mappingTorusMk (reflectedSphereData period hPeriod)) ∘ ((1 : Int) +ᵥ ·)) point vector := by
      rw [hComposite]
      rfl
    _ = _ := by rw [hMap]

theorem liftedQuotientTangentField_deckGenerator
    (vector : SmoothTangentField period hPeriod) (point : EffectiveCover period hPeriod) :
    liftedQuotientTangentField period hPeriod vector ((1 : Int) +ᵥ point) =
      mfderiv coverModelWithCorners coverModelWithCorners ((1 : Int) +ᵥ ·) point
        (liftedQuotientTangentField period hPeriod vector point) := by
  apply (quotientProjectionDerivativeEquiv period hPeriod ((1 : Int) +ᵥ point)).injective
  rw [liftedQuotientTangentField_projection]
  change vector (mappingTorusMk (reflectedSphereData period hPeriod) ((1 : Int) +ᵥ point)) =
    mfderiv coverModelWithCorners coverModelWithCorners
      (mappingTorusMk (reflectedSphereData period hPeriod)) ((1 : Int) +ᵥ point)
      (mfderiv coverModelWithCorners coverModelWithCorners ((1 : Int) +ᵥ ·) point
        (liftedQuotientTangentField period hPeriod vector point))
  rw [quotientProjectionDerivative_deckGenerator, ← quotientProjectionDerivativeEquiv_coe]
  change (vector (mappingTorusMk (reflectedSphereData period hPeriod) ((1 : Int) +ᵥ point)) :
    CoverCoordinates) = quotientProjectionDerivativeEquiv period hPeriod point
      (liftedQuotientTangentField period hPeriod vector point)
  rw [liftedQuotientTangentField_projection]
  have hPoint : mappingTorusMk (reflectedSphereData period hPeriod) ((1 : Int) +ᵥ point) =
      mappingTorusMk (reflectedSphereData period hPeriod) point :=
    (mappingTorusMk_eq_iff_exists_vadd (reflectedSphereData period hPeriod) _ _).2 ⟨1, rfl⟩
  rw [hPoint]

theorem liftedQuotientRadialCoordinates_deckGenerator
    (vector : SmoothTangentField period hPeriod) (point : EffectiveCover period hPeriod) :
    liftedQuotientRadialCoordinates period hPeriod vector ((1 : Int) +ᵥ point) =
      P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection
        (liftedQuotientRadialCoordinates period hPeriod vector point) := by
  unfold liftedQuotientRadialCoordinates
  rw [liftedQuotientTangentField_deckGenerator]
  exact genuineStableRadialTangentEquiv_deckGenerator period hPeriod point _

end
end JanusFormal.P0EFTJanusProgramPT12LiftedFrameDeck4D
