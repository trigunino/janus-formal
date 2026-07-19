import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientAtlasRadialTangentTransition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusStableRadialReferenceConjugacy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalReferenceOrthogonalCocycle4D

/-!
# Reference form of the genuine radial atlas transition

The fixed coordinate split conjugates every integer power of the genuine
ambient deck reflection to the canonical reference orthogonal phase.  Applied
to the differentiated overlap law, this identifies the true atlas Jacobian in
the genuine radial coordinate frames.  Smooth dependence of these frames on
the chart coordinate is not asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientAtlasRadialReferenceTransition4D

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceOrthogonalCocycle4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusGenuineStableRadialTangentTrivialization4D
open P0EFTJanusMappingTorusAmbientAtlasRadialTangentTransition4D
open P0EFTJanusMappingTorusStableRadialReferenceConjugacy4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

private local instance ambientCoverChartedSpace :
    ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance ambientCoverIsManifold :
    IsManifold coverModelWithCorners ω (AmbientCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private abbrev ambientReflection : EuclideanR4 ≃L[Real] EuclideanR4 :=
  P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection
    |>.toContinuousLinearEquiv

private abbrev referenceReflection :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  ambientPinMinusReferenceOrthogonalIsometry.toLinearEquiv

private theorem ambientReflection_mul_self :
    ambientReflection * ambientReflection = 1 := by
  apply ContinuousLinearEquiv.ext
  funext vector
  exact
    P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection_involutive
      vector

private theorem ambientReflection_inv :
    ambientReflection⁻¹ = ambientReflection :=
  inv_eq_of_mul_eq_one_right ambientReflection_mul_self

private theorem referenceReflection_mul_self :
    referenceReflection * referenceReflection = 1 := by
  apply LinearEquiv.ext
  intro vector
  simp [referenceReflection, ambientPinMinusReferenceOrthogonalIsometry,
    ambientPinMinusReferenceReflection_apply]

private theorem referenceReflection_inv :
    referenceReflection⁻¹ = referenceReflection :=
  inv_eq_of_mul_eq_one_right referenceReflection_mul_self

private theorem stableRadialReferenceEquiv_ambientReflection
    (vector : EuclideanR4) :
    stableRadialReferenceEquiv (ambientReflection vector) =
      referenceReflection (stableRadialReferenceEquiv vector) := by
  change stableRadialReferenceEquiv
      (P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection
        vector) =
    ambientPinMinusReferenceReflection (stableRadialReferenceEquiv vector)
  exact stableRadialReferenceEquiv_euclideanReflection vector

private theorem ambientDeckOperator_add_one_apply
    (winding : Int) (vector : EuclideanR4) :
    genuineStableRadialDeckOperator (winding + 1) vector =
      ambientReflection (genuineStableRadialDeckOperator winding vector) := by
  change (ambientReflection ^ (winding + 1)) vector =
    ambientReflection ((ambientReflection ^ winding) vector)
  rw [show winding + 1 = 1 + winding by omega, zpow_one_add]
  rfl

private theorem ambientDeckOperator_sub_one_apply
    (winding : Int) (vector : EuclideanR4) :
    genuineStableRadialDeckOperator (winding - 1) vector =
      ambientReflection (genuineStableRadialDeckOperator winding vector) := by
  change (ambientReflection ^ (winding - 1)) vector =
    ambientReflection ((ambientReflection ^ winding) vector)
  rw [show winding - 1 = (-1 : Int) + winding by omega, zpow_add]
  simp only [zpow_neg, zpow_one, ambientReflection_inv]
  rfl

private theorem referenceDeckOperator_add_one_apply
    (winding : Int) (vector : CoverCoordinates) :
    (referenceReflection ^ (winding + 1)) vector =
      referenceReflection ((referenceReflection ^ winding) vector) := by
  rw [show winding + 1 = 1 + winding by omega, zpow_one_add]
  rfl

private theorem referenceDeckOperator_sub_one_apply
    (winding : Int) (vector : CoverCoordinates) :
    (referenceReflection ^ (winding - 1)) vector =
      referenceReflection ((referenceReflection ^ winding) vector) := by
  rw [show winding - 1 = (-1 : Int) + winding by omega, zpow_add]
  simp only [zpow_neg, zpow_one, referenceReflection_inv]
  rfl

/-- The fixed reference split intertwines every positive or negative deck
winding with the corresponding power of the reference reflection. -/
theorem stableRadialReferenceEquiv_deckOperator
    (winding : Int) (vector : EuclideanR4) :
    stableRadialReferenceEquiv
        (genuineStableRadialDeckOperator winding vector) =
      (referenceReflection ^ winding) (stableRadialReferenceEquiv vector) := by
  refine Int.inductionOn' winding 0 ?_ (fun current _ ih ↦ ?_)
      (fun current _ ih ↦ ?_)
  · change stableRadialReferenceEquiv ((ambientReflection ^ (0 : Int)) vector) =
      (referenceReflection ^ (0 : Int)) (stableRadialReferenceEquiv vector)
    rw [zpow_zero, zpow_zero]
    rfl
  · rw [ambientDeckOperator_add_one_apply,
      stableRadialReferenceEquiv_ambientReflection, ih,
      referenceDeckOperator_add_one_apply]
  · rw [ambientDeckOperator_sub_one_apply,
      stableRadialReferenceEquiv_ambientReflection, ih,
      referenceDeckOperator_sub_one_apply]

/-- The preceding power is exactly the canonical `ZMod 4` orthogonal phase
selected by the same integer winding. -/
theorem stableRadialReferenceEquiv_deckOperator_referencePhase
    (winding : Int) (vector : EuclideanR4) :
    stableRadialReferenceEquiv
        (genuineStableRadialDeckOperator winding vector) =
      (ambientPinMinusReferenceZ4OrthogonalIsometry
        (winding : ZMod 4)).toLinearEquiv
          (stableRadialReferenceEquiv vector) := by
  rw [ambientPinMinusReferenceZ4OrthogonalIsometry_intCast]
  exact stableRadialReferenceEquiv_deckOperator winding vector

/-- Genuine radial reference frame on the target of a real cover chart. -/
def ambientRadialReferenceCoordinateFrame
    (anchor : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈ (chartAt CoverModel anchor).target) :
    TangentSpace coverModelWithCorners coordinate ≃L[Real] CoverCoordinates :=
  ((((mdifferentiable_chart (I := coverModelWithCorners) anchor).symm
      |>.mfderiv hCoordinate).trans
        (genuineStableRadialTangentEquiv period hPeriod
          ((chartAt CoverModel anchor).symm coordinate))).trans
    stableRadialReferenceEquiv)

@[simp] theorem ambientRadialReferenceCoordinateFrame_apply
    (anchor : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈ (chartAt CoverModel anchor).target)
    (vector : TangentSpace coverModelWithCorners coordinate) :
    ambientRadialReferenceCoordinateFrame period hPeriod anchor coordinate
        hCoordinate vector =
      stableRadialReferenceEquiv
        (genuineStableRadialTangentEquiv period hPeriod
          ((chartAt CoverModel anchor).symm coordinate)
          (mfderiv coverModelWithCorners coverModelWithCorners
            (chartAt CoverModel anchor).symm coordinate vector)) :=
  rfl

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

/-- In the genuine radial reference coordinate frames, the derivative of the
actual atlas transition is precisely the canonical reference `O(4)` phase of
the true overlap winding. -/
theorem ambientAtlasTangentTransition_radialReferencePhase
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (vector : TangentSpace coverModelWithCorners coordinate) :
    ambientRadialReferenceCoordinateFrame period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate)
        (transition_mem_secondCoverChart_target period hPeriod
          first second coordinate hCoordinate)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (ambientAtlasTransition period hPeriod first second)
          coordinate vector) =
      (canonicalAmbientReferenceOrthogonalTransition period hPeriod
        first second coordinate).toLinearEquiv
        (ambientRadialReferenceCoordinateFrame period hPeriod first coordinate
          (coordinate_mem_firstCoverChart_target period hPeriod
            first second coordinate hCoordinate) vector) := by
  rw [ambientRadialReferenceCoordinateFrame_apply,
    ambientRadialReferenceCoordinateFrame_apply,
    ambientAtlasTangentTransition_radialDeckOperator period hPeriod
      first second coordinate hCoordinate vector]
  unfold canonicalAmbientReferenceOrthogonalTransition
  exact stableRadialReferenceEquiv_deckOperator_referencePhase
    (ambientTransitionWinding period hPeriod first second coordinate)
    (genuineStableRadialTangentEquiv period hPeriod
      ((chartAt CoverModel first).symm coordinate)
      (mfderiv coverModelWithCorners coverModelWithCorners
        (chartAt CoverModel first).symm coordinate vector))

end

end P0EFTJanusMappingTorusAmbientAtlasRadialReferenceTransition4D
end JanusFormal
