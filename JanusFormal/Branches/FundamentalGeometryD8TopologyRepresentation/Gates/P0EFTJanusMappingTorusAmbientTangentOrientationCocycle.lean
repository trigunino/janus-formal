import Mathlib.LinearAlgebra.QuadraticForm.Radical
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle

/-!
# Ambient tangent orientation data from the real quotient atlas

This gate starts from the actual local-section charts of the analytic ambient
mapping torus.  Their coordinate changes give genuine partial
diffeomorphisms, hence invertible tangent maps and nonzero real determinants.
The determinant sign is the orientation cocycle presently available from the
ambient tangent atlas.

The existing `Pin⁻(1)` bundle lifts only the normal-line sign cocycle.  No
ambient tangent quadratic-form reduction, orthonormal frame bundle, or
Pin/SpinC covering cocycle has been constructed, so none is promoted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientTangentOrientationCocycle

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod

private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

private abbrev AmbientBase := MappingTorus (AmbientData period hPeriod)

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

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

/-- Actual quotient chart obtained by composing a covering local section with
the real chart of the ambient cover. -/
def ambientQuotientLocalChart (anchor : AmbientCover period hPeriod) :
    OpenPartialHomeomorph (AmbientBase period hPeriod) CoverModel :=
  let projection :=
    (mappingTorusMk_isCoveringMap (AmbientData period hPeriod)).isLocalHomeomorph
  (projection.localInverseAt anchor).trans (chartAt CoverModel anchor)

/-- Actual coordinate change between two local-section charts of the ambient
four-manifold. -/
def ambientAtlasTransition
    (first second : AmbientCover period hPeriod) :
    OpenPartialHomeomorph CoverModel CoverModel :=
  (ambientQuotientLocalChart period hPeriod first).symm.trans
    (ambientQuotientLocalChart period hPeriod second)

/-- The real ambient transition belongs to the analytic structure groupoid.
This uses the full ambient deck action, not the rank-one normal cocycle. -/
theorem ambientAtlasTransition_mem_contDiffGroupoid
    (first second : AmbientCover period hPeriod) :
    ambientAtlasTransition period hPeriod first second ∈
      contDiffGroupoid ω coverModelWithCorners := by
  exact localSectionChart_transition_mem_groupoid
    coverModelWithCorners ω (AmbientData period hPeriod)
      (reflectedSphereCover_deck_contMDiff period hPeriod) first second

/-- The actual ambient coordinate change, with its analytic inverse, packaged
as a partial diffeomorphism. -/
def ambientAtlasPartialDiffeomorph
    (first second : AmbientCover period hPeriod) :
    PartialDiffeomorph coverModelWithCorners coverModelWithCorners
      CoverModel CoverModel ω where
  __ := ambientAtlasTransition period hPeriod first second
  contMDiffOn_toFun := contMDiffOn_of_mem_contDiffGroupoid
    (ambientAtlasTransition_mem_contDiffGroupoid period hPeriod first second)
  contMDiffOn_invFun := contMDiffOn_of_mem_contDiffGroupoid
    ((contDiffGroupoid ω coverModelWithCorners).symm
      (ambientAtlasTransition_mem_contDiffGroupoid
        period hPeriod first second))

/-- Invertible derivative of an actual ambient atlas transition at a point of
its source. -/
def ambientAtlasTangentTransition
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    ContinuousLinearEquiv (RingHom.id Real)
      CoverCoordinates CoverCoordinates :=
  ((ambientAtlasPartialDiffeomorph period hPeriod first second).isLocalDiffeomorphAt
      (I := coverModelWithCorners) (J := coverModelWithCorners)
      (n := ω)
      hCoordinate).mfderivToContinuousLinearEquiv (by simp)

@[simp] theorem ambientAtlasTangentTransition_coe
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    (ambientAtlasTangentTransition period hPeriod first second
        coordinate hCoordinate : CoverCoordinates →L[Real] CoverCoordinates) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (ambientAtlasTransition period hPeriod first second) coordinate :=
  rfl

/-- Real Jacobian determinant of the actual ambient tangent transition. -/
def ambientAtlasDeterminant
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) : Real :=
  (LinearEquiv.det
    ((ambientAtlasTangentTransition period hPeriod first second
      coordinate hCoordinate).toLinearEquiv) : Realˣ)

/-- Atlas tangent transitions have nonzero determinant because they are
derivatives of local diffeomorphisms. -/
theorem ambientAtlasDeterminant_ne_zero
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    ambientAtlasDeterminant period hPeriod first second coordinate hCoordinate ≠ 0 :=
  (LinearEquiv.det
    ((ambientAtlasTangentTransition period hPeriod first second
      coordinate hCoordinate).toLinearEquiv)).ne_zero

/-- Orientation parity extracted from the sign of the actual ambient
Jacobian: `0` for positive determinant and `1` for negative determinant. -/
def ambientAtlasOrientationParity
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    ZMod 2 :=
  if 0 < ambientAtlasDeterminant period hPeriod first second coordinate hCoordinate
  then 0 else 1

theorem ambientAtlasOrientationParity_eq_zero_iff
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    ambientAtlasOrientationParity period hPeriod first second coordinate hCoordinate = 0 ↔
      0 < ambientAtlasDeterminant period hPeriod first second coordinate hCoordinate := by
  unfold ambientAtlasOrientationParity
  split_ifs with hSign <;> simp [hSign]

theorem ambientAtlasOrientationParity_eq_one_iff
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    ambientAtlasOrientationParity period hPeriod first second coordinate hCoordinate = 1 ↔
      ambientAtlasDeterminant period hPeriod first second coordinate hCoordinate < 0 := by
  have hNonzero := ambientAtlasDeterminant_ne_zero period hPeriod
    first second coordinate hCoordinate
  unfold ambientAtlasOrientationParity
  by_cases hPositive :
      0 < ambientAtlasDeterminant period hPeriod first second coordinate hCoordinate
  · have hNotNegative :
        ¬ ambientAtlasDeterminant period hPeriod first second coordinate hCoordinate < 0 :=
      not_lt_of_ge (le_of_lt hPositive)
    simp [hPositive, hNotNegative]
  · have hNonpositive :
        ambientAtlasDeterminant period hPeriod first second coordinate hCoordinate ≤ 0 :=
      le_of_not_gt hPositive
    have hNegative :
        ambientAtlasDeterminant period hPeriod first second coordinate hCoordinate < 0 :=
      lt_of_le_of_ne hNonpositive hNonzero
    simp [hPositive, hNegative]

theorem ambientAtlasOrientationParity_eq_zero_or_one
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    ambientAtlasOrientationParity period hPeriod first second coordinate hCoordinate = 0 ∨
      ambientAtlasOrientationParity period hPeriod first second coordinate hCoordinate = 1 := by
  unfold ambientAtlasOrientationParity
  split_ifs <;> simp

/-- The exact algebraic metric-reduction contract still needed before the
ambient atlas transitions can even be regarded as orthogonal transitions.
Smoothness and a Pin/SpinC Cech lift would be further obligations. -/
structure AmbientTangentQuadraticAtlasContract where
  form : AmbientCover period hPeriod → CoverModel →
    QuadraticForm Real CoverCoordinates
  nondegenerate : ∀ anchor coordinate, (form anchor coordinate).Nondegenerate
  transition_isometry :
    ∀ first second coordinate
      (hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
      tangent,
      form second (ambientAtlasTransition period hPeriod first second coordinate)
          (ambientAtlasTangentTransition period hPeriod first second
            coordinate hCoordinate tangent) =
        form first coordinate tangent

/-- Concrete comparison datum required to identify the normal orientation
character with the determinant sign of the full ambient tangent transition.
It deliberately compares the two cocycles instead of identifying their
bundles. -/
structure AmbientNormalOrientationComparisonAt
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) where
  ambientCoordinate : CoverModel
  ambientCoordinate_mem :
    ambientCoordinate ∈
      (ambientAtlasTransition period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)).source
  parity_eq_normal :
    ambientAtlasOrientationParity period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        ambientCoordinate ambientCoordinate_mem =
      normalPinMinusOrientationReduction
        (localTransitionWinding period hPeriod first second base : ZMod 4)

/-- A normal `Pin⁻(1)` transition can be compared with the ambient
orientation only after supplying the explicit determinant comparison above. -/
theorem normalPinMinus_reduction_eq_ambientParity
    {first second : ThroatCover period hPeriod}
    {base : ThroatBase period hPeriod}
    (comparison :
      AmbientNormalOrientationComparisonAt period hPeriod first second base) :
    normalPinMinusOrientationReduction
        (localTransitionWinding period hPeriod first second base : ZMod 4) =
      ambientAtlasOrientationParity period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        comparison.ambientCoordinate comparison.ambientCoordinate_mem :=
  comparison.parity_eq_normal.symm

end

end P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
end JanusFormal
