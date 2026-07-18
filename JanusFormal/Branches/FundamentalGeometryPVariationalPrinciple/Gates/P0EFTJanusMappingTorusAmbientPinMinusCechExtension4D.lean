import Mathlib.Algebra.Group.AddChar
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinOrientation
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusProjection4D

/-!
# Normal-compatible ambient Pin-minus Cech extension

The ambient mapping torus is nonorientable.  Its real tangent transitions are
therefore lifted through the full twisted `Pin⁻(4)` projection constructed on
the negative Euclidean Clifford algebra, not through the connected Spin map.

Everything independent of an atlas lift is fixed here: the group, projection,
twisted Clifford action, central sign and order-four reflection generator.
The sole residual object is one continuous normalized Cech cocycle lifting the
actual reduced `O(4)` transitions.  Compatibility with the already-constructed
normal `Pin⁻(1) ≃ ZMod 4` principal bundle is imposed by an additive character
and an exact restriction law on throat overlaps.

The reference Clifford reflection axis is not silently identified with the
geometric throat normal.  That identification is precisely the restriction
field of the residual Cech choice below.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D

set_option autoImplicit false

noncomputable section

open Set Topology
open CliffordAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinProjection
open P0EFTJanusMappingTorusAmbientSpinOrientation
open P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

/-- Orientation parity of an arbitrary real linear automorphism. -/
def ambientLinearOrientationParity
    (transition : CoverCoordinates ≃ₗ[Real] CoverCoordinates) : ZMod 2 :=
  if 0 < (((LinearEquiv.det transition : Realˣ) : Real)) then 0 else 1

theorem ambientLinearOrientationParity_eq_one_iff
    (transition : CoverCoordinates ≃ₗ[Real] CoverCoordinates) :
    ambientLinearOrientationParity transition = 1 ↔
      (((LinearEquiv.det transition : Realˣ) : Real)) < 0 := by
  rw [LinearEquiv.coe_det]
  have hNonzero : LinearMap.det (transition : CoverCoordinates →ₗ[Real]
      CoverCoordinates) ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact (LinearEquiv.det transition).ne_zero
  unfold ambientLinearOrientationParity
  by_cases hPositive :
      0 < LinearMap.det (transition : CoverCoordinates →ₗ[Real] CoverCoordinates)
  · have hNotNegative :
        ¬ LinearMap.det (transition : CoverCoordinates →ₗ[Real]
          CoverCoordinates) < 0 :=
      not_lt_of_ge (le_of_lt hPositive)
    simp [hPositive, hNotNegative]
  · have hNonpositive :
        LinearMap.det (transition : CoverCoordinates →ₗ[Real]
          CoverCoordinates) ≤ 0 :=
      le_of_not_gt hPositive
    have hNegative :
        LinearMap.det (transition : CoverCoordinates →ₗ[Real]
          CoverCoordinates) < 0 :=
      lt_of_le_of_ne hNonpositive hNonzero
    simp [hPositive, hNegative]

/-- Exact residual datum.  The topology on the Clifford Pin group is supplied
as the intended Lie-group topology.  All atlas-specific choices, their Cech
law, continuity and their restriction to the normal principal lift live in
this single structure. -/
structure AmbientNormalCompatibleContinuousPinMinusCechChoice
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) where
  transitionLift :
    AmbientCover period hPeriod → AmbientCover period hPeriod →
      CoverModel → AmbientCoordinatePinMinusGroup
  projects_to_transition :
    ∀ first second coordinate
      (hCoordinate :
        coordinate ∈
          (ambientAtlasTransition period hPeriod first second).source),
      ambientPinMinusProjection
          (transitionLift first second coordinate) =
        (reduction.orthogonalTransition period hPeriod first second
          coordinate hCoordinate).toLinearEquiv
  normalized :
    ∀ anchor coordinate
      (_hCoordinate :
        coordinate ∈
          (ambientAtlasTransition period hPeriod anchor anchor).source),
      transitionLift anchor anchor coordinate = 1
  cocycle :
    ∀ first second third coordinate
      (_hFirstSecond :
        coordinate ∈
          (ambientAtlasTransition period hPeriod first second).source)
      (_hSecondThird :
        ambientAtlasTransition period hPeriod first second coordinate ∈
          (ambientAtlasTransition period hPeriod second third).source)
      (_hFirstThird :
        coordinate ∈
          (ambientAtlasTransition period hPeriod first third).source),
      transitionLift second third
          (ambientAtlasTransition period hPeriod first second coordinate) *
          transitionLift first second coordinate =
        transitionLift first third coordinate
  transitionLift_continuousOn : ∀ first second,
    ContinuousOn (transitionLift first second)
      (ambientAtlasTransition period hPeriod first second).source
  normalCharacter_projects_orientation : ∀ phase,
    ambientLinearOrientationParity
        (ambientPinMinusProjection
          (ambientPinMinusReferenceZ4Character phase)) =
      normalPinMinusOrientationReduction phase
  normalComparison :
    ∀ first second base,
      AmbientNormalOrientationComparisonAt period hPeriod first second base
  normalCoordinate_continuous : ∀ first second,
    Continuous (fun base : ThroatBase period hPeriod ↦
      (normalComparison first second base).ambientCoordinate)
  restricts_to_normal :
    ∀ first second base,
      transitionLift
          (fixedThroatCoverInclusion period hPeriod first)
          (fixedThroatCoverInclusion period hPeriod second)
          (normalComparison first second base).ambientCoordinate =
        ambientPinMinusReferenceZ4Character
          (localTransitionWinding period hPeriod first second base : ZMod 4)

/-- Honest frontier: existence of the one normal-compatible continuous Pin
Cech choice above. -/
def AmbientNormalCompatibleContinuousPinMinusCechChoiceExists
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) : Prop :=
  Nonempty (AmbientNormalCompatibleContinuousPinMinusCechChoice
    period hPeriod reduction)

/-- Each chosen lift implements the actual reduced atlas transition through
twisted Clifford conjugation. -/
theorem AmbientNormalCompatibleContinuousPinMinusCechChoice.transition_implements_twisted_action
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈
        (ambientAtlasTransition period hPeriod first second).source)
    (tangent : CoverCoordinates) :
    CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        ((reduction.orthogonalTransition period hPeriod first second
          coordinate hCoordinate).toLinearEquiv tangent) =
      involute
          (choice.transitionLift first second coordinate :
            AmbientPinMinusCliffordAlgebra) *
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm tangent *
        (↑((choice.transitionLift first second coordinate)⁻¹) :
          AmbientPinMinusCliffordAlgebra) := by
  rw [← choice.projects_to_transition first second coordinate hCoordinate]
  exact ambientPinMinusVectorAction_spec
    (choice.transitionLift first second coordinate) tangent

/-- Although global orthogonality of every abstract Pin element is not needed,
every selected atlas lift projects to a genuine `O(4)` transition. -/
theorem AmbientNormalCompatibleContinuousPinMinusCechChoice.selected_transition_is_orthogonal
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈
        (ambientAtlasTransition period hPeriod first second).source)
    (tangent : CoverCoordinates) :
    ambientCoverEuclideanQuadraticForm
        (ambientPinMinusProjection
          (choice.transitionLift first second coordinate) tangent) =
      ambientCoverEuclideanQuadraticForm tangent := by
  rw [choice.projects_to_transition first second coordinate hCoordinate]
  exact (reduction.orthogonalTransition period hPeriod first second
    coordinate hCoordinate).map_app tangent

/-- The normal principal coordinate change is intertwined exactly with the
restriction of the ambient Pin Cech transition. -/
theorem AmbientNormalCompatibleContinuousPinMinusCechChoice.intertwines_normal_coordChange
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (phase : NormalPinMinusOne) :
    ambientPinMinusReferenceZ4Character
        (normalPinMinusCoordChange period hPeriod first second base phase) =
      choice.transitionLift
          (fixedThroatCoverInclusion period hPeriod first)
          (fixedThroatCoverInclusion period hPeriod second)
          (choice.normalComparison first second base).ambientCoordinate *
        ambientPinMinusReferenceZ4Character phase := by
  rw [normalPinMinusCoordChange,
    ambientPinMinusReferenceZ4Character.map_add_eq_mul]
  rw [← choice.restricts_to_normal first second base]

/-- Minimal regularity of the throat restriction follows by composition from
the single continuous Cech choice. -/
theorem AmbientNormalCompatibleContinuousPinMinusCechChoice.throat_restriction_continuous
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (first second : ThroatCover period hPeriod) :
    Continuous (fun base : ThroatBase period hPeriod ↦
      choice.transitionLift
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        (choice.normalComparison first second base).ambientCoordinate) :=
  (choice.transitionLift_continuousOn
      (fixedThroatCoverInclusion period hPeriod first)
      (fixedThroatCoverInclusion period hPeriod second)).comp_continuous
    (choice.normalCoordinate_continuous first second)
    (fun base ↦
      (choice.normalComparison first second base).ambientCoordinate_mem)

/-- On every throat overlap, the projected ambient Pin parity is exactly the
already-constructed normal orientation reduction. -/
theorem AmbientNormalCompatibleContinuousPinMinusCechChoice.projectedParity_eq_normalReduction
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) :
    ambientLinearOrientationParity
        (ambientPinMinusProjection
          (choice.transitionLift
            (fixedThroatCoverInclusion period hPeriod first)
            (fixedThroatCoverInclusion period hPeriod second)
            (choice.normalComparison first second base).ambientCoordinate)) =
      normalPinMinusOrientationReduction
        (localTransitionWinding period hPeriod first second base : ZMod 4) := by
  rw [choice.restricts_to_normal first second base]
  exact choice.normalCharacter_projects_orientation _

/-- The same parity is the parity of the genuine ambient atlas transition,
not an independently postulated sign. -/
theorem AmbientNormalCompatibleContinuousPinMinusCechChoice.projectedParity_eq_ambientAtlasParity
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) :
    ambientLinearOrientationParity
        (ambientPinMinusProjection
          (choice.transitionLift
            (fixedThroatCoverInclusion period hPeriod first)
            (fixedThroatCoverInclusion period hPeriod second)
            (choice.normalComparison first second base).ambientCoordinate)) =
      ambientAtlasOrientationParity period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        (choice.normalComparison first second base).ambientCoordinate
        (choice.normalComparison first second base).ambientCoordinate_mem := by
  rw [AmbientNormalCompatibleContinuousPinMinusCechChoice.projectedParity_eq_normalReduction
      period hPeriod reduction choice
      first second base]
  exact normalPinMinus_reduction_eq_ambientParity period hPeriod
    (choice.normalComparison first second base)

/-- One circuit restricts to the order-four reference generator. -/
theorem AmbientNormalCompatibleContinuousPinMinusCechChoice.oneLoop_transitionLift_eq_referenceGenerator
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (anchor : ThroatCover period hPeriod) :
    choice.transitionLift
        (fixedThroatCoverInclusion period hPeriod anchor)
        (fixedThroatCoverInclusion period hPeriod ((1 : Int) +ᵥ anchor))
        (choice.normalComparison anchor ((1 : Int) +ᵥ anchor)
          (mappingTorusMk (ThroatData period hPeriod) anchor)).ambientCoordinate =
      ambientPinMinusReferenceGenerator := by
  rw [choice.restricts_to_normal anchor ((1 : Int) +ᵥ anchor)
    (mappingTorusMk (ThroatData period hPeriod) anchor)]
  rw [localTransitionWinding_one_loop period hPeriod anchor]
  simpa using ambientPinMinusReferenceZ4Character_one

/-- The normal generator projects with reversing parity. -/
theorem AmbientNormalCompatibleContinuousPinMinusCechChoice.normalGenerator_projectedParity
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction) :
    ambientLinearOrientationParity
        (ambientPinMinusProjection
          (ambientPinMinusReferenceZ4Character 1)) = 1 :=
  (choice.normalCharacter_projects_orientation 1).trans
    one_loop_pinMinus_projects_nontrivially

/-- Hence the normal-compatible generator cannot come from the connected
Spin projection.  This is a Pin conclusion only. -/
theorem AmbientNormalCompatibleContinuousPinMinusCechChoice.normalGenerator_not_spinProjection
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (spin : AmbientCoordinateSpinGroup) :
    ambientPinMinusProjection (ambientPinMinusReferenceZ4Character 1) ≠
      ambientSpinProjection spin := by
  intro hProjection
  have hNegative :
      (((LinearEquiv.det
        (ambientPinMinusProjection
          (ambientPinMinusReferenceZ4Character 1)) : Realˣ) :
          Real)) < 0 :=
    (ambientLinearOrientationParity_eq_one_iff _).1
      (AmbientNormalCompatibleContinuousPinMinusCechChoice.normalGenerator_projectedParity
        period hPeriod reduction choice)
  rw [hProjection, ambientSpinProjection_det] at hNegative
  norm_num at hNegative

end

end P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D
end JanusFormal
