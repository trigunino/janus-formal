import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D

/-!
# Exact reference-winding frontier for the ambient Pin-minus Cech choice

The reference `ZMod 4` character already supplies normalization and the
multiplicative lift of an additive deck-winding cocycle.  This gate separates
that topological input from the one genuinely metric-dependent statement:
the chosen orthonormal reduction must turn every reduced `O(4)` transition
into the reference reflection raised to the actual overlap winding.

No such canonical orthonormal reduction is currently constructed.  The exact
missing equality is isolated as
`AmbientReferenceWindingOrthogonalReductionLaw`; all consequences for the
existing ambient Cech-choice interface are proved from it.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusReferenceWindingFrontier4D

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev AmbientBase := MappingTorus (AmbientData period hPeriod)
private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

private abbrev ambientProjectionIsLocalHomeomorph :
    IsLocalHomeomorph (mappingTorusMk (AmbientData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap (AmbientData period hPeriod)).isLocalHomeomorph

/-- Integer overlap winding attached to the actual quotient local sections.
Besides the Cech laws used below, `realizes_deck` records that this is not an
abstract parity label: it is the deck transformation relating the two real
local inverses at the quotient point represented by the transition
coordinate. -/
structure AmbientReferenceWindingCechData
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup] where
  transitionWinding :
    AmbientCover period hPeriod → AmbientCover period hPeriod →
      CoverModel → Int
  realizes_deck :
    ∀ first second coordinate
      (_hCoordinate :
        coordinate ∈
          (ambientAtlasTransition period hPeriod first second).source),
      let base :=
        (ambientQuotientLocalChart period hPeriod first).symm coordinate
      transitionWinding first second coordinate +ᵥ
          (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
            first base =
        (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
          second base
  normalized :
    ∀ anchor coordinate
      (_hCoordinate :
        coordinate ∈
          (ambientAtlasTransition period hPeriod anchor anchor).source),
      transitionWinding anchor anchor coordinate = 0
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
      transitionWinding second third
          (ambientAtlasTransition period hPeriod first second coordinate) +
          transitionWinding first second coordinate =
        transitionWinding first third coordinate
  transitionCharacter_continuousOn : ∀ first second,
    ContinuousOn
      (fun coordinate ↦
        ambientPinMinusReferenceZ4Character
          (transitionWinding first second coordinate : ZMod 4))
      (ambientAtlasTransition period hPeriod first second).source

/-- The normal restriction is kept separate because the current upstream
Cech interface asks for a comparison at every throat base point, rather than
only on the overlap of the two throat charts.  This is an independent atlas
domain obligation, not part of the `O(4)` reduction law. -/
structure AmbientReferenceWindingNormalComparison
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (winding : AmbientReferenceWindingCechData period hPeriod) where
  normalComparison :
    ∀ first second base,
      AmbientNormalOrientationComparisonAt period hPeriod first second base
  normalCoordinate_continuous : ∀ first second,
    Continuous (fun base : ThroatBase period hPeriod ↦
      (normalComparison first second base).ambientCoordinate)
  restricts_to_normal_winding :
    ∀ first second base,
      winding.transitionWinding
          (fixedThroatCoverInclusion period hPeriod first)
          (fixedThroatCoverInclusion period hPeriod second)
          (normalComparison first second base).ambientCoordinate =
        localTransitionWinding period hPeriod first second base

/-- Domain-correct normal comparison.  The coordinate is totalized only to
state continuity conveniently; every geometric assertion is restricted to
the genuine intersection of the two throat chart domains. -/
structure AmbientReferenceWindingNormalComparisonOnOverlap
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (winding : AmbientReferenceWindingCechData period hPeriod) where
  normalCoordinate :
    ThroatCover period hPeriod → ThroatCover period hPeriod →
      ThroatBase period hPeriod → CoverModel
  normalCoordinate_continuousOn : ∀ first second,
    ContinuousOn (normalCoordinate first second)
      (normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second)
  ambientCoordinate_mem :
    ∀ first second base
      (_hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second),
      normalCoordinate first second base ∈
        (ambientAtlasTransition period hPeriod
          (fixedThroatCoverInclusion period hPeriod first)
          (fixedThroatCoverInclusion period hPeriod second)).source
  parity_eq_normal :
    ∀ first second base
      (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second),
      ambientAtlasOrientationParity period hPeriod
          (fixedThroatCoverInclusion period hPeriod first)
          (fixedThroatCoverInclusion period hPeriod second)
          (normalCoordinate first second base)
          (ambientCoordinate_mem first second base hBase) =
        normalPinMinusOrientationReduction
          (localTransitionWinding period hPeriod first second base : ZMod 4)
  restricts_to_normal_winding :
    ∀ first second base
      (_hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second),
      winding.transitionWinding
          (fixedThroatCoverInclusion period hPeriod first)
          (fixedThroatCoverInclusion period hPeriod second)
          (normalCoordinate first second base) =
        localTransitionWinding period hPeriod first second base

/-- Smallest metric-dependent lemma still missing.  It says exactly that the
reduced `O(4)` transition is the projection of the reference Pin-minus phase
of the actual deck winding. -/
def AmbientReferenceWindingOrthogonalReductionLaw
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (winding : AmbientReferenceWindingCechData period hPeriod) : Prop :=
  ∀ first second coordinate
    (hCoordinate :
      coordinate ∈
        (ambientAtlasTransition period hPeriod first second).source),
    ambientPinMinusProjection
        (ambientPinMinusReferenceZ4Character
          (winding.transitionWinding first second coordinate : ZMod 4)) =
      (reduction.orthogonalTransition period hPeriod first second
        coordinate hCoordinate).toLinearEquiv

/-- Purely algebraic orientation character law, independent of the atlas and
its orthonormal reduction. -/
def AmbientReferenceCharacterOrientationLaw : Prop :=
  ∀ phase : ZMod 4,
    ambientLinearOrientationParity
        (ambientPinMinusProjection
          (ambientPinMinusReferenceZ4Character phase)) =
      normalPinMinusOrientationReduction phase

/-- The reference Clifford generator and its central square already prove the
orientation character law; it is not an additional atlas hypothesis. -/
theorem ambientReferenceCharacterOrientationLaw :
    AmbientReferenceCharacterOrientationLaw := by
  intro phase
  have hCases : phase.val = 0 ∨ phase.val = 1 ∨
      phase.val = 2 ∨ phase.val = 3 := by
    have hBound := phase.val_lt
    omega
  rcases hCases with hValue | hValue | hValue | hValue
  all_goals
    rw [← ZMod.natCast_zmod_val phase, hValue]
    simp [ambientLinearOrientationParity,
      normalPinMinusOrientationReduction,
      ambientPinMinusProjection_referenceGenerator,
      ambientPinMinusReferenceReflection_det] <;> norm_num <;> decide

/-- Corrected overlap-level Pin-minus choice.  Unlike the older total normal
comparison interface, this object never asks a transition coordinate outside
the intersection where that transition is defined. -/
structure AmbientReferenceWindingPinMinusCechChoiceOnOverlap
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) where
  winding : AmbientReferenceWindingCechData period hPeriod
  normal : AmbientReferenceWindingNormalComparisonOnOverlap
    period hPeriod winding
  reductionLaw : AmbientReferenceWindingOrthogonalReductionLaw
    period hPeriod reduction winding

def AmbientReferenceWindingPinMinusCechChoiceOnOverlapExists
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) : Prop :=
  Nonempty (AmbientReferenceWindingPinMinusCechChoiceOnOverlap
    period hPeriod reduction)

theorem ambientReferenceWindingPinMinusCechChoiceOnOverlapExists_of_reductionLaw
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (winding : AmbientReferenceWindingCechData period hPeriod)
    (normal : AmbientReferenceWindingNormalComparisonOnOverlap
      period hPeriod winding)
    (hReduction : AmbientReferenceWindingOrthogonalReductionLaw
      period hPeriod reduction winding) :
    AmbientReferenceWindingPinMinusCechChoiceOnOverlapExists
      period hPeriod reduction :=
  ⟨{ winding := winding, normal := normal, reductionLaw := hReduction }⟩

/-- Selected lift of the corrected choice. -/
def AmbientReferenceWindingPinMinusCechChoiceOnOverlap.transitionLift
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientReferenceWindingPinMinusCechChoiceOnOverlap
      period hPeriod reduction)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel) : AmbientCoordinatePinMinusGroup :=
  ambientPinMinusReferenceZ4Character
    (choice.winding.transitionWinding first second coordinate : ZMod 4)

theorem AmbientReferenceWindingPinMinusCechChoiceOnOverlap.projects_to_transition
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientReferenceWindingPinMinusCechChoiceOnOverlap
      period hPeriod reduction)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ambientPinMinusProjection
        (choice.transitionLift period hPeriod reduction first second coordinate) =
      (reduction.orthogonalTransition period hPeriod first second coordinate
        hCoordinate).toLinearEquiv :=
  choice.reductionLaw first second coordinate hCoordinate

theorem AmbientReferenceWindingPinMinusCechChoiceOnOverlap.normalized
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientReferenceWindingPinMinusCechChoiceOnOverlap
      period hPeriod reduction)
    (anchor : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod anchor anchor).source) :
    choice.transitionLift period hPeriod reduction anchor anchor coordinate = 1 := by
  rw [AmbientReferenceWindingPinMinusCechChoiceOnOverlap.transitionLift,
    choice.winding.normalized anchor coordinate hCoordinate]
  simp

theorem AmbientReferenceWindingPinMinusCechChoiceOnOverlap.cocycle
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientReferenceWindingPinMinusCechChoiceOnOverlap
      period hPeriod reduction)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird : coordinate ∈
      (ambientAtlasTransition period hPeriod first third).source) :
    choice.transitionLift period hPeriod reduction second third
          (ambientAtlasTransition period hPeriod first second coordinate) *
        choice.transitionLift period hPeriod reduction first second coordinate =
      choice.transitionLift period hPeriod reduction first third coordinate := by
  rw [AmbientReferenceWindingPinMinusCechChoiceOnOverlap.transitionLift,
    AmbientReferenceWindingPinMinusCechChoiceOnOverlap.transitionLift,
    AmbientReferenceWindingPinMinusCechChoiceOnOverlap.transitionLift,
    ← ambientPinMinusReferenceZ4Character.map_add_eq_mul]
  apply congrArg ambientPinMinusReferenceZ4Character
  have hWinding := choice.winding.cocycle first second third coordinate
    hFirstSecond hSecondThird hFirstThird
  simpa using congrArg (fun value : Int ↦ (value : ZMod 4)) hWinding

theorem AmbientReferenceWindingPinMinusCechChoiceOnOverlap.transitionLift_continuousOn
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientReferenceWindingPinMinusCechChoiceOnOverlap
      period hPeriod reduction)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (choice.transitionLift period hPeriod reduction first second)
      (ambientAtlasTransition period hPeriod first second).source :=
  choice.winding.transitionCharacter_continuousOn first second

theorem AmbientReferenceWindingPinMinusCechChoiceOnOverlap.restricts_to_normal
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientReferenceWindingPinMinusCechChoiceOnOverlap
      period hPeriod reduction)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second) :
    choice.transitionLift period hPeriod reduction
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        (choice.normal.normalCoordinate first second base) =
      ambientPinMinusReferenceZ4Character
        (localTransitionWinding period hPeriod first second base : ZMod 4) := by
  rw [AmbientReferenceWindingPinMinusCechChoiceOnOverlap.transitionLift,
    choice.normal.restricts_to_normal_winding first second base hBase]

theorem AmbientReferenceWindingPinMinusCechChoiceOnOverlap.projectedParity_eq_normalReduction
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientReferenceWindingPinMinusCechChoiceOnOverlap
      period hPeriod reduction)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second) :
    ambientLinearOrientationParity
        (ambientPinMinusProjection
          (choice.transitionLift period hPeriod reduction
            (fixedThroatCoverInclusion period hPeriod first)
            (fixedThroatCoverInclusion period hPeriod second)
            (choice.normal.normalCoordinate first second base))) =
      normalPinMinusOrientationReduction
        (localTransitionWinding period hPeriod first second base : ZMod 4) := by
  rw [choice.restricts_to_normal period hPeriod reduction first second base hBase]
  exact ambientReferenceCharacterOrientationLaw _

/-- The exact reduction law promotes the reference winding character to the
full existing normal-compatible continuous Cech-choice interface. -/
def ambientNormalCompatibleContinuousPinMinusCechChoiceOfReferenceWinding
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (winding : AmbientReferenceWindingCechData period hPeriod)
    (normal : AmbientReferenceWindingNormalComparison
      period hPeriod winding)
    (hReduction : AmbientReferenceWindingOrthogonalReductionLaw
      period hPeriod reduction winding)
    (hOrientation : AmbientReferenceCharacterOrientationLaw) :
    AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction where
  transitionLift first second coordinate :=
    ambientPinMinusReferenceZ4Character
      (winding.transitionWinding first second coordinate : ZMod 4)
  projects_to_transition first second coordinate hCoordinate :=
    hReduction first second coordinate hCoordinate
  normalized anchor coordinate hCoordinate := by
    rw [winding.normalized anchor coordinate hCoordinate]
    simp
  cocycle first second third coordinate hFirstSecond hSecondThird hFirstThird := by
    rw [← ambientPinMinusReferenceZ4Character.map_add_eq_mul]
    apply congrArg ambientPinMinusReferenceZ4Character
    have hWinding := winding.cocycle first second third coordinate
      hFirstSecond hSecondThird hFirstThird
    simpa using congrArg (fun value : Int ↦ (value : ZMod 4)) hWinding
  transitionLift_continuousOn :=
    winding.transitionCharacter_continuousOn
  normalCharacter_projects_orientation := hOrientation
  normalComparison := normal.normalComparison
  normalCoordinate_continuous := normal.normalCoordinate_continuous
  restricts_to_normal first second base := by
    rw [normal.restricts_to_normal_winding first second base]

/-- Existential closure of the conditional ambient Pin-minus frontier. -/
theorem ambientNormalCompatibleContinuousPinMinusCechChoiceExists_of_referenceWinding
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (winding : AmbientReferenceWindingCechData period hPeriod)
    (normal : AmbientReferenceWindingNormalComparison
      period hPeriod winding)
    (hReduction : AmbientReferenceWindingOrthogonalReductionLaw
      period hPeriod reduction winding)
    (hOrientation : AmbientReferenceCharacterOrientationLaw) :
    AmbientNormalCompatibleContinuousPinMinusCechChoiceExists
      period hPeriod reduction :=
  ⟨ambientNormalCompatibleContinuousPinMinusCechChoiceOfReferenceWinding
    period hPeriod reduction winding normal hReduction hOrientation⟩

/-- Convenient closure with the now-proved reference orientation character;
only the actual winding data, the normal-domain comparison and the exact
`O(4)` reduction equality remain. -/
theorem ambientNormalCompatibleContinuousPinMinusCechChoiceExists_of_referenceWinding_reduction
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (winding : AmbientReferenceWindingCechData period hPeriod)
    (normal : AmbientReferenceWindingNormalComparison
      period hPeriod winding)
    (hReduction : AmbientReferenceWindingOrthogonalReductionLaw
      period hPeriod reduction winding) :
    AmbientNormalCompatibleContinuousPinMinusCechChoiceExists
      period hPeriod reduction :=
  ambientNormalCompatibleContinuousPinMinusCechChoiceExists_of_referenceWinding
    period hPeriod reduction winding normal hReduction
      ambientReferenceCharacterOrientationLaw

/-- Under the exact reduction law, each selected lift is literally the
reference Pin-minus character of the true overlap deck winding. -/
@[simp] theorem ambientNormalCompatibleContinuousPinMinusCechChoiceOfReferenceWinding_transitionLift
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (winding : AmbientReferenceWindingCechData period hPeriod)
    (normal : AmbientReferenceWindingNormalComparison
      period hPeriod winding)
    (hReduction : AmbientReferenceWindingOrthogonalReductionLaw
      period hPeriod reduction winding)
    (hOrientation : AmbientReferenceCharacterOrientationLaw)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel) :
    (ambientNormalCompatibleContinuousPinMinusCechChoiceOfReferenceWinding
      period hPeriod reduction winding normal hReduction hOrientation).transitionLift
        first second coordinate =
      ambientPinMinusReferenceZ4Character
        (winding.transitionWinding first second coordinate : ZMod 4) :=
  rfl

end

end P0EFTJanusMappingTorusAmbientPinMinusReferenceWindingFrontier4D
end JanusFormal
