import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCTwistedCechBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D

/-! # Ambient circle bundle from the canonical deck winding

The actual ambient integer overlap winding is evaluated in either quarter-turn
circle character.  This produces a continuous principal `U(1)` bundle core on
the ambient Janus quotient and supplies the circle Cech twist required by the
twisted `PinC(4)` construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientCircleWindingBundle4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusProgramPNormalZ4RootHermitianMetric4D
open P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D
open P0EFTJanusProgramPAmbientPinCCechExtension4D
open P0EFTJanusProgramPAmbientPinCTwistedCechBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

/-- Quarter-turn circle lift of the actual ambient overlap winding. -/
def ambientCircleReferenceTransitionLift
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel) : Circle :=
  normalRootCircleCharacter choice
    (ambientTransitionWinding period hPeriod first second coordinate : ZMod 4)

theorem ambientCircleReferenceTransitionLift_normalized
    (choice : NormalRootChoice)
    (anchor : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod anchor anchor).source) :
    ambientCircleReferenceTransitionLift period hPeriod choice
        anchor anchor coordinate = 1 := by
  unfold ambientCircleReferenceTransitionLift
  have hWinding := (ambientReferenceWindingCechData period hPeriod).normalized
    anchor coordinate hCoordinate
  change ambientTransitionWinding period hPeriod anchor anchor coordinate = 0
    at hWinding
  rw [hWinding]
  simp

theorem ambientCircleReferenceTransitionLift_cocycle
    (choice : NormalRootChoice)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird : coordinate ∈
      (ambientAtlasTransition period hPeriod first third).source) :
    ambientCircleReferenceTransitionLift period hPeriod choice second third
          (ambientAtlasTransition period hPeriod first second coordinate) *
        ambientCircleReferenceTransitionLift period hPeriod choice first second
          coordinate =
      ambientCircleReferenceTransitionLift period hPeriod choice first third
        coordinate := by
  unfold ambientCircleReferenceTransitionLift
  rw [← (normalRootCircleCharacter choice).map_add_eq_mul]
  apply congrArg (normalRootCircleCharacter choice)
  have hWinding := (ambientReferenceWindingCechData period hPeriod).cocycle
    first second third coordinate hFirstSecond hSecondThird hFirstThird
  change ambientTransitionWinding period hPeriod second third
        (ambientAtlasTransition period hPeriod first second coordinate) +
      ambientTransitionWinding period hPeriod first second coordinate =
    ambientTransitionWinding period hPeriod first third coordinate at hWinding
  simpa using congrArg (fun value : Int ↦ (value : ZMod 4)) hWinding

theorem ambientCircleReferenceTransitionLift_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (ambientCircleReferenceTransitionLift period hPeriod choice first second)
      (ambientAtlasTransition period hPeriod first second).source := by
  intro coordinate hCoordinate
  let overlap := (ambientAtlasTransition period hPeriod first second).source
  have hWindingEq : Filter.EventuallyEq (nhdsWithin coordinate overlap)
      (ambientTransitionWinding period hPeriod first second)
      (fun _ ↦ ambientTransitionWinding period hPeriod first second coordinate) :=
    (ambientTransitionWinding_eventuallyEq period hPeriod
      first second coordinate hCoordinate).filter_mono inf_le_left
  have hCharacterEq := hWindingEq.fun_comp
    (fun winding : Int ↦ normalRootCircleCharacter choice (winding : ZMod 4))
  exact (continuousWithinAt_const : ContinuousWithinAt
    (fun _ : CoverModel ↦ normalRootCircleCharacter choice
      (ambientTransitionWinding period hPeriod first second coordinate : ZMod 4))
    overlap coordinate).congr_of_eventuallyEq_of_mem hCharacterEq hCoordinate

private theorem chartCoordinate_mem_transition_source
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (hBase : base ∈ ambientPinMinusBundleBaseSet period hPeriod first ∩
      ambientPinMinusBundleBaseSet period hPeriod second) :
    ambientQuotientLocalChart period hPeriod first base ∈
      (ambientAtlasTransition period hPeriod first second).source := by
  change ambientQuotientLocalChart period hPeriod first base ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).source
  rw [OpenPartialHomeomorph.trans_source]
  refine ⟨(ambientQuotientLocalChart period hPeriod first).map_source hBase.1, ?_⟩
  change (ambientQuotientLocalChart period hPeriod first).symm
      (ambientQuotientLocalChart period hPeriod first base) ∈
    (ambientQuotientLocalChart period hPeriod second).source
  rw [(ambientQuotientLocalChart period hPeriod first).left_inv hBase.1]
  exact hBase.2

private theorem transition_chartCoordinate
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (hBase : base ∈ ambientPinMinusBundleBaseSet period hPeriod first ∩
      ambientPinMinusBundleBaseSet period hPeriod second) :
    ambientAtlasTransition period hPeriod first second
        (ambientQuotientLocalChart period hPeriod first base) =
      ambientQuotientLocalChart period hPeriod second base := by
  change (ambientQuotientLocalChart period hPeriod second)
      ((ambientQuotientLocalChart period hPeriod first).symm
        (ambientQuotientLocalChart period hPeriod first base)) = _
  rw [(ambientQuotientLocalChart period hPeriod first).left_inv hBase.1]

def canonicalAmbientCirclePrincipalCoordChange
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (phase : Circle) : Circle :=
  ambientCircleReferenceTransitionLift period hPeriod choice first second
      (ambientQuotientLocalChart period hPeriod first base) * phase

theorem canonicalAmbientCirclePrincipalCoordChange_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun point : AmbientBase period hPeriod × Circle ↦
        canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
          first second point.1 point.2)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  apply ContinuousOn.mul
  · apply (ambientCircleReferenceTransitionLift_continuousOn
      period hPeriod choice first second).comp
      ((ambientQuotientLocalChart period hPeriod first).continuousOn.comp
        continuousOn_fst (fun point hPoint ↦ hPoint.1.1))
    intro point hPoint
    exact chartCoordinate_mem_transition_source period hPeriod first second
      point.1 ⟨hPoint.1.1, hPoint.1.2⟩
  · exact continuousOn_snd

theorem canonicalAmbientCirclePrincipalTransition_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun base : AmbientBase period hPeriod ↦
        canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
          first second base 1)
      (ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) := by
  have hTransition :=
    (ambientCircleReferenceTransitionLift_continuousOn
      period hPeriod choice first second).comp
      ((ambientQuotientLocalChart period hPeriod first).continuousOn.mono
        (show
          ambientPinMinusBundleBaseSet period hPeriod first ∩
              ambientPinMinusBundleBaseSet period hPeriod second ⊆
            (ambientQuotientLocalChart period hPeriod first).source by
          intro base hBase
          exact hBase.1)) (by
        intro base hBase
        exact chartCoordinate_mem_transition_source period hPeriod first second
          base hBase)
  simp only [canonicalAmbientCirclePrincipalCoordChange, mul_one]
  change ContinuousOn
    (ambientCircleReferenceTransitionLift period hPeriod choice first second ∘
      (ambientQuotientLocalChart period hPeriod first :
        AmbientBase period hPeriod → CoverModel))
    (ambientPinMinusBundleBaseSet period hPeriod first ∩
      ambientPinMinusBundleBaseSet period hPeriod second)
  exact hTransition

/-- Genuine continuous principal circle bundle core selected by the winding. -/
def canonicalAmbientCirclePrincipalBundleCore
    (choice : NormalRootChoice) :
    FiberBundleCore (AmbientCover period hPeriod) (AmbientBase period hPeriod)
      Circle where
  baseSet := ambientPinMinusBundleBaseSet period hPeriod
  isOpen_baseSet := ambientPinMinusBundleBaseSet_isOpen period hPeriod
  indexAt := ambientPinMinusBundleIndexAt period hPeriod
  mem_baseSet_at := mem_ambientPinMinusBundleBaseSet_indexAt period hPeriod
  coordChange := canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
  coordChange_self anchor base hBase phase := by
    unfold canonicalAmbientCirclePrincipalCoordChange
    rw [ambientCircleReferenceTransitionLift_normalized period hPeriod choice
      anchor (ambientQuotientLocalChart period hPeriod anchor base)
      (chartCoordinate_mem_transition_source period hPeriod anchor anchor base
        ⟨hBase, hBase⟩)]
    exact one_mul phase
  continuousOn_coordChange :=
    canonicalAmbientCirclePrincipalCoordChange_continuousOn
      period hPeriod choice
  coordChange_comp first second third base hBase phase := by
    unfold canonicalAmbientCirclePrincipalCoordChange
    have hFirstSecond := chartCoordinate_mem_transition_source period hPeriod
      first second base ⟨hBase.1.1, hBase.1.2⟩
    have hSecondThird := chartCoordinate_mem_transition_source period hPeriod
      second third base ⟨hBase.1.2, hBase.2⟩
    have hFirstThird := chartCoordinate_mem_transition_source period hPeriod
      first third base ⟨hBase.1.1, hBase.2⟩
    have hTransition := transition_chartCoordinate period hPeriod first second
      base ⟨hBase.1.1, hBase.1.2⟩
    have hSecondThird' :
        ambientAtlasTransition period hPeriod first second
            (ambientQuotientLocalChart period hPeriod first base) ∈
          (ambientAtlasTransition period hPeriod second third).source := by
      rw [hTransition]
      exact hSecondThird
    have hCocycle := ambientCircleReferenceTransitionLift_cocycle
      period hPeriod choice first second third
      (ambientQuotientLocalChart period hPeriod first base)
      hFirstSecond hSecondThird' hFirstThird
    rw [← hTransition, ← mul_assoc, hCocycle]

/-- Cech twist extracted from the genuine circle principal core. -/
def canonicalAmbientCircleCechTwist
    (choice : NormalRootChoice) :
    AmbientCircleCechTwist period hPeriod := by
  let core := canonicalAmbientCirclePrincipalBundleCore period hPeriod choice
  exact {
    transition := fun first second base => core.coordChange second first base 1
    transition_self := by
      intro index base hBase
      change base ∈ ambientPinMinusBundleBaseSet period hPeriod index at hBase
      have hBase' : base ∈ core.baseSet index := by
        exact hBase
      exact core.coordChange_self index base hBase' 1
    transition_inverse := by
      intro first second base hFirst hSecond
      change base ∈ ambientPinMinusBundleBaseSet period hPeriod first at hFirst
      change base ∈ ambientPinMinusBundleBaseSet period hPeriod second at hSecond
      have hFirst' : base ∈ core.baseSet first := by
        exact hFirst
      have hSecond' : base ∈ core.baseSet second := by
        exact hSecond
      have hComp := core.coordChange_comp first second first base
        ⟨⟨hFirst', hSecond'⟩, hFirst'⟩ 1
      rw [core.coordChange_self first base hFirst' 1] at hComp
      simpa [core, canonicalAmbientCirclePrincipalBundleCore,
        canonicalAmbientCirclePrincipalCoordChange] using hComp
    transition_cocycle := by
      intro first second third base hFirst hSecond hThird
      change base ∈ ambientPinMinusBundleBaseSet period hPeriod first at hFirst
      change base ∈ ambientPinMinusBundleBaseSet period hPeriod second at hSecond
      change base ∈ ambientPinMinusBundleBaseSet period hPeriod third at hThird
      have hFirst' : base ∈ core.baseSet first := by
        exact hFirst
      have hSecond' : base ∈ core.baseSet second := by
        exact hSecond
      have hThird' : base ∈ core.baseSet third := by
        exact hThird
      have hComp := core.coordChange_comp third second first base
        ⟨⟨hThird', hSecond'⟩, hFirst'⟩ 1
      simpa [core, canonicalAmbientCirclePrincipalBundleCore,
        canonicalAmbientCirclePrincipalCoordChange] using hComp
  }

/-- On compatible throat overlaps, the ambient circle lift is the established
normal quarter-root transition. -/
theorem ambientCircleReferenceTransitionLift_restricts_to_throat
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod first second) :
    ambientCircleReferenceTransitionLift period hPeriod choice
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        (throatAmbientOverlapCoordinate period hPeriod first base) =
      quarterRootCircleRepresentation choice
        (localTransitionWinding period hPeriod first second base) := by
  unfold ambientCircleReferenceTransitionLift
  rw [ambientTransitionWinding_throatAmbientOverlapCoordinate
    period hPeriod first second base hBase]
  exact normalRootCircleCharacter_intCast choice _

/-- A unit winding has determinant phase `-1`, so this twist is not the
determinant-trivial canonical phase sector. -/
theorem ambientCircleWinding_generator_square
    (choice : NormalRootChoice) :
    normalRootCircleCharacter choice (1 : ZMod 4) ^ 2 = (-1 : Circle) := by
  rw [show (1 : ZMod 4) = ((1 : Int) : ZMod 4) by norm_num,
    normalRootCircleCharacter_intCast]
  apply Circle.ext
  cases choice <;>
    simp [quarterRootCircleRepresentation, quarterRootRepresentation,
      normalRootMultiplier, pow_two, Complex.I_mul_I]

/-- The overlap from an ambient cover anchor to its next deck translate has
actual winding one. -/
theorem ambientTransitionWinding_one_loop
    (anchor : AmbientCover period hPeriod) :
    let base := mappingTorusMk (reflectedSphereData period hPeriod) anchor
    let coordinate := ambientQuotientLocalChart period hPeriod anchor base
    ambientTransitionWinding period hPeriod anchor ((1 : Int) +ᵥ anchor)
      coordinate = 1 := by
  let data := reflectedSphereData period hPeriod
  let projection := (mappingTorusMk_isCoveringMap data).isLocalHomeomorph
  let base := mappingTorusMk data anchor
  let second := (1 : Int) +ᵥ anchor
  let coordinate := ambientQuotientLocalChart period hPeriod anchor base
  have hProjection : mappingTorusMk data second = base := by
    exact (mappingTorusMk_isAddQuotientCoveringMap data).map_vadd 1
  have hFirst : base ∈ ambientPinMinusBundleBaseSet period hPeriod anchor := by
    exact ambientQuotientLocalChart_mk_mem_source period hPeriod anchor
  have hSecond : base ∈ ambientPinMinusBundleBaseSet period hPeriod second := by
    rw [← hProjection]
    exact ambientQuotientLocalChart_mk_mem_source period hPeriod second
  have hCoordinate := chartCoordinate_mem_transition_source period hPeriod
    anchor second base ⟨hFirst, hSecond⟩
  have hBaseCoordinate :
      (ambientQuotientLocalChart period hPeriod anchor).symm coordinate = base := by
    exact (ambientQuotientLocalChart period hPeriod anchor).left_inv hFirst
  have hFirstValue : projection.localInverseAt anchor base = anchor := by
    exact projection.localInverseAt_apply_self
  have hSecondValue : projection.localInverseAt second base = second := by
    rw [← hProjection]
    exact projection.localInverseAt_apply_self
  change ambientTransitionWinding period hPeriod anchor second coordinate = 1
  symm
  apply ambientTransitionWinding_unique period hPeriod anchor second coordinate
    hCoordinate 1
  change (1 : Int) +ᵥ projection.localInverseAt anchor
        ((ambientQuotientLocalChart period hPeriod anchor).symm coordinate) =
    projection.localInverseAt second
      ((ambientQuotientLocalChart period hPeriod anchor).symm coordinate)
  rw [hBaseCoordinate, hFirstValue, hSecondValue]

structure ProgramPAmbientCircleWindingBundleCertificate4D where
  choice : NormalRootChoice
  core : FiberBundleCore (AmbientCover period hPeriod)
    (AmbientBase period hPeriod) Circle
  coreCanonical :
    core = canonicalAmbientCirclePrincipalBundleCore period hPeriod choice
  twist : AmbientCircleCechTwist period hPeriod
  twistCanonical : twist = canonicalAmbientCircleCechTwist period hPeriod choice
  generatorDeterminantNontrivial :
    normalRootCircleCharacter choice (1 : ZMod 4) ^ 2 = (-1 : Circle)

def programPAmbientCircleWindingBundleCertificate4D
    (choice : NormalRootChoice) :
    ProgramPAmbientCircleWindingBundleCertificate4D period hPeriod where
  choice := choice
  core := canonicalAmbientCirclePrincipalBundleCore period hPeriod choice
  coreCanonical := rfl
  twist := canonicalAmbientCircleCechTwist period hPeriod choice
  twistCanonical := rfl
  generatorDeterminantNontrivial := ambientCircleWinding_generator_square choice

theorem programPAmbientCircleWindingBundleCertificate4D_nonempty :
    Nonempty (ProgramPAmbientCircleWindingBundleCertificate4D
      period hPeriod) :=
  ⟨programPAmbientCircleWindingBundleCertificate4D period hPeriod
    .positiveQuarter⟩

end
end P0EFTJanusProgramPAmbientCircleWindingBundle4D
end JanusFormal
