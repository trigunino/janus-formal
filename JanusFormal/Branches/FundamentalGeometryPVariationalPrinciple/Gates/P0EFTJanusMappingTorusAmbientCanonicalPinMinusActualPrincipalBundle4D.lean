import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientRadialReferenceSmoothReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D

/-!
# Canonical ambient Pin-minus principal bundle

The canonical winding lift supplies the transition functions of an actual
principal `Pin⁻(4)` bundle over the quotient.  Its orthogonal projection is
the smooth radial reduction and its throat restriction is the existing
normal `Pin⁻(1)` transition.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D
open P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceOrthogonalCocycle4D
open P0EFTJanusMappingTorusAmbientRadialReferenceSmoothReduction4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev AmbientBase := MappingTorus (AmbientData period hPeriod)
private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

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

/-- Canonical left transition on the principal fiber. -/
def canonicalAmbientPinMinusPrincipalCoordChange
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (pin : AmbientCoordinatePinMinusGroup) : AmbientCoordinatePinMinusGroup :=
  canonicalAmbientReferencePinMinusTransitionLift period hPeriod first second
      (ambientQuotientLocalChart period hPeriod first base) * pin

private theorem canonicalAmbientPinMinusPrincipalCoordChange_continuousOn
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun point : AmbientBase period hPeriod × AmbientCoordinatePinMinusGroup =>
        canonicalAmbientPinMinusPrincipalCoordChange period hPeriod first second
          point.1 point.2)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  apply ContinuousOn.mul
  · apply (canonicalAmbientReferencePinMinusTransitionLift_continuousOn
      period hPeriod first second).comp
      ((ambientQuotientLocalChart period hPeriod first).continuousOn.comp
        continuousOn_fst (fun point hPoint => hPoint.1.1))
    intro point hPoint
    exact chartCoordinate_mem_transition_source period hPeriod first second
      point.1 ⟨hPoint.1.1, hPoint.1.2⟩
  · exact continuousOn_snd

/-- Genuine canonical principal-bundle core over the ambient quotient. -/
def canonicalAmbientPinMinusPrincipalBundleCore
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup] :
    FiberBundleCore (AmbientCover period hPeriod) (AmbientBase period hPeriod)
      AmbientCoordinatePinMinusGroup where
  baseSet := ambientPinMinusBundleBaseSet period hPeriod
  isOpen_baseSet := ambientPinMinusBundleBaseSet_isOpen period hPeriod
  indexAt := ambientPinMinusBundleIndexAt period hPeriod
  mem_baseSet_at := mem_ambientPinMinusBundleBaseSet_indexAt period hPeriod
  coordChange := canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
  coordChange_self anchor base hBase pin := by
    unfold canonicalAmbientPinMinusPrincipalCoordChange
    rw [canonicalAmbientReferencePinMinusTransitionLift_normalized period hPeriod
      anchor (ambientQuotientLocalChart period hPeriod anchor base)
      (chartCoordinate_mem_transition_source period hPeriod anchor anchor base
        ⟨hBase, hBase⟩)]
    exact one_mul pin
  continuousOn_coordChange :=
    canonicalAmbientPinMinusPrincipalCoordChange_continuousOn period hPeriod
  coordChange_comp first second third base hBase pin := by
    unfold canonicalAmbientPinMinusPrincipalCoordChange
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
    have hCocycle :=
      canonicalAmbientReferencePinMinusTransitionLift_cocycle period hPeriod
        first second third
        (ambientQuotientLocalChart period hPeriod first base)
        hFirstSecond hSecondThird' hFirstThird
    rw [← hTransition, ← mul_assoc, hCocycle]

/-- Associated canonical principal fiber family. -/
abbrev CanonicalAmbientPinMinusPrincipalFiber
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup] :=
  (canonicalAmbientPinMinusPrincipalBundleCore period hPeriod).Fiber

@[reducible] def canonicalAmbientPinMinusPrincipalFiber_isFiberBundle
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup] :
    FiberBundle AmbientCoordinatePinMinusGroup
      (CanonicalAmbientPinMinusPrincipalFiber period hPeriod) :=
  inferInstance

theorem canonicalAmbientPinMinusPrincipalCoordChange_right_equivariant
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (pin groupElement : AmbientCoordinatePinMinusGroup) :
    canonicalAmbientPinMinusPrincipalCoordChange period hPeriod first second base
        (ambientPinMinusRightAction pin groupElement) =
      ambientPinMinusRightAction
        (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod first second
          base pin) groupElement := by
  simp [canonicalAmbientPinMinusPrincipalCoordChange,
    ambientPinMinusRightAction, mul_assoc]

/-- The canonical lift projects exactly to the smooth radial transition. -/
theorem canonicalAmbientPinMinusTransitionLift_projects_to_radialReduction
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ambientPinMinusProjection
        (canonicalAmbientReferencePinMinusTransitionLift period hPeriod
          first second coordinate) =
      (ambientRadialReferenceContMDiffOrthonormalAtlasReduction period hPeriod
        |>.toPointwise.orthogonalTransition period hPeriod first second coordinate
          hCoordinate).toLinearEquiv := by
  rw [← canonicalAmbientReferenceOrthogonalTransition_toLinearEquiv]
  exact (ambientRadialReferenceSmoothOrthogonalTransition_eq_canonical
    period hPeriod first second coordinate hCoordinate).symm

/-- The canonical principal transition restricts to the established normal
`Pin⁻(1)` transition on every compatible throat overlap. -/
theorem canonicalAmbientPinMinusPrincipalTransition_restricts_to_throat
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod first second) :
    canonicalAmbientReferencePinMinusTransitionLift period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        (throatAmbientOverlapCoordinate period hPeriod first base) =
      ambientPinMinusReferenceZ4Character
        (localTransitionWinding period hPeriod first second base : ZMod 4) :=
  canonicalAmbientReferencePinMinusTransitionLift_restricts_to_throat
    period hPeriod first second base hBase

/-- Packaged principal data: genuine core and free/transitive right action. -/
structure CanonicalAmbientPinMinusActualPrincipalBundle
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup] where
  core : FiberBundleCore (AmbientCover period hPeriod) (AmbientBase period hPeriod)
    AmbientCoordinatePinMinusGroup
  core_eq : core = canonicalAmbientPinMinusPrincipalBundleCore period hPeriod
  coordChangeEquivariant : ∀ first second base pin groupElement,
    core.coordChange first second base
        (ambientPinMinusRightAction pin groupElement) =
      ambientPinMinusRightAction (core.coordChange first second base pin)
        groupElement
  rightActionFree : ∀ pin groupElement,
    ambientPinMinusRightAction pin groupElement = pin → groupElement = 1
  rightActionTransitive : ∀ first second,
    ∃ groupElement, ambientPinMinusRightAction first groupElement = second

def canonicalAmbientPinMinusActualPrincipalBundle
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup] :
    CanonicalAmbientPinMinusActualPrincipalBundle period hPeriod where
  core := canonicalAmbientPinMinusPrincipalBundleCore period hPeriod
  core_eq := rfl
  coordChangeEquivariant :=
    canonicalAmbientPinMinusPrincipalCoordChange_right_equivariant period hPeriod
  rightActionFree := ambientPinMinusRightAction_free
  rightActionTransitive := ambientPinMinusRightAction_transitive

end
end P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
end JanusFormal
