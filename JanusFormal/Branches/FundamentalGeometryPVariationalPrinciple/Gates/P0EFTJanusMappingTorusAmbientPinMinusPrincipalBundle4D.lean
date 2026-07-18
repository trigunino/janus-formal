import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D

/-!
# Principal ambient Pin-minus bundle from the actual Cech lift

Any continuous normal-compatible `Pin⁻(4)` lift of the real reduced ambient
atlas now produces a genuine fiber-bundle core on the effective four-manifold.
Its transition functions are equivariant for the free and transitive right
regular action.  Existence of the required ambient Cech lift remains the
separate geometric frontier.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev AmbientBase := MappingTorus (AmbientData period hPeriod)

/-- Domain of the actual quotient chart indexed by an ambient cover point. -/
def ambientPinMinusBundleBaseSet
    (anchor : AmbientCover period hPeriod) : Set (AmbientBase period hPeriod) :=
  (ambientQuotientLocalChart period hPeriod anchor).source

theorem ambientPinMinusBundleBaseSet_isOpen
    (anchor : AmbientCover period hPeriod) :
    IsOpen (ambientPinMinusBundleBaseSet period hPeriod anchor) :=
  (ambientQuotientLocalChart period hPeriod anchor).open_source

/-- Preferred chart index over every quotient point. -/
def ambientPinMinusBundleIndexAt
    (base : AmbientBase period hPeriod) : AmbientCover period hPeriod :=
  Classical.choose (mappingTorusMk_surjective (AmbientData period hPeriod) base)

@[simp] theorem ambientPinMinusBundleIndexAt_projects
    (base : AmbientBase period hPeriod) :
    mappingTorusMk (AmbientData period hPeriod)
        (ambientPinMinusBundleIndexAt period hPeriod base) = base :=
  Classical.choose_spec
    (mappingTorusMk_surjective (AmbientData period hPeriod) base)

theorem mem_ambientPinMinusBundleBaseSet_indexAt
    (base : AmbientBase period hPeriod) :
    base ∈ ambientPinMinusBundleBaseSet period hPeriod
      (ambientPinMinusBundleIndexAt period hPeriod base) := by
  simpa only [ambientPinMinusBundleBaseSet,
    ambientPinMinusBundleIndexAt_projects] using
      (ambientQuotientLocalChart_mk_mem_source period hPeriod
        (ambientPinMinusBundleIndexAt period hPeriod base))

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
  refine ⟨(ambientQuotientLocalChart period hPeriod first).map_source hBase.1,
    ?_⟩
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

/-- Left Cech transition on the principal fiber. -/
def ambientPinMinusPrincipalCoordChange
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (pin : AmbientCoordinatePinMinusGroup) : AmbientCoordinatePinMinusGroup :=
  choice.transitionLift first second
      (ambientQuotientLocalChart period hPeriod first base) * pin

private theorem ambientPinMinusPrincipalCoordChange_continuousOn
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun point : AmbientBase period hPeriod × AmbientCoordinatePinMinusGroup =>
        ambientPinMinusPrincipalCoordChange period hPeriod reduction choice
          first second point.1 point.2)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  apply ContinuousOn.mul
  · apply (choice.transitionLift_continuousOn first second).comp
      ((ambientQuotientLocalChart period hPeriod first).continuousOn.comp
        continuousOn_fst (fun point hPoint => hPoint.1.1))
    intro point hPoint
    exact chartCoordinate_mem_transition_source period hPeriod first second
      point.1 ⟨hPoint.1.1, hPoint.1.2⟩
  · exact continuousOn_snd

/-- Genuine ambient `Pin⁻(4)` fiber-bundle core determined by the chosen
continuous lift of the actual atlas. -/
def ambientPinMinusPrincipalBundleCore
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction) :
    FiberBundleCore (AmbientCover period hPeriod) (AmbientBase period hPeriod)
      AmbientCoordinatePinMinusGroup where
  baseSet := ambientPinMinusBundleBaseSet period hPeriod
  isOpen_baseSet := ambientPinMinusBundleBaseSet_isOpen period hPeriod
  indexAt := ambientPinMinusBundleIndexAt period hPeriod
  mem_baseSet_at := mem_ambientPinMinusBundleBaseSet_indexAt period hPeriod
  coordChange := ambientPinMinusPrincipalCoordChange period hPeriod reduction choice
  coordChange_self anchor base hBase pin := by
    unfold ambientPinMinusPrincipalCoordChange
    rw [choice.normalized anchor
      (ambientQuotientLocalChart period hPeriod anchor base)
      (chartCoordinate_mem_transition_source period hPeriod anchor anchor base
        ⟨hBase, hBase⟩)]
    exact one_mul pin
  continuousOn_coordChange :=
    ambientPinMinusPrincipalCoordChange_continuousOn period hPeriod reduction
      choice
  coordChange_comp first second third base hBase pin := by
    unfold ambientPinMinusPrincipalCoordChange
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
    have hCocycle := choice.cocycle first second third
      (ambientQuotientLocalChart period hPeriod first base)
      hFirstSecond hSecondThird' hFirstThird
    rw [← hTransition, ← mul_assoc, hCocycle]

/-- Associated topological fiber family. -/
abbrev AmbientPinMinusPrincipalFiber
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction) :=
  (ambientPinMinusPrincipalBundleCore period hPeriod reduction choice).Fiber

@[reducible] def ambientPinMinusPrincipalFiber_isFiberBundle
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction) :
    FiberBundle AmbientCoordinatePinMinusGroup
      (AmbientPinMinusPrincipalFiber period hPeriod reduction choice) :=
  inferInstance

/-- Right regular action in every principal fiber. -/
def ambientPinMinusRightAction
    (pin groupElement : AmbientCoordinatePinMinusGroup) :
    AmbientCoordinatePinMinusGroup :=
  pin * groupElement

theorem ambientPinMinusPrincipalCoordChange_right_equivariant
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (pin groupElement : AmbientCoordinatePinMinusGroup) :
    ambientPinMinusPrincipalCoordChange period hPeriod reduction choice
        first second base (ambientPinMinusRightAction pin groupElement) =
      ambientPinMinusRightAction
        (ambientPinMinusPrincipalCoordChange period hPeriod reduction choice
          first second base pin) groupElement := by
  simp [ambientPinMinusPrincipalCoordChange, ambientPinMinusRightAction,
    mul_assoc]

theorem ambientPinMinusRightAction_free
    (pin groupElement : AmbientCoordinatePinMinusGroup)
    (hFixed : ambientPinMinusRightAction pin groupElement = pin) :
    groupElement = 1 := by
  simpa [ambientPinMinusRightAction] using congrArg (fun value => pin⁻¹ * value)
    hFixed

theorem ambientPinMinusRightAction_transitive
  (first second : AmbientCoordinatePinMinusGroup) :
    ∃ groupElement : AmbientCoordinatePinMinusGroup,
      ambientPinMinusRightAction first groupElement = second :=
  ⟨first⁻¹ * second, by simp [ambientPinMinusRightAction]⟩

/-- Full principal-bundle atlas data over the actual ambient quotient. -/
structure AmbientPinMinusPrincipalBundle
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) where
  choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
    period hPeriod reduction
  core : FiberBundleCore (AmbientCover period hPeriod)
    (AmbientBase period hPeriod) AmbientCoordinatePinMinusGroup
  core_eq : core = ambientPinMinusPrincipalBundleCore period hPeriod reduction
    choice
  coordChangeEquivariant : ∀ first second base pin groupElement,
    core.coordChange first second base
        (ambientPinMinusRightAction pin groupElement) =
      ambientPinMinusRightAction (core.coordChange first second base pin)
        groupElement
  rightActionFree : ∀ pin groupElement,
    ambientPinMinusRightAction pin groupElement = pin → groupElement = 1
  rightActionTransitive : ∀ first second,
    ∃ groupElement, ambientPinMinusRightAction first groupElement = second

/-- Every certified continuous ambient Cech lift produces the full principal
bundle data. -/
def ambientPinMinusPrincipalBundleOfCechChoice
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientNormalCompatibleContinuousPinMinusCechChoice
      period hPeriod reduction) :
    AmbientPinMinusPrincipalBundle period hPeriod reduction where
  choice := choice
  core := ambientPinMinusPrincipalBundleCore period hPeriod reduction choice
  core_eq := rfl
  coordChangeEquivariant :=
    ambientPinMinusPrincipalCoordChange_right_equivariant period hPeriod
      reduction choice
  rightActionFree := ambientPinMinusRightAction_free
  rightActionTransitive := ambientPinMinusRightAction_transitive

end

end P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
end JanusFormal
