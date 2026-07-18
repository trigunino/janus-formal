import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalVectorBundle

/-!
# Principal `Pin⁻(1)` lift of the effective-throat normal line

The standard additive model `Pin⁻(1) ≃ ZMod 4` is used as fiber.  The
transition is translation by the integer deck winding modulo four.  Thus the
same global covering cocycle that constructs the normal line constructs an
actual fiber-bundle core with a free and transitive right `ZMod 4` action.

This is the principal lift of the rank-one normal bundle only.  It is not an
ambient tangent `Pin` or `SpinC` structure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothNormalVectorBundle

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Additive model of the one-dimensional normal `Pin⁻` group. -/
abbrev NormalPinMinusOne := ZMod 4

/-- Projection from the lifted normal phase to orientation parity. -/
def normalPinMinusOrientationReduction
    (phase : NormalPinMinusOne) : ZMod 2 :=
  phase.val

theorem normalPinMinusOrientationReduction_add
    (first second : NormalPinMinusOne) :
    normalPinMinusOrientationReduction (first + second) =
      normalPinMinusOrientationReduction first +
        normalPinMinusOrientationReduction second := by
  native_decide +revert

/-- Right regular action in each `Pin⁻(1)` fiber. -/
def normalPinMinusRightAction
    (pin groupElement : NormalPinMinusOne) : NormalPinMinusOne :=
  pin + groupElement

/-- A change of normal chart is left translation by the deck winding. -/
def normalPinMinusCoordChange
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (pin : NormalPinMinusOne) : NormalPinMinusOne :=
  (localTransitionWinding period hPeriod first second base : ZMod 4) + pin

private theorem continuousOn_normalPinMinusPhase
    (first second : ThroatCover period hPeriod) :
    ContinuousOn
      (fun base : ThroatBase period hPeriod ↦
        (localTransitionWinding period hPeriod first second base : ZMod 4))
      (normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) := by
  intro base hBase
  let overlap := normalBundleBaseSet period hPeriod first ∩
    normalBundleBaseSet period hPeriod second
  have hWindingEq : Filter.EventuallyEq (nhdsWithin base overlap)
      (localTransitionWinding period hPeriod first second)
      (fun _ ↦ localTransitionWinding period hPeriod first second base) :=
    (localTransitionWinding_eventuallyEq period hPeriod first second base hBase).filter_mono
      inf_le_left
  have hPhaseEq := hWindingEq.fun_comp (fun winding : ℤ ↦ (winding : ZMod 4))
  exact (continuousWithinAt_const : ContinuousWithinAt
      (fun _ : ThroatBase period hPeriod ↦
        (localTransitionWinding period hPeriod first second base : ZMod 4))
      overlap base).congr_of_eventuallyEq_of_mem hPhaseEq hBase

private theorem continuousOn_normalPinMinusCoordChange
    (first second : ThroatCover period hPeriod) :
    ContinuousOn
      (fun point : ThroatBase period hPeriod × NormalPinMinusOne ↦
        normalPinMinusCoordChange period hPeriod first second point.1 point.2)
      ((normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  apply ContinuousOn.add
  · exact (continuousOn_normalPinMinusPhase period hPeriod first second).comp
      continuousOn_fst (fun _ hPoint ↦ hPoint.1)
  · exact continuousOn_snd

/-- Fiber-bundle core of the global normal `Pin⁻(1)` principal lift. -/
def fixedThroatNormalPinMinusBundleCore :
    FiberBundleCore (ThroatCover period hPeriod)
      (ThroatBase period hPeriod) NormalPinMinusOne where
  baseSet := normalBundleBaseSet period hPeriod
  isOpen_baseSet := normalBundleBaseSet_isOpen period hPeriod
  indexAt := normalBundleIndexAt period hPeriod
  mem_baseSet_at := mem_normalBundleBaseSet_indexAt period hPeriod
  coordChange := normalPinMinusCoordChange period hPeriod
  coordChange_self anchor base hBase pin := by
    simp [normalPinMinusCoordChange,
      localTransitionWinding_self period hPeriod anchor base hBase]
  continuousOn_coordChange :=
    continuousOn_normalPinMinusCoordChange period hPeriod
  coordChange_comp first second third base hBase pin := by
    simp only [normalPinMinusCoordChange]
    rw [← add_assoc, ← Int.cast_add]
    rw [localTransitionWinding_add period hPeriod first second third base hBase]

/-- Associated globally topologized fiber family. -/
abbrev FixedThroatNormalPinMinusFiber :=
  (fixedThroatNormalPinMinusBundleCore period hPeriod).Fiber

/-- The cocycle produces an actual topological fiber bundle. -/
@[reducible] def fixedThroatNormalPinMinusFiber_isFiberBundle :
    FiberBundle NormalPinMinusOne
      (FixedThroatNormalPinMinusFiber period hPeriod) :=
  inferInstance

/-- Chart transitions commute with the right regular action. -/
theorem coordChange_right_equivariant
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (pin groupElement : NormalPinMinusOne) :
    normalPinMinusCoordChange period hPeriod first second base
        (normalPinMinusRightAction pin groupElement) =
      normalPinMinusRightAction
        (normalPinMinusCoordChange period hPeriod first second base pin)
        groupElement := by
  simp [normalPinMinusCoordChange, normalPinMinusRightAction, add_assoc]

/-- The right action is free on every model fiber. -/
theorem normalPinMinusRightAction_free
    (pin groupElement : NormalPinMinusOne)
    (hFixed : normalPinMinusRightAction pin groupElement = pin) :
    groupElement = 0 := by
  simpa [normalPinMinusRightAction] using hFixed

/-- The right action is transitive on every model fiber. -/
theorem normalPinMinusRightAction_transitive
    (first second : NormalPinMinusOne) :
    ∃ groupElement : NormalPinMinusOne,
      normalPinMinusRightAction first groupElement = second := by
  exact ⟨second - first, by simp [normalPinMinusRightAction]⟩

/-- The full principal-atlas data: a genuine fiber-bundle core whose changes
of chart are equivariant for a free and transitive right action. -/
structure NormalPinMinusPrincipalBundle where
  core : FiberBundleCore (ThroatCover period hPeriod)
    (ThroatBase period hPeriod) NormalPinMinusOne
  coordChangeEquivariant :
    ∀ first second base pin groupElement,
      core.coordChange first second base
          (normalPinMinusRightAction pin groupElement) =
        normalPinMinusRightAction (core.coordChange first second base pin)
          groupElement
  rightActionFree :
    ∀ pin groupElement,
      normalPinMinusRightAction pin groupElement = pin → groupElement = 0
  rightActionTransitive :
    ∀ first second,
      ∃ groupElement,
        normalPinMinusRightAction first groupElement = second

/-- The normal winding cocycle supplies the complete principal bundle. -/
def fixedThroatNormalPinMinusPrincipalBundle :
    NormalPinMinusPrincipalBundle period hPeriod where
  core := fixedThroatNormalPinMinusBundleCore period hPeriod
  coordChangeEquivariant :=
    coordChange_right_equivariant period hPeriod
  rightActionFree := normalPinMinusRightAction_free
  rightActionTransitive := normalPinMinusRightAction_transitive

/-- One circuit is the order-four generator of the principal transition. -/
theorem one_loop_pinMinus_coordChange
    (anchor : ThroatCover period hPeriod) (pin : NormalPinMinusOne) :
    (fixedThroatNormalPinMinusBundleCore period hPeriod).coordChange anchor
        ((1 : ℤ) +ᵥ anchor)
        (mappingTorusMk (fixedEquatorData period hPeriod) anchor) pin =
      1 + pin := by
  simp [fixedThroatNormalPinMinusBundleCore, normalPinMinusCoordChange,
    localTransitionWinding_one_loop period hPeriod anchor]

/-- The square of the lifted generator is the central sign. -/
theorem pinMinus_generator_square (pin : NormalPinMinusOne) :
    normalPinMinusRightAction
        (normalPinMinusRightAction pin 1) 1 = pin + 2 := by
  native_decide +revert

/-- Four lifted circuits act trivially. -/
theorem pinMinus_generator_fourth (pin : NormalPinMinusOne) :
    normalPinMinusRightAction
      (normalPinMinusRightAction
        (normalPinMinusRightAction
          (normalPinMinusRightAction pin 1) 1) 1) 1 = pin := by
  native_decide +revert

/-- Reduction modulo two intertwines principal transition and orientation
transition. -/
theorem reduce_coordChange_to_orientation
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (pin : NormalPinMinusOne) :
    normalPinMinusOrientationReduction
        (normalPinMinusCoordChange period hPeriod first second base pin) =
      normalPinMinusOrientationReduction
          (localTransitionWinding period hPeriod first second base : ZMod 4) +
        normalPinMinusOrientationReduction pin := by
  exact normalPinMinusOrientationReduction_add _ _

/-- In particular, one lifted circuit projects to the nontrivial orientation
deck transformation. -/
theorem one_loop_pinMinus_projects_nontrivially :
    normalPinMinusOrientationReduction (1 : NormalPinMinusOne) = 1 := by
  native_decide

end

end P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
end JanusFormal
