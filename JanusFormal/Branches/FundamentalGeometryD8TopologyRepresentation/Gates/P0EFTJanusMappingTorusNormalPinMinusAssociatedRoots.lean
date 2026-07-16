import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalZ4RootBundle

/-!
# Root characters associated to the normal `Pin⁻(1)` principal bundle

The two additive quarter characters act on a `ZMod 4` root fiber.  Applying
either character to every transition of the constructed principal normal
bundle gives an actual associated fiber-bundle core.  Its character squares
to the normal half-turn for every winding and PT exchanges the two choices.

This is a compatibility theorem for the rank-one normal lift.  It does not
construct an ambient tangent `Pin`/`SpinC` structure or its characteristic
classes.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusNormalPinMinusAssociatedRoots

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
open P0EFTJanusNormalOrientationZ4Lift
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Character of `Pin⁻(1) ≃ ZMod 4` selected by either normal root. -/
def pinMinusRootCharacter
    (choice : NormalRootChoice) (phase : NormalPinMinusOne) : ZMod 4 :=
  phase * normalRootPhase choice

theorem pinMinusRootCharacter_zero
    (choice : NormalRootChoice) :
    pinMinusRootCharacter choice 0 = 0 := by
  simp [pinMinusRootCharacter]

theorem pinMinusRootCharacter_add
    (choice : NormalRootChoice) (first second : NormalPinMinusOne) :
    pinMinusRootCharacter choice (first + second) =
      pinMinusRootCharacter choice first +
        pinMinusRootCharacter choice second := by
  simp [pinMinusRootCharacter, add_mul]

/-- On an integer deck winding this is exactly the previously classified
normal-root character. -/
theorem pinMinusRootCharacter_intCast
    (choice : NormalRootChoice) (winding : ℤ) :
    pinMinusRootCharacter choice (winding : NormalPinMinusOne) =
      normalRootCharacter (normalRootPhase choice) winding := by
  rfl

/-- Both associated characters square to the orientation half-turn. -/
theorem pinMinusRootCharacter_square
    (choice : NormalRootChoice) (phase : NormalPinMinusOne) :
    pinMinusRootCharacter choice phase +
        pinMinusRootCharacter choice phase =
      phase * normalHalfTurn := by
  unfold pinMinusRootCharacter
  rw [← mul_add, normal_root_phase_is_square_root choice]

@[simp]
theorem oppositeRoot_phase
    (choice : NormalRootChoice) :
    normalRootPhase (oppositeRoot choice) = -normalRootPhase choice := by
  cases choice <;> native_decide

/-- PT sends the associated character to its additive inverse. -/
theorem pinMinusRootCharacter_opposite
    (choice : NormalRootChoice) (phase : NormalPinMinusOne) :
    pinMinusRootCharacter (oppositeRoot choice) phase =
      -pinMinusRootCharacter choice phase := by
  simp [pinMinusRootCharacter]

/-- The two opposite root characters multiply to the trivial character for
every winding, after viewing their additive phases multiplicatively. -/
theorem pinMinusRootCharacter_mul_opposite
    (choice : NormalRootChoice) (winding : NormalPinMinusOne) :
    Multiplicative.ofAdd (pinMinusRootCharacter choice winding) *
        Multiplicative.ofAdd
          (pinMinusRootCharacter (oppositeRoot choice) winding) = 1 := by
  rw [pinMinusRootCharacter_opposite]
  simp

/-- Action of the principal normal group on the associated root-phase fiber. -/
def associatedRootPhaseAction
    (choice : NormalRootChoice)
    (principalPhase rootPhase : ZMod 4) : ZMod 4 :=
  pinMinusRootCharacter choice principalPhase + rootPhase

theorem associatedRootPhaseAction_zero
    (choice : NormalRootChoice) (rootPhase : ZMod 4) :
    associatedRootPhaseAction choice 0 rootPhase = rootPhase := by
  simp [associatedRootPhaseAction, pinMinusRootCharacter]

theorem associatedRootPhaseAction_add
    (choice : NormalRootChoice)
    (first second rootPhase : ZMod 4) :
    associatedRootPhaseAction choice second
        (associatedRootPhaseAction choice first rootPhase) =
      associatedRootPhaseAction choice (first + second) rootPhase := by
  simp [associatedRootPhaseAction, pinMinusRootCharacter]
  ring

/-- The associated action is free because both root characters are units. -/
theorem associatedRootPhaseAction_free
    (choice : NormalRootChoice)
    (principalPhase rootPhase : ZMod 4)
    (hFixed : associatedRootPhaseAction choice principalPhase rootPhase =
      rootPhase) :
    principalPhase = 0 := by
  cases choice <;> native_decide +revert

/-- The associated action is transitive on the root-phase fiber. -/
theorem associatedRootPhaseAction_transitive
    (choice : NormalRootChoice) (first second : ZMod 4) :
    ∃ principalPhase : ZMod 4,
      associatedRootPhaseAction choice principalPhase first = second := by
  cases choice
  · exact ⟨second - first, by
      simp [associatedRootPhaseAction, pinMinusRootCharacter,
        normalRootPhase]⟩
  · exact ⟨first - second, by
      native_decide +revert⟩

/-- Associated chart transition obtained by applying a root character to the
principal normal transition. -/
def associatedRootPhaseCoordChange
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (rootPhase : ZMod 4) : ZMod 4 :=
  associatedRootPhaseAction choice
    (localTransitionWinding period hPeriod first second base : ZMod 4)
    rootPhase

private theorem continuousOn_associatedRootPhase
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod) :
    ContinuousOn
      (fun base : ThroatBase period hPeriod ↦
        pinMinusRootCharacter choice
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
  have hPhaseEq := hWindingEq.fun_comp
    (fun winding : ℤ ↦ pinMinusRootCharacter choice (winding : ZMod 4))
  exact (continuousWithinAt_const : ContinuousWithinAt
      (fun _ : ThroatBase period hPeriod ↦ pinMinusRootCharacter choice
        (localTransitionWinding period hPeriod first second base : ZMod 4))
      overlap base).congr_of_eventuallyEq_of_mem hPhaseEq hBase

private theorem continuousOn_associatedRootPhaseCoordChange
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod) :
    ContinuousOn
      (fun point : ThroatBase period hPeriod × ZMod 4 ↦
        associatedRootPhaseCoordChange period hPeriod choice first second
          point.1 point.2)
      ((normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  apply ContinuousOn.add
  · exact (continuousOn_associatedRootPhase period hPeriod choice first second).comp
      continuousOn_fst (fun _ hPoint ↦ hPoint.1)
  · exact continuousOn_snd

/-- Actual associated root-phase fiber-bundle core. -/
def fixedThroatAssociatedRootPhaseBundleCore
    (choice : NormalRootChoice) :
    FiberBundleCore (ThroatCover period hPeriod)
      (ThroatBase period hPeriod) (ZMod 4) where
  baseSet := normalBundleBaseSet period hPeriod
  isOpen_baseSet := normalBundleBaseSet_isOpen period hPeriod
  indexAt := normalBundleIndexAt period hPeriod
  mem_baseSet_at := mem_normalBundleBaseSet_indexAt period hPeriod
  coordChange := associatedRootPhaseCoordChange period hPeriod choice
  coordChange_self anchor base hBase rootPhase := by
    simp [associatedRootPhaseCoordChange, associatedRootPhaseAction,
      localTransitionWinding_self period hPeriod anchor base hBase,
      pinMinusRootCharacter]
  continuousOn_coordChange :=
    continuousOn_associatedRootPhaseCoordChange period hPeriod choice
  coordChange_comp first second third base hBase rootPhase := by
    simp only [associatedRootPhaseCoordChange]
    rw [associatedRootPhaseAction_add]
    congr 2
    rw [add_comm, ← Int.cast_add]
    exact congrArg (fun winding : ℤ ↦ (winding : ZMod 4))
      (localTransitionWinding_add period hPeriod first second third base hBase)

abbrev FixedThroatAssociatedRootPhaseFiber
    (choice : NormalRootChoice) :=
  (fixedThroatAssociatedRootPhaseBundleCore period hPeriod choice).Fiber

@[reducible] def fixedThroatAssociatedRootPhaseFiber_isFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle (ZMod 4)
      (FixedThroatAssociatedRootPhaseFiber period hPeriod choice) :=
  inferInstance

/-- The associated transition is definitionally induced from the principal
transition phase through the chosen character. -/
theorem associated_coordChange_from_principal
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (rootPhase : ZMod 4) :
    (fixedThroatAssociatedRootPhaseBundleCore period hPeriod choice).coordChange
        first second base rootPhase =
      associatedRootPhaseAction choice
        (localTransitionWinding period hPeriod first second base : ZMod 4)
        rootPhase := by
  rfl

/-- One loop acts by the selected quarter phase. -/
theorem one_loop_associatedRootPhase_coordChange
    (choice : NormalRootChoice)
    (anchor : ThroatCover period hPeriod)
    (rootPhase : ZMod 4) :
    (fixedThroatAssociatedRootPhaseBundleCore period hPeriod choice).coordChange
        anchor ((1 : ℤ) +ᵥ anchor)
        (mappingTorusMk (fixedEquatorData period hPeriod) anchor) rootPhase =
      normalRootPhase choice + rootPhase := by
  simp [fixedThroatAssociatedRootPhaseBundleCore,
    associatedRootPhaseCoordChange, associatedRootPhaseAction,
    pinMinusRootCharacter,
    localTransitionWinding_one_loop period hPeriod anchor]

/-- Two associated generator transitions give the central half-turn. -/
theorem associatedRootPhase_generator_square
    (choice : NormalRootChoice) (rootPhase : ZMod 4) :
    associatedRootPhaseAction choice 1
        (associatedRootPhaseAction choice 1 rootPhase) =
      normalHalfTurn + rootPhase := by
  cases choice <;> native_decide +revert

/-- Four associated generator transitions are the identity. -/
theorem associatedRootPhase_generator_fourth
    (choice : NormalRootChoice) (rootPhase : ZMod 4) :
    associatedRootPhaseAction choice 1
      (associatedRootPhaseAction choice 1
        (associatedRootPhaseAction choice 1
          (associatedRootPhaseAction choice 1 rootPhase))) = rootPhase := by
  cases choice <;> native_decide +revert

end

end P0EFTJanusMappingTorusNormalPinMinusAssociatedRoots
end JanusFormal
