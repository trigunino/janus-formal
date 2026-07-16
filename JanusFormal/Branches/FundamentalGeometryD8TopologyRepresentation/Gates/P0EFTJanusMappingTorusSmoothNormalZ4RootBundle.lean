import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalVectorBundle
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusNormalPinLiftBoundaryConditions

/-!
# Global `Z4` root line of the effective throat normal bundle

The two quarter phases are promoted from loop multipliers to actual complex
line-bundle cores on the effective D8 throat.  Their transition representation
is defined for every deck winding, satisfies the cocycle law, and its generator
squares to the real normal sign.  This constructs the global normal-root line;
it does not construct the ambient SpinC or Pin principal bundle.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothNormalZ4RootBundle

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

theorem normalRootMultiplier_ne_zero (choice : NormalRootChoice) :
    normalRootMultiplier choice ≠ 0 := by
  cases choice <;> simp [normalRootMultiplier]

/-- Multiplicative quarter-phase representation of every deck winding. -/
def quarterRootRepresentation
    (choice : NormalRootChoice) (winding : ℤ) : ℂ :=
  normalRootMultiplier choice ^ winding

@[simp] theorem quarterRootRepresentation_zero
    (choice : NormalRootChoice) :
    quarterRootRepresentation choice 0 = 1 := by
  simp [quarterRootRepresentation]

@[simp] theorem quarterRootRepresentation_one
    (choice : NormalRootChoice) :
    quarterRootRepresentation choice 1 = normalRootMultiplier choice := by
  simp [quarterRootRepresentation]

theorem quarterRootRepresentation_add
    (choice : NormalRootChoice) (first second : ℤ) :
    quarterRootRepresentation choice (first + second) =
      quarterRootRepresentation choice first *
        quarterRootRepresentation choice second := by
  exact zpow_add₀ (normalRootMultiplier_ne_zero choice) first second

/-- Squaring either quarter representation recovers the complexification of
the real normal-sign representation for every deck winding. -/
theorem quarterRootRepresentation_square
    (choice : NormalRootChoice) (winding : ℤ) :
    quarterRootRepresentation choice winding *
        quarterRootRepresentation choice winding =
      ((normalSignRepresentation winding : ℝ) : ℂ) := by
  rw [quarterRootRepresentation, ← mul_zpow,
    normal_root_multiplier_square]
  by_cases hEven : Even winding
  · rw [normal_sign_even winding hEven,
      ← Int.cast_negOnePow ℂ winding,
      Int.negOnePow_even winding hEven]
    norm_num
  · have hOdd : Odd winding := Int.not_even_iff_odd.mp hEven
    rw [normal_sign_odd winding hEven,
      ← Int.cast_negOnePow ℂ winding,
      Int.negOnePow_odd winding hOdd]
    norm_num

/-- Complex-linear action of a deck winding on the root coordinate. -/
def quarterRootCLM
    (choice : NormalRootChoice) (winding : ℤ) : ℂ →L[ℂ] ℂ :=
  quarterRootRepresentation choice winding • ContinuousLinearMap.id ℂ ℂ

@[simp] theorem quarterRootCLM_apply
    (choice : NormalRootChoice) (winding : ℤ) (root : ℂ) :
    quarterRootCLM choice winding root =
      quarterRootRepresentation choice winding * root := by
  simp [quarterRootCLM]

theorem quarterRootCLM_square_eq_normalSign
    (choice : NormalRootChoice) (winding : ℤ) (root : ℂ) :
    quarterRootCLM choice winding (quarterRootCLM choice winding root) =
      ((normalSignRepresentation winding : ℝ) : ℂ) * root := by
  simp only [quarterRootCLM_apply]
  rw [← mul_assoc, quarterRootRepresentation_square]

private theorem continuousOn_quarterRootTransition
    (choice : NormalRootChoice)
    (first second : ThroatCover period hPeriod) :
    ContinuousOn
      (fun base ↦ quarterRootCLM choice
        (localTransitionWinding period hPeriod first second base))
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
  have hRootEq := hWindingEq.fun_comp (quarterRootCLM choice)
  exact (continuousWithinAt_const : ContinuousWithinAt
      (fun _ : ThroatBase period hPeriod ↦
        quarterRootCLM choice
          (localTransitionWinding period hPeriod first second base))
      overlap base).congr_of_eventuallyEq_of_mem hRootEq hBase

/-- The positive or negative quarter choice defines an actual complex line
bundle core over the same effective throat as the real normal line. -/
def fixedThroatNormalZ4RootBundleCore
    (choice : NormalRootChoice) :
    VectorBundleCore ℂ (ThroatBase period hPeriod) ℂ
      (ThroatCover period hPeriod) where
  baseSet := normalBundleBaseSet period hPeriod
  isOpen_baseSet := normalBundleBaseSet_isOpen period hPeriod
  indexAt := normalBundleIndexAt period hPeriod
  mem_baseSet_at := mem_normalBundleBaseSet_indexAt period hPeriod
  coordChange first second base :=
    quarterRootCLM choice
      (localTransitionWinding period hPeriod first second base)
  coordChange_self anchor base hBase root := by
    simp [localTransitionWinding_self period hPeriod anchor base hBase]
  continuousOn_coordChange :=
    continuousOn_quarterRootTransition period hPeriod choice
  coordChange_comp first second third base hBase root := by
    simp only [quarterRootCLM_apply]
    rw [← mul_assoc, ← quarterRootRepresentation_add,
      localTransitionWinding_add period hPeriod first second third base hBase]

/-- The associated fiber family is a genuine topological complex line bundle. -/
abbrev FixedThroatNormalZ4RootFiber (choice : NormalRootChoice) :=
  (fixedThroatNormalZ4RootBundleCore period hPeriod choice).Fiber

theorem fixedThroatNormalZ4RootFiber_isVectorBundle
    (choice : NormalRootChoice) :
    VectorBundle ℂ ℂ
      (FixedThroatNormalZ4RootFiber period hPeriod choice) :=
  inferInstance

/-- One throat circuit acts by the selected quarter multiplier. -/
theorem one_loop_root_coordChange
    (choice : NormalRootChoice)
    (anchor : ThroatCover period hPeriod) (root : ℂ) :
    (fixedThroatNormalZ4RootBundleCore period hPeriod choice).coordChange anchor
        ((1 : ℤ) +ᵥ anchor)
        (mappingTorusMk (fixedEquatorData period hPeriod) anchor) root =
      normalRootMultiplier choice * root := by
  simp [fixedThroatNormalZ4RootBundleCore,
    localTransitionWinding_one_loop period hPeriod anchor]

/-- The generator transition squares exactly to the real normal sign `-1`. -/
theorem one_loop_root_transition_square
    (choice : NormalRootChoice) (root : ℂ) :
    quarterRootCLM choice 1 (quarterRootCLM choice 1 root) = -root := by
  simp only [quarterRootCLM_apply, quarterRootRepresentation_one]
  rw [← mul_assoc, normal_root_multiplier_square]
  simp

/-- Four generator transitions are the identity, so the root holonomy is
genuinely `Z4`. -/
theorem one_loop_root_transition_fourth
    (choice : NormalRootChoice) (root : ℂ) :
    quarterRootCLM choice 1
        (quarterRootCLM choice 1
          (quarterRootCLM choice 1
            (quarterRootCLM choice 1 root))) = root := by
  simp only [quarterRootCLM_apply, quarterRootRepresentation_one]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
    normal_root_multiplier_fourth]
  simp

end

end P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
end JanusFormal
