import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusNormalOrientationZ4Lift

namespace JanusFormal
namespace P0EFTJanusCyclicHolonomyOrderNoGo

set_option autoImplicit false

open P0EFTJanusNormalOrientationZ4Lift

/-- Order-three phase character of the cyclic loop model. -/
def orderThreeCharacter (winding : ℤ) : ZMod 3 := winding

/-- Order-four phase character of the same cyclic loop model. -/
def orderFourCharacter (winding : ℤ) : ZMod 4 := winding

/-- Order-five phase character of the same cyclic loop model. -/
def orderFiveCharacter (winding : ℤ) : ZMod 5 := winding

/-- Each character respects addition of loop windings. -/
theorem order_three_character_additive
    (first second : ℤ) :
    orderThreeCharacter (first + second) =
      orderThreeCharacter first + orderThreeCharacter second := by
  unfold orderThreeCharacter
  push_cast
  ring


theorem order_four_character_additive
    (first second : ℤ) :
    orderFourCharacter (first + second) =
      orderFourCharacter first + orderFourCharacter second := by
  unfold orderFourCharacter
  push_cast
  ring


theorem order_five_character_additive
    (first second : ℤ) :
    orderFiveCharacter (first + second) =
      orderFiveCharacter first + orderFiveCharacter second := by
  unfold orderFiveCharacter
  push_cast
  ring

/-- The three examples are genuinely nontrivial on the generator. -/
theorem competing_finite_holonomies_exist :
    orderThreeCharacter 1 ≠ 0 /\
      orderFourCharacter 1 ≠ 0 /\
      orderFiveCharacter 1 ≠ 0 := by
  native_decide

/-- Their declared periods close on the cyclic generator. -/
theorem competing_finite_holonomies_close :
    orderThreeCharacter 3 = 0 /\
      orderFourCharacter 4 = 0 /\
      orderFiveCharacter 5 = 0 := by
  native_decide

/-- The same infinite-cyclic loop group therefore supports several finite orders. -/
theorem cyclic_topology_does_not_select_order_four :
    (∃ character : ℤ → ZMod 3,
      (∀ first second,
        character (first + second) =
          character first + character second) /\
      character 1 ≠ 0 /\
      character 3 = 0) /\
    (∃ character : ℤ → ZMod 4,
      (∀ first second,
        character (first + second) =
          character first + character second) /\
      character 1 ≠ 0 /\
      character 4 = 0) /\
    (∃ character : ℤ → ZMod 5,
      (∀ first second,
        character (first + second) =
          character first + character second) /\
      character 1 ≠ 0 /\
      character 5 = 0) := by
  exact ⟨⟨orderThreeCharacter,
      order_three_character_additive,
      competing_finite_holonomies_exist.1,
      competing_finite_holonomies_close.1⟩,
    ⟨orderFourCharacter,
      order_four_character_additive,
      competing_finite_holonomies_exist.2.1,
      competing_finite_holonomies_close.2.1⟩,
    ⟨orderFiveCharacter,
      order_five_character_additive,
      competing_finite_holonomies_exist.2.2,
      competing_finite_holonomies_close.2.2⟩⟩

/-- The normal-square-root condition is the extra law that reduces the Z4 phase to `1` or `3`. -/
theorem normal_square_root_condition_selects_quarter_pair
    (phase : ZMod 4)
    (hRoot : IsNormalSquareRoot phase) :
    phase = 1 \/ phase = 3 :=
  (normal_square_root_iff_one_or_three phase).mp hRoot

/--
Thus `pi1 = Z` supplies a continuous/cyclic holonomy slot, not a distinguished
`Z4`.  The quarter pair is selected only after adding the geometric requirement
that the character square to the one-sided normal sign.  Even then, the choice
between the two PT-conjugate roots remains open.
-/
structure CyclicHolonomySelectionStatus where
  actualFundamentalGroupProvedCyclic : Prop
  flatCharacterClassificationDerived : Prop
  competingOrdersExhibited : Prop
  normalSignCharacterDerived : Prop
  squareRootConstraintDerived : Prop
  quarterPairClassified : Prop
  physicalRootOrPTPairSelected : Prop


def cyclicHolonomySelectionClosed
    (s : CyclicHolonomySelectionStatus) : Prop :=
  s.actualFundamentalGroupProvedCyclic /\
  s.flatCharacterClassificationDerived /\
  s.competingOrdersExhibited /\
  s.normalSignCharacterDerived /\
  s.squareRootConstraintDerived /\
  s.quarterPairClassified /\
  s.physicalRootOrPTPairSelected

end P0EFTJanusCyclicHolonomyOrderNoGo
end JanusFormal
