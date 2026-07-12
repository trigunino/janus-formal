import Mathlib

namespace JanusFormal
namespace P0EFTJanusNormalOrientationZ4Lift

set_option autoImplicit false

/-- Additive fourth-root phases. -/
abbrev NormalRootPhase := ZMod 4

/-- The nontrivial normal-line holonomy is the additive half-turn `2 mod 4`. -/
def normalHalfTurn : NormalRootPhase := 2

/-- A quarter phase whose square is the normal half-turn. -/
def IsNormalSquareRoot (phase : NormalRootPhase) : Prop :=
  phase + phase = normalHalfTurn

instance normalSquareRootDecidable
    (phase : NormalRootPhase) :
    Decidable (IsNormalSquareRoot phase) := by
  unfold IsNormalSquareRoot
  infer_instance

/-- Exactly the phases `1` and `3` square to the normal half-turn. -/
theorem normal_square_root_iff_one_or_three :
    ∀ phase : NormalRootPhase,
      IsNormalSquareRoot phase ↔ phase = 1 \/ phase = 3 := by
  native_decide

/-- The positive quarter phase is a square root. -/
@[simp] theorem one_is_normal_square_root :
    IsNormalSquareRoot 1 := by
  native_decide

/-- The negative quarter phase is the other square root. -/
@[simp] theorem three_is_normal_square_root :
    IsNormalSquareRoot 3 := by
  native_decide

/-- PT/conjugation reverses a phase. -/
def ptConjugatePhase (phase : NormalRootPhase) : NormalRootPhase :=
  -phase

/-- Conjugation exchanges the two roots. -/
@[simp] theorem pt_conjugates_one_to_three :
    ptConjugatePhase 1 = 3 := by
  native_decide

@[simp] theorem pt_conjugates_three_to_one :
    ptConjugatePhase 3 = 1 := by
  native_decide

/-- Conjugation preserves the square-root condition. -/
theorem pt_preserves_normal_square_roots
    (phase : NormalRootPhase)
    (hRoot : IsNormalSquareRoot phase) :
    IsNormalSquareRoot (ptConjugatePhase phase) := by
  have hClass :=
    (normal_square_root_iff_one_or_three phase).mp hRoot
  rcases hClass with rfl | rfl
  · exact three_is_normal_square_root
  · exact one_is_normal_square_root

/-- Neither square root is invariant under PT. -/
theorem normal_square_root_is_not_pt_fixed
    (phase : NormalRootPhase)
    (hRoot : IsNormalSquareRoot phase) :
    ptConjugatePhase phase ≠ phase := by
  have hClass :=
    (normal_square_root_iff_one_or_three phase).mp hRoot
  rcases hClass with rfl | rfl <;> native_decide

/-- Flat cyclic character determined by the phase of one generator. -/
def normalRootCharacter
    (phase : NormalRootPhase) (winding : ℤ) : NormalRootPhase :=
  (winding : NormalRootPhase) * phase

/-- The character respects addition of windings. -/
theorem normal_root_character_additive
    (phase : NormalRootPhase)
    (first second : ℤ) :
    normalRootCharacter phase (first + second) =
      normalRootCharacter phase first +
        normalRootCharacter phase second := by
  unfold normalRootCharacter
  push_cast
  ring

/-- Embedded normal sign character in fourth-root notation. -/
def normalHalfTurnCharacter
    (winding : ℤ) : NormalRootPhase :=
  (winding : NormalRootPhase) * normalHalfTurn

/-- Squaring either root character reproduces the normal orientation character. -/
theorem square_root_character_squares_to_normal_holonomy
    (phase : NormalRootPhase)
    (hRoot : IsNormalSquareRoot phase)
    (winding : ℤ) :
    normalRootCharacter phase winding +
        normalRootCharacter phase winding =
      normalHalfTurnCharacter winding := by
  unfold normalRootCharacter normalHalfTurnCharacter
  calc
    (winding : NormalRootPhase) * phase +
        (winding : NormalRootPhase) * phase =
      (winding : NormalRootPhase) * (phase + phase) := by ring
    _ = (winding : NormalRootPhase) * normalHalfTurn := by
      rw [hRoot]

/-- The two root characters are inverse/PT-conjugate characters. -/
theorem two_normal_root_characters_are_conjugate
    (winding : ℤ) :
    normalRootCharacter 3 winding =
      -normalRootCharacter 1 winding := by
  unfold normalRootCharacter
  have hThree : (3 : NormalRootPhase) = -(1 : NormalRootPhase) := by
    native_decide
  rw [hThree]
  ring

/--
The one-sided normal line therefore has an order-four complex square-root local
system, unique only up to PT conjugation. Topology selects the pair `{+i,-i}`
but does not select one member without an additional orientation/Pin or vacuum
choice.
-/
structure NormalRootLocalSystemStatus where
  oneSidedNormalLineConstructed : Prop
  normalHolonomyMinusOneProved : Prop
  complexifiedNormalLineConstructed : Prop
  squareRootFlatLineConstructed : Prop
  squareIsNormalComplexificationProved : Prop
  exactlyTwoFiniteOrderRootsClassified : Prop
  ptExchangesRootsProved : Prop
  physicalRootOrPairedSectorSelected : Prop


def normalRootLocalSystemClosed
    (s : NormalRootLocalSystemStatus) : Prop :=
  s.oneSidedNormalLineConstructed /\
  s.normalHolonomyMinusOneProved /\
  s.complexifiedNormalLineConstructed /\
  s.squareRootFlatLineConstructed /\
  s.squareIsNormalComplexificationProved /\
  s.exactlyTwoFiniteOrderRootsClassified /\
  s.ptExchangesRootsProved /\
  s.physicalRootOrPairedSectorSelected

end P0EFTJanusNormalOrientationZ4Lift
end JanusFormal
