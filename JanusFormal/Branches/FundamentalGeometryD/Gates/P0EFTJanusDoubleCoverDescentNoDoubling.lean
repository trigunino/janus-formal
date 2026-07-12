import Mathlib

namespace JanusFormal
namespace P0EFTJanusDoubleCoverDescentNoDoubling

set_option autoImplicit false

variable {V : Type*}

/-- A pair of cover fields related by the deck action. -/
structure EquivariantFoldPair (deckAction : V → V) where
  positiveFold : V
  negativeFold : V
  descentLaw : negativeFold = deckAction positiveFold

/-- Construct the equivariant pair from one fold. -/
def fromPositiveFold
    (deckAction : V → V)
    (value : V) : EquivariantFoldPair deckAction :=
  { positiveFold := value
    negativeFold := deckAction value
    descentLaw := rfl }

/-- Forget to the positive sheet. -/
def toPositiveFold
    (deckAction : V → V)
    (pair : EquivariantFoldPair deckAction) : V :=
  pair.positiveFold

/-- An equivariant pair is determined by one fold. -/
theorem equivariant_pair_ext
    (deckAction : V → V)
    (first second : EquivariantFoldPair deckAction)
    (hPositive : first.positiveFold = second.positiveFold) :
    first = second := by
  cases first with
  | mk firstPositive firstNegative firstLaw =>
      cases second with
      | mk secondPositive secondNegative secondLaw =>
          simp_all

/-- Descent data are equivalent to one copy of the fiber, not two independent copies. -/
def equivariantPairEquiv
    (deckAction : V → V) :
    EquivariantFoldPair deckAction ≃ V where
  toFun := toPositiveFold deckAction
  invFun := fromPositiveFold deckAction
  left_inv := by
    intro pair
    apply equivariant_pair_ext deckAction
    rfl
  right_inv := by
    intro value
    rfl

/-- Reconstruction from the positive fold is exact. -/
theorem reconstruct_from_positive_fold
    (deckAction : V → V)
    (pair : EquivariantFoldPair deckAction) :
    fromPositiveFold deckAction
        (toPositiveFold deckAction pair) = pair :=
  (equivariantPairEquiv deckAction).left_inv pair

/-- Independent two-fold data are a different type with no descent constraint. -/
abbrev IndependentFoldPair (V : Type*) := V × V

/-- A claimed second independent value is fixed once descent is imposed. -/
theorem negative_fold_is_not_independent
    (deckAction : V → V)
    (pair : EquivariantFoldPair deckAction) :
    pair.negativeFold = deckAction pair.positiveFold :=
  pair.descentLaw

/-- Finite-component field on one sheet. -/
abbrev RankField (rank : ℕ) := Fin rank → ℝ

/-- Cover descent of a rank-`r` field is equivalent to rank `r`, not rank `2r`. -/
def descendedRankFieldEquiv
    (rank : ℕ)
    (deckAction : RankField rank → RankField rank) :
    EquivariantFoldPair deckAction ≃ RankField rank :=
  equivariantPairEquiv deckAction

/--
Passing to the orientation double cover produces two sheet values only before
imposing deck equivariance.  A field descending from the base has one physical
fiber's worth of data.  Multiplying determinant weights by two therefore
requires an additional independent copy or a pushforward/induced field, not
merely the existence of two cover sheets.
-/
structure CoverMultiplicityPhysicalStatus where
  orientationDoubleCoverConstructed : Prop
  deckActionOnFieldBundleDerived : Prop
  equivariantDescentConditionDerived : Prop
  descendedFieldEquivalentToOneFoldProved : Prop
  independentPushforwardFieldConstructed : Prop
  independentCopyCountDerived : Prop
  determinantMultiplicityComputedWithoutDoubleCounting : Prop


def coverMultiplicityPhysicalClosed
    (s : CoverMultiplicityPhysicalStatus) : Prop :=
  s.orientationDoubleCoverConstructed /\
  s.deckActionOnFieldBundleDerived /\
  s.equivariantDescentConditionDerived /\
  s.descendedFieldEquivalentToOneFoldProved /\
  s.independentPushforwardFieldConstructed /\
  s.independentCopyCountDerived /\
  s.determinantMultiplicityComputedWithoutDoubleCounting

end P0EFTJanusDoubleCoverDescentNoDoubling
end JanusFormal
