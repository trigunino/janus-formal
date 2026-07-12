import Mathlib

namespace JanusFormal
namespace P0EFTJanusCodimensionOneZ4NoGo

set_option autoImplicit false

/-- Any real scalar of fourth power one already has square one. -/
theorem real_fourth_root_of_unity_has_order_at_most_two
    (scalar : ℝ)
    (hFourth : scalar ^ 4 = 1) :
    scalar ^ 2 = 1 := by
  have hSquareNonnegative : 0 ≤ scalar ^ 2 := sq_nonneg scalar
  have hSquareSquared : (scalar ^ 2) ^ 2 = 1 := by
    nlinarith [hFourth]
  nlinarith

/-- A genuine order-four action on a real line does not exist. -/
theorem no_genuine_order_four_real_line_action
    (scalar : ℝ) :
    Not (scalar ^ 4 = 1 /\ scalar ^ 2 ≠ 1) := by
  rintro ⟨hFourth, hNotSquare⟩
  exact hNotSquare
    (real_fourth_root_of_unity_has_order_at_most_two
      scalar hFourth)

/-- Every real orthogonal line action is a sign. -/
theorem real_line_isometry_is_sign
    (scalar : ℝ)
    (hNorm : scalar ^ 2 = 1) :
    scalar = 1 \/ scalar = -1 := by
  have hFactor : (scalar - 1) * (scalar + 1) = 0 := by
    nlinarith [hNorm]
  rcases mul_eq_zero.mp hFactor with hPositive | hNegative
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- A two-dimensional real quarter-turn does exist. -/
abbrev RealPlane := Fin 2 → ℝ

/-- `J(x,y)=(-y,x)`. -/
def planeQuarterTurn (v : RealPlane) : RealPlane :=
  fun index => if index = 0 then -v 1 else v 0

/-- Squaring gives minus the identity. -/
theorem plane_quarter_turn_square
    (v : RealPlane) :
    planeQuarterTurn (planeQuarterTurn v) =
      fun index => -v index := by
  funext index
  fin_cases index <;> simp [planeQuarterTurn]

/-- Four applications give the identity. -/
theorem plane_quarter_turn_four
    (v : RealPlane) :
    planeQuarterTurn
      (planeQuarterTurn
        (planeQuarterTurn
          (planeQuarterTurn v))) = v := by
  rw [plane_quarter_turn_square,
    plane_quarter_turn_square]
  funext index
  simp

/--
The codimension-one Janus normal bundle itself carries only sign holonomy.
A genuine `Z4` action needs a complex square-root line, a doubled real plane or
another higher-rank bundle.  It cannot be an ordinary rotation of the single
real normal coordinate.
-/
structure CodimensionOneZ4ExitStatus where
  throatCodimensionOneProved : Prop
  realNormalLineConstructed : Prop
  normalSignHolonomyDerived : Prop
  directRealLineZ4Rejected : Prop
  complexNormalSquareRootConstructed : Prop
  doubledRealPlaneConstructed : Prop
  higherRankInternalBundleConstructed : Prop
  selectedExitCoupledToFields : Prop


def codimensionOneZ4ExitClosed
    (s : CodimensionOneZ4ExitStatus) : Prop :=
  s.throatCodimensionOneProved /\
  s.realNormalLineConstructed /\
  s.normalSignHolonomyDerived /\
  s.directRealLineZ4Rejected /\
  (s.complexNormalSquareRootConstructed \/
    s.doubledRealPlaneConstructed \/
    s.higherRankInternalBundleConstructed) /\
  s.selectedExitCoupledToFields

end P0EFTJanusCodimensionOneZ4NoGo
end JanusFormal
