import Mathlib

namespace JanusFormal
namespace P0EFTJanusPrimitiveChargeAreaScaleLaw

set_option autoImplicit false

/--
A primitive LL flux sector whose charge unit is normalized by one fundamental
area.  The laws are kept in cleared form:

* `q * ell^2 = 1`;
* `16*q^2*R^4 = 1`.
-/
structure FundamentalAreaNormalizedFlux where
  chargeUnit : ℝ
  fundamentalLength : ℝ
  throatRadius : ℝ
  chargeUnitPositive : 0 < chargeUnit
  fundamentalLengthPositive : 0 < fundamentalLength
  throatRadiusPositive : 0 < throatRadius
  chargeAreaNormalization :
    chargeUnit * fundamentalLength ^ 2 = 1
  primitiveRadiusLaw :
    16 * chargeUnit ^ 2 * throatRadius ^ 4 = 1

/-- The positive primitive flux law first reduces to `4*q*R^2=1`. -/
theorem positive_primitive_radius_law
    (s : FundamentalAreaNormalizedFlux) :
    4 * s.chargeUnit * s.throatRadius ^ 2 = 1 := by
  let x : ℝ := 4 * s.chargeUnit * s.throatRadius ^ 2
  have hSquare : x ^ 2 = 1 := by
    dsimp [x]
    calc
      (4 * s.chargeUnit * s.throatRadius ^ 2) ^ 2 =
          16 * s.chargeUnit ^ 2 * s.throatRadius ^ 4 := by ring
      _ = 1 := s.primitiveRadiusLaw
  have hPositive : 0 < x := by
    dsimp [x]
    exact mul_pos
      (mul_pos (by norm_num) s.chargeUnitPositive)
      (pow_pos s.throatRadiusPositive 2)
  have hFactor : (x - 1) * (x + 1) = 0 := by
    nlinarith [hSquare]
  rcases mul_eq_zero.mp hFactor with hMinus | hPlus
  · dsimp [x] at hMinus ⊢
    linarith
  · have hSumPositive : 0 < x + 1 := by linarith
    exfalso
    exact (ne_of_gt hSumPositive) hPlus

/--
A one-quantum inverse-area normalization fixes the throat to half the
fundamental length: `R = ell/2`.
-/
theorem primitive_radius_is_half_fundamental_length
    (s : FundamentalAreaNormalizedFlux) :
    2 * s.throatRadius = s.fundamentalLength := by
  have hRadius := positive_primitive_radius_law s
  have hFactor :
      s.chargeUnit *
        (4 * s.throatRadius ^ 2 - s.fundamentalLength ^ 2) = 0 := by
    calc
      s.chargeUnit *
          (4 * s.throatRadius ^ 2 - s.fundamentalLength ^ 2) =
          4 * s.chargeUnit * s.throatRadius ^ 2 -
            s.chargeUnit * s.fundamentalLength ^ 2 := by ring
      _ = 1 - 1 := by
        rw [hRadius, s.chargeAreaNormalization]
      _ = 0 := by norm_num
  have hChargeNonzero : s.chargeUnit ≠ 0 :=
    ne_of_gt s.chargeUnitPositive
  have hSquares :
      4 * s.throatRadius ^ 2 = s.fundamentalLength ^ 2 := by
    have hDifference := (mul_eq_zero.mp hFactor).resolve_left hChargeNonzero
    linarith
  have hRootFactor :
      (2 * s.throatRadius - s.fundamentalLength) *
        (2 * s.throatRadius + s.fundamentalLength) = 0 := by
    nlinarith [hSquares]
  rcases mul_eq_zero.mp hRootFactor with hDifference | hSum
  · linarith
  · have hSumPositive :
        0 < 2 * s.throatRadius + s.fundamentalLength := by
      nlinarith [s.throatRadiusPositive, s.fundamentalLengthPositive]
    exfalso
    exact (ne_of_gt hSumPositive) hSum

/--
Consequently a Planck-area normalization produces a Planckian throat.  A
cosmological throat requires a new hierarchy in the charge unit or a large
non-primitive sector.
-/
structure HierarchyStatus where
  primitiveSectorUsed : Prop
  chargeNormalizedByPlanckArea : Prop
  cosmologicalRadiusRequired : Prop
  hierarchyMechanismDerived : Prop


def cosmologicalPrimitiveClosure (s : HierarchyStatus) : Prop :=
  s.primitiveSectorUsed /\
  s.chargeNormalizedByPlanckArea /\
  s.cosmologicalRadiusRequired /\
  s.hierarchyMechanismDerived

end P0EFTJanusPrimitiveChargeAreaScaleLaw
end JanusFormal
