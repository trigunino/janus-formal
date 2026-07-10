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
  have hSquare :
      (4 * s.chargeUnit * s.throatRadius ^ 2) ^ 2 = 1 := by
    nlinarith [s.primitiveRadiusLaw]
  have hPositive :
      0 < 4 * s.chargeUnit * s.throatRadius ^ 2 := by
    positivity
  nlinarith [hSquare]

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
    nlinarith [hRadius, s.chargeAreaNormalization]
  have hChargeNonzero : s.chargeUnit ≠ 0 :=
    ne_of_gt s.chargeUnitPositive
  have hSquares :
      4 * s.throatRadius ^ 2 = s.fundamentalLength ^ 2 := by
    have hDifference := (mul_eq_zero.mp hFactor).resolve_left hChargeNonzero
    linarith
  nlinarith [s.throatRadiusPositive, s.fundamentalLengthPositive]

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
