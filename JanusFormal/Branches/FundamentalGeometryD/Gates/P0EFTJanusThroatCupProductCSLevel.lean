import Mathlib

namespace JanusFormal
namespace P0EFTJanusThroatCupProductCSLevel

set_option autoImplicit false

/--
Integral cohomology generators of `Sigma = S2 x S1` are represented by a
circle winding in degree one and a monopole Chern number in degree two.  Their
cup product evaluates on the fundamental class as the integer product.
-/
structure ThroatCohomologyPairing where
  circleWinding : ℤ
  monopoleChernNumber : ℤ
  topPairingNumber : ℤ
  cupEvaluationLaw :
    topPairingNumber = circleWinding * monopoleChernNumber

/-- Primitive degree-one and degree-two classes give a primitive top pairing. -/
theorem primitive_generators_give_unit_top_pairing
    (s : ThroatCohomologyPairing)
    (hCircle : s.circleWinding.natAbs = 1)
    (hMonopole : s.monopoleChernNumber.natAbs = 1) :
    s.topPairingNumber.natAbs = 1 := by
  rw [s.cupEvaluationLaw, Int.natAbs_mul, hCircle, hMonopole]
  norm_num

/-- Simultaneous PT reversal of circle and monopole classes preserves the top pairing. -/
theorem simultaneous_pt_reversal_preserves_top_pairing
    (circle monopole : ℤ) :
    (-circle) * (-monopole) = circle * monopole := by
  ring

/-- Reversing only one of the two classes reverses the top pairing. -/
theorem single_pt_reversal_reverses_top_pairing
    (circle monopole : ℤ) :
    (-circle) * monopole = -(circle * monopole) /\
      circle * (-monopole) = -(circle * monopole) := by
  constructor <;> ring

/--
A Chern--Simons sector whose allowed nonzero levels are integers and whose
physical principle selects least magnitude is primitive.
-/
structure MinimalChernSimonsLevel where
  level : ℤ
  nonzero : level ≠ 0
  leastNonzeroMagnitude :
    ∀ k : ℤ, k ≠ 0 → level.natAbs ≤ k.natAbs

/-- Least nonzero integral Chern--Simons level has magnitude one. -/
theorem minimal_cs_level_is_primitive
    (s : MinimalChernSimonsLevel) :
    s.level.natAbs = 1 := by
  have hLe := s.leastNonzeroMagnitude 1 (by norm_num)
  have hPos : 0 < s.level.natAbs := Int.natAbs_pos.mpr s.nonzero
  omega

/--
Program D can therefore target a level-one spin/Pin Chern--Simons theory, but it
must still derive why the least nonzero anomaly-compatible level is selected
and how the geometric cup pairing enters the renormalized action.
-/
structure GeometricCSLevelStatus where
  throatH1GeneratorDerived : Prop
  throatH2GeneratorDerived : Prop
  cupProductToH3Derived : Prop
  primitiveTopPairingDerived : Prop
  etaInvariantRefinementDerived : Prop
  anomalyAllowedLevelsComputed : Prop
  leastNonzeroLevelSelected : Prop
  levelMagnitudeOneDerived : Prop


def geometricCSLevelClosed (s : GeometricCSLevelStatus) : Prop :=
  s.throatH1GeneratorDerived /\
  s.throatH2GeneratorDerived /\
  s.cupProductToH3Derived /\
  s.primitiveTopPairingDerived /\
  s.etaInvariantRefinementDerived /\
  s.anomalyAllowedLevelsComputed /\
  s.leastNonzeroLevelSelected /\
  s.levelMagnitudeOneDerived

end P0EFTJanusThroatCupProductCSLevel
end JanusFormal
