import Mathlib

namespace JanusFormal
namespace P0EFTJanusThroatMonopoleEmergence

set_option autoImplicit false

/--
Integer monopole class on the canonical `S2` factor of the resolved throat
`Sigma = S2 x S1`.
-/
structure ThroatMonopoleClass where
  firstChernNumber : ℤ
  nontrivial : firstChernNumber ≠ 0
  leastNonzeroMagnitude :
    ∀ m : ℤ, m ≠ 0 → firstChernNumber.natAbs ≤ m.natAbs

/-- A least nonzero Chern class is necessarily primitive. -/
theorem least_nonzero_c1_is_primitive
    (s : ThroatMonopoleClass) :
    s.firstChernNumber.natAbs = 1 := by
  have hLe : s.firstChernNumber.natAbs ≤ 1 :=
    s.leastNonzeroMagnitude 1 (by norm_num)
  have hPos : 0 < s.firstChernNumber.natAbs :=
    Int.natAbs_pos.mpr s.nontrivial
  omega

/-- PT reverses the signed monopole class. -/
def ptConjugateChernNumber (n : ℤ) : ℤ := -n

@[simp] theorem pt_conjugation_preserves_c1_magnitude (n : ℤ) :
    (ptConjugateChernNumber n).natAbs = n.natAbs := by
  simp [ptConjugateChernNumber]

@[simp] theorem pt_conjugation_is_involutive (n : ℤ) :
    ptConjugateChernNumber (ptConjugateChernNumber n) = n := by
  simp [ptConjugateChernNumber]

/--
The mapping-torus circle lowers a degree-three boundary class to the degree-two
monopole class.  On integers the transgression is multiplication by the circle
winding.
-/
structure ThroatCircleTransgression where
  boundaryThreeClass : ℤ
  circleWinding : ℤ
  throatChernNumber : ℤ
  transportLaw :
    throatChernNumber = circleWinding * boundaryThreeClass
  primitiveBoundaryClass : boundaryThreeClass.natAbs = 1
  primitiveCircleWinding : circleWinding.natAbs = 1

/-- Primitive boundary class and primitive circle winding give primitive monopole flux. -/
theorem primitive_transgression_gives_primitive_monopole
    (s : ThroatCircleTransgression) :
    s.throatChernNumber.natAbs = 1 := by
  rw [s.transportLaw, Int.natAbs_mul,
    s.primitiveCircleWinding, s.primitiveBoundaryClass]

/--
The topology fixes the integer sector but not the dimensionful normalization of
the physical curvature.  That normalization remains an interface to the
world-volume quantum theory.
-/
structure EmergentThroatGaugeStatus where
  canonicalS2FactorDerived : Prop
  compactMappingTorusCircleDerived : Prop
  primitiveMonopoleLineBundleDerived : Prop
  connectionWithCurvatureDerived : Prop
  ptConjugateBundleDerived : Prop
  dimensionfulGaugeNormalizationDerived : Prop
  llAuxiliaryFieldIdentified : Prop


def emergentThroatGaugeClosed
    (s : EmergentThroatGaugeStatus) : Prop :=
  s.canonicalS2FactorDerived /\
  s.compactMappingTorusCircleDerived /\
  s.primitiveMonopoleLineBundleDerived /\
  s.connectionWithCurvatureDerived /\
  s.ptConjugateBundleDerived /\
  s.dimensionfulGaugeNormalizationDerived /\
  s.llAuxiliaryFieldIdentified

end P0EFTJanusThroatMonopoleEmergence
end JanusFormal
