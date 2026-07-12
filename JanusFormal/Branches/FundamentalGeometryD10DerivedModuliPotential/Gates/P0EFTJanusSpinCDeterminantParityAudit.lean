import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpinCDeterminantParityAudit

set_option autoImplicit false

/--
On a spin three-manifold, twisting a chosen spinor bundle by a complex line
`E` produces a SpinC structure whose determinant line is `E^2`. This module
records only the resulting Chern-number arithmetic.
-/
structure SpinTwistChernData where
  twistChernNumber : ℤ
  determinantChernNumber : ℤ
  determinantLaw :
    determinantChernNumber = 2 * twistChernNumber

/-- The determinant Chern number is even in the spin-plus-line realization. -/
theorem determinant_chern_number_even
    (s : SpinTwistChernData) :
    Even s.determinantChernNumber := by
  refine ⟨s.twistChernNumber, ?_⟩
  rw [s.determinantLaw]
  ring

/-- A primitive twist line has determinant Chern magnitude two. -/
theorem primitive_twist_forces_determinant_magnitude_two
    (s : SpinTwistChernData)
    (hPrimitive : s.twistChernNumber.natAbs = 1) :
    s.determinantChernNumber.natAbs = 2 := by
  rw [s.determinantLaw, Int.natAbs_mul, hPrimitive]
  norm_num

/-- A primitive twist line cannot simultaneously be a determinant line of Chern magnitude one. -/
theorem primitive_twist_and_primitive_determinant_incompatible
    (s : SpinTwistChernData)
    (hTwistPrimitive : s.twistChernNumber.natAbs = 1)
    (hDeterminantPrimitive : s.determinantChernNumber.natAbs = 1) :
    False := by
  have hMagnitude :=
    primitive_twist_forces_determinant_magnitude_two
      s hTwistPrimitive
  omega

/-- A determinant line of odd Chern number cannot arise by twisting a fixed spin structure by one line. -/
theorem odd_determinant_excludes_spin_twist_realization
    (s : SpinTwistChernData)
    (hOdd : Odd s.determinantChernNumber) :
    False := by
  rcases determinant_chern_number_even s with ⟨evenHalf, hEven⟩
  rcases hOdd with ⟨oddHalf, hOdd⟩
  omega

/--
Correct convention for the Janus primitive monopole candidate:

* either `c1(E)=±1` is the charge-one **twisting line** of a spin Dirac
  operator, in which case the associated SpinC determinant has `c1=±2`;
* or a different charge normalization must be stated explicitly.

Calling the same line both a primitive `c1=1` monopole line and the SpinC
determinant line silently mixes these two conventions.
-/
structure SpinCConventionPhysicalStatus where
  throatSpinStructureConstructed : Prop
  primitiveTwistingLineConstructed : Prop
  twistChernNumberNormalized : Prop
  determinantLineIdentifiedAsSquare : Prop
  determinantChernNumberComputed : Prop
  gaugeChargeConventionMatched : Prop
  diracSpectrumRecomputedInSameConvention : Prop
  llChargeNormalizationMatched : Prop


def spinCConventionPhysicalClosure
    (s : SpinCConventionPhysicalStatus) : Prop :=
  s.throatSpinStructureConstructed /\
  s.primitiveTwistingLineConstructed /\
  s.twistChernNumberNormalized /\
  s.determinantLineIdentifiedAsSquare /\
  s.determinantChernNumberComputed /\
  s.gaugeChargeConventionMatched /\
  s.diracSpectrumRecomputedInSameConvention /\
  s.llChargeNormalizationMatched

end P0EFTJanusSpinCDeterminantParityAudit
end JanusFormal
