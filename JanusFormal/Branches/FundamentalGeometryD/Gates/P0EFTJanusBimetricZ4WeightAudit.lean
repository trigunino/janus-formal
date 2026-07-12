import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusPeriodicQuarterCompetition

namespace JanusFormal
namespace P0EFTJanusBimetricZ4WeightAudit

set_option autoImplicit false

open P0EFTJanusPeriodicQuarterCompetition

/-- Four-dimensional physical helicity counts. -/
def masslessSpinTwoPolarizations : ℝ := 2

/-- A healthy massive spin-two field in four dimensions has five polarizations. -/
def massiveSpinTwoPolarizations : ℝ := 5

/-- One massless plus one massive spin-two determinant is below the periodic/Z4 threshold. -/
theorem standard_bimetric_two_to_five_has_no_stationary_radial
    (radial : ℝ) :
    stationarityPolynomial
      masslessSpinTwoPolarizations
      massiveSpinTwoPolarizations radial ≠ 0 := by
  apply negative_discriminant_has_no_stationary_point
  norm_num [masslessSpinTwoPolarizations, massiveSpinTwoPolarizations]

/-- Two PT-related massive towers versus one shared massless tower give weights `2:10`. -/
def doubledMassiveSpinTwoWeight : ℝ :=
  2 * massiveSpinTwoPolarizations

/-- The `2:10` polynomial is twice the first `1:5` polynomial. -/
theorem doubled_massive_polynomial_factorization
    (radial : ℝ) :
    stationarityPolynomial
      masslessSpinTwoPolarizations
      doubledMassiveSpinTwoWeight radial =
      2 * (2 * radial - 1) * (3 * radial - 1) := by
  unfold stationarityPolynomial masslessSpinTwoPolarizations
    doubledMassiveSpinTwoWeight massiveSpinTwoPolarizations
  ring

/-- The doubled-spin-two candidate has exactly the radial roots `1/2` and `1/3`. -/
theorem doubled_massive_stationary_iff
    (radial : ℝ) :
    stationarityPolynomial
      masslessSpinTwoPolarizations
      doubledMassiveSpinTwoWeight radial = 0 ↔
      2 * radial = 1 \/ 3 * radial = 1 := by
  rw [doubled_massive_polynomial_factorization]
  constructor
  · intro hProduct
    have hTwo : (2 : ℝ) ≠ 0 := by norm_num
    have hReduced :
        (2 * radial - 1) * (3 * radial - 1) = 0 :=
      (mul_eq_zero.mp hProduct).resolve_left hTwo
    rcases mul_eq_zero.mp hReduced with hHalf | hThird
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (hHalf | hThird)
    · have hZero : 2 * radial - 1 = 0 := by linarith
      rw [hZero]
      ring
    · have hZero : 3 * radial - 1 = 0 := by linarith
      rw [hZero]
      ring

/-- The smaller root `r=1/3` is present in the doubled massive-spin-two model. -/
@[simp] theorem one_third_is_doubled_massive_stationary :
    stationarityPolynomial
      masslessSpinTwoPolarizations
      doubledMassiveSpinTwoWeight (1 / 3) = 0 := by
  norm_num [stationarityPolynomial, masslessSpinTwoPolarizations,
    doubledMassiveSpinTwoWeight, massiveSpinTwoPolarizations]

/--
The determinant algebra therefore distinguishes two architectures:

* standard ghost-free bimetric count `2+5`: insufficient by itself;
* one shared massless mode plus two PT-related massive towers `2+10`: exactly
  the ratio `1:5`, with the candidate minimum at `exp(-m*T)=1/3`.

The second interpretation is physical only if the two massive towers are truly
independent and the shared massless determinant is counted once rather than
being a double-counting artifact.
-/
structure BimetricWeightDerivationStatus where
  diagonalMasslessModeConstructed : Prop
  relativeMassiveModeConstructed : Prop
  ptRelatedSecondMassiveTowerDerived : Prop
  noDoubleCountingProved : Prop
  gaugeAndGhostWeightsComputed : Prop
  effectivePeriodicWeightEqualsTwo : Prop
  effectiveQuarterWeightEqualsTen : Prop
  determinantSignsDerived : Prop
  stableOneThirdRootDerived : Prop


def bimetricWeightDerivationClosed
    (s : BimetricWeightDerivationStatus) : Prop :=
  s.diagonalMasslessModeConstructed /\
  s.relativeMassiveModeConstructed /\
  s.ptRelatedSecondMassiveTowerDerived /\
  s.noDoubleCountingProved /\
  s.gaugeAndGhostWeightsComputed /\
  s.effectivePeriodicWeightEqualsTwo /\
  s.effectiveQuarterWeightEqualsTen /\
  s.determinantSignsDerived /\
  s.stableOneThirdRootDerived

end P0EFTJanusBimetricZ4WeightAudit
end JanusFormal
