import Mathlib

namespace JanusFormal
namespace P0EFTJanusPeriodicQuarterCompetition

set_option autoImplicit false

/--
Cleared stationarity polynomial for a common-mass competition between a
periodic determinant sector of weight `p` and an exact-quarter-holonomy sector
of weight `q`:

`(p+q) r^2 - q r + p = 0`, where `r=exp(-m*T)` lies in `(0,1)`.
-/
def stationarityPolynomial
    (periodicWeight quarterWeight radial : ℝ) : ℝ :=
  (periodicWeight + quarterWeight) * radial ^ 2 -
    quarterWeight * radial + periodicWeight

/-- Cleared derivative numerator; its denominator is positive for `0<r<1`. -/
def derivativeNumerator
    (periodicWeight quarterWeight radial : ℝ) : ℝ :=
  2 * radial *
    stationarityPolynomial periodicWeight quarterWeight radial

/-- Stationarity forces a nonnegative discriminant. -/
theorem stationary_implies_nonnegative_discriminant
    (periodicWeight quarterWeight radial : ℝ)
    (hStationary :
      stationarityPolynomial periodicWeight quarterWeight radial = 0) :
    0 ≤ quarterWeight ^ 2 -
      4 * periodicWeight * (periodicWeight + quarterWeight) := by
  have hSquare :
      0 ≤
        (2 * (periodicWeight + quarterWeight) * radial -
          quarterWeight) ^ 2 := sq_nonneg _
  have hIdentity :
      (2 * (periodicWeight + quarterWeight) * radial -
          quarterWeight) ^ 2 =
        quarterWeight ^ 2 -
          4 * periodicWeight *
            (periodicWeight + quarterWeight) := by
    unfold stationarityPolynomial at hStationary
    nlinarith [hStationary]
  rw [hIdentity] at hSquare
  exact hSquare

/-- A negative discriminant rules out every real stationary modulus. -/
theorem negative_discriminant_has_no_stationary_point
    (periodicWeight quarterWeight radial : ℝ)
    (hNegative :
      quarterWeight ^ 2 <
        4 * periodicWeight * (periodicWeight + quarterWeight)) :
    stationarityPolynomial periodicWeight quarterWeight radial ≠ 0 := by
  intro hStationary
  have hNonnegative :=
    stationary_implies_nonnegative_discriminant
      periodicWeight quarterWeight radial hStationary
  linarith

/-- Equal positive weights are far below the stabilization threshold. -/
theorem equal_positive_weights_have_no_stationary_point
    (weight radial : ℝ)
    (hWeight : 0 < weight) :
    stationarityPolynomial weight weight radial ≠ 0 := by
  apply negative_discriminant_has_no_stationary_point
  nlinarith [sq_pos_of_pos hWeight]

/-- For integer weights with one periodic degree of freedom, quarter weight at most four is insufficient. -/
theorem one_periodic_at_most_four_quarter_has_no_stationary
    (quarterWeight : ℕ)
    (hQuarter : quarterWeight ≤ 4)
    (radial : ℝ) :
    stationarityPolynomial 1 (quarterWeight : ℝ) radial ≠ 0 := by
  apply negative_discriminant_has_no_stationary_point
  interval_cases quarterWeight <;> norm_num

/-- The first integer weight pair crossing the threshold is `p:q=1:5`. -/
theorem one_to_five_stationarity_factorization
    (radial : ℝ) :
    stationarityPolynomial 1 5 radial =
      (2 * radial - 1) * (3 * radial - 1) := by
  unfold stationarityPolynomial
  ring

/-- The two stationary radial values are exactly `1/2` and `1/3`. -/
theorem one_to_five_stationary_iff
    (radial : ℝ) :
    stationarityPolynomial 1 5 radial = 0 ↔
      2 * radial = 1 \/ 3 * radial = 1 := by
  rw [one_to_five_stationarity_factorization]
  constructor
  · intro hProduct
    rcases mul_eq_zero.mp hProduct with hHalf | hThird
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (hHalf | hThird)
    · have : 2 * radial - 1 = 0 := by linarith
      rw [this, zero_mul]
    · have : 3 * radial - 1 = 0 := by linarith
      rw [this, mul_zero]

/-- The larger radial root is one half. -/
@[simp] theorem half_is_one_to_five_stationary :
    stationarityPolynomial 1 5 (1 / 2) = 0 := by
  norm_num [stationarityPolynomial]

/-- The smaller radial root is one third. -/
@[simp] theorem third_is_one_to_five_stationary :
    stationarityPolynomial 1 5 (1 / 3) = 0 := by
  norm_num [stationarityPolynomial]

/-- Below `r=1/3`, the cleared derivative is positive. -/
theorem one_to_five_derivative_positive_below_third
    (radial : ℝ)
    (hRadial : 0 < radial)
    (hBelow : 3 * radial < 1) :
    0 < derivativeNumerator 1 5 radial := by
  rw [derivativeNumerator, one_to_five_stationarity_factorization]
  have hTwoNegative : 2 * radial - 1 < 0 := by nlinarith
  have hThreeNegative : 3 * radial - 1 < 0 := by linarith
  have hProductPositive :
      0 < (2 * radial - 1) * (3 * radial - 1) :=
    mul_pos_of_neg_of_neg hTwoNegative hThreeNegative
  exact mul_pos (mul_pos (by norm_num) hRadial) hProductPositive

/-- Between the roots, the cleared derivative is negative. -/
theorem one_to_five_derivative_negative_between_roots
    (radial : ℝ)
    (hAboveThird : 1 < 3 * radial)
    (hBelowHalf : 2 * radial < 1) :
    derivativeNumerator 1 5 radial < 0 := by
  rw [derivativeNumerator, one_to_five_stationarity_factorization]
  have hRadial : 0 < radial := by nlinarith
  have hTwoNegative : 2 * radial - 1 < 0 := by linarith
  have hThreePositive : 0 < 3 * radial - 1 := by linarith
  have hProductNegative :
      (2 * radial - 1) * (3 * radial - 1) < 0 :=
    mul_neg_of_neg_of_pos hTwoNegative hThreePositive
  exact mul_neg_of_pos_of_neg
    (mul_pos (by norm_num) hRadial) hProductNegative

/-- Above `r=1/2`, the cleared derivative is positive. -/
theorem one_to_five_derivative_positive_above_half
    (radial : ℝ)
    (hAbove : 1 < 2 * radial) :
    0 < derivativeNumerator 1 5 radial := by
  rw [derivativeNumerator, one_to_five_stationarity_factorization]
  have hRadial : 0 < radial := by nlinarith
  have hTwoPositive : 0 < 2 * radial - 1 := by linarith
  have hThreePositive : 0 < 3 * radial - 1 := by nlinarith
  exact mul_pos
    (mul_pos (by norm_num) hRadial)
    (mul_pos hTwoPositive hThreePositive)

/--
Since `r=exp(-x)` decreases as `x=m*T` increases, the root `r=1/2`
corresponds to an extremum at `x=log 2`, while `r=1/3` corresponds to the
opposite extremum at `x=log 3`.  For the bosonic-sign potential the sign pattern
selects the latter as the local minimum; an overall fermionic sign exchanges
their roles.
-/
structure PeriodicQuarterPhysicalStatus where
  periodicSectorDerived : Prop
  quarterHolonomySectorDerived : Prop
  commonMassApproximationControlled : Prop
  effectiveWeightRatioComputed : Prop
  thresholdExceeded : Prop
  localCountertermsFixed : Prop
  higherModesIncluded : Prop
  stableRootSelected : Prop
  alphaLockRecoveredAtStableRoot : Prop


def periodicQuarterPhysicalClosure
    (s : PeriodicQuarterPhysicalStatus) : Prop :=
  s.periodicSectorDerived /\
  s.quarterHolonomySectorDerived /\
  s.commonMassApproximationControlled /\
  s.effectiveWeightRatioComputed /\
  s.thresholdExceeded /\
  s.localCountertermsFixed /\
  s.higherModesIncluded /\
  s.stableRootSelected /\
  s.alphaLockRecoveredAtStableRoot

end P0EFTJanusPeriodicQuarterCompetition
end JanusFormal
