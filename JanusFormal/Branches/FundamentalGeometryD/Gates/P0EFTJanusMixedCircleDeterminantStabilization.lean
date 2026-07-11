import Mathlib

namespace JanusFormal
namespace P0EFTJanusMixedCircleDeterminantStabilization

set_option autoImplicit false

/--
Cleared stationarity equation for a common-mass approximation containing
periodic and antiperiodic determinant sectors.  With `y=exp(m*T)>1`, the
renormalized derivative is proportional to

`p/(y-1) - a/(y+1)`.
-/
def mixedStationarity
    (periodicWeight antiperiodicWeight exponent : ℝ) : Prop :=
  periodicWeight * (exponent + 1) =
    antiperiodicWeight * (exponent - 1)

/-- Candidate stationary exponential. -/
noncomputable def stationaryExponent
    (periodicWeight antiperiodicWeight : ℝ) : ℝ :=
  (antiperiodicWeight + periodicWeight) /
    (antiperiodicWeight - periodicWeight)

/-- The candidate is strictly larger than one exactly in the useful weight cone. -/
theorem stationary_exponent_gt_one
    (periodicWeight antiperiodicWeight : ℝ)
    (hPeriodic : 0 < periodicWeight)
    (hDominance : periodicWeight < antiperiodicWeight) :
    1 < stationaryExponent periodicWeight antiperiodicWeight := by
  have hDen : 0 < antiperiodicWeight - periodicWeight :=
    sub_pos.mpr hDominance
  have hDenNonzero : antiperiodicWeight - periodicWeight ≠ 0 :=
    ne_of_gt hDen
  have hDifference :
      stationaryExponent periodicWeight antiperiodicWeight - 1 =
        (2 * periodicWeight) /
          (antiperiodicWeight - periodicWeight) := by
    unfold stationaryExponent
    field_simp [hDenNonzero]
    ring
  rw [sub_pos, hDifference]
  exact div_pos (by nlinarith) hDen

/-- The candidate satisfies the cleared stationarity equation. -/
theorem stationary_exponent_satisfies_equation
    (periodicWeight antiperiodicWeight : ℝ)
    (hDominance : periodicWeight < antiperiodicWeight) :
    mixedStationarity periodicWeight antiperiodicWeight
      (stationaryExponent periodicWeight antiperiodicWeight) := by
  have hDen : antiperiodicWeight - periodicWeight ≠ 0 :=
    ne_of_gt (sub_pos.mpr hDominance)
  unfold mixedStationarity stationaryExponent
  field_simp [hDen]
  ring

/-- Positive unequal weights give a unique stationary exponential. -/
theorem mixed_stationarity_unique
    (periodicWeight antiperiodicWeight exponent : ℝ)
    (hDominance : periodicWeight < antiperiodicWeight)
    (hStationary :
      mixedStationarity periodicWeight antiperiodicWeight exponent) :
    exponent = stationaryExponent periodicWeight antiperiodicWeight := by
  have hDen : antiperiodicWeight - periodicWeight ≠ 0 :=
    ne_of_gt (sub_pos.mpr hDominance)
  unfold mixedStationarity at hStationary
  unfold stationaryExponent
  apply (eq_div_iff hDen).2
  nlinarith [hStationary]

/-- Equal positive weights cannot stabilize at finite exponent. -/
theorem equal_positive_weights_have_no_stationary_exponent
    (weight exponent : ℝ)
    (hWeight : 0 < weight) :
    Not (mixedStationarity weight weight exponent) := by
  intro hStationary
  unfold mixedStationarity at hStationary
  nlinarith

/-- If the antiperiodic weight does not dominate, no `y>1` stationary point exists. -/
theorem nondominant_antiperiodic_weight_has_no_physical_stationary
    (periodicWeight antiperiodicWeight exponent : ℝ)
    (hPeriodic : 0 < periodicWeight)
    (hAntiperiodic : 0 ≤ antiperiodicWeight)
    (hNondominant : antiperiodicWeight ≤ periodicWeight)
    (hExponent : 1 < exponent) :
    Not (mixedStationarity periodicWeight antiperiodicWeight exponent) := by
  intro hStationary
  unfold mixedStationarity at hStationary
  have hPositive :
      0 <
        periodicWeight * (exponent + 1) -
          antiperiodicWeight * (exponent - 1) := by
    have hGap : 0 ≤ periodicWeight - antiperiodicWeight :=
      sub_nonneg.mpr hNondominant
    have hExpGap : 0 < exponent - 1 := sub_pos.mpr hExponent
    nlinarith [mul_nonneg hGap (le_of_lt hExpGap)]
  nlinarith

/-- Numerator controlling the second derivative sign at fixed `y`. -/
def mixedCurvatureNumerator
    (periodicWeight antiperiodicWeight exponent : ℝ) : ℝ :=
  exponent *
    (antiperiodicWeight * (exponent - 1) ^ 2 -
      periodicWeight * (exponent + 1) ^ 2)

/-- Under stationarity the curvature numerator factorizes exactly. -/
theorem mixed_curvature_factorization_at_stationarity
    (periodicWeight antiperiodicWeight exponent : ℝ)
    (hStationary :
      mixedStationarity periodicWeight antiperiodicWeight exponent) :
    mixedCurvatureNumerator periodicWeight antiperiodicWeight exponent =
      exponent * (exponent - 1) * (exponent + 1) *
        (periodicWeight - antiperiodicWeight) := by
  have hResidual :
      periodicWeight * (exponent + 1) -
        antiperiodicWeight * (exponent - 1) = 0 := by
    unfold mixedStationarity at hStationary
    linarith
  unfold mixedCurvatureNumerator
  calc
    exponent *
        (antiperiodicWeight * (exponent - 1) ^ 2 -
          periodicWeight * (exponent + 1) ^ 2) =
      exponent *
        ((exponent - 1) * (exponent + 1) *
            (periodicWeight - antiperiodicWeight) -
          2 * exponent *
            (periodicWeight * (exponent + 1) -
              antiperiodicWeight * (exponent - 1))) := by ring
    _ = exponent * (exponent - 1) * (exponent + 1) *
        (periodicWeight - antiperiodicWeight) := by
      rw [hResidual]
      ring

/-- In the physical weight cone, the bosonic-sign curvature numerator is negative. -/
theorem mixed_curvature_negative_at_physical_stationary
    (periodicWeight antiperiodicWeight exponent : ℝ)
    (hDominance : periodicWeight < antiperiodicWeight)
    (hExponent : 1 < exponent)
    (hStationary :
      mixedStationarity periodicWeight antiperiodicWeight exponent) :
    mixedCurvatureNumerator periodicWeight antiperiodicWeight exponent < 0 := by
  rw [mixed_curvature_factorization_at_stationarity
    periodicWeight antiperiodicWeight exponent hStationary]
  have hExponentPositive : 0 < exponent := lt_trans (by norm_num) hExponent
  have hMinusPositive : 0 < exponent - 1 := sub_pos.mpr hExponent
  have hPlusPositive : 0 < exponent + 1 := by linarith
  have hWeightNegative : periodicWeight - antiperiodicWeight < 0 :=
    sub_neg.mpr hDominance
  exact mul_neg_of_pos_of_neg
    (mul_pos (mul_pos hExponentPositive hMinusPositive) hPlusPositive)
    hWeightNegative

/-- With the overall fermionic determinant sign, the same stationary point is a local minimum proxy. -/
theorem fermionic_sign_reverses_curvature_to_positive
    (periodicWeight antiperiodicWeight exponent : ℝ)
    (hDominance : periodicWeight < antiperiodicWeight)
    (hExponent : 1 < exponent)
    (hStationary :
      mixedStationarity periodicWeight antiperiodicWeight exponent) :
    0 < -mixedCurvatureNumerator
      periodicWeight antiperiodicWeight exponent := by
  exact neg_pos.mpr
    (mixed_curvature_negative_at_physical_stationary
      periodicWeight antiperiodicWeight exponent
      hDominance hExponent hStationary)

/-- The smallest integer weight pair `p=2`, `a=3` gives `exp(m*T)=5`. -/
@[simp] theorem two_periodic_three_antiperiodic_exponent :
    stationaryExponent 2 3 = 5 := by
  norm_num [stationaryExponent]

/--
This mechanism is a genuine finite-modulus candidate, but it requires a derived
field content with unequal periodic/antiperiodic effective weights and the
fermionic sign.  It is not generated by a single exact-quarter-holonomy tower.
-/
structure MixedDeterminantPhysicalStatus where
  circleProductFormulaDerived : Prop
  commonMassApproximationControlled : Prop
  periodicSectorDerived : Prop
  antiperiodicSectorDerived : Prop
  effectiveWeightsComputed : Prop
  antiperiodicWeightDominates : Prop
  fermionicOverallSignDerived : Prop
  higherSphereModesControlled : Prop
  localCountertermsFixed : Prop
  stableFiniteModulusDerived : Prop


def mixedDeterminantPhysicalClosure
    (s : MixedDeterminantPhysicalStatus) : Prop :=
  s.circleProductFormulaDerived /\
  s.commonMassApproximationControlled /\
  s.periodicSectorDerived /\
  s.antiperiodicSectorDerived /\
  s.effectiveWeightsComputed /\
  s.antiperiodicWeightDominates /\
  s.fermionicOverallSignDerived /\
  s.higherSphereModesControlled /\
  s.localCountertermsFixed /\
  s.stableFiniteModulusDerived

end P0EFTJanusMixedCircleDeterminantStabilization
end JanusFormal
