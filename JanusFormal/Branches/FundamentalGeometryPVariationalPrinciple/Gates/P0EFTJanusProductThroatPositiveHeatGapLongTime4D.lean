import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHeatOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D

/-!
# Positive heat gap and long-time decay on the product throat

The monopole sphere already supplies a strictly positive uniform lower bound
for every separated product mode:

```text
1 / R^2 ≤ lambda_sphere ≤ lambda_sphere + lambda_circle.
```

The circle contribution is nonnegative.  Consequently the genuine infinite
product-throat nuclear heat trace satisfies, for `t ≥ 1`,

```text
Tr(exp(-t H_product))
  ≤ exp(1 / R^2) Tr(exp(-H_product)) exp(-(1 / R^2) t).
```

This is a positive spectral statement for the concrete reference heat
generator.  It is deliberately distinct from the two-sided H14 Fredholm norm
gap, which by itself would not imply heat decay.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatPositiveHeatGapLongTime4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleSphereHeatTrace
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusProductThroatNuclearHeatTrace4D
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D

/-- Uniform positive heat gap supplied by the first monopole-sphere level. -/
def productThroatPositiveHeatGap
    (data : ProductThroatSpectralData) : Real :=
  1 / data.sphereRadius ^ 2

/-- Unit positive heat time used to normalize the long-time envelope. -/
def unitProductThroatHeatTime : HeatTime :=
  ⟨1, zero_lt_one⟩

/-- Full squared heat energy of one degenerate product mode. -/
def productThroatModeEnergy
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) : Real :=
  sphereEigenvalueSquared data mode.1.1 +
    circleOperatorSquaredEigenvalue fold twist mode.2

/-- The sphere radius gives a genuinely positive decay rate. -/
theorem productThroatPositiveHeatGap_pos
    (data : ProductThroatSpectralData) :
    0 < productThroatPositiveHeatGap data := by
  unfold productThroatPositiveHeatGap
  exact div_pos zero_lt_one (sq_pos_of_pos data.sphereRadiusPositive)

/-- Every monopole-sphere eigenvalue is at least the uniform radius gap. -/
theorem productThroatPositiveHeatGap_le_sphereEigenvalueSquared
    (data : ProductThroatSpectralData) (level : Nat) :
    productThroatPositiveHeatGap data ≤
      sphereEigenvalueSquared data level := by
  have hRadius : 0 < data.sphereRadius ^ 2 :=
    sq_pos_of_pos data.sphereRadiusPositive
  have hLevel : (1 : Real) ≤ ((level + 1 : Nat) : Real) := by
    norm_num
  calc
    productThroatPositiveHeatGap data =
        1 / data.sphereRadius ^ 2 := rfl
    _ ≤ ((level + 1 : Nat) : Real) / data.sphereRadius ^ 2 :=
      (div_le_div_iff_of_pos_right hRadius).2 hLevel
    _ ≤ sphereEigenvalueSquared data level :=
      sphere_eigenvalue_linear_lower_bound data level

/-- The same positive gap controls the complete product energy because the
circle square is nonnegative. -/
theorem productThroatPositiveHeatGap_le_modeEnergy
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatPositiveHeatGap data ≤
      productThroatModeEnergy data fold twist mode := by
  unfold productThroatModeEnergy
  exact (productThroatPositiveHeatGap_le_sphereEigenvalueSquared
    data mode.1.1).trans
      (le_add_of_nonneg_right
        (circleOperatorSquaredEigenvalue_nonnegative fold twist mode.2))

/-- The factorized product weight is the exponential of the full product
energy. -/
theorem productThroatHeatWeight_eq_exp_modeEnergy
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatHeatWeight data time fold twist mode =
      Real.exp
        (-time.1 * productThroatModeEnergy data fold twist mode) := by
  unfold productThroatHeatWeight sphereModeHeatWeight
    circleOperatorHeatWeight productThroatModeEnergy
  rw [← Real.exp_add]
  congr 1
  ring

/-- Modewise long-time decay relative to the unit-time heat weight. -/
theorem productThroatHeatWeight_le_shifted_exponential
    (data : ProductThroatSpectralData) (time : HeatTime)
    (hTime : 1 ≤ time.1) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatHeatWeight data time fold twist mode ≤
      Real.exp
          (-productThroatPositiveHeatGap data * (time.1 - 1)) *
        productThroatHeatWeight data unitProductThroatHeatTime fold twist mode := by
  have hGap := productThroatPositiveHeatGap_le_modeEnergy
    data fold twist mode
  have hDelta : 0 ≤ time.1 - 1 := sub_nonneg.mpr hTime
  have hMul :
      productThroatPositiveHeatGap data * (time.1 - 1) ≤
        productThroatModeEnergy data fold twist mode * (time.1 - 1) :=
    mul_le_mul_of_nonneg_right hGap hDelta
  have hExponent :
      -time.1 * productThroatModeEnergy data fold twist mode ≤
        -productThroatPositiveHeatGap data * (time.1 - 1) +
          (-1 * productThroatModeEnergy data fold twist mode) := by
    calc
      -time.1 * productThroatModeEnergy data fold twist mode =
          -(productThroatModeEnergy data fold twist mode * (time.1 - 1)) -
            productThroatModeEnergy data fold twist mode := by ring
      _ ≤ -(productThroatPositiveHeatGap data * (time.1 - 1)) -
          productThroatModeEnergy data fold twist mode :=
        sub_le_sub_right (neg_le_neg hMul)
          (productThroatModeEnergy data fold twist mode)
      _ = -productThroatPositiveHeatGap data * (time.1 - 1) +
          (-1 * productThroatModeEnergy data fold twist mode) := by ring
  rw [productThroatHeatWeight_eq_exp_modeEnergy,
    productThroatHeatWeight_eq_exp_modeEnergy]
  change
    Real.exp (-time.1 * productThroatModeEnergy data fold twist mode) ≤
      Real.exp
          (-productThroatPositiveHeatGap data * (time.1 - 1)) *
        Real.exp (-1 * productThroatModeEnergy data fold twist mode)
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr hExponent

/-- Summing the modewise estimate gives long-time decay of the complete
infinite diagonal trace. -/
theorem productThroatHeatOperatorDiagonalTrace_le_shifted_exponential
    (data : ProductThroatSpectralData) (time : HeatTime)
    (hTime : 1 ≤ time.1) (fold : Fold) (twist : CircleTwist) :
    productThroatHeatOperatorDiagonalTrace data time fold twist ≤
      Real.exp
          (-productThroatPositiveHeatGap data * (time.1 - 1)) *
        productThroatHeatOperatorDiagonalTrace data
          unitProductThroatHeatTime fold twist := by
  unfold productThroatHeatOperatorDiagonalTrace
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (productThroatHeatWeight_le_shifted_exponential
      data time hTime fold twist)
    (productThroatHeatWeight_summable data time fold twist)
    ((productThroatHeatWeight_summable data unitProductThroatHeatTime
      fold twist).mul_left
        (Real.exp
          (-productThroatPositiveHeatGap data * (time.1 - 1))))

/-- Long-time scale obtained from the genuine unit-time product trace. -/
def productThroatLongTimeScale
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    Real :=
  Real.exp (productThroatPositiveHeatGap data) *
    productThroatHeatOperatorDiagonalTrace data
      unitProductThroatHeatTime fold twist

/-- The long-time scale is nonnegative. -/
theorem productThroatLongTimeScale_nonnegative
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    0 ≤ productThroatLongTimeScale data fold twist := by
  unfold productThroatLongTimeScale
  exact mul_nonneg (Real.exp_pos _).le (by
    unfold productThroatHeatOperatorDiagonalTrace
    exact tsum_nonneg
      (productThroatHeatWeight_nonnegative data unitProductThroatHeatTime
        fold twist))

/-- The scale is the unit-time intrinsic nuclear trace multiplied by the gap
normalization. -/
theorem productThroatLongTimeScale_eq_nuclearTrace
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    productThroatLongTimeScale data fold twist =
      Real.exp (productThroatPositiveHeatGap data) *
        productThroatNuclearHeatTrace data unitProductThroatHeatTime
          fold twist := by
  unfold productThroatLongTimeScale
  rw [productThroatHeatOperatorDiagonalTrace_eq_nuclearTrace]

/-- Standard `C exp(-c t)` bound for the genuine product-throat nuclear heat
trace. -/
theorem productThroatNuclearHeatTrace_le_longTimeExponentialBound
    (data : ProductThroatSpectralData) (time : HeatTime)
    (hTime : 1 ≤ time.1) (fold : Fold) (twist : CircleTwist) :
    productThroatNuclearHeatTrace data time fold twist ≤
      longTimeExponentialBound
        (productThroatLongTimeScale data fold twist)
        (productThroatPositiveHeatGap data) time.1 := by
  rw [← productThroatHeatOperatorDiagonalTrace_eq_nuclearTrace]
  calc
    productThroatHeatOperatorDiagonalTrace data time fold twist ≤
        Real.exp
            (-productThroatPositiveHeatGap data * (time.1 - 1)) *
          productThroatHeatOperatorDiagonalTrace data
            unitProductThroatHeatTime fold twist :=
      productThroatHeatOperatorDiagonalTrace_le_shifted_exponential
        data time hTime fold twist
    _ = longTimeExponentialBound
        (productThroatLongTimeScale data fold twist)
        (productThroatPositiveHeatGap data) time.1 := by
      unfold longTimeExponentialBound productThroatLongTimeScale
      rw [show
        -productThroatPositiveHeatGap data * (time.1 - 1) =
          productThroatPositiveHeatGap data +
            (-productThroatPositiveHeatGap data * time.1) by ring,
        Real.exp_add]
      ring

/-- Product heat trace extended by zero away from positive times. -/
def extendedProductThroatNuclearHeatTrace
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (time : Real) : Real :=
  if hTime : 0 < time then
    productThroatNuclearHeatTrace data ⟨time, hTime⟩ fold twist
  else 0

/-- The extended product heat trace remains nonnegative. -/
theorem extendedProductThroatNuclearHeatTrace_nonnegative
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (time : Real) :
    0 ≤ extendedProductThroatNuclearHeatTrace data fold twist time := by
  by_cases hTime : 0 < time
  · simp only [extendedProductThroatNuclearHeatTrace, hTime, dite_true]
    exact productThroatNuclearHeatTrace_nonnegative data ⟨time, hTime⟩
      fold twist
  · simp [extendedProductThroatNuclearHeatTrace, hTime]

/-- The same exponential majorant controls the zero-extended heat trace on the
long-time half-line. -/
theorem extendedProductThroatNuclearHeatTrace_le_longTimeExponentialBound
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (time : Real) (hTime : 1 ≤ time) :
    extendedProductThroatNuclearHeatTrace data fold twist time ≤
      longTimeExponentialBound
        (productThroatLongTimeScale data fold twist)
        (productThroatPositiveHeatGap data) time := by
  have hPositive : 0 < time := zero_lt_one.trans_le hTime
  simp only [extendedProductThroatNuclearHeatTrace, hPositive, dite_true]
  exact productThroatNuclearHeatTrace_le_longTimeExponentialBound
    data ⟨time, hPositive⟩ hTime fold twist

/-- The concrete exponential envelope is integrable on the long-time
half-line. -/
theorem productThroatLongTimeExponentialBound_integrable
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    Integrable
      (longTimeExponentialBound
        (productThroatLongTimeScale data fold twist)
        (productThroatPositiveHeatGap data))
      (volume.restrict (Set.Ioi 1)) :=
  integrableOn_longTimeExponentialBound
    (productThroatLongTimeScale data fold twist)
    (productThroatPositiveHeatGap_pos data) 1

/-- Public product-throat positive-gap long-time checkpoint. -/
theorem product_throat_positive_heat_gap_long_time_gate
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    0 < productThroatPositiveHeatGap data ∧
    (∀ mode : ProductThroatHeatMode data,
      productThroatPositiveHeatGap data ≤
        productThroatModeEnergy data fold twist mode) ∧
    (∀ time : HeatTime, 1 ≤ time.1 →
      productThroatNuclearHeatTrace data time fold twist ≤
        longTimeExponentialBound
          (productThroatLongTimeScale data fold twist)
          (productThroatPositiveHeatGap data) time.1) ∧
    Integrable
      (longTimeExponentialBound
        (productThroatLongTimeScale data fold twist)
        (productThroatPositiveHeatGap data))
      (volume.restrict (Set.Ioi 1)) :=
  ⟨productThroatPositiveHeatGap_pos data,
    productThroatPositiveHeatGap_le_modeEnergy data fold twist,
    fun time hTime =>
      productThroatNuclearHeatTrace_le_longTimeExponentialBound
        data time hTime fold twist,
    productThroatLongTimeExponentialBound_integrable data fold twist⟩

end
end P0EFTJanusProductThroatPositiveHeatGapLongTime4D
end JanusFormal
