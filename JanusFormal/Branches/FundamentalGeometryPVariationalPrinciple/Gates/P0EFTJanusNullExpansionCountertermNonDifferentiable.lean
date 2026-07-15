import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNullExpansionCountertermVariation
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Zero-expansion non-differentiability

The scalar null-counterterm factor has the continuous extension

`f(0) = 0`, `f(theta) = theta * log (lengthScale * |theta|)` for `theta != 0`.

For positive `lengthScale`, its difference quotient along the explicit
positive sequence `exp (-n) / lengthScale` is exactly `-n`, hence tends to
`-infinity`.  This contradicts the finite slope limit forced by any derivative
at zero.

This is a local one-variable obstruction.  It constructs neither an integrated
null-boundary functional nor a zero-expansion boundary prescription.
-/

namespace JanusFormal
namespace P0EFTJanusNullExpansionCountertermNonDifferentiable

set_option autoImplicit false

noncomputable section

open Filter Set
open P0EFTJanusNullExpansionCountertermVariation

/-- The explicit continuous extension at zero. -/
def zeroExtendedExpansionCountertermFactor
    (lengthScale expansion : ℝ) : ℝ :=
  if expansion = 0 then 0
  else expansionCountertermFactor lengthScale expansion

@[simp]
theorem zeroExtendedExpansionCountertermFactor_zero
    (lengthScale : ℝ) :
    zeroExtendedExpansionCountertermFactor lengthScale 0 = 0 := by
  simp [zeroExtendedExpansionCountertermFactor]

theorem zeroExtendedExpansionCountertermFactor_eq_of_ne
    (lengthScale expansion : ℝ) (hExpansion : expansion ≠ 0) :
    zeroExtendedExpansionCountertermFactor lengthScale expansion =
      expansion * Real.log (lengthScale * |expansion|) := by
  simp [zeroExtendedExpansionCountertermFactor, hExpansion,
    expansionCountertermFactor]

/-- Lean's totalized scalar formula already realizes this extension. -/
theorem zeroExtendedExpansionCountertermFactor_eq
    (lengthScale : ℝ) :
    zeroExtendedExpansionCountertermFactor lengthScale =
      expansionCountertermFactor lengthScale := by
  funext expansion
  by_cases hExpansion : expansion = 0
  · simp [zeroExtendedExpansionCountertermFactor, expansionCountertermFactor,
      hExpansion]
  · simp [zeroExtendedExpansionCountertermFactor, hExpansion]

theorem expansionCountertermFactor_decomposition
    (lengthScale expansion : ℝ) (hLength : lengthScale ≠ 0) :
    expansionCountertermFactor lengthScale expansion =
      expansion * Real.log lengthScale + expansion * Real.log expansion := by
  by_cases hExpansion : expansion = 0
  · simp [expansionCountertermFactor, hExpansion]
  · rw [expansionCountertermFactor,
      Real.log_mul hLength (abs_ne_zero.mpr hExpansion),
      Real.log_abs]
    ring

/-- The zero extension is continuous (indeed, the displayed decomposition is
continuous everywhere). -/
theorem zeroExtendedExpansionCountertermFactor_continuous
    (lengthScale : ℝ) (hLength : 0 < lengthScale) :
    Continuous (zeroExtendedExpansionCountertermFactor lengthScale) := by
  rw [zeroExtendedExpansionCountertermFactor_eq]
  have hFunction :
      expansionCountertermFactor lengthScale =
        fun expansion : ℝ =>
          expansion * Real.log lengthScale + expansion * Real.log expansion := by
    funext expansion
    exact expansionCountertermFactor_decomposition lengthScale expansion
      hLength.ne'
  rw [hFunction]
  exact (continuous_id.mul continuous_const).add Real.continuous_mul_log

theorem zeroExtendedExpansionCountertermFactor_continuousAt_zero
    (lengthScale : ℝ) (hLength : 0 < lengthScale) :
    ContinuousAt (zeroExtendedExpansionCountertermFactor lengthScale) 0 :=
  (zeroExtendedExpansionCountertermFactor_continuous lengthScale hLength).continuousAt

/-- Explicit positive sequence approaching zero expansion. -/
def zeroExpansionSequence (lengthScale : ℝ) (index : ℕ) : ℝ :=
  zeroExpansionApproach lengthScale index

theorem zeroExpansionSequence_pos
    (lengthScale : ℝ) (hLength : 0 < lengthScale) (index : ℕ) :
    0 < zeroExpansionSequence lengthScale index := by
  exact zeroExpansionApproach_pos lengthScale index hLength

theorem zeroExpansionSequence_tendsto_zero
    (lengthScale : ℝ) :
    Tendsto (zeroExpansionSequence lengthScale) atTop (nhds 0) := by
  exact (zeroExpansionApproach_tendsto_zero lengthScale).comp
    tendsto_natCast_atTop_atTop

theorem zeroExpansionSequence_tendsto_zero_from_right
    (lengthScale : ℝ) (hLength : 0 < lengthScale) :
    Tendsto (zeroExpansionSequence lengthScale) atTop (nhdsWithin 0 (Ioi 0)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (zeroExpansionSequence_tendsto_zero lengthScale) ?_
  exact Eventually.of_forall fun index => zeroExpansionSequence_pos lengthScale hLength index

/-- Difference quotient at zero along the explicit positive sequence. -/
def zeroExpansionDifferenceQuotient
    (lengthScale : ℝ) (index : ℕ) : ℝ :=
  (zeroExpansionSequence lengthScale index)⁻¹ *
    (zeroExtendedExpansionCountertermFactor lengthScale
      (zeroExpansionSequence lengthScale index) -
        zeroExtendedExpansionCountertermFactor lengthScale 0)

theorem zeroExpansionDifferenceQuotient_eq
    (lengthScale : ℝ) (hLength : 0 < lengthScale) (index : ℕ) :
    zeroExpansionDifferenceQuotient lengthScale index = -(index : ℝ) := by
  have hPath := zeroExpansionSequence_pos lengthScale hLength index
  have hPathNe : zeroExpansionSequence lengthScale index ≠ 0 := hPath.ne'
  rw [zeroExpansionDifferenceQuotient,
    zeroExtendedExpansionCountertermFactor_zero,
    zeroExtendedExpansionCountertermFactor_eq_of_ne _ _ hPathNe,
    sub_zero]
  rw [abs_of_pos hPath, zeroExpansionSequence, zeroExpansionApproach]
  field_simp [hLength.ne']
  rw [Real.log_exp]

/-- The explicit difference quotients tend to negative infinity. -/
theorem zeroExpansionDifferenceQuotient_tendsto_atBot
    (lengthScale : ℝ) (hLength : 0 < lengthScale) :
    Tendsto (zeroExpansionDifferenceQuotient lengthScale) atTop atBot := by
  refine (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop).congr' ?_
  exact Eventually.of_forall fun index =>
    (zeroExpansionDifferenceQuotient_eq lengthScale hLength index).symm

/-- No finite derivative can exist at zero expansion. -/
theorem zeroExtendedExpansionCountertermFactor_not_hasDerivAt_zero
    (lengthScale derivative : ℝ) (hLength : 0 < lengthScale) :
    ¬ HasDerivAt (zeroExtendedExpansionCountertermFactor lengthScale)
      derivative 0 := by
  intro hDerivative
  have hFinite :
      Tendsto (zeroExpansionDifferenceQuotient lengthScale) atTop
        (nhds derivative) := by
    have hSlope := hDerivative.tendsto_slope_zero_right.comp
      (zeroExpansionSequence_tendsto_zero_from_right lengthScale hLength)
    convert hSlope using 1
    funext index
    simp [zeroExpansionDifferenceQuotient, smul_eq_mul]
  exact (not_tendsto_nhds_of_tendsto_atBot
    (zeroExpansionDifferenceQuotient_tendsto_atBot lengthScale hLength)
    derivative) hFinite

/-- The continuous zero extension is not differentiable at zero. -/
theorem zeroExtendedExpansionCountertermFactor_not_differentiableAt_zero
    (lengthScale : ℝ) (hLength : 0 < lengthScale) :
    ¬ DifferentiableAt ℝ
      (zeroExtendedExpansionCountertermFactor lengthScale) 0 := by
  intro hDifferentiable
  exact zeroExtendedExpansionCountertermFactor_not_hasDerivAt_zero
    lengthScale (deriv (zeroExtendedExpansionCountertermFactor lengthScale) 0)
    hLength hDifferentiable.hasDerivAt

end

end P0EFTJanusNullExpansionCountertermNonDifferentiable
end JanusFormal
