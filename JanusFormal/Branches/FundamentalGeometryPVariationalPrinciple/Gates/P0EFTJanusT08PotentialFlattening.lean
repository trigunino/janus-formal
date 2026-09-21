import Mathlib

/-!
# T08: scalar potential flattening changes the canonical kinetic coefficient

The exact nonlinear coordinate `x * sqrt (1 + lambda * x^2)` flattens
`x^2 + lambda * x^4` to a square. For nonnegative lambda it is differentiable
with positive derivative. The derivative is one at the reference zero, but
its square is strictly greater than one away from zero when lambda is
positive. These pointwise scalar identities assert no Janus or BV action.
-/

namespace JanusFormal
namespace P0EFTJanusT08PotentialFlattening

set_option autoImplicit false
noncomputable section

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

def quarticFlattening (coupling value : Real) : Real :=
  value * Real.sqrt (1 + coupling * value ^ 2)

def quarticFlatteningDerivative (coupling value : Real) : Real :=
  (1 + 2 * coupling * value ^ 2) / Real.sqrt (1 + coupling * value ^ 2)

private theorem radicand_pos {coupling : Real} (hCoupling : 0 ≤ coupling) (value : Real) :
    0 < 1 + coupling * value ^ 2 := by
  have h := mul_nonneg hCoupling (sq_nonneg value)
  linarith

theorem quarticFlattening_square {coupling : Real} (hCoupling : 0 ≤ coupling)
    (value : Real) :
    quarticFlattening coupling value ^ 2 = value ^ 2 + coupling * value ^ 4 := by
  unfold quarticFlattening
  rw [mul_pow, Real.sq_sqrt (le_of_lt (radicand_pos hCoupling value))]
  ring

@[simp] theorem quarticFlattening_zero (coupling : Real) :
    quarticFlattening coupling 0 = 0 := by
  simp [quarticFlattening]

theorem quarticFlattening_hasDerivAt {coupling : Real} (hCoupling : 0 ≤ coupling)
    (value : Real) :
    HasDerivAt (quarticFlattening coupling)
      (quarticFlatteningDerivative coupling value) value := by
  have hInner : HasDerivAt (fun x : Real => 1 + coupling * x ^ 2)
      (coupling * (2 * value)) value := by
    simpa using (((hasDerivAt_id value).pow 2).const_mul coupling).const_add 1
  have hSqrt := hInner.sqrt (ne_of_gt (radicand_pos hCoupling value))
  have hRoot : 0 < Real.sqrt (1 + coupling * value ^ 2) :=
    Real.sqrt_pos.2 (radicand_pos hCoupling value)
  have hSquare := Real.sq_sqrt (le_of_lt (radicand_pos hCoupling value))
  have hDerivative : quarticFlatteningDerivative coupling value =
      1 * Real.sqrt (1 + coupling * value ^ 2) +
        value * (coupling * (2 * value) / (2 * Real.sqrt (1 + coupling * value ^ 2))) := by
    dsimp [quarticFlatteningDerivative]
    field_simp [ne_of_gt hRoot]
    nlinarith
  rw [hDerivative]
  change HasDerivAt (fun x : Real => x * Real.sqrt (1 + coupling * x ^ 2)) _ value
  exact (hasDerivAt_id value).mul hSqrt

theorem quarticFlattening_differentiable {coupling : Real} (hCoupling : 0 ≤ coupling) :
    Differentiable Real (quarticFlattening coupling) :=
  fun value => (quarticFlattening_hasDerivAt hCoupling value).differentiableAt

theorem quarticFlattening_deriv {coupling : Real} (hCoupling : 0 ≤ coupling)
    (value : Real) :
    deriv (quarticFlattening coupling) value = quarticFlatteningDerivative coupling value :=
  (quarticFlattening_hasDerivAt hCoupling value).deriv

theorem quarticFlatteningDerivative_pos {coupling : Real} (hCoupling : 0 ≤ coupling)
    (value : Real) :
    0 < quarticFlatteningDerivative coupling value := by
  apply div_pos
  · have h := mul_nonneg hCoupling (sq_nonneg value)
    linarith
  · exact Real.sqrt_pos.2 (radicand_pos hCoupling value)

@[simp] theorem quarticFlatteningDerivative_zero (coupling : Real) :
    quarticFlatteningDerivative coupling 0 = 1 := by
  simp [quarticFlatteningDerivative]

/-- The potential-preserving change has strictly increased kinetic multiplier
at every nonzero scalar value when the quartic coefficient is positive. -/
theorem quarticFlatteningDerivative_sq_gt_one {coupling value : Real}
    (hCoupling : 0 < coupling) (hValue : value ≠ 0) :
    1 < quarticFlatteningDerivative coupling value ^ 2 := by
  have hProduct : 0 < coupling * value ^ 2 :=
    mul_pos hCoupling (sq_pos_of_ne_zero hValue)
  have hRoot : 0 < Real.sqrt (1 + coupling * value ^ 2) :=
    Real.sqrt_pos.2 (radicand_pos (le_of_lt hCoupling) value)
  have hSquare := Real.sq_sqrt (le_of_lt (radicand_pos (le_of_lt hCoupling) value))
  have hBound : Real.sqrt (1 + coupling * value ^ 2) < 1 + 2 * coupling * value ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (1 + coupling * value ^ 2) - 1)]
  have hDerivative : 1 < quarticFlatteningDerivative coupling value := by
    apply (lt_div_iff₀ hRoot).2
    simpa only [one_mul] using hBound
  nlinarith [sq_nonneg (quarticFlatteningDerivative coupling value - 1)]

theorem quarticFlattening_preserves_reference_kinetic {coupling : Real}
    (hCoupling : 0 ≤ coupling) :
    deriv (quarticFlattening coupling) 0 ^ 2 = 1 := by
  rw [quarticFlattening_deriv hCoupling, quarticFlatteningDerivative_zero]
  norm_num

theorem quarticFlattening_changes_kinetic {coupling value : Real}
    (hCoupling : 0 < coupling) (hValue : value ≠ 0) :
    deriv (quarticFlattening coupling) value ^ 2 ≠ 1 := by
  rw [quarticFlattening_deriv (le_of_lt hCoupling)]
  exact ne_of_gt (quarticFlatteningDerivative_sq_gt_one hCoupling hValue)

theorem quarticFlattening_strictMono {coupling : Real} (hCoupling : 0 ≤ coupling) :
    StrictMono (quarticFlattening coupling) := by
  apply strictMono_of_deriv_pos
  intro value
  rw [quarticFlattening_deriv hCoupling]
  exact quarticFlatteningDerivative_pos hCoupling value

private theorem radicand_sqrt_ge_one {coupling : Real}
    (hCoupling : 0 ≤ coupling) (value : Real) :
    1 ≤ Real.sqrt (1 + coupling * value ^ 2) := by
  have h := Real.sqrt_le_sqrt
    (show 1 ≤ 1 + coupling * value ^ 2 from
      le_add_of_nonneg_right (mul_nonneg hCoupling (sq_nonneg value)))
  simpa only [Real.sqrt_one] using h

theorem quarticFlattening_surjective {coupling : Real} (hCoupling : 0 ≤ coupling) :
    Function.Surjective (quarticFlattening coupling) := by
  intro target
  have hLeft : quarticFlattening coupling (-|target|) ≤ target := by
    have h := mul_le_mul_of_nonpos_left
      (radicand_sqrt_ge_one hCoupling (-|target|))
      (neg_nonpos.mpr (abs_nonneg target))
    have hBound : quarticFlattening coupling (-|target|) ≤ -|target| := by
      simpa only [quarticFlattening, mul_one] using h
    exact hBound.trans (neg_abs_le target)
  have hRight : target ≤ quarticFlattening coupling |target| := by
    have h := mul_le_mul_of_nonneg_left
      (radicand_sqrt_ge_one hCoupling |target|) (abs_nonneg target)
    exact (le_abs_self target).trans (by simpa only [quarticFlattening, mul_one] using h)
  have hInterval : -|target| ≤ |target| := by linarith [abs_nonneg target]
  obtain ⟨value, _, hValue⟩ := intermediate_value_Icc hInterval
    (quarticFlattening_differentiable hCoupling).continuous.continuousOn
    ⟨hLeft, hRight⟩
  exact ⟨value, hValue⟩

/-- An actual global scalar bijection. The kinetic multiplier results above
still prevent treating it as preserving a canonically normalized kinetic term. -/
theorem quarticFlattening_bijective {coupling : Real} (hCoupling : 0 ≤ coupling) :
    Function.Bijective (quarticFlattening coupling) :=
  ⟨(quarticFlattening_strictMono hCoupling).injective,
    quarticFlattening_surjective hCoupling⟩

end
end P0EFTJanusT08PotentialFlattening
end JanusFormal
