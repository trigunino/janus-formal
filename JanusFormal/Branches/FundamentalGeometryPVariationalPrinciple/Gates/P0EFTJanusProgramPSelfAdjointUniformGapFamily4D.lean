import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Uniformly gapped self-adjoint operator families

The determinant and Bismut--Freed layers require an actual family of reduced
operators, not only a scalar family of zeta functions.  This file works on one
fixed real Hilbert space, which is the correct target after trivializing the
actual kernel complements along a parameter path.

A uniform positive lower bound

`c ‖x‖ ≤ ‖H_a x‖`

and self-adjointness make every member bijective.  The inverse Green family is
therefore constructed canonically, with the uniform estimate

`‖G_a‖ ≤ c⁻¹`.

No compactness, differentiability or trace-class hypothesis is used here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointUniformGapFamily4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

variable {E : Type*}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- A self-adjoint family on one fixed Hilbert space with one positive lower
bound valid at every parameter. -/
structure SelfAdjointUniformGapFamilyData
    (operator : Real → E →L[Real] E) where
  selfAdjoint : ∀ parameter, IsSelfAdjoint (operator parameter)
  gap : Real
  gap_pos : 0 < gap
  lowerBound : ∀ parameter vector,
    gap * ‖vector‖ ≤ ‖operator parameter vector‖

namespace SelfAdjointUniformGapFamilyData

/-- Reciprocal gap as the nonnegative constant consumed by the global
lower-bound surjectivity theorem. -/
def inverseGapConstant
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator) : NNReal :=
  ⟨data.gap⁻¹, inv_nonneg.mpr (le_of_lt data.gap_pos)⟩

/-- Rewrite the uniform estimate as `‖x‖ ≤ c⁻¹ ‖H_a x‖`. -/
theorem globalLowerBound
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) (vector : E) :
    ‖vector‖ ≤ (data.inverseGapConstant : Real) *
      ‖operator parameter vector‖ := by
  have hLower := data.lowerBound parameter vector
  have hGapNe : data.gap ≠ 0 := ne_of_gt data.gap_pos
  change ‖vector‖ ≤ data.gap⁻¹ * ‖operator parameter vector‖
  calc
    ‖vector‖ = data.gap⁻¹ * (data.gap * ‖vector‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ data.gap⁻¹ * ‖operator parameter vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt data.gap_pos))

/-- Every member of the family is bijective. -/
theorem bijective
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) : Function.Bijective (operator parameter) :=
  selfAdjoint_bijective_of_globalLowerBound
    (operator parameter) (data.selfAdjoint parameter)
    data.inverseGapConstant (data.globalLowerBound parameter)

/-- Continuous linear equivalence represented by `H_a`. -/
noncomputable def operatorEquiv
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) : E ≃L[Real] E :=
  ContinuousLinearEquiv.ofBijective (operator parameter)
    (LinearMap.ker_eq_bot.mpr (data.bijective parameter).1)
    (LinearMap.range_eq_top.mpr (data.bijective parameter).2)

/-- Canonical inverse Green family. -/
noncomputable def green
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) : E →L[Real] E :=
  (data.operatorEquiv parameter).symm

@[simp]
theorem operator_green
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) (vector : E) :
    operator parameter (data.green parameter vector) = vector :=
  by
    change (data.operatorEquiv parameter)
      ((data.operatorEquiv parameter).symm vector) = vector
    exact (data.operatorEquiv parameter).apply_symm_apply vector

@[simp]
theorem green_operator
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) (vector : E) :
    data.green parameter (operator parameter vector) = vector :=
  by
    change (data.operatorEquiv parameter).symm
      ((data.operatorEquiv parameter) vector) = vector
    exact (data.operatorEquiv parameter).symm_apply_apply vector

/-- Equality of endomorphisms for the left inverse. -/
theorem operator_comp_green
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) :
    (operator parameter).comp (data.green parameter) =
      ContinuousLinearMap.id Real E := by
  ext vector
  exact data.operator_green parameter vector

/-- Equality of endomorphisms for the right inverse. -/
theorem green_comp_operator
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) :
    (data.green parameter).comp (operator parameter) =
      ContinuousLinearMap.id Real E := by
  ext vector
  exact data.green_operator parameter vector

/-- Pointwise inverse estimate. -/
theorem green_norm_le
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) (vector : E) :
    ‖data.green parameter vector‖ ≤ data.gap⁻¹ * ‖vector‖ := by
  let preimage := data.green parameter vector
  have hLower := data.lowerBound parameter preimage
  rw [data.operator_green parameter vector] at hLower
  have hGapNe : data.gap ≠ 0 := ne_of_gt data.gap_pos
  calc
    ‖preimage‖ = data.gap⁻¹ * (data.gap * ‖preimage‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ data.gap⁻¹ * ‖vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt data.gap_pos))

/-- Uniform operator-norm bound for the Green family. -/
theorem green_opNorm_le
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) :
    ‖data.green parameter‖ ≤ data.gap⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound (data.green parameter)
    (inv_nonneg.mpr (le_of_lt data.gap_pos))
  intro vector
  exact data.green_norm_le parameter vector

/-- The family has no nonzero zero crossing. -/
theorem kernel_eq_bot
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapFamilyData operator)
    (parameter : Real) :
    (operator parameter).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact (data.bijective parameter).1

/-- Public uniformly-gapped family checkpoint. -/
theorem self_adjoint_uniform_gap_family_gate
    (operator : Real → E →L[Real] E)
    (data : SelfAdjointUniformGapFamilyData operator) :
    (∀ parameter, Function.Bijective (operator parameter)) ∧
      (∀ parameter vector,
        operator parameter (data.green parameter vector) = vector) ∧
      (∀ parameter vector,
        data.green parameter (operator parameter vector) = vector) ∧
      (∀ parameter, ‖data.green parameter‖ ≤ data.gap⁻¹) ∧
      (∀ parameter, (operator parameter).ker = ⊥) :=
  ⟨data.bijective,
    data.operator_green,
    data.green_operator,
    data.green_opNorm_le,
    data.kernel_eq_bot⟩

end SelfAdjointUniformGapFamilyData

end
end P0EFTJanusProgramPSelfAdjointUniformGapFamily4D
end JanusFormal
