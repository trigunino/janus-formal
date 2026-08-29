import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

/-!
# Uniformly gapped self-adjoint families over an arbitrary base

The one-parameter Green-family implementation does not use any algebraic or
topological property of `Real` in its gap/inversion layer.  This file extracts
the genuinely base-independent construction.

For `H : Base → E →L E`, one positive lower bound and fiberwise
self-adjointness construct the canonical inverse `G_b` at every base point,
with the same uniform norm estimate.  No differentiability or trace-class
input is used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointUniformGapBaseFamily4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section

open P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

variable {Base E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Self-adjoint operator family over an arbitrary base with one uniform
positive lower bound. -/
structure SelfAdjointUniformGapBaseFamilyData
    (operator : Base → E →L[Real] E) : Prop where
  selfAdjoint : ∀ base, IsSelfAdjoint (operator base)
  gap : Real
  gap_pos : 0 < gap
  lowerBound : ∀ base vector,
    gap * ‖vector‖ ≤ ‖operator base vector‖

namespace SelfAdjointUniformGapBaseFamilyData

/-- Reciprocal uniform gap. -/
def inverseGapConstant
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator) : NNReal :=
  ⟨data.gap⁻¹, inv_nonneg.mpr (le_of_lt data.gap_pos)⟩

/-- Uniform global lower-bound form. -/
theorem globalLowerBound
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    (base : Base) (vector : E) :
    ‖vector‖ ≤ (data.inverseGapConstant : Real) * ‖operator base vector‖ := by
  have hLower := data.lowerBound base vector
  have hGapNe : data.gap ≠ 0 := ne_of_gt data.gap_pos
  change ‖vector‖ ≤ data.gap⁻¹ * ‖operator base vector‖
  calc
    ‖vector‖ = data.gap⁻¹ * (data.gap * ‖vector‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ data.gap⁻¹ * ‖operator base vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt data.gap_pos))

/-- Every basepoint operator is bijective. -/
theorem bijective
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    (base : Base) : Function.Bijective (operator base) :=
  selfAdjoint_bijective_of_globalLowerBound
    (operator base) (data.selfAdjoint base)
    data.inverseGapConstant (data.globalLowerBound base)

/-- Continuous linear equivalence represented by `H_b`. -/
noncomputable def operatorEquiv
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    (base : Base) : E ≃L[Real] E :=
  ContinuousLinearEquiv.ofBijective (operator base) (data.bijective base)

/-- Canonical inverse Green operator at a base point. -/
noncomputable def green
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    (base : Base) : E →L[Real] E :=
  (data.operatorEquiv base).symm

@[simp]
theorem operator_green
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    (base : Base) (vector : E) :
    operator base (data.green base vector) = vector :=
  (data.operatorEquiv base).apply_symm_apply vector

@[simp]
theorem green_operator
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    (base : Base) (vector : E) :
    data.green base (operator base vector) = vector :=
  (data.operatorEquiv base).symm_apply_apply vector

/-- Pointwise inverse estimate. -/
theorem green_norm_le
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    (base : Base) (vector : E) :
    ‖data.green base vector‖ ≤ data.gap⁻¹ * ‖vector‖ := by
  let preimage := data.green base vector
  have hLower := data.lowerBound base preimage
  rw [data.operator_green base vector] at hLower
  have hGapNe : data.gap ≠ 0 := ne_of_gt data.gap_pos
  calc
    ‖preimage‖ = data.gap⁻¹ * (data.gap * ‖preimage‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ data.gap⁻¹ * ‖vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt data.gap_pos))

/-- Uniform Green operator norm bound. -/
theorem green_opNorm_le
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    (base : Base) : ‖data.green base‖ ≤ data.gap⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (inv_nonneg.mpr (le_of_lt data.gap_pos))
  intro vector
  exact data.green_norm_le base vector

/-- Every reduced operator has trivial kernel. -/
theorem kernel_eq_bot
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    (base : Base) : (operator base).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact (data.bijective base).1

/-- Restrict an arbitrary-base family along any map of parameter sets. -/
def pullback
    {operator : Base → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    {Parameter : Type*} (map : Parameter → Base) :
    SelfAdjointUniformGapBaseFamilyData (fun parameter => operator (map parameter)) where
  selfAdjoint := fun parameter => data.selfAdjoint (map parameter)
  gap := data.gap
  gap_pos := data.gap_pos
  lowerBound := fun parameter => data.lowerBound (map parameter)

/-- Public arbitrary-base uniform-gap checkpoint. -/
theorem self_adjoint_uniform_gap_base_family_gate
    (operator : Base → E →L[Real] E)
    (data : SelfAdjointUniformGapBaseFamilyData operator) :
    (∀ base, Function.Bijective (operator base)) ∧
    (∀ base vector, operator base (data.green base vector) = vector) ∧
    (∀ base vector, data.green base (operator base vector) = vector) ∧
    (∀ base, ‖data.green base‖ ≤ data.gap⁻¹) ∧
    (∀ base, (operator base).ker = ⊥) :=
  ⟨data.bijective, data.operator_green, data.green_operator,
    data.green_opNorm_le, data.kernel_eq_bot⟩

end SelfAdjointUniformGapBaseFamilyData

end
end P0EFTJanusProgramPSelfAdjointUniformGapBaseFamily4D
end JanusFormal
