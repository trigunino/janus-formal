import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

/-!
# Stability of a self-adjoint gap under a small bounded perturbation

Let `H` be self-adjoint and satisfy

`c ‖x‖ ≤ ‖Hx‖`, `c > 0`.

Let `K` be self-adjoint and bounded pointwise by

`‖Kx‖ ≤ δ ‖x‖`, `0 ≤ δ < c`.

Then

`(c - δ) ‖x‖ ≤ ‖(H + K)x‖`.

The perturbed operator is self-adjoint, hence the resulting global lower bound
forces surjectivity.  This gives a quantitative open neighborhood of stable
invertible Hessians.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointSmallPerturbation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Quantitative small self-adjoint perturbation data. -/
structure SelfAdjointSmallPerturbationData
    (operator perturbation : E →L[Real] E) : Prop where
  operator_selfAdjoint : IsSelfAdjoint operator
  perturbation_selfAdjoint : IsSelfAdjoint perturbation
  gap : Real
  gap_pos : 0 < gap
  operator_lowerBound : ∀ vector,
    gap * ‖vector‖ ≤ ‖operator vector‖
  perturbationBound : Real
  perturbationBound_nonneg : 0 ≤ perturbationBound
  perturbation_norm_le : ∀ vector,
    ‖perturbation vector‖ ≤ perturbationBound * ‖vector‖
  perturbation_small : perturbationBound < gap

/-- Remaining positive gap. -/
def SelfAdjointSmallPerturbationData.remainingGap
    {operator perturbation : E →L[Real] E}
    (data : SelfAdjointSmallPerturbationData operator perturbation) : Real :=
  data.gap - data.perturbationBound

/-- Positivity of the remaining gap. -/
theorem SelfAdjointSmallPerturbationData.remainingGap_pos
    {operator perturbation : E →L[Real] E}
    (data : SelfAdjointSmallPerturbationData operator perturbation) :
    0 < data.remainingGap := by
  unfold SelfAdjointSmallPerturbationData.remainingGap
  linarith [data.perturbation_small]

/-- Robust lower bound for the perturbed operator. -/
theorem selfAdjointSmallPerturbation_lowerBound
    (operator perturbation : E →L[Real] E)
    (data : SelfAdjointSmallPerturbationData operator perturbation)
    (vector : E) :
    data.remainingGap * ‖vector‖ ≤ ‖(operator + perturbation) vector‖ := by
  have hTriangle :
      ‖operator vector‖ ≤
        ‖(operator + perturbation) vector‖ + ‖perturbation vector‖ := by
    have hIdentity :
        operator vector =
          (operator + perturbation) vector - perturbation vector := by
      simp
    rw [hIdentity]
    exact norm_sub_le _ _
  have hOperator := data.operator_lowerBound vector
  have hPerturbation := data.perturbation_norm_le vector
  unfold SelfAdjointSmallPerturbationData.remainingGap
  linarith

/-- The perturbed operator stays self-adjoint. -/
theorem selfAdjointSmallPerturbation_isSelfAdjoint
    (operator perturbation : E →L[Real] E)
    (data : SelfAdjointSmallPerturbationData operator perturbation) :
    IsSelfAdjoint (operator + perturbation) :=
  data.operator_selfAdjoint.add data.perturbation_selfAdjoint

/-- Reciprocal remaining-gap constant in the form used by the global lower
bound theorem. -/
def SelfAdjointSmallPerturbationData.inverseGapConstant
    {operator perturbation : E →L[Real] E}
    (data : SelfAdjointSmallPerturbationData operator perturbation) : NNReal :=
  ⟨data.remainingGap⁻¹,
    inv_nonneg.mpr (le_of_lt data.remainingGap_pos)⟩

/-- Convert the coercive lower bound to `‖x‖ ≤ C ‖(H+K)x‖`. -/
theorem selfAdjointSmallPerturbation_globalLowerBound
    (operator perturbation : E →L[Real] E)
    (data : SelfAdjointSmallPerturbationData operator perturbation)
    (vector : E) :
    ‖vector‖ ≤
      (data.inverseGapConstant : Real) *
        ‖(operator + perturbation) vector‖ := by
  have hLower := selfAdjointSmallPerturbation_lowerBound operator perturbation
    data vector
  have hNonzero : data.remainingGap ≠ 0 := ne_of_gt data.remainingGap_pos
  calc
    ‖vector‖ = data.remainingGap⁻¹ *
        (data.remainingGap * ‖vector‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hNonzero, one_mul]
    _ ≤ data.remainingGap⁻¹ * ‖(operator + perturbation) vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt data.remainingGap_pos))

/-- A sufficiently small self-adjoint perturbation remains surjective. -/
theorem selfAdjointSmallPerturbation_surjective
    (operator perturbation : E →L[Real] E)
    (data : SelfAdjointSmallPerturbationData operator perturbation) :
    Function.Surjective (operator + perturbation) :=
  selfAdjoint_surjective_of_globalLowerBound
    (operator + perturbation)
    (selfAdjointSmallPerturbation_isSelfAdjoint operator perturbation data)
    data.inverseGapConstant
    (selfAdjointSmallPerturbation_globalLowerBound operator perturbation data)

/-- Complete perturbative stability certificate. -/
structure SelfAdjointSmallPerturbationCertificate
    (operator perturbation : E →L[Real] E)
    (data : SelfAdjointSmallPerturbationData operator perturbation) : Prop where
  selfAdjoint : IsSelfAdjoint (operator + perturbation)
  lowerBound : ∀ vector,
    data.remainingGap * ‖vector‖ ≤ ‖(operator + perturbation) vector‖
  surjective : Function.Surjective (operator + perturbation)
  injective : Function.Injective (operator + perturbation)

/-- Construction of the perturbative stability certificate. -/
def selfAdjointSmallPerturbationCertificate
    (operator perturbation : E →L[Real] E)
    (data : SelfAdjointSmallPerturbationData operator perturbation) :
    SelfAdjointSmallPerturbationCertificate operator perturbation data where
  selfAdjoint := selfAdjointSmallPerturbation_isSelfAdjoint operator
    perturbation data
  lowerBound := selfAdjointSmallPerturbation_lowerBound operator perturbation
    data
  surjective := selfAdjointSmallPerturbation_surjective operator perturbation
    data
  injective := by
    intro first second hEqual
    have hZero : (operator + perturbation) (first - second) = 0 := by
      rw [map_sub, hEqual, sub_self]
    have hLower := selfAdjointSmallPerturbation_lowerBound operator perturbation
      data (first - second)
    rw [hZero, norm_zero] at hLower
    have hNorm : ‖first - second‖ = 0 := by
      by_contra hNonzero
      have hNormPos : 0 < ‖first - second‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hNonzero)
      have hProductPos : 0 < data.remainingGap * ‖first - second‖ :=
        mul_pos data.remainingGap_pos hNormPos
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Public perturbative stability gate. -/
theorem self_adjoint_small_perturbation_gate
    (operator perturbation : E →L[Real] E)
    (data : SelfAdjointSmallPerturbationData operator perturbation) :
    SelfAdjointSmallPerturbationCertificate operator perturbation data :=
  selfAdjointSmallPerturbationCertificate operator perturbation data

end
end P0EFTJanusProgramPSelfAdjointSmallPerturbation4D
end JanusFormal
