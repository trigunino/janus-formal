import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointSmallPerturbation4D

/-!
# Quantitative stability on the actual kernel complement

Let `H_red` be the restriction of a bounded self-adjoint operator to
`(ker H)ᗮ`, with gap `c > 0`.  Every bounded self-adjoint perturbation `K` on
that same reduced space satisfying

`‖Kx‖ ≤ delta ‖x‖`, `delta < c`,

preserves invertibility.  The perturbed reduced Green operator satisfies

`‖(H_red + K)⁻¹‖ ≤ (c - delta)⁻¹`.

This is the local nondegeneracy/stability statement needed before parameter
families, spectral flow and reduced determinant constructions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementStability4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointSmallPerturbation4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

local instance actualKernelStabilityCompleteSpace
    (operator : E →L[Real] E) :
    CompleteSpace (SelfAdjointKernelComplement operator) :=
  inferInstance

/-- Perturbation input measured against the actual reduced gap. -/
structure SelfAdjointKernelComplementPerturbationData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (gapData : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator) : Prop where
  perturbation_selfAdjoint : IsSelfAdjoint perturbation
  bound : Real
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ vector, ‖perturbation vector‖ ≤ bound * ‖vector‖
  small : bound < gapData.gap

/-- Convert to the generic small-perturbation packet. -/
def SelfAdjointKernelComplementPerturbationData.toSmallPerturbation
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {gapData : SelfAdjointKernelComplementGapData operator hSelfAdjoint}
    {perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator}
    (data : SelfAdjointKernelComplementPerturbationData operator hSelfAdjoint
      gapData perturbation) :
    SelfAdjointSmallPerturbationData
      (selfAdjointKernelComplementOperator operator hSelfAdjoint)
      perturbation where
  operator_selfAdjoint :=
    selfAdjointKernelComplementOperator_isSelfAdjoint operator hSelfAdjoint
  perturbation_selfAdjoint := data.perturbation_selfAdjoint
  gap := gapData.gap
  gap_pos := gapData.gap_pos
  operator_lowerBound := gapData.lowerBound
  perturbationBound := data.bound
  perturbationBound_nonneg := data.bound_nonneg
  perturbation_norm_le := data.norm_le
  perturbation_small := data.small

/-- Perturbed reduced Hessian. -/
def selfAdjointKernelComplementPerturbedOperator
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator :=
  selfAdjointKernelComplementOperator operator hSelfAdjoint + perturbation

/-- Quantitative stability certificate. -/
def selfAdjointKernelComplementPerturbedCertificate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (gapData : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator)
    (data : SelfAdjointKernelComplementPerturbationData operator hSelfAdjoint
      gapData perturbation) :=
  selfAdjointSmallPerturbationCertificate
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
    perturbation data.toSmallPerturbation

/-- Continuous equivalence associated with the perturbed reduced Hessian. -/
noncomputable def selfAdjointKernelComplementPerturbedEquiv
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (gapData : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator)
    (data : SelfAdjointKernelComplementPerturbationData operator hSelfAdjoint
      gapData perturbation) :
    SelfAdjointKernelComplement operator ≃L[Real]
      SelfAdjointKernelComplement operator :=
  ContinuousLinearEquiv.ofBijective
    (selfAdjointKernelComplementPerturbedOperator operator hSelfAdjoint
      perturbation)
    ⟨(selfAdjointKernelComplementPerturbedCertificate operator hSelfAdjoint
        gapData perturbation data).injective,
      (selfAdjointKernelComplementPerturbedCertificate operator hSelfAdjoint
        gapData perturbation data).surjective⟩

/-- Green operator of the perturbed reduced Hessian. -/
noncomputable def selfAdjointKernelComplementPerturbedGreen
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (gapData : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator)
    (data : SelfAdjointKernelComplementPerturbationData operator hSelfAdjoint
      gapData perturbation) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator :=
  (selfAdjointKernelComplementPerturbedEquiv operator hSelfAdjoint gapData
    perturbation data).symm

@[simp]
theorem selfAdjointKernelComplementPerturbedOperator_green
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (gapData : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator)
    (data : SelfAdjointKernelComplementPerturbationData operator hSelfAdjoint
      gapData perturbation)
    (vector : SelfAdjointKernelComplement operator) :
    selfAdjointKernelComplementPerturbedOperator operator hSelfAdjoint
        perturbation
        (selfAdjointKernelComplementPerturbedGreen operator hSelfAdjoint gapData
          perturbation data vector) =
      vector :=
  (selfAdjointKernelComplementPerturbedEquiv operator hSelfAdjoint gapData
    perturbation data).apply_symm_apply vector

@[simp]
theorem selfAdjointKernelComplementPerturbedGreen_operator
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (gapData : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator)
    (data : SelfAdjointKernelComplementPerturbationData operator hSelfAdjoint
      gapData perturbation)
    (vector : SelfAdjointKernelComplement operator) :
    selfAdjointKernelComplementPerturbedGreen operator hSelfAdjoint gapData
        perturbation data
        (selfAdjointKernelComplementPerturbedOperator operator hSelfAdjoint
          perturbation vector) =
      vector :=
  (selfAdjointKernelComplementPerturbedEquiv operator hSelfAdjoint gapData
    perturbation data).symm_apply_apply vector

/-- Pointwise inverse estimate with the remaining gap. -/
theorem selfAdjointKernelComplementPerturbedGreen_norm_le
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (gapData : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator)
    (data : SelfAdjointKernelComplementPerturbationData operator hSelfAdjoint
      gapData perturbation)
    (vector : SelfAdjointKernelComplement operator) :
    ‖selfAdjointKernelComplementPerturbedGreen operator hSelfAdjoint gapData
        perturbation data vector‖ ≤
      (gapData.gap - data.bound)⁻¹ * ‖vector‖ := by
  let small := data.toSmallPerturbation
  let preimage := selfAdjointKernelComplementPerturbedGreen operator
    hSelfAdjoint gapData perturbation data vector
  have hLower := selfAdjointSmallPerturbation_lowerBound
    (selfAdjointKernelComplementOperator operator hSelfAdjoint)
    perturbation small preimage
  rw [selfAdjointKernelComplementPerturbedOperator_green operator hSelfAdjoint
      gapData perturbation data vector] at hLower
  have hGapPos : 0 < gapData.gap - data.bound := by
    linarith [data.small]
  have hGapNe : gapData.gap - data.bound ≠ 0 := ne_of_gt hGapPos
  change (gapData.gap - data.bound) * ‖preimage‖ ≤ ‖vector‖ at hLower
  calc
    ‖preimage‖ = (gapData.gap - data.bound)⁻¹ *
        ((gapData.gap - data.bound) * ‖preimage‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ (gapData.gap - data.bound)⁻¹ * ‖vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt hGapPos))

/-- Operator norm estimate for the perturbed Green operator. -/
theorem selfAdjointKernelComplementPerturbedGreen_opNorm_le
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (gapData : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator)
    (data : SelfAdjointKernelComplementPerturbationData operator hSelfAdjoint
      gapData perturbation) :
    ‖selfAdjointKernelComplementPerturbedGreen operator hSelfAdjoint gapData
        perturbation data‖ ≤
      (gapData.gap - data.bound)⁻¹ := by
  have hGapPos : 0 < gapData.gap - data.bound := by
    linarith [data.small]
  apply ContinuousLinearMap.opNorm_le_bound
    (inv_nonneg.mpr (le_of_lt hGapPos))
  intro vector
  exact selfAdjointKernelComplementPerturbedGreen_norm_le operator hSelfAdjoint
    gapData perturbation data vector

/-- Public stability checkpoint. -/
theorem self_adjoint_actual_kernel_stability_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (gapData : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    (perturbation : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator)
    (data : SelfAdjointKernelComplementPerturbationData operator hSelfAdjoint
      gapData perturbation) :
    IsSelfAdjoint
        (selfAdjointKernelComplementPerturbedOperator operator hSelfAdjoint
          perturbation) ∧
      Function.Injective
        (selfAdjointKernelComplementPerturbedOperator operator hSelfAdjoint
          perturbation) ∧
      Function.Surjective
        (selfAdjointKernelComplementPerturbedOperator operator hSelfAdjoint
          perturbation) ∧
      ‖selfAdjointKernelComplementPerturbedGreen operator hSelfAdjoint gapData
          perturbation data‖ ≤
        (gapData.gap - data.bound)⁻¹ := by
  let certificate := selfAdjointKernelComplementPerturbedCertificate operator
    hSelfAdjoint gapData perturbation data
  exact
    ⟨certificate.selfAdjoint, certificate.injective, certificate.surjective,
      selfAdjointKernelComplementPerturbedGreen_opNorm_le operator hSelfAdjoint
        gapData perturbation data⟩

end
end P0EFTJanusProgramPSelfAdjointKernelComplementStability4D
end JanusFormal
