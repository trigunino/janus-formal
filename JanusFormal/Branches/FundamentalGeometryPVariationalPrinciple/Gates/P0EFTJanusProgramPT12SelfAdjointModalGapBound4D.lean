import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

/-! # A kernel-complement gap bounds every nonzero eigenvalue -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12SelfAdjointModalGapBound4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- A nonzero-eigenvalue mode is orthogonal to the actual kernel. -/
theorem eigenvector_mem_kernelComplement
    (operator : E →L[Real] E) (hSelfAdjoint : IsSelfAdjoint operator)
    {eigenvalue : Real} (hEigenvalue : eigenvalue ≠ 0)
    {vector : E} (hEigen : operator vector = eigenvalue • vector) :
    vector ∈ operator.kerᗮ := by
  rw [Submodule.mem_orthogonal']
  intro zeroMode hZeroMode
  have hZero : operator zeroMode = 0 := LinearMap.mem_ker.mp hZeroMode
  have hPair : inner Real (operator vector) zeroMode = 0 := by
    calc
      inner Real (operator vector) zeroMode =
          inner Real vector (operator zeroMode) :=
        hSelfAdjoint.isSymmetric vector zeroMode
      _ = 0 := by rw [hZero, inner_zero_right]
  rw [hEigen, inner_smul_left] at hPair
  exact (mul_eq_zero.mp hPair).resolve_left hEigenvalue

/-- The H12 norm gap excludes arbitrarily small nonzero eigenvalues. -/
theorem gap_le_abs_nonzero_eigenvalue
    (operator : E →L[Real] E) (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapData operator hSelfAdjoint)
    {eigenvalue : Real} (hEigenvalue : eigenvalue ≠ 0)
    {vector : E} (hVector : vector ≠ 0)
    (hEigen : operator vector = eigenvalue • vector) :
    data.gap ≤ |eigenvalue| := by
  let reduced : SelfAdjointKernelComplement operator :=
    ⟨vector, eigenvector_mem_kernelComplement operator hSelfAdjoint
      hEigenvalue hEigen⟩
  have hLower := data.lowerBound reduced
  change data.gap * ‖vector‖ ≤ ‖operator vector‖ at hLower
  rw [hEigen, norm_smul, Real.norm_eq_abs] at hLower
  exact le_of_mul_le_mul_right hLower (norm_pos_iff.mpr hVector)

end
end P0EFTJanusProgramPT12SelfAdjointModalGapBound4D
end JanusFormal
