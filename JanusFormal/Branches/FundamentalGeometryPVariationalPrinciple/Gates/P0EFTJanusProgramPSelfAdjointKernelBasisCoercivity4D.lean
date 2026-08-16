import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

/-!
# Actual-kernel basis and quadratic coercivity

For a bounded self-adjoint operator, the PDE input naturally produced by an
elliptic estimate is not an abstract norm gap.  It is:

* a finite basis of the genuine kernel;
* a positive quadratic coercivity estimate on the orthogonal complement of
  that kernel.

Cauchy--Schwarz converts

`c * ‖x‖² ≤ ⟪x, H x⟫`

into the operator lower bound

`c * ‖x‖ ≤ ‖H x‖`.

This file performs that conversion once and constructs the exact
`SelfAdjointKernelComplementGapData` consumed by the existing Fredholm, Green
and resolvent gates.  No finite projector, generalized inverse or auxiliary
zero-mode space is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelBasisCoercivity4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- A finite basis of the actual kernel together with quadratic coercivity on
its exact orthogonal complement. -/
structure SelfAdjointKernelBasisCoercivityData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  basis : Basis ZeroMode Real operator.ker
  constant : Real
  constant_pos : 0 < constant
  coercive : ∀ vector : SelfAdjointKernelComplement operator,
    constant * ‖(vector : E)‖ ^ 2 ≤
      ⟪(vector : E), operator (vector : E), Real⟫

/-- Cauchy--Schwarz converts quadratic coercivity into the norm lower bound
used by the actual-kernel complement reduction. -/
theorem SelfAdjointKernelBasisCoercivityData.lowerBound
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : SelfAdjointKernelBasisCoercivityData operator hSelfAdjoint ZeroMode)
    (vector : SelfAdjointKernelComplement operator) :
    data.constant * ‖vector‖ ≤
      ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ := by
  change data.constant * ‖(vector : E)‖ ≤ ‖operator (vector : E)‖
  by_cases hNorm : ‖(vector : E)‖ = 0
  · simp [hNorm]
  · have hNormPos : 0 < ‖(vector : E)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hNorm)
    have hInnerUpper :
        ⟪(vector : E), operator (vector : E), Real⟫ ≤
          ‖(vector : E)‖ * ‖operator (vector : E)‖ :=
      real_inner_le_norm _ _
    have hMul :
        ‖(vector : E)‖ * (data.constant * ‖(vector : E)‖) ≤
          ‖(vector : E)‖ * ‖operator (vector : E)‖ := by
      calc
        ‖(vector : E)‖ * (data.constant * ‖(vector : E)‖) =
            data.constant * ‖(vector : E)‖ ^ 2 := by ring
        _ ≤ ⟪(vector : E), operator (vector : E), Real⟫ :=
          data.coercive vector
        _ ≤ ‖(vector : E)‖ * ‖operator (vector : E)‖ := hInnerUpper
    exact (mul_le_mul_left hNormPos).mp hMul

/-- The basis itself supplies finite-dimensionality of the genuine kernel, and
the quadratic estimate supplies the gap. -/
def SelfAdjointKernelBasisCoercivityData.toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : SelfAdjointKernelBasisCoercivityData operator hSelfAdjoint ZeroMode) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint where
  kernel_finite := data.basis.finiteDimensional_of_finite
  gap := data.constant
  gap_pos := data.constant_pos
  lowerBound := data.lowerBound

/-- The zero-mode count is exactly the cardinality of the supplied physical
kernel basis. -/
theorem SelfAdjointKernelBasisCoercivityData.kernel_finrank_eq_card
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : SelfAdjointKernelBasisCoercivityData operator hSelfAdjoint ZeroMode) :
    Module.finrank Real operator.ker = Fintype.card ZeroMode := by
  letI : FiniteDimensional Real operator.ker :=
    data.basis.finiteDimensional_of_finite
  exact Module.finrank_eq_card_basis data.basis

/-- Public PDE-to-gap checkpoint. -/
theorem self_adjoint_kernel_basis_coercivity_gate
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : SelfAdjointKernelBasisCoercivityData operator hSelfAdjoint ZeroMode) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  ⟨data.toGapData, data.kernel_finrank_eq_card⟩

end
end P0EFTJanusProgramPSelfAdjointKernelBasisCoercivity4D
end JanusFormal
