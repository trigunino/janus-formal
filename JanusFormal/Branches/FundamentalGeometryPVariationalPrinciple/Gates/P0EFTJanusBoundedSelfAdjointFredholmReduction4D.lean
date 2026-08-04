import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Fredholm reduction for bounded self-adjoint operators

For a bounded self-adjoint operator on a real Hilbert space, closed range and
finite kernel already force a finite cokernel.  This isolates the two genuine
analytic estimates needed by the off-shell LL block.
-/

namespace JanusFormal
namespace P0EFTJanusBoundedSelfAdjointFredholmReduction4D

set_option autoImplicit false
noncomputable section

open Set

variable {Hilbert : Type*}
  [NormedAddCommGroup Hilbert]
  [InnerProductSpace Real Hilbert]
  [CompleteSpace Hilbert]

/-- Self-adjoint closed-range operators have finite cokernel whenever their
kernel is finite-dimensional. -/
theorem boundedSelfAdjoint_cokernel_finite
    (operator : Hilbert →L[Real] Hilbert)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set Hilbert))
    (hKernel : FiniteDimensional Real operator.ker) :
    FiniteDimensional Real (Hilbert ⧸ operator.range) := by
  letI : CompleteSpace operator.range := hClosed.completeSpace_coe
  letI : FiniteDimensional Real operator.ker := hKernel
  have hOrthogonal : operator.rangeᗮ = operator.ker := by
    rw [ContinuousLinearMap.orthogonal_range, hSelfAdjoint.adjoint_eq]
  letI : FiniteDimensional Real ↥operator.rangeᗮ := by
    rw [hOrthogonal]
    infer_instance
  exact
    operator.range.quotientEquivOrthogonal.symm.toLinearEquiv.finiteDimensional

/-- Hence the bounded self-adjoint Fredholm package reduces exactly to closed
range plus finite kernel. -/
theorem boundedSelfAdjoint_fredholm_of_closedRange_finiteKernel
    (operator : Hilbert →L[Real] Hilbert)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set Hilbert))
    (hKernel : FiniteDimensional Real operator.ker) :
    IsClosed (operator.range : Set Hilbert) ∧
      FiniteDimensional Real operator.ker ∧
      FiniteDimensional Real (Hilbert ⧸ operator.range) :=
  ⟨hClosed, hKernel,
    boundedSelfAdjoint_cokernel_finite operator hSelfAdjoint hClosed hKernel⟩

/-- A bounded self-adjoint Fredholm realization has index zero. -/
theorem boundedSelfAdjoint_index_zero
    (operator : Hilbert →L[Real] Hilbert)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hClosed : IsClosed (operator.range : Set Hilbert))
    (hKernel : FiniteDimensional Real operator.ker) :
    operator.toLinearMap.index = 0 := by
  letI : CompleteSpace operator.range := hClosed.completeSpace_coe
  letI : FiniteDimensional Real operator.ker := hKernel
  have hOrthogonal : operator.rangeᗮ = operator.ker := by
    rw [ContinuousLinearMap.orthogonal_range, hSelfAdjoint.adjoint_eq]
  letI : FiniteDimensional Real ↥operator.rangeᗮ := by
    rw [hOrthogonal]
    infer_instance
  letI : FiniteDimensional Real (Hilbert ⧸ operator.range) :=
    operator.range.quotientEquivOrthogonal.symm.toLinearEquiv.finiteDimensional
  have hFinrank :
      Module.finrank Real (Hilbert ⧸ operator.range) =
        Module.finrank Real operator.ker := by
    calc
      Module.finrank Real (Hilbert ⧸ operator.range) =
          Module.finrank Real ↥operator.rangeᗮ :=
        operator.range.quotientEquivOrthogonal.toLinearEquiv.finrank_eq
      _ = Module.finrank Real operator.ker := by rw [hOrthogonal]
  rw [LinearMap.index_eq_finrank_sub, hFinrank, sub_self]

end
end P0EFTJanusBoundedSelfAdjointFredholmReduction4D
end JanusFormal
