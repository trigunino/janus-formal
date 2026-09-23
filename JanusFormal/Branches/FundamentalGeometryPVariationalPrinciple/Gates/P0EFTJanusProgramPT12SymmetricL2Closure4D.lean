import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! Small real-Hilbert-space lemmas for densely defined symmetric operators. -/
namespace JanusFormal.P0EFTJanusProgramPT12SymmetricL2Closure4D
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

theorem symmetric_le_adjoint (operator : H →ₗ.[Real] H)
    (hDense : Dense (operator.domain : Set H))
    (hSymmetric : LinearPMap.IsFormalAdjoint (𝕜 := Real) operator operator) :
    operator ≤ LinearPMap.adjoint (𝕜 := Real) operator :=
  LinearPMap.IsFormalAdjoint.le_adjoint (𝕜 := Real) (E := H) (F := H)
    (T := operator) (S := operator) hDense hSymmetric

theorem symmetric_isClosable (operator : H →ₗ.[Real] H)
    (hDense : Dense (operator.domain : Set H))
    (hSymmetric : LinearPMap.IsFormalAdjoint (𝕜 := Real) operator operator) : operator.IsClosable :=
  (LinearPMap.adjoint_isClosed (𝕜 := Real) (T := operator) hDense).isClosable.leIsClosable
    (symmetric_le_adjoint operator hDense hSymmetric)

end
end JanusFormal.P0EFTJanusProgramPT12SymmetricL2Closure4D
