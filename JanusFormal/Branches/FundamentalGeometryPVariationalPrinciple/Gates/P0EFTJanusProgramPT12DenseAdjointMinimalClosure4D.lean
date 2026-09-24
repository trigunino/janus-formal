import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-! A dense adjoint yields a closed minimal realization with the same adjoint. -/
namespace JanusFormal.P0EFTJanusProgramPT12DenseAdjointMinimalClosure4D
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]

theorem closable_of_dense_adjoint (operator : E →ₗ.[Real] F)
    (hDense : Dense (operator.domain : Set E))
    (hAdjointDense : Dense (operator.adjoint.domain : Set F)) : operator.IsClosable :=
  (LinearPMap.adjoint_isClosed hAdjointDense).isClosable.leIsClosable
    ((LinearPMap.adjoint_isFormalAdjoint hDense).le_adjoint hAdjointDense)

omit [CompleteSpace E] [CompleteSpace F] in
theorem minimalClosure_denseDomain (operator : E →ₗ.[Real] F)
    (hDense : Dense (operator.domain : Set E)) : Dense (operator.closure.domain : Set E) :=
  hDense.mono operator.le_closure.1

omit [CompleteSpace F] in
theorem minimalClosure_adjoint_eq (operator : E →ₗ.[Real] F)
    (hDense : Dense (operator.domain : Set E)) (hClosable : operator.IsClosable) :
    operator.closure.adjoint = operator.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨input, output⟩
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (minimalClosure_denseDomain operator hDense),
    ← hClosable.graph_closure_eq_closure_graph,
    LinearPMap.adjoint_graph_eq_graph_adjoint hDense,
    Submodule.mem_adjoint_iff, Submodule.mem_adjoint_iff]
  constructor
  · intro h first second hGraph
    exact h first second (operator.graph.le_topologicalClosure hGraph)
  · intro h first second hGraph
    have hClosed : IsClosed {pair : E × F |
        inner Real pair.2 input - inner Real pair.1 output = 0} := by
      apply isClosed_eq <;> fun_prop
    exact closure_minimal (by rintro ⟨a, b⟩ hPair; exact h a b hPair) hClosed hGraph

end
end JanusFormal.P0EFTJanusProgramPT12DenseAdjointMinimalClosure4D
