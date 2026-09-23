import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! Graph closure preserves symmetry and inclusion in a closed extension. -/
namespace JanusFormal.P0EFTJanusProgramPT12SymmetricL2GraphClosure4D
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

theorem symmetric_closure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →ₗ.[Real] E)
    (hClosable : T.IsClosable) (hSym : T.IsFormalAdjoint T) :
    T.closure.IsFormalAdjoint T.closure := by
  let C := T.closure
  have hGraph : T.graph.topologicalClosure = C.graph :=
    hClosable.graph_closure_eq_closure_graph
  have hFirst (x : C.domain) (y : T.domain) :
      inner Real (C x) (y : E) = inner Real (x : E) (T y) := by
    have hSubset : (T.graph : Set (E × E)) ⊆
        {p | inner Real p.2 (y : E) = inner Real p.1 (T y)} := by
      intro p hp
      obtain ⟨z, hz₁, hz₂⟩ := T.mem_graph_iff.mp hp
      change inner Real p.2 (y : E) = inner Real p.1 (T y)
      rw [← hz₁, ← hz₂]
      exact hSym z y
    have hClosed : IsClosed
        {p : E × E | inner Real p.2 (y : E) = inner Real p.1 (T y)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hx : ((x : E), C x) ∈ closure (T.graph : Set (E × E)) := by
      rw [← Submodule.topologicalClosure_coe, hGraph]
      exact C.mem_graph x
    exact (closure_minimal hSubset hClosed) hx
  intro x y
  have hSubset : (T.graph : Set (E × E)) ⊆
      {p | inner Real (C x) p.1 = inner Real (x : E) p.2} := by
    intro p hp
    obtain ⟨z, hz₁, hz₂⟩ := T.mem_graph_iff.mp hp
    change inner Real (C x) p.1 = inner Real (x : E) p.2
    rw [← hz₁, ← hz₂]
    exact hFirst x z
  have hClosed : IsClosed
      {p : E × E | inner Real (C x) p.1 = inner Real (x : E) p.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hy : ((y : E), C y) ∈ closure (T.graph : Set (E × E)) := by
    rw [← Submodule.topologicalClosure_coe, hGraph]
    exact C.mem_graph y
  exact (closure_minimal hSubset hClosed) hy

theorem closure_le_closed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
    (operator extension : H →ₗ.[Real] H) (hClosed : extension.IsClosed)
    (hLe : operator ≤ extension) : operator.closure ≤ extension := by
  apply LinearPMap.le_of_le_graph
  rw [← (hClosed.isClosable.leIsClosable hLe).graph_closure_eq_closure_graph]
  exact closure_minimal (LinearPMap.le_graph_of_le hLe) hClosed

end
end JanusFormal.P0EFTJanusProgramPT12SymmetricL2GraphClosure4D