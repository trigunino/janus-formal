import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! A real Hilbert adjoint is characterized by its weak pairings. -/
namespace JanusFormal.P0EFTJanusProgramPT12DenseL2AdjointGraph4D
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

theorem adjoint_graph_iff (operator : H →ₗ.[Real] H)
    (hDense : Dense (operator.domain : Set H)) (input output : H) :
    (input, output) ∈ (LinearPMap.adjoint (𝕜 := Real) operator).graph ↔
      ∀ test : operator.domain, inner Real output test.val = inner Real input (operator test) := by
  constructor
  · intro h test
    obtain ⟨field, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp h
    dsimp only at hInput hOutput
    rw [← hInput, ← hOutput]
    exact LinearPMap.adjoint_isFormalAdjoint (𝕜 := Real) hDense field test
  · intro h
    let field : (LinearPMap.adjoint (𝕜 := Real) operator).domain :=
      ⟨input, LinearPMap.mem_adjoint_domain_of_exists (𝕜 := Real) input ⟨output, h⟩⟩
    exact (LinearPMap.mem_graph_iff _).mpr
      ⟨field, rfl, LinearPMap.adjoint_apply_eq (𝕜 := Real) hDense field h⟩

end
end JanusFormal.P0EFTJanusProgramPT12DenseL2AdjointGraph4D
