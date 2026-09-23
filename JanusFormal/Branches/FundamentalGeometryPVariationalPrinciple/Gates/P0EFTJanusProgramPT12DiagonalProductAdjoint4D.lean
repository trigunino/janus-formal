import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalProductPMap4D

/-! Adjoint and self-adjointness of a direct sum, with its full product domain. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiagonalProductAdjoint4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12DiagonalProductPMap4D
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]

theorem diagonalProductOperator_adjoint (first : E →ₗ.[Real] E) (second : F →ₗ.[Real] F)
    (hFirst : Dense (first.domain : Set E)) (hSecond : Dense (second.domain : Set F)) :
    (diagonalProductOperator first second).adjoint = diagonalProductOperator first.adjoint second.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (diagonalProductOperator_dense_domain first second hFirst hSecond),
    diagonalProductOperator_graph, Submodule.mem_adjoint_iff,
    diagonalProductOperator_mem_graph_iff,
    LinearPMap.adjoint_graph_eq_graph_adjoint hFirst,
    LinearPMap.adjoint_graph_eq_graph_adjoint hSecond,
    Submodule.mem_adjoint_iff, Submodule.mem_adjoint_iff]
  constructor
  · intro h
    constructor
    · intro input output hGraph
      have hPair := h (WithLp.toLp 2 (input, 0)) (WithLp.toLp 2 (output, 0))
        ⟨hGraph, second.graph.zero_mem⟩
      simpa only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
        inner_zero_left, zero_add, add_zero] using hPair
    · intro input output hGraph
      have hPair := h (WithLp.toLp 2 (0, input)) (WithLp.toLp 2 (0, output))
        ⟨first.graph.zero_mem, hGraph⟩
      simpa only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
        inner_zero_left, zero_add, add_zero] using hPair
  · rintro ⟨hFirstAdj, hSecondAdj⟩ input output hGraph
    have hOne := hFirstAdj input.fst output.fst hGraph.1
    have hTwo := hSecondAdj input.snd output.snd hGraph.2
    change (inner Real output.fst pair.1.fst + inner Real output.snd pair.1.snd) -
      (inner Real input.fst pair.2.fst + inner Real input.snd pair.2.snd) = 0
    linarith

theorem diagonalProductOperator_selfAdjoint (first : E →ₗ.[Real] E) (second : F →ₗ.[Real] F)
    (hFirst : IsSelfAdjoint first) (hSecond : IsSelfAdjoint second) :
    IsSelfAdjoint (diagonalProductOperator first second) := by
  rw [LinearPMap.isSelfAdjoint_def,
    diagonalProductOperator_adjoint first second hFirst.dense_domain hSecond.dense_domain,
    LinearPMap.isSelfAdjoint_def.mp hFirst, LinearPMap.isSelfAdjoint_def.mp hSecond]

end
end JanusFormal.P0EFTJanusProgramPT12DiagonalProductAdjoint4D
