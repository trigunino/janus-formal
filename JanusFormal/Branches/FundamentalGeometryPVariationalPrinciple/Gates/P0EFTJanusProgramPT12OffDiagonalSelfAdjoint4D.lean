import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedDoubleAdjoint4D

/-! The canonical self-adjoint block built from a closed operator and its adjoint. -/
namespace JanusFormal.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12ClosedDoubleAdjoint4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

theorem offDiagonalOperator_adjoint (first second : H →ₗ.[Real] H)
    (hFirst : Dense (first.domain : Set H)) (hSecond : Dense (second.domain : Set H)) :
    (offDiagonalOperator first second).adjoint = offDiagonalOperator second.adjoint first.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (offDiagonalOperator_dense_domain first second hFirst hSecond),
    offDiagonalOperator_graph, Submodule.mem_adjoint_iff,
    offDiagonalOperator_mem_graph_iff,
    LinearPMap.adjoint_graph_eq_graph_adjoint hSecond,
    LinearPMap.adjoint_graph_eq_graph_adjoint hFirst,
    Submodule.mem_adjoint_iff, Submodule.mem_adjoint_iff]
  constructor
  · intro h
    constructor
    · intro input output hGraph
      have hPair := h (WithLp.toLp 2 (input, 0)) (WithLp.toLp 2 (0, output))
        ⟨first.graph.zero_mem, hGraph⟩
      simpa only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
        inner_zero_left, zero_add, add_zero] using hPair
    · intro input output hGraph
      have hPair := h (WithLp.toLp 2 (0, input)) (WithLp.toLp 2 (output, 0))
        ⟨hGraph, second.graph.zero_mem⟩
      simpa only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
        inner_zero_left, zero_add, add_zero] using hPair
  · rintro ⟨hSecondAdj, hFirstAdj⟩ input output hGraph
    have hOne := hFirstAdj input.snd output.fst hGraph.1
    have hTwo := hSecondAdj input.fst output.snd hGraph.2
    change (inner Real output.fst pair.1.fst + inner Real output.snd pair.1.snd) -
      (inner Real input.fst pair.2.fst + inner Real input.snd pair.2.snd) = 0
    linarith

theorem offDiagonalOperator_selfAdjoint (operator : H →ₗ.[Real] H)
    (hClosed : operator.IsClosed) (hDense : Dense (operator.domain : Set H))
    (hAdjointDense : Dense (operator.adjoint.domain : Set H)) :
    IsSelfAdjoint (offDiagonalOperator operator operator.adjoint) := by
  rw [LinearPMap.isSelfAdjoint_def,
    offDiagonalOperator_adjoint operator operator.adjoint hDense hAdjointDense,
    closedOperator_adjoint_adjoint operator hClosed hDense hAdjointDense]

end
end JanusFormal.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
