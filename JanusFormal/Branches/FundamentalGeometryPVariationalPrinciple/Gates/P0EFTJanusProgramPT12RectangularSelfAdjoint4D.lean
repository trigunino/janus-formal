import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RectangularOffDiagonal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RectangularDoubleAdjoint4D

/-! The canonical self-adjoint block built from a closed operator and its adjoint. -/
namespace JanusFormal.P0EFTJanusProgramPT12RectangularSelfAdjoint4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12RectangularOffDiagonal4D
open P0EFTJanusProgramPT12RectangularDoubleAdjoint4D
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]

theorem rectangularOffDiagonalOperator_adjoint (first : F →ₗ.[Real] E) (second : E →ₗ.[Real] F)
    (hFirst : Dense (first.domain : Set F)) (hSecond : Dense (second.domain : Set E)) :
    (rectangularOffDiagonalOperator first second).adjoint = rectangularOffDiagonalOperator second.adjoint first.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (rectangularOffDiagonalOperator_dense_domain first second hFirst hSecond),
    rectangularOffDiagonalOperator_graph, Submodule.mem_adjoint_iff,
    rectangularOffDiagonalOperator_mem_graph_iff,
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

theorem rectangularOffDiagonalOperator_selfAdjoint (operator : E →ₗ.[Real] F)
    (hClosed : operator.IsClosed) (hDense : Dense (operator.domain : Set E))
    (hAdjointDense : Dense (operator.adjoint.domain : Set F)) :
    IsSelfAdjoint (rectangularOffDiagonalOperator operator.adjoint operator) := by
  rw [LinearPMap.isSelfAdjoint_def,
    rectangularOffDiagonalOperator_adjoint operator.adjoint operator hAdjointDense hDense,
    closedRectangularOperator_adjoint_adjoint operator hClosed hDense hAdjointDense]

end
end JanusFormal.P0EFTJanusProgramPT12RectangularSelfAdjoint4D
