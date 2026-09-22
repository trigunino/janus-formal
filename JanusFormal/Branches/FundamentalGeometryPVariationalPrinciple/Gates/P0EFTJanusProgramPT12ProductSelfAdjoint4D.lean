import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductClosedOperator4D


/-! Self-adjoint products, including bounded symmetric factors. -/
namespace JanusFormal.P0EFTJanusProgramPT12ProductSelfAdjoint4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12ProductClosedOperator4D
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace Real K] [CompleteSpace K]

theorem productOperator_adjoint (first : H →ₗ.[Real] H) (second : K →ₗ.[Real] K)
    (hFirst : Dense (first.domain : Set H)) (hSecond : Dense (second.domain : Set K)) :
    (productOperator first second).adjoint = productOperator first.adjoint second.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (productOperator_dense_domain first second hFirst hSecond),
    productOperator_graph, Submodule.mem_adjoint_iff,
    productOperator_mem_graph_iff,
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

theorem productOperator_selfAdjoint (first : H →ₗ.[Real] H) (second : K →ₗ.[Real] K)
    (hFirst : IsSelfAdjoint first) (hSecond : IsSelfAdjoint second) :
    IsSelfAdjoint (productOperator first second) := by
  rw [LinearPMap.isSelfAdjoint_def,
    productOperator_adjoint first second hFirst.dense_domain hSecond.dense_domain,
    (LinearPMap.isSelfAdjoint_def.mp hFirst), (LinearPMap.isSelfAdjoint_def.mp hSecond)]

/-- A bounded symmetric block can be coupled to an unbounded self-adjoint block. -/
theorem bounded_toPMap_selfAdjoint (operator : H →L[Real] H)
    (hSym : ∀ x y, inner Real (operator x) y = inner Real x (operator y)) :
    IsSelfAdjoint (operator.toPMap ⊤) := by
  rw [LinearPMap.isSelfAdjoint_def,
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense operator dense_univ]
  congr 1
  apply LinearMap.ext
  intro x
  apply ext_inner_right Real
  intro y
  change inner Real (operator.adjoint x) y = inner Real (operator x) y
  rw [operator.adjoint_inner_left, hSym]

end
end JanusFormal.P0EFTJanusProgramPT12ProductSelfAdjoint4D
