import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalClosedOperator4D

/-! Closure of the off-diagonal graph separates into the two actual graph closures. -/
namespace JanusFormal.P0EFTJanusProgramPT12OffDiagonalClosure4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]

def offDiagonalGraphShuffle :
    (WithLp 2 (H × H) × WithLp 2 (H × H)) ≃L[Real] ((H × H) × (H × H)) where
  toFun pair := ((pair.1.snd, pair.2.fst), (pair.1.fst, pair.2.snd))
  invFun pair := (WithLp.toLp 2 (pair.2.1, pair.1.1), WithLp.toLp 2 (pair.1.2, pair.2.2))
  left_inv pair := by
    apply Prod.ext <;> apply WithLp.ofLp_injective 2 <;> rfl
  right_inv pair := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem offDiagonalGraph_closure (first second : H →ₗ.[Real] H)
    (hFirst : first.IsClosable) (hSecond : second.IsClosable) :
    (offDiagonalGraph first second).topologicalClosure =
      offDiagonalGraph first.closure second.closure := by
  apply SetLike.ext'
  change closure ((offDiagonalGraphShuffle (H := H)).toHomeomorph ⁻¹'
    ((first.graph : Set (H × H)) ×ˢ (second.graph : Set (H × H)))) = _
  rw [← (offDiagonalGraphShuffle (H := H)).toHomeomorph.preimage_closure, closure_prod_eq]
  change (offDiagonalGraphShuffle (H := H)).toHomeomorph ⁻¹'
    ((first.graph.topologicalClosure : Set (H × H)) ×ˢ
      (second.graph.topologicalClosure : Set (H × H))) = _
  rw [hFirst.graph_closure_eq_closure_graph, hSecond.graph_closure_eq_closure_graph]
  rfl

theorem offDiagonalOperator_isClosable (first second : H →ₗ.[Real] H)
    (hFirst : first.IsClosable) (hSecond : second.IsClosable) :
    (offDiagonalOperator first second).IsClosable := by
  refine ⟨offDiagonalOperator first.closure second.closure, ?_⟩
  rw [offDiagonalOperator_graph, offDiagonalGraph_closure first second hFirst hSecond,
    offDiagonalOperator_graph]

theorem offDiagonalOperator_closure (first second : H →ₗ.[Real] H)
    (hFirst : first.IsClosable) (hSecond : second.IsClosable) :
    (offDiagonalOperator first second).closure =
      offDiagonalOperator first.closure second.closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [← (offDiagonalOperator_isClosable first second hFirst hSecond).graph_closure_eq_closure_graph,
    offDiagonalOperator_graph, offDiagonalGraph_closure first second hFirst hSecond,
    offDiagonalOperator_graph]

end
end JanusFormal.P0EFTJanusProgramPT12OffDiagonalClosure4D
