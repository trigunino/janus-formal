import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductClosedOperator4D

/-! Closure of a product separates into the two actual graph closures. -/
namespace JanusFormal.P0EFTJanusProgramPT12ProductClosure4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12ProductClosedOperator4D
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [NormedAddCommGroup K] [InnerProductSpace Real K]

def productGraphShuffle :
    (WithLp 2 (H × K) × WithLp 2 (H × K)) ≃L[Real] ((H × H) × (K × K)) where
  toFun pair := ((pair.1.fst, pair.2.fst), (pair.1.snd, pair.2.snd))
  invFun pair := (WithLp.toLp 2 (pair.1.1, pair.2.1), WithLp.toLp 2 (pair.1.2, pair.2.2))
  left_inv pair := by
    apply Prod.ext <;> apply WithLp.ofLp_injective 2 <;> rfl
  right_inv pair := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem productGraph_closure (first : H →ₗ.[Real] H) (second : K →ₗ.[Real] K)
    (hFirst : first.IsClosable) (hSecond : second.IsClosable) :
    (productGraph first second).topologicalClosure =
      productGraph first.closure second.closure := by
  apply SetLike.ext'
  change closure ((productGraphShuffle (H := H) (K := K)).toHomeomorph ⁻¹'
    ((first.graph : Set (H × H)) ×ˢ (second.graph : Set (K × K)))) = _
  rw [← (productGraphShuffle (H := H) (K := K)).toHomeomorph.preimage_closure, closure_prod_eq]
  change (productGraphShuffle (H := H) (K := K)).toHomeomorph ⁻¹'
    ((first.graph.topologicalClosure : Set (H × H)) ×ˢ
      (second.graph.topologicalClosure : Set (K × K))) = _
  rw [hFirst.graph_closure_eq_closure_graph, hSecond.graph_closure_eq_closure_graph]
  rfl

theorem productOperator_isClosable (first : H →ₗ.[Real] H) (second : K →ₗ.[Real] K)
    (hFirst : first.IsClosable) (hSecond : second.IsClosable) :
    (productOperator first second).IsClosable := by
  refine ⟨productOperator first.closure second.closure, ?_⟩
  rw [productOperator_graph, productGraph_closure first second hFirst hSecond,
    productOperator_graph]

theorem productOperator_closure (first : H →ₗ.[Real] H) (second : K →ₗ.[Real] K)
    (hFirst : first.IsClosable) (hSecond : second.IsClosable) :
    (productOperator first second).closure =
      productOperator first.closure second.closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [← (productOperator_isClosable first second hFirst hSecond).graph_closure_eq_closure_graph,
    productOperator_graph, productGraph_closure first second hFirst hSecond,
    productOperator_graph]

end
end JanusFormal.P0EFTJanusProgramPT12ProductClosure4D
