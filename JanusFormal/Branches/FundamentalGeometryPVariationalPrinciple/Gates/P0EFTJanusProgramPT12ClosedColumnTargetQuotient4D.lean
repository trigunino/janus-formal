import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

/-! Quotient the target of a closed column with outputs orthogonal to the null space. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedColumnTargetQuotient4D
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
variable (operator : E →ₗ.[Real] F) (nullSpace : Submodule Real F) [IsClosed (nullSpace : Set F)]

def targetQuotientGraph : Submodule Real (E × (F ⧸ nullSpace)) :=
  operator.graph.comap ((LinearMap.id : E →ₗ[Real] E).prodMap (quotientLift nullSpace).toLinearMap)

private theorem targetQuotientGraph_functional
    (pair : E × (F ⧸ nullSpace)) (hPair : pair ∈ targetQuotientGraph operator nullSpace)
    (hZero : pair.1 = 0) : pair.2 = 0 := by
  have hGraph : (pair.1, quotientLift nullSpace pair.2) ∈ operator.graph := hPair
  have hOutput := operator.graph_fst_eq_zero_snd hGraph hZero
  calc
    pair.2 = nullSpace.mkQ (quotientLift nullSpace pair.2) := (mk_quotientLift nullSpace _).symm
    _ = 0 := by rw [hOutput, map_zero]

def targetQuotient : E →ₗ.[Real] (F ⧸ nullSpace) :=
  (targetQuotientGraph operator nullSpace).toLinearPMap

theorem targetQuotient_graph :
    (targetQuotient operator nullSpace).graph = targetQuotientGraph operator nullSpace :=
  Submodule.toLinearPMap_graph_eq _ (targetQuotientGraph_functional operator nullSpace)

theorem targetQuotient_graph_iff (input : E) (output : F ⧸ nullSpace) :
    (input, output) ∈ (targetQuotient operator nullSpace).graph ↔
      (input, quotientLift nullSpace output) ∈ operator.graph := by
  rw [targetQuotient_graph]
  rfl

theorem targetQuotient_isClosed (hClosed : operator.IsClosed) :
    (targetQuotient operator nullSpace).IsClosed := by
  change IsClosed ((targetQuotient operator nullSpace).graph : Set (E × (F ⧸ nullSpace)))
  rw [targetQuotient_graph]
  exact hClosed.preimage
    (continuous_fst.prodMk ((quotientLift nullSpace).continuous.comp continuous_snd))

variable (hOrth : ∀ input output, (input, output) ∈ operator.graph → output ∈ nullSpaceᗮ)
include hOrth in
theorem targetQuotient_graph_project (input : E) (output : F)
    (hGraph : (input, output) ∈ operator.graph) :
    (input, nullSpace.mkQ output) ∈ (targetQuotient operator nullSpace).graph := by
  rw [targetQuotient_graph_iff, quotientLift_mk nullSpace output (hOrth input output hGraph)]
  exact hGraph

include hOrth in
theorem targetQuotient_domain : (targetQuotient operator nullSpace).domain = operator.domain := by
  ext input
  constructor
  · intro hInput
    exact LinearPMap.mem_domain_of_mem_graph
      ((targetQuotient_graph_iff operator nullSpace input _).mp
        ((targetQuotient operator nullSpace).mem_graph ⟨input, hInput⟩))
  · intro hInput
    exact LinearPMap.mem_domain_of_mem_graph
      (targetQuotient_graph_project operator nullSpace hOrth input _ (operator.mem_graph ⟨input, hInput⟩))

include hOrth in
theorem targetQuotient_denseDomain (hDense : Dense (operator.domain : Set E)) :
    Dense ((targetQuotient operator nullSpace).domain : Set E) := by
  rw [targetQuotient_domain operator nullSpace hOrth]
  exact hDense

theorem targetQuotient_zero_graph_iff (input : E) :
    (input, 0) ∈ (targetQuotient operator nullSpace).graph ↔ (input, 0) ∈ operator.graph := by
  rw [targetQuotient_graph_iff, map_zero]

end
end JanusFormal.P0EFTJanusProgramPT12ClosedColumnTargetQuotient4D
