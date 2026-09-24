import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

/-! Quotient the source of a closed column by a closed subspace of its kernel. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedColumnSourceQuotient4D
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace Real F]
variable (operator : E →ₗ.[Real] F) (nullSpace : Submodule Real E) [IsClosed (nullSpace : Set E)]

def sourceQuotientGraph : Submodule Real ((E ⧸ nullSpace) × F) :=
  operator.graph.comap ((quotientLift nullSpace).toLinearMap.prodMap (LinearMap.id : F →ₗ[Real] F))

private theorem sourceQuotientGraph_functional
    (pair : (E ⧸ nullSpace) × F) (hPair : pair ∈ sourceQuotientGraph operator nullSpace)
    (hZero : pair.1 = 0) : pair.2 = 0 := by
  have hGraph : (quotientLift nullSpace pair.1, pair.2) ∈ operator.graph := hPair
  rw [hZero, map_zero] at hGraph
  exact operator.graph_fst_eq_zero_snd hGraph rfl

def sourceQuotient : (E ⧸ nullSpace) →ₗ.[Real] F :=
  (sourceQuotientGraph operator nullSpace).toLinearPMap

theorem sourceQuotient_graph :
    (sourceQuotient operator nullSpace).graph = sourceQuotientGraph operator nullSpace :=
  Submodule.toLinearPMap_graph_eq _ (sourceQuotientGraph_functional operator nullSpace)

theorem sourceQuotient_graph_iff (input : E ⧸ nullSpace) (output : F) :
    (input, output) ∈ (sourceQuotient operator nullSpace).graph ↔
      (quotientLift nullSpace input, output) ∈ operator.graph := by
  rw [sourceQuotient_graph]
  rfl

theorem sourceQuotient_isClosed (hClosed : operator.IsClosed) :
    (sourceQuotient operator nullSpace).IsClosed := by
  change IsClosed ((sourceQuotient operator nullSpace).graph : Set ((E ⧸ nullSpace) × F))
  rw [sourceQuotient_graph]
  exact hClosed.preimage
    (((quotientLift nullSpace).continuous.comp continuous_fst).prodMk continuous_snd)

variable (hNull : ∀ input ∈ nullSpace, (input, (0 : F)) ∈ operator.graph)

include hNull in
theorem sourceQuotient_graph_mk_iff (input : E) (output : F) :
    (nullSpace.mkQ input, output) ∈ (sourceQuotient operator nullSpace).graph ↔
      (input, output) ∈ operator.graph := by
  have hDifference : input - quotientLift nullSpace (nullSpace.mkQ input) ∈ nullSpace :=
    (Submodule.Quotient.eq nullSpace).mp (mk_quotientLift nullSpace _).symm
  rw [sourceQuotient_graph_iff]
  constructor
  · intro hGraph
    have h := operator.graph.add_mem (hNull _ hDifference) hGraph
    simpa only [Prod.mk_add_mk, zero_add, sub_add_cancel] using h
  · intro hGraph
    have h := operator.graph.sub_mem hGraph (hNull _ hDifference)
    simpa only [Prod.mk_sub_mk, sub_sub_cancel, sub_zero] using h

include hNull in
theorem sourceQuotient_domain :
    (sourceQuotient operator nullSpace).domain = operator.domain.map nullSpace.mkQ := by
  ext input
  constructor
  · intro hInput
    have hGraph := (sourceQuotient_graph_iff operator nullSpace input _).mp
      ((sourceQuotient operator nullSpace).mem_graph ⟨input, hInput⟩)
    exact ⟨_, LinearPMap.mem_domain_of_mem_graph hGraph, mk_quotientLift nullSpace input⟩
  · rintro ⟨input, hInput, rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((sourceQuotient_graph_mk_iff operator nullSpace hNull input _).mpr
        (operator.mem_graph ⟨input, hInput⟩))

include hNull in
theorem sourceQuotient_denseDomain (hDense : Dense (operator.domain : Set E)) :
    Dense ((sourceQuotient operator nullSpace).domain : Set (E ⧸ nullSpace)) := by
  have hRange : DenseRange (fun input : operator.domain => (input : E)) := by
    simpa [DenseRange] using hDense
  have hProjected := nullSpace.mkQ_surjective.denseRange.comp hRange nullSpace.mkQL.continuous
  apply hProjected.mono
  rintro _ ⟨input, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph
    ((sourceQuotient_graph_mk_iff operator nullSpace hNull input _).mpr (operator.mem_graph input))

end
end JanusFormal.P0EFTJanusProgramPT12ClosedColumnSourceQuotient4D
