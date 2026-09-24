import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedColumnSourceQuotient4D

/-! Exact adjoint transport under reduction of a closed null source subspace. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedColumnSourceAdjoint4D
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
open P0EFTJanusProgramPT12ClosedNullQuotient4D
open P0EFTJanusProgramPT12ClosedColumnSourceQuotient4D
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace Real F]
variable (operator : E →ₗ.[Real] F) (nullSpace : Submodule Real E) [IsClosed (nullSpace : Set E)]
  (hDense : Dense (operator.domain : Set E))
  (hNull : ∀ input ∈ nullSpace, (input, (0 : F)) ∈ operator.graph)

private theorem inner_mk_lift (input : E) (output : E ⧸ nullSpace) :
    inner Real (nullSpace.mkQ input) output = inner Real input (quotientLift nullSpace output) := by
  have h := inner_mk_of_left_orthogonal nullSpace (quotientLift nullSpace output) input
    (nullSpace.quotientEquivOrthogonal output).property
  rw [mk_quotientLift] at h
  exact (real_inner_comm _ _).trans (h.trans (real_inner_comm _ _))

include hDense hNull in
theorem sourceQuotient_adjoint_graph_iff (input : F) (output : E ⧸ nullSpace) :
    (input, output) ∈ (sourceQuotient operator nullSpace).adjoint.graph ↔
      (input, quotientLift nullSpace output) ∈ operator.adjoint.graph := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (sourceQuotient_denseDomain operator nullSpace hNull hDense),
    LinearPMap.adjoint_graph_eq_graph_adjoint hDense,
    Submodule.mem_adjoint_iff, Submodule.mem_adjoint_iff]
  constructor
  · intro h source value hGraph
    have hPair := h (nullSpace.mkQ source) value
      ((sourceQuotient_graph_mk_iff operator nullSpace hNull source value).mpr hGraph)
    rw [inner_mk_lift] at hPair
    exact hPair
  · intro h source value hGraph
    have hPair := h (quotientLift nullSpace source) value
      ((sourceQuotient_graph_iff operator nullSpace source value).mp hGraph)
    have hInner : inner Real (quotientLift nullSpace source) (quotientLift nullSpace output) =
        inner Real source output := nullSpace.quotientEquivOrthogonal.inner_map_map source output
    rw [hInner] at hPair
    exact hPair

include hDense hNull in
omit [IsClosed (nullSpace : Set E)] in
theorem adjoint_output_orthogonal (input : F) (output : E)
    (hGraph : (input, output) ∈ operator.adjoint.graph) : output ∈ nullSpaceᗮ := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hDense, Submodule.mem_adjoint_iff] at hGraph
  rw [Submodule.mem_orthogonal]
  intro zeroMode hZeroMode
  simpa only [inner_zero_left] using (sub_eq_zero.mp (hGraph zeroMode 0 (hNull zeroMode hZeroMode))).symm

include hDense hNull in
theorem sourceQuotient_adjoint_graph_project (input : F) (output : E)
    (hGraph : (input, output) ∈ operator.adjoint.graph) :
    (input, nullSpace.mkQ output) ∈ (sourceQuotient operator nullSpace).adjoint.graph := by
  rw [sourceQuotient_adjoint_graph_iff operator nullSpace hDense hNull,
    quotientLift_mk nullSpace output (adjoint_output_orthogonal operator nullSpace hDense hNull input output hGraph)]
  exact hGraph

include hDense hNull in
theorem sourceQuotient_adjoint_domain :
    (sourceQuotient operator nullSpace).adjoint.domain = operator.adjoint.domain := by
  ext input
  constructor
  · intro hInput
    exact LinearPMap.mem_domain_of_mem_graph
      ((sourceQuotient_adjoint_graph_iff operator nullSpace hDense hNull input _).mp
        ((sourceQuotient operator nullSpace).adjoint.mem_graph ⟨input, hInput⟩))
  · intro hInput
    exact LinearPMap.mem_domain_of_mem_graph
      (sourceQuotient_adjoint_graph_project operator nullSpace hDense hNull input _
        (operator.adjoint.mem_graph ⟨input, hInput⟩))

include hDense hNull in
theorem sourceQuotient_adjoint_denseDomain (hAdjointDense : Dense (operator.adjoint.domain : Set F)) :
    Dense ((sourceQuotient operator nullSpace).adjoint.domain : Set F) := by
  rw [sourceQuotient_adjoint_domain operator nullSpace hDense hNull]
  exact hAdjointDense

include hDense hNull in
theorem sourceQuotient_adjoint_zero_graph_iff (input : F) :
    (input, 0) ∈ (sourceQuotient operator nullSpace).adjoint.graph ↔
      (input, 0) ∈ operator.adjoint.graph := by
  rw [sourceQuotient_adjoint_graph_iff operator nullSpace hDense hNull, map_zero]

end
end JanusFormal.P0EFTJanusProgramPT12ClosedColumnSourceAdjoint4D
