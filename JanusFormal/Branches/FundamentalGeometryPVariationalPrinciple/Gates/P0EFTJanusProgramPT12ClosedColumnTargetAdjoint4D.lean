import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedColumnTargetQuotient4D

/-! Exact Hilbert adjoint transport for an orthogonal target reduction. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedColumnTargetAdjoint4D
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
open P0EFTJanusProgramPT12ClosedNullQuotient4D
open P0EFTJanusProgramPT12ClosedColumnTargetQuotient4D
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
variable (operator : E →ₗ.[Real] F) (nullSpace : Submodule Real F) [IsClosed (nullSpace : Set F)]
  (hDense : Dense (operator.domain : Set E))
  (hOrth : ∀ input output, (input, output) ∈ operator.graph → output ∈ nullSpaceᗮ)

include hDense hOrth in
theorem targetQuotient_adjoint_mk_graph_iff (input : F) (output : E) :
    (nullSpace.mkQ input, output) ∈ (targetQuotient operator nullSpace).adjoint.graph ↔
      (input, output) ∈ operator.adjoint.graph := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (targetQuotient_denseDomain operator nullSpace hOrth hDense),
    LinearPMap.adjoint_graph_eq_graph_adjoint hDense,
    Submodule.mem_adjoint_iff, Submodule.mem_adjoint_iff]
  constructor
  · intro h source value hGraph
    have hPair := h source (nullSpace.mkQ value)
      (targetQuotient_graph_project operator nullSpace hOrth source value hGraph)
    rw [inner_mk_of_left_orthogonal nullSpace value input (hOrth source value hGraph)] at hPair
    exact hPair
  · intro h source value hGraph
    have hLift := (targetQuotient_graph_iff operator nullSpace source value).mp hGraph
    have hPair := h source (quotientLift nullSpace value) hLift
    have hInner := inner_mk_of_left_orthogonal nullSpace (quotientLift nullSpace value) input
      (hOrth source (quotientLift nullSpace value) hLift)
    rw [mk_quotientLift] at hInner
    rw [← hInner] at hPair
    exact hPair

include hDense hOrth in
theorem targetQuotient_adjoint_mk_domain_iff (input : F) :
    nullSpace.mkQ input ∈ (targetQuotient operator nullSpace).adjoint.domain ↔
      input ∈ operator.adjoint.domain := by
  constructor
  · intro hInput
    exact LinearPMap.mem_domain_of_mem_graph
      ((targetQuotient_adjoint_mk_graph_iff operator nullSpace hDense hOrth input _).mp
        ((targetQuotient operator nullSpace).adjoint.mem_graph ⟨nullSpace.mkQ input, hInput⟩))
  · intro hInput
    exact LinearPMap.mem_domain_of_mem_graph
      ((targetQuotient_adjoint_mk_graph_iff operator nullSpace hDense hOrth input _).mpr
        (operator.adjoint.mem_graph ⟨input, hInput⟩))

include hDense hOrth in
theorem targetQuotient_adjoint_denseDomain (hAdjointDense : Dense (operator.adjoint.domain : Set F)) :
    Dense ((targetQuotient operator nullSpace).adjoint.domain : Set (F ⧸ nullSpace)) := by
  have hRange : DenseRange (fun input : operator.adjoint.domain => (input : F)) := by
    simpa [DenseRange] using hAdjointDense
  have hProjected := nullSpace.mkQ_surjective.denseRange.comp hRange nullSpace.mkQL.continuous
  apply hProjected.mono
  rintro _ ⟨input, rfl⟩
  exact (targetQuotient_adjoint_mk_domain_iff operator nullSpace hDense hOrth input).mpr input.property

end
end JanusFormal.P0EFTJanusProgramPT12ClosedColumnTargetAdjoint4D
