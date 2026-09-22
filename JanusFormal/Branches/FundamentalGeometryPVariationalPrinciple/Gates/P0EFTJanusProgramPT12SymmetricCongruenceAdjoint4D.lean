import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12UnboundedCongruence4D

/-! Self-adjointness survives congruence by a bounded symmetric equivalence. -/
namespace JanusFormal.P0EFTJanusProgramPT12SymmetricCongruenceAdjoint4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12UnboundedCongruence4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
variable (operator : H →ₗ.[Real] H) (change : H ≃L[Real] H)
variable (hSymmetric : ∀ x y, inner Real (change x) y = inner Real x (change y))
include hSymmetric

theorem symmetricEquiv_inverse_pairing (x y : H) :
    inner Real (change.symm x) y = inner Real x (change.symm y) := by
  have h := hSymmetric (change.symm x) (change.symm y)
  simpa only [change.apply_symm_apply] using h.symm

theorem unboundedCongruence_pairing
    (input : (unboundedCongruence operator change).domain) (test : H) :
    inner Real (unboundedCongruence operator change input) test =
    inner Real (operator ⟨change input.val,
      (unboundedCongruence_domain_iff operator change _).mp input.property⟩) (change test) := by
  rw [unboundedCongruence_apply, hSymmetric]

variable [CompleteSpace H]

theorem unboundedCongruence_adjoint (hDense : Dense (operator.domain : Set H)) :
    (unboundedCongruence operator change).adjoint = unboundedCongruence operator.adjoint change := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (unboundedCongruence_dense_domain operator change hDense),
    unboundedCongruence_graph, Submodule.mem_adjoint_iff,
    unboundedCongruence_mem_graph_iff,
    LinearPMap.adjoint_graph_eq_graph_adjoint hDense, Submodule.mem_adjoint_iff]
  constructor
  · intro h input output hGraph
    have hMember : (change.symm input, change output) ∈ congruenceGraph operator change := by
      change (change (change.symm input), change.symm (change output)) ∈ operator.graph
      simpa only [change.apply_symm_apply, change.symm_apply_apply] using hGraph
    have hPair := h (change.symm input) (change output) hMember
    rw [hSymmetric, symmetricEquiv_inverse_pairing change hSymmetric] at hPair
    exact hPair
  · intro h input output hGraph
    have hPair := h (change input) (change.symm output) hGraph
    rw [symmetricEquiv_inverse_pairing change hSymmetric, change.symm_apply_apply,
      hSymmetric, change.apply_symm_apply] at hPair
    exact hPair

theorem unboundedCongruence_selfAdjoint (hSelf : IsSelfAdjoint operator) :
    IsSelfAdjoint (unboundedCongruence operator change) := by
  rw [LinearPMap.isSelfAdjoint_def,
    unboundedCongruence_adjoint operator change hSymmetric hSelf.dense_domain,
    (LinearPMap.isSelfAdjoint_def.mp hSelf)]

end
end JanusFormal.P0EFTJanusProgramPT12SymmetricCongruenceAdjoint4D
