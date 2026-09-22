import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-! Domain-exact congruence of unbounded operators by a bounded equivalence. -/
namespace JanusFormal.P0EFTJanusProgramPT12UnboundedCongruence4D
set_option autoImplicit false
noncomputable section
open Set Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
variable (operator : H →ₗ.[Real] H) (change : H ≃L[Real] H)

def congruenceGraph : Submodule Real (H × H) :=
  operator.graph.comap (change.toLinearMap.prodMap change.symm.toLinearMap)

def unboundedCongruence : H →ₗ.[Real] H :=
  (congruenceGraph operator change).toLinearPMap

theorem unboundedCongruence_graph :
    (unboundedCongruence operator change).graph = congruenceGraph operator change := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  apply change.symm.injective
  rw [map_zero]
  exact operator.graph_fst_eq_zero_snd hPair (by change change pair.1 = 0; rw [hZero, map_zero])

theorem unboundedCongruence_mem_graph_iff (input output : H) :
    (input, output) ∈ (unboundedCongruence operator change).graph ↔
      (change input, change.symm output) ∈ operator.graph := by
  rw [unboundedCongruence_graph]
  rfl

theorem unboundedCongruence_domain_iff (input : H) :
    input ∈ (unboundedCongruence operator change).domain ↔ change input ∈ operator.domain := by
  constructor
  · intro hInput
    have h := (unboundedCongruence_mem_graph_iff operator change _ _).mp
      ((unboundedCongruence operator change).mem_graph ⟨input, hInput⟩)
    obtain ⟨vector, hVector, _⟩ := operator.mem_graph_iff.mp h
    change (vector : H) = change input at hVector
    rw [← hVector]
    exact vector.property
  · intro hInput
    refine ⟨(input, change (operator ⟨change input, hInput⟩)), ?_, rfl⟩
    change (change input, change.symm (change (operator ⟨change input, hInput⟩))) ∈ operator.graph
    rw [change.symm_apply_apply]
    exact operator.mem_graph ⟨change input, hInput⟩

theorem unboundedCongruence_apply (input : (unboundedCongruence operator change).domain) :
    unboundedCongruence operator change input = change (operator
      ⟨change input.val, (unboundedCongruence_domain_iff operator change _).mp input.property⟩) := by
  have h := (unboundedCongruence_mem_graph_iff operator change _ _).mp
    ((unboundedCongruence operator change).mem_graph input)
  obtain ⟨vector, hVector, hValue⟩ := operator.mem_graph_iff.mp h
  apply change.symm.injective
  rw [change.symm_apply_apply]
  exact hValue.symm.trans (congrArg operator (Subtype.ext hVector))

theorem unboundedCongruence_dense_domain (hDense : Dense (operator.domain : Set H)) :
    Dense ((unboundedCongruence operator change).domain : Set H) := by
  convert hDense.preimage change.toHomeomorph.isOpenMap using 1
  ext input
  exact unboundedCongruence_domain_iff operator change input

theorem unboundedCongruence_isClosed (hClosed : operator.IsClosed) :
    (unboundedCongruence operator change).IsClosed := by
  rw [LinearPMap.IsClosed, unboundedCongruence_graph]
  exact hClosed.preimage (by fun_prop : Continuous
    (fun pair : H × H => (change pair.1, change.symm pair.2)))

end
end JanusFormal.P0EFTJanusProgramPT12UnboundedCongruence4D
