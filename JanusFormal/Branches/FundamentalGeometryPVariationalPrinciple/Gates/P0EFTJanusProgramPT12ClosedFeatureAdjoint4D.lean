import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureOperator4D

/-! The Hilbert adjoint of the minimal closure, tested on the original core. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedFeatureAdjoint4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D

variable {D H : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable (inclusion operator : D →ₗ[Real] H)
variable (hSingle : Function.Injective
  (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1))
variable (hDense : DenseRange inclusion)
include hSingle hDense

theorem closedFeatureAdjoint_graph_iff (input output : H) :
    (input, output) ∈ (closedFeatureOperator inclusion operator).adjoint.graph ↔
    ∀ test, inner Real (operator test) input = inner Real (inclusion test) output := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (closedFeatureOperator_dense_domain inclusion operator hDense),
    closedFeatureOperator_graph inclusion operator hSingle, Submodule.mem_adjoint_iff]
  constructor
  · intro h test
    exact sub_eq_zero.mp (h (inclusion test) (operator test)
      ((inclusion.prod operator).range.le_topologicalClosure ⟨test, rfl⟩))
  · intro h first second hGraph
    have hClosed : IsClosed {pair : H × H |
        inner Real pair.2 input = inner Real pair.1 output} := by
      apply isClosed_eq <;> fun_prop
    exact sub_eq_zero.mpr (closure_minimal
      (by rintro pair ⟨test, rfl⟩; exact h test) hClosed hGraph)

theorem closedFeatureAdjoint_domain_iff (input : H) :
    input ∈ (closedFeatureOperator inclusion operator).adjoint.domain ↔
    ∃ output, ∀ test, inner Real (operator test) input = inner Real (inclusion test) output := by
  constructor
  · intro hInput
    exact ⟨_, (closedFeatureAdjoint_graph_iff inclusion operator hSingle hDense _ _).mp
      ((closedFeatureOperator inclusion operator).adjoint.mem_graph ⟨input, hInput⟩)⟩
  · rintro ⟨output, hPair⟩
    obtain ⟨vector, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
      ((closedFeatureAdjoint_graph_iff inclusion operator hSingle hDense input output).mpr hPair)
    change (vector : H) = input at hInput
    rw [← hInput]
    exact vector.property

variable (formalAdjoint : D → H)
variable (hPairing : ∀ field test, inner Real (operator field) (inclusion test) =
  inner Real (inclusion field) (formalAdjoint test))
include hPairing

theorem closedFeatureAdjoint_smooth_mem (test : D) :
    inclusion test ∈ (closedFeatureOperator inclusion operator).adjoint.domain :=
  (closedFeatureAdjoint_domain_iff inclusion operator hSingle hDense _).mpr
    ⟨formalAdjoint test, fun field => hPairing field test⟩

theorem closedFeatureAdjoint_smooth_apply (test : D) :
    (closedFeatureOperator inclusion operator).adjoint
      ⟨inclusion test, closedFeatureAdjoint_smooth_mem inclusion operator hSingle hDense
        formalAdjoint hPairing test⟩ = formalAdjoint test := by
  apply LinearPMap.adjoint_apply_eq
    (closedFeatureOperator_dense_domain inclusion operator hDense)
  intro vector
  have hGraph := (closedFeatureOperator inclusion operator).mem_graph vector
  rw [closedFeatureOperator_graph inclusion operator hSingle] at hGraph
  have h := linearFeatureGraphClosure_pairing inclusion operator formalAdjoint hPairing
    ⟨_, hGraph⟩ test
  exact (real_inner_comm _ _).trans (h.symm.trans (real_inner_comm _ _))

theorem closedFeatureAdjoint_dense_domain :
    Dense ((closedFeatureOperator inclusion operator).adjoint.domain : Set H) :=
  hDense.mono (by
    rintro _ ⟨test, rfl⟩
    exact closedFeatureAdjoint_smooth_mem inclusion operator hSingle hDense formalAdjoint hPairing test)

end
end JanusFormal.P0EFTJanusProgramPT12ClosedFeatureAdjoint4D
