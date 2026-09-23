import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RectangularFeatureClosed4D

/-! The Hilbert adjoint of the minimal closure, tested on the original core. -/
namespace JanusFormal.P0EFTJanusProgramPT12RectangularFeatureAdjoint4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12RectangularFeatureClosed4D

variable {D E F : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace Real F]
variable (inclusion : D →ₗ[Real] E) (operator : D →ₗ[Real] F)
variable (hSingle : Function.Injective
  (fun graph : rectangularFeatureGraphClosure inclusion operator => graph.val.1))
variable (hDense : DenseRange inclusion)
include hSingle hDense

theorem rectangularFeatureAdjoint_graph_iff (input : F) (output : E) :
    (input, output) ∈ (rectangularFeatureOperator inclusion operator).adjoint.graph ↔
    ∀ test, inner Real (operator test) input = inner Real (inclusion test) output := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (rectangularFeatureOperator_dense_domain inclusion operator hDense),
    rectangularFeatureOperator_graph inclusion operator hSingle, Submodule.mem_adjoint_iff]
  constructor
  · intro h test
    exact sub_eq_zero.mp (h (inclusion test) (operator test)
      ((inclusion.prod operator).range.le_topologicalClosure ⟨test, rfl⟩))
  · intro h first second hGraph
    have hClosed : IsClosed {pair : E × F |
        inner Real pair.2 input = inner Real pair.1 output} := by
      apply isClosed_eq <;> fun_prop
    exact sub_eq_zero.mpr (closure_minimal
      (by rintro pair ⟨test, rfl⟩; exact h test) hClosed hGraph)

theorem rectangularFeatureAdjoint_domain_iff (input : F) :
    input ∈ (rectangularFeatureOperator inclusion operator).adjoint.domain ↔
    ∃ output, ∀ test, inner Real (operator test) input = inner Real (inclusion test) output := by
  constructor
  · intro hInput
    exact ⟨_, (rectangularFeatureAdjoint_graph_iff inclusion operator hSingle hDense _ _).mp
      ((rectangularFeatureOperator inclusion operator).adjoint.mem_graph ⟨input, hInput⟩)⟩
  · rintro ⟨output, hPair⟩
    obtain ⟨vector, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
      ((rectangularFeatureAdjoint_graph_iff inclusion operator hSingle hDense input output).mpr hPair)
    change (vector : F) = input at hInput
    rw [← hInput]
    exact vector.property

variable (testInclusion : D → F) (formalAdjoint : D → E)
variable (hPairing : ∀ field test, inner Real (operator field) (testInclusion test) =
  inner Real (inclusion field) (formalAdjoint test))
include hPairing

theorem rectangularFeatureAdjoint_smooth_mem (test : D) :
    testInclusion test ∈ (rectangularFeatureOperator inclusion operator).adjoint.domain :=
  (rectangularFeatureAdjoint_domain_iff inclusion operator hSingle hDense _).mpr
    ⟨formalAdjoint test, fun field => hPairing field test⟩

theorem rectangularFeatureAdjoint_smooth_apply (test : D) :
    (rectangularFeatureOperator inclusion operator).adjoint
      ⟨testInclusion test, rectangularFeatureAdjoint_smooth_mem inclusion operator hSingle hDense
        testInclusion formalAdjoint hPairing test⟩ = formalAdjoint test := by
  exact (rectangularFeatureOperator inclusion operator).adjoint.mem_graph_snd_inj
    ((rectangularFeatureOperator inclusion operator).adjoint.mem_graph
      ⟨testInclusion test, rectangularFeatureAdjoint_smooth_mem inclusion operator hSingle hDense
        testInclusion formalAdjoint hPairing test⟩)
    ((rectangularFeatureAdjoint_graph_iff inclusion operator hSingle hDense _ _).mpr
      (fun field => hPairing field test)) rfl

theorem rectangularFeatureAdjoint_dense_domain (hTestDense : DenseRange testInclusion) :
    Dense ((rectangularFeatureOperator inclusion operator).adjoint.domain : Set F) :=
  hTestDense.mono (by
    rintro _ ⟨test, rfl⟩
    exact rectangularFeatureAdjoint_smooth_mem inclusion operator hSingle hDense testInclusion formalAdjoint hPairing test)

end
end JanusFormal.P0EFTJanusProgramPT12RectangularFeatureAdjoint4D
