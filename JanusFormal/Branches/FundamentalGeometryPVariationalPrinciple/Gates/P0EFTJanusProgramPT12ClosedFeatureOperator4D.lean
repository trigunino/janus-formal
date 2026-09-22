import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! The closed L2 operator determined by a single-valued feature graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedFeatureOperator4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D

variable {D H : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup H] [InnerProductSpace Real H]
variable (inclusion operator : D →ₗ[Real] H)

def closedFeatureOperator : H →ₗ.[Real] H :=
  (linearFeatureGraphClosure inclusion operator).toLinearPMap

theorem closedFeatureOperator_graph
    (hSingle : Function.Injective
      (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1)) :
    (closedFeatureOperator inclusion operator).graph =
      linearFeatureGraphClosure inclusion operator := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  exact congrArg (fun graph => graph.val.2)
    (hSingle (a₁ := ⟨pair, hPair⟩) (a₂ := 0) hZero)

theorem closedFeatureOperator_isClosed
    (hSingle : Function.Injective
      (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1)) :
    (closedFeatureOperator inclusion operator).IsClosed := by
  rw [LinearPMap.IsClosed, closedFeatureOperator_graph inclusion operator hSingle]
  exact (inclusion.prod operator).range.isClosed_topologicalClosure

theorem closedFeatureOperator_smooth_mem (field : D) :
    inclusion field ∈ (closedFeatureOperator inclusion operator).domain :=
  ⟨(inclusion field, operator field),
    (inclusion.prod operator).range.le_topologicalClosure ⟨field, rfl⟩, rfl⟩

theorem closedFeatureOperator_smooth_apply
    (hSingle : Function.Injective
      (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1)) (field : D) :
    closedFeatureOperator inclusion operator
      ⟨inclusion field, closedFeatureOperator_smooth_mem inclusion operator field⟩ = operator field := by
  have hGraph := (closedFeatureOperator inclusion operator).mem_graph
    ⟨inclusion field, closedFeatureOperator_smooth_mem inclusion operator field⟩
  rw [closedFeatureOperator_graph inclusion operator hSingle] at hGraph
  exact congrArg (fun graph => graph.val.2)
    (hSingle (a₁ := ⟨_, hGraph⟩) (a₂ := ⟨(inclusion field, operator field),
      (inclusion.prod operator).range.le_topologicalClosure ⟨field, rfl⟩⟩) rfl)

theorem closedFeatureOperator_dense_domain (hDense : DenseRange inclusion) :
    Dense ((closedFeatureOperator inclusion operator).domain : Set H) :=
  hDense.mono (by rintro _ ⟨field, rfl⟩; exact closedFeatureOperator_smooth_mem inclusion operator field)

/-- Every closed extension of the smooth action contains this operator. -/
theorem closedFeatureOperator_minimal
    (hSingle : Function.Injective
      (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1))
    (extension : H →ₗ.[Real] H) (hClosed : extension.IsClosed)
    (hExtends : ∀ field, (inclusion field, operator field) ∈ extension.graph) :
    closedFeatureOperator inclusion operator ≤ extension := by
  apply LinearPMap.le_of_le_graph
  rw [closedFeatureOperator_graph inclusion operator hSingle]
  exact closure_minimal (by rintro pair ⟨field, rfl⟩; exact hExtends field) hClosed

end
end JanusFormal.P0EFTJanusProgramPT12ClosedFeatureOperator4D
