import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FiniteObservationEstimate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureOperator4D

/-! Transfer genuine smooth estimates through graph closure, not through L2 density alone. -/
namespace JanusFormal.P0EFTJanusProgramPT12GraphClosureEstimate4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusProgramPT12FiniteObservationEstimate4D
variable {D H F : Type*} [AddCommGroup D] [Module Real D]
variable [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable [NormedAddCommGroup F] [NormedSpace Real F]
variable (inclusion operator : D →ₗ[Real] H)
variable (hSingle : Function.Injective
  (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1))
variable (observation : H →L[Real] F) (C : NNReal)
include hSingle

omit [CompleteSpace H] in
theorem closedFeatureOperator_estimate
    (hEstimate : ∀ field, ‖inclusion field‖ ≤ C * (‖operator field‖ + ‖observation (inclusion field)‖))
    (u : (closedFeatureOperator inclusion operator).domain) :
    ‖(u : H)‖ ≤ C * (‖closedFeatureOperator inclusion operator u‖ + ‖observation u‖) := by
  have hSet : IsClosed {pair : H × H | ‖pair.1‖ ≤ C * (‖pair.2‖ + ‖observation pair.1‖)} := by
    apply isClosed_le <;> fun_prop
  have hGraph := (closedFeatureOperator inclusion operator).mem_graph u
  rw [closedFeatureOperator_graph inclusion operator hSingle] at hGraph
  exact closure_minimal (by rintro pair ⟨field, rfl⟩; exact hEstimate field) hSet hGraph

theorem closedFeatureOperator_finite_observation [FiniteDimensional Real F]
    (hEstimate : ∀ field, ‖inclusion field‖ ≤ C * (‖operator field‖ + ‖observation (inclusion field)‖)) :
    IsClosed (LinearMap.range (closedFeatureOperator inclusion operator).toFun : Set H) ∧
      FiniteDimensional Real (LinearMap.ker (closedFeatureOperator inclusion operator).toFun) :=
  closedOperator_finite_observation _ (closedFeatureOperator_isClosed inclusion operator hSingle)
    observation C (closedFeatureOperator_estimate inclusion operator hSingle observation C hEstimate)

end
end JanusFormal.P0EFTJanusProgramPT12GraphClosureEstimate4D
