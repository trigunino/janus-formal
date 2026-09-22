import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-! Double adjunction recovers a closed real Hilbert graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedDoubleAdjoint4D
set_option autoImplicit false
noncomputable section
open Set Topology
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

theorem closedSubmodule_adjoint_adjoint (graph : Submodule Real (H × H))
    (hClosed : IsClosed (graph : Set (H × H))) : graph.adjoint.adjoint = graph := by
  apply le_antisymm
  · intro pair hPair
    let hilbertGraph : Submodule Real (WithLp 2 (H × H)) :=
      graph.comap (WithLp.linearEquiv 2 Real (H × H)).toLinearMap
    have hHilbertClosed : IsClosed (hilbertGraph : Set (WithLp 2 (H × H))) :=
      hClosed.preimage (WithLp.prod_continuous_ofLp 2 H H)
    have hDouble : WithLp.toLp 2 pair ∈ hilbertGraph.orthogonal.orthogonal := by
      rw [Submodule.mem_orthogonal]
      intro test hTest
      have hTestAdj : (-test.snd, test.fst) ∈ graph.adjoint := by
        rw [Submodule.mem_adjoint_iff]
        intro first second hGraph
        have h := (hilbertGraph.mem_orthogonal test).mp hTest
          (WithLp.toLp 2 (first, second)) hGraph
        change inner Real first test.fst + inner Real second test.snd = 0 at h
        simp only [inner_neg_right]
        linarith
      have h := (graph.adjoint.mem_adjoint_iff pair).mp hPair
        (-test.snd) test.fst hTestAdj
      simp only [inner_neg_left] at h
      change inner Real test.fst pair.1 + inner Real test.snd pair.2 = 0
      linarith
    rw [Submodule.orthogonal_orthogonal_eq_closure,
      hHilbertClosed.submodule_topologicalClosure_eq] at hDouble
    exact hDouble
  · intro pair hPair
    rw [Submodule.mem_adjoint_iff]
    intro first second hAdj
    have h := (graph.mem_adjoint_iff (first, second)).mp hAdj pair.1 pair.2 hPair
    rw [real_inner_comm pair.1 second, real_inner_comm pair.2 first]
    exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm

theorem closedOperator_adjoint_adjoint (operator : H →ₗ.[Real] H)
    (hClosed : operator.IsClosed) (hDense : Dense (operator.domain : Set H))
    (hAdjointDense : Dense (operator.adjoint.domain : Set H)) :
    operator.adjoint.adjoint = operator := by
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hAdjointDense,
    LinearPMap.adjoint_graph_eq_graph_adjoint hDense,
    closedSubmodule_adjoint_adjoint operator.graph hClosed]

end
end JanusFormal.P0EFTJanusProgramPT12ClosedDoubleAdjoint4D
