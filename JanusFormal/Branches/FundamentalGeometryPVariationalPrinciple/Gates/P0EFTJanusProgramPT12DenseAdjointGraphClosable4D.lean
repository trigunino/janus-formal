import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-! Single-valued closure from a dense formal-adjoint test domain. -/
namespace JanusFormal.P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
set_option autoImplicit false
noncomputable section
open Set Topology
variable {D H : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup H] [InnerProductSpace Real H]

def linearFeatureGraphClosure (inclusion operator : D →ₗ[Real] H) : Submodule Real (H × H) :=
  (inclusion.prod operator).range.topologicalClosure

theorem linearFeatureGraphClosure_pairing
    (inclusion operator : D →ₗ[Real] H) (adjoint : D → H)
    (hPairing : ∀ field test, inner Real (operator field) (inclusion test) =
      inner Real (inclusion field) (adjoint test))
    (graph : linearFeatureGraphClosure inclusion operator) (test : D) :
    inner Real graph.val.2 (inclusion test) = inner Real graph.val.1 (adjoint test) := by
  have hClosed : IsClosed {pair : H × H |
      inner Real pair.2 (inclusion test) = inner Real pair.1 (adjoint test)} := by
    apply isClosed_eq <;> fun_prop
  exact closure_minimal (by rintro pair ⟨field, rfl⟩; exact hPairing field test) hClosed graph.property

theorem linearFeatureGraphClosure_fst_injective
    (inclusion operator : D →ₗ[Real] H) (adjoint : D → H)
    (hDense : DenseRange inclusion)
    (hPairing : ∀ field test, inner Real (operator field) (inclusion test) =
      inner Real (inclusion field) (adjoint test)) :
    Function.Injective (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1) := by
  intro first second hEqual
  have hAll : (fun test : H => inner Real first.val.2 test) =
      (fun test : H => inner Real second.val.2 test) := by
    apply hDense.equalizer
    · fun_prop
    · fun_prop
    · funext test
      exact (linearFeatureGraphClosure_pairing inclusion operator adjoint hPairing first test).trans
        ((congrArg (fun field => inner Real field (adjoint test)) hEqual).trans
          (linearFeatureGraphClosure_pairing inclusion operator adjoint hPairing second test).symm)
  exact Subtype.ext (Prod.ext hEqual (ext_inner_right Real (congrFun hAll)))

end
end JanusFormal.P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
