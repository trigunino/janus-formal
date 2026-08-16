import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointAntilipschitzSurjective4D

/-!
# Self-adjoint operators with a global lower bound are onto

The anti-Lipschitz formulation used by the preceding Hilbert-space range gate
is exactly the bundled form of the standard operator estimate

`‖x‖ ≤ C ‖H x‖`.

This adapter makes the PDE-facing input explicit.  A single global lower bound
constructs the anti-Lipschitz certificate through Mathlib, while
self-adjointness supplies dense range.  Bijectivity and surjectivity then follow
without a separately supplied range theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointAntilipschitzSurjective4D

variable {E : Type*}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [CompleteSpace E]

/-- Convert the usual global lower-bound estimate into anti-Lipschitz control. -/
theorem continuousLinearMap_antilipschitz_of_globalLowerBound
    (operator : E →L[Real] E)
    (constant : NNReal)
    (hBound : ∀ vector : E,
      ‖vector‖ ≤ (constant : Real) * ‖operator vector‖) :
    AntilipschitzWith constant operator :=
  operator.antilipschitz_of_bound hBound

/-- A self-adjoint bounded operator satisfying the global lower bound is
bijective. -/
theorem selfAdjoint_bijective_of_globalLowerBound
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (constant : NNReal)
    (hBound : ∀ vector : E,
      ‖vector‖ ≤ (constant : Real) * ‖operator vector‖) :
    Function.Bijective operator :=
  selfAdjoint_bijective_of_antilipschitz operator hSelfAdjoint constant
    (continuousLinearMap_antilipschitz_of_globalLowerBound operator constant
      hBound)

/-- The range conclusion used by the shifted Candidate-A Hessian. -/
theorem selfAdjoint_surjective_of_globalLowerBound
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (constant : NNReal)
    (hBound : ∀ vector : E,
      ‖vector‖ ≤ (constant : Real) * ‖operator vector‖) :
    Function.Surjective operator :=
  (selfAdjoint_bijective_of_globalLowerBound operator hSelfAdjoint constant
    hBound).2

/-- Public PDE-facing range gate. -/
theorem self_adjoint_global_lower_bound_surjective_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (constant : NNReal)
    (hBound : ∀ vector : E,
      ‖vector‖ ≤ (constant : Real) * ‖operator vector‖) :
    Function.Bijective operator :=
  selfAdjoint_bijective_of_globalLowerBound operator hSelfAdjoint constant
    hBound

end
end P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D
end JanusFormal
