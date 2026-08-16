import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Self-adjoint anti-Lipschitz operators are onto

For a bounded self-adjoint endomorphism of a real Hilbert space, injectivity
forces dense range because the orthogonal complement of the range closure is
the kernel of the adjoint.  An anti-Lipschitz estimate supplies injectivity and
closed range.  Equivalently, Mathlib's Banach-space criterion upgrades dense
range plus anti-Lipschitz control directly to bijectivity.

This is the functional-analytic step needed by the terminal H12 shift: once
`H + P` is self-adjoint and bounded below, surjectivity is no longer an
independent premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointAntilipschitzSurjective4D

set_option autoImplicit false
noncomputable section

open Set

variable {E : Type*}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]
  [CompleteSpace E]

/-- An injective bounded self-adjoint endomorphism has dense range. -/
theorem selfAdjoint_denseRange_of_injective
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hInjective : Function.Injective operator) :
    (operator.toLinearMap.range).topologicalClosure = ⊤ := by
  have hKernel : operator.toLinearMap.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hInjective
  have hOrthogonal := ContinuousLinearMap.orthogonal_ker operator
  rw [hKernel, hSelfAdjoint.adjoint_eq] at hOrthogonal
  simpa using hOrthogonal.symm

/-- Anti-Lipschitz control makes a self-adjoint Hilbert endomorphism bijective. -/
theorem selfAdjoint_bijective_of_antilipschitz
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (constant : NNReal)
    (hAntilipschitz : AntilipschitzWith constant operator) :
    Function.Bijective operator := by
  have hDense : operator.toLinearMap.range.topologicalClosure = ⊤ :=
    selfAdjoint_denseRange_of_injective operator hSelfAdjoint
      hAntilipschitz.injective
  exact
    (ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz
      operator).2 ⟨hDense, ⟨constant, hAntilipschitz⟩⟩

/-- In particular, no separate range theorem is needed after self-adjointness
and the anti-Lipschitz estimate have been established. -/
theorem selfAdjoint_surjective_of_antilipschitz
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (constant : NNReal)
    (hAntilipschitz : AntilipschitzWith constant operator) :
    Function.Surjective operator :=
  (selfAdjoint_bijective_of_antilipschitz operator hSelfAdjoint constant
    hAntilipschitz).2

/-- Public checkpoint for the generic H12 range argument. -/
theorem self_adjoint_antilipschitz_surjective_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (constant : NNReal)
    (hAntilipschitz : AntilipschitzWith constant operator) :
    Function.Bijective operator :=
  selfAdjoint_bijective_of_antilipschitz operator hSelfAdjoint constant
    hAntilipschitz

end
end P0EFTJanusProgramPSelfAdjointAntilipschitzSurjective4D
end JanusFormal
