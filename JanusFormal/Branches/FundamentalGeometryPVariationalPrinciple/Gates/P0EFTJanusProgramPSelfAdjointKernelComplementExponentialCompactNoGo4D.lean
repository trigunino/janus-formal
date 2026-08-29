import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementExponential4D

/-!
# Compactness no-go for the actual-kernel exponential

The exact bounded exponential on `(ker H)ᗮ` is everywhere invertible.  If one
such exponential were compact, composing it with its bounded inverse would make
the identity compact and hence force `(ker H)ᗮ` to be finite-dimensional.

Thus, in an infinite-dimensional Candidate-A realization, the bounded Riesz
exponential cannot itself be the nuclear elliptic heat operator.  Heat traces,
zeta determinants and Quillen metrics require an unbounded compact-resolvent
realization or a relative trace-class comparison.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementExponentialCompactNoGo4D

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 1100000

noncomputable section

open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementExponential4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

local instance actualKernelExponentialNoGoCompleteSpace
    (operator : E →L[Real] E) :
    CompleteSpace (SelfAdjointKernelComplement operator) :=
  inferInstance

/-- Compactness of one actual-complement exponential forces finite dimension of
the genuine zero-mode complement. -/
theorem finiteDimensional_of_compact_selfAdjointKernelComplementExponential
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (time : Real)
    (hCompact : IsCompactOperator
      (selfAdjointKernelComplementExponential operator hSelfAdjoint time)) :
    FiniteDimensional Real (SelfAdjointKernelComplement operator) := by
  let forward :=
    selfAdjointKernelComplementExponential operator hSelfAdjoint time
  let backward :=
    selfAdjointKernelComplementExponential operator hSelfAdjoint (-time)
  have hComposition : IsCompactOperator (backward.comp forward) :=
    hCompact.clm_comp backward
  have hIdentity : backward.comp forward =
      ContinuousLinearMap.id Real (SelfAdjointKernelComplement operator) := by
    apply ContinuousLinearMap.ext
    intro vector
    have hMul := congrArg
      (fun map : SelfAdjointKernelComplement operator →L[Real]
          SelfAdjointKernelComplement operator => map vector)
      (selfAdjointKernelComplementExponential_neg_mul operator hSelfAdjoint time)
    simpa [forward, backward] using hMul
  rw [hIdentity] at hComposition
  have hId : IsCompactOperator
      (id : SelfAdjointKernelComplement operator →
        SelfAdjointKernelComplement operator) := by
    simpa using hComposition
  exact FiniteDimensional.of_isCompactOperator_id hId

/-- Infinite-dimensional actual complements have no compact bounded
exponential at any real time. -/
theorem selfAdjointKernelComplementExponential_not_compact_of_infinite
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (hInfinite : ¬ FiniteDimensional Real
      (SelfAdjointKernelComplement operator))
    (time : Real) :
    ¬ IsCompactOperator
      (selfAdjointKernelComplementExponential operator hSelfAdjoint time) := by
  intro hCompact
  exact hInfinite
    (finiteDimensional_of_compact_selfAdjointKernelComplementExponential
      operator hSelfAdjoint time hCompact)

/-- Public bounded-heat no-go checkpoint. -/
theorem self_adjoint_kernel_complement_bounded_heat_no_go_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (time : Real)
    (hCompact : IsCompactOperator
      (selfAdjointKernelComplementExponential operator hSelfAdjoint time)) :
    FiniteDimensional Real (SelfAdjointKernelComplement operator) :=
  finiteDimensional_of_compact_selfAdjointKernelComplementExponential operator
    hSelfAdjoint time hCompact

end
end P0EFTJanusProgramPSelfAdjointKernelComplementExponentialCompactNoGo4D
end JanusFormal
