import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleDiracHeatTraceCancellation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementExponentialCompactNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSummableCompactOperatorExpansion4D

/-!
# Relative heat input on the actual kernel complement

The bounded exponential of the actual reduced Hessian is invertible and hence
cannot be compact on a genuinely infinite-dimensional complement.  The correct
bounded comparison object is the relative difference

`exp (-t H_red) - exp (-t H_ref)`

for a self-adjoint gapped reference operator on the same genuine kernel
complement.

A norm-summable compact expansion of this difference at every positive time
makes relative compactness a theorem.  No finite defect projector or shifted
complement appears.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementRelativeHeat4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1500000

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementExponential4D
open P0EFTJanusProgramPSelfAdjointKernelComplementExponentialCompactNoGo4D
open P0EFTJanusProgramPSummableCompactOperatorExpansion4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

local instance actualKernelRelativeHeatCompleteSpace
    (operator : E →L[Real] E) :
    CompleteSpace (SelfAdjointKernelComplement operator) :=
  inferInstance

/-- Bounded exponential of a reference operator on the same actual complement. -/
noncomputable def selfAdjointKernelComplementReferenceExponential
    (operator : E →L[Real] E)
    (referenceOperator : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator)
    (time : HeatTime) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator :=
  NormedSpace.exp ((-time.1) • referenceOperator)

/-- Exact relative heat difference on `(ker H)ᗮ`. -/
def selfAdjointKernelComplementRelativeHeatDifference
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (referenceOperator : SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator)
    (time : HeatTime) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator :=
  selfAdjointKernelComplementExponential operator hSelfAdjoint time.1 -
    selfAdjointKernelComplementReferenceExponential operator referenceOperator
      time

/-- Minimal relative-heat analytic packet on the true zero-mode complement. -/
structure SelfAdjointKernelComplementRelativeHeatData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  referenceOperator : SelfAdjointKernelComplement operator →L[Real]
    SelfAdjointKernelComplement operator
  reference_selfAdjoint : IsSelfAdjoint referenceOperator
  referenceGap : Real
  referenceGap_pos : 0 < referenceGap
  reference_lowerBound : ∀ vector,
    referenceGap * ‖vector‖ ≤ ‖referenceOperator vector‖
  relativeExpansion : ∀ time : HeatTime,
    SummableCompactOperatorExpansion
      (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
        referenceOperator time)

/-- Relative heat is compact at every positive time. -/
theorem SelfAdjointKernelComplementRelativeHeatData.relativeHeat_compact
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementRelativeHeatData operator hSelfAdjoint)
    (time : HeatTime) :
    IsCompactOperator
      (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
        relative.referenceOperator time) :=
  (relative.relativeExpansion time).operator_compact

/-- Compactness of the absolute bounded exponential still forces finite
dimension, independently of the valid relative comparison. -/
theorem SelfAdjointKernelComplementRelativeHeatData.absoluteHeat_compact_implies_finiteDimensional
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (_relative : SelfAdjointKernelComplementRelativeHeatData operator hSelfAdjoint)
    (time : HeatTime)
    (hCompact : IsCompactOperator
      (selfAdjointKernelComplementExponential operator hSelfAdjoint time.1)) :
    FiniteDimensional Real (SelfAdjointKernelComplement operator) :=
  finiteDimensional_of_compact_selfAdjointKernelComplementExponential operator
    hSelfAdjoint time.1 hCompact

/-- Public actual-kernel relative-heat checkpoint. -/
theorem self_adjoint_kernel_complement_relative_heat_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementRelativeHeatData operator hSelfAdjoint) :
    (∀ time : HeatTime,
      IsCompactOperator
        (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
          relative.referenceOperator time)) ∧
      0 < relative.referenceGap ∧
      (∀ vector,
        relative.referenceGap * ‖vector‖ ≤
          ‖relative.referenceOperator vector‖) :=
  ⟨relative.relativeHeat_compact operator hSelfAdjoint,
    relative.referenceGap_pos,
    relative.reference_lowerBound⟩

end
end P0EFTJanusProgramPSelfAdjointKernelComplementRelativeHeat4D
end JanusFormal
