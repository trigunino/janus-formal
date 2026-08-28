import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementRelativeTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Intrinsic relative heat trace on the actual kernel complement

The presentation-level relative trace on `(ker H)ᗮ` is strengthened by the
uniqueness theorem for its summable rank-one expansion at every positive time.
The resulting scalar trace depends only on the actual-minus-reference relative
heat operator, not on one chosen nuclear presentation.

This is the canonical trace input for finite-part, Mellin, zeta and Quillen
constructions based on the genuine Hessian kernel complement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementIntrinsicRelativeTrace4D

set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 1700000

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementRelativeHeat4D
open P0EFTJanusProgramPSelfAdjointKernelComplementRelativeTrace4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

local instance actualKernelIntrinsicRelativeTraceCompleteSpace
    (operator : E →L[Real] E) :
    CompleteSpace (SelfAdjointKernelComplement operator) :=
  inferInstance

/-- Relative heat data whose trace is intrinsic at every positive time. -/
structure SelfAdjointKernelComplementIntrinsicRelativeTraceData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  referenceOperator : SelfAdjointKernelComplement operator →L[Real]
    SelfAdjointKernelComplement operator
  reference_selfAdjoint : IsSelfAdjoint referenceOperator
  referenceGap : Real
  referenceGap_pos : 0 < referenceGap
  reference_lowerBound : ∀ vector,
    referenceGap * ‖vector‖ ≤ ‖referenceOperator vector‖
  relativeTraceClass : ∀ time : HeatTime,
    IntrinsicNuclearTraceData.{_, 0}
      (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
        referenceOperator time)

/-- Forget uniqueness while retaining the stored summable rank-one
presentation. -/
def SelfAdjointKernelComplementIntrinsicRelativeTraceData.toRelativeTraceData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementIntrinsicRelativeTraceData operator
      hSelfAdjoint) :
    SelfAdjointKernelComplementRelativeTraceData operator hSelfAdjoint where
  referenceOperator := relative.referenceOperator
  reference_selfAdjoint := relative.reference_selfAdjoint
  referenceGap := relative.referenceGap
  referenceGap_pos := relative.referenceGap_pos
  reference_lowerBound := relative.reference_lowerBound
  relativeRankOneExpansion := fun time =>
    (relative.relativeTraceClass time).expansion

/-- Canonical positive-time relative heat trace. -/
def selfAdjointKernelComplementIntrinsicRelativeHeatTrace
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementIntrinsicRelativeTraceData operator
      hSelfAdjoint)
    (time : HeatTime) : Real :=
  intrinsicNuclearTrace (relative.relativeTraceClass time)

/-- The presentation-level trace obtained by forgetting uniqueness agrees with
the intrinsic scalar. -/
theorem selfAdjointKernelComplementRelativeHeatTrace_toRelativeTraceData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementIntrinsicRelativeTraceData operator
      hSelfAdjoint)
    (time : HeatTime) :
    selfAdjointKernelComplementRelativeHeatTrace operator hSelfAdjoint
        (relative.toRelativeTraceData operator hSelfAdjoint) time =
      selfAdjointKernelComplementIntrinsicRelativeHeatTrace operator hSelfAdjoint
        relative time :=
  rfl

/-- Every certified rank-one expansion of the same relative heat difference
computes the canonical trace. -/
theorem SelfAdjointKernelComplementIntrinsicRelativeTraceData.expansionTrace_eq
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementIntrinsicRelativeTraceData operator
      hSelfAdjoint)
    (time : HeatTime)
    (expansion : SummableRankOneOperatorExpansion.{0, _}
      (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
        relative.referenceOperator time)) :
    expansion.expansionTrace =
      selfAdjointKernelComplementIntrinsicRelativeHeatTrace operator hSelfAdjoint
        relative time :=
  (relative.relativeTraceClass time).expansionTrace_eq expansion

/-- Every positive-time relative heat difference is compact. -/
theorem SelfAdjointKernelComplementIntrinsicRelativeTraceData.relativeHeat_compact
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementIntrinsicRelativeTraceData operator
      hSelfAdjoint)
    (time : HeatTime) :
    IsCompactOperator
      (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
        relative.referenceOperator time) :=
  (relative.relativeTraceClass time).operator_compact

/-- The stored expansion computes the intrinsic trace definitionally. -/
@[simp]
theorem SelfAdjointKernelComplementIntrinsicRelativeTraceData.storedTrace_eq
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementIntrinsicRelativeTraceData operator
      hSelfAdjoint)
    (time : HeatTime) :
    (relative.relativeTraceClass time).expansion.expansionTrace =
      selfAdjointKernelComplementIntrinsicRelativeHeatTrace operator hSelfAdjoint
        relative time :=
  rfl

/-- Public intrinsic actual-kernel relative-trace checkpoint. -/
theorem self_adjoint_kernel_complement_intrinsic_relative_trace_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementIntrinsicRelativeTraceData operator
      hSelfAdjoint) :
    (∀ time : HeatTime,
      IsCompactOperator
        (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
          relative.referenceOperator time)) ∧
      (∀ time : HeatTime,
        ∀ expansion : SummableRankOneOperatorExpansion.{0, _}
          (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
            relative.referenceOperator time),
          expansion.expansionTrace =
            selfAdjointKernelComplementIntrinsicRelativeHeatTrace operator
              hSelfAdjoint relative time) :=
  ⟨relative.relativeHeat_compact operator hSelfAdjoint,
    relative.expansionTrace_eq operator hSelfAdjoint⟩

end
end P0EFTJanusProgramPSelfAdjointKernelComplementIntrinsicRelativeTrace4D
end JanusFormal
