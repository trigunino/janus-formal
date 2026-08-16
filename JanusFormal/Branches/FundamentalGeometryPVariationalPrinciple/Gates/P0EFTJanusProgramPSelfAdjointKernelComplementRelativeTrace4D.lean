import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementRelativeHeat4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

/-!
# Relative heat trace series on the actual kernel complement

A norm-summable rank-one expansion of the relative heat difference on
`(ker H)ᗮ` supplies both compactness and an absolutely summable scalar trace
series at every positive time.

The trace below is the trace of the explicit rank-one presentation.  Its
representation independence, small-time asymptotics and Mellin continuation
remain separate analytic statements; they are not consequences of bounded
Fredholm theory alone.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementRelativeTrace4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1500000

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementRelativeHeat4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

local instance actualKernelRelativeTraceCompleteSpace
    (operator : E →L[Real] E) :
    CompleteSpace (SelfAdjointKernelComplement operator) :=
  inferInstance

/-- Relative heat data strengthened to a summable rank-one presentation. -/
structure SelfAdjointKernelComplementRelativeTraceData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  referenceOperator : SelfAdjointKernelComplement operator →L[Real]
    SelfAdjointKernelComplement operator
  reference_selfAdjoint : IsSelfAdjoint referenceOperator
  referenceGap : Real
  referenceGap_pos : 0 < referenceGap
  reference_lowerBound : ∀ vector,
    referenceGap * ‖vector‖ ≤ ‖referenceOperator vector‖
  relativeRankOneExpansion : ∀ time : HeatTime,
    SummableRankOneOperatorExpansion
      (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
        referenceOperator time)

/-- Forget the rank-one trace presentation and retain compact relative heat. -/
def SelfAdjointKernelComplementRelativeTraceData.toRelativeHeatData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementRelativeTraceData operator
      hSelfAdjoint) :
    SelfAdjointKernelComplementRelativeHeatData operator hSelfAdjoint where
  referenceOperator := relative.referenceOperator
  reference_selfAdjoint := relative.reference_selfAdjoint
  referenceGap := relative.referenceGap
  referenceGap_pos := relative.referenceGap_pos
  reference_lowerBound := relative.reference_lowerBound
  relativeExpansion := fun time =>
    (relative.relativeRankOneExpansion time).toCompactExpansion

/-- Positive-time scalar trace series of the relative heat difference. -/
def selfAdjointKernelComplementRelativeHeatTrace
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementRelativeTraceData operator
      hSelfAdjoint)
    (time : HeatTime) : Real :=
  (relative.relativeRankOneExpansion time).expansionTrace

/-- The relative heat difference is compact. -/
theorem SelfAdjointKernelComplementRelativeTraceData.relativeHeat_compact
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementRelativeTraceData operator
      hSelfAdjoint)
    (time : HeatTime) :
    IsCompactOperator
      (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
        relative.referenceOperator time) :=
  (relative.relativeRankOneExpansion time).operator_compact

/-- The scalar trace series is absolutely summable at each positive time. -/
theorem SelfAdjointKernelComplementRelativeTraceData.relativeTrace_summable
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementRelativeTraceData operator
      hSelfAdjoint)
    (time : HeatTime) :
    Summable (fun index =>
      (relative.relativeRankOneExpansion time).coefficient index *
        inner Real
          ((relative.relativeRankOneExpansion time).leftVector index)
          ((relative.relativeRankOneExpansion time).rightVector index)) :=
  (relative.relativeRankOneExpansion time).trace_summable

/-- The explicit trace series has the declared relative heat trace as sum. -/
theorem SelfAdjointKernelComplementRelativeTraceData.hasSum_relativeHeatTrace
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementRelativeTraceData operator
      hSelfAdjoint)
    (time : HeatTime) :
    HasSum
      (fun index =>
        (relative.relativeRankOneExpansion time).coefficient index *
          inner Real
            ((relative.relativeRankOneExpansion time).leftVector index)
            ((relative.relativeRankOneExpansion time).rightVector index))
      (selfAdjointKernelComplementRelativeHeatTrace operator hSelfAdjoint
        relative time) :=
  (relative.relativeRankOneExpansion time).hasSum_expansionTrace

/-- Public actual-kernel relative-trace checkpoint. -/
theorem self_adjoint_kernel_complement_relative_trace_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (relative : SelfAdjointKernelComplementRelativeTraceData operator
      hSelfAdjoint) :
    (∀ time : HeatTime,
      IsCompactOperator
        (selfAdjointKernelComplementRelativeHeatDifference operator hSelfAdjoint
          relative.referenceOperator time)) ∧
      (∀ time : HeatTime,
        Summable (fun index =>
          (relative.relativeRankOneExpansion time).coefficient index *
            inner Real
              ((relative.relativeRankOneExpansion time).leftVector index)
              ((relative.relativeRankOneExpansion time).rightVector index))) :=
  ⟨relative.relativeHeat_compact operator hSelfAdjoint,
    relative.relativeTrace_summable operator hSelfAdjoint⟩

end
end P0EFTJanusProgramPSelfAdjointKernelComplementRelativeTrace4D
end JanusFormal
