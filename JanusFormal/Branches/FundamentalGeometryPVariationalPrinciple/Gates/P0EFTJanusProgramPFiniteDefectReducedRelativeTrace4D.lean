import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedRelativeHeat4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

/-!
# Relative heat trace series on the finite-defect complement

A norm-summable rank-one expansion of the actual-minus-reference heat
difference gives both compactness and an absolutely summable scalar trace
series at every positive time.

This file defines that series and reduces the next determinant step to trace
representation independence plus Mellin/zeta continuation.  It does not claim
those two results prematurely.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectReducedRelativeTrace4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectReducedRelativeHeat4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

local instance finiteDefectReducedRelativeTraceCompleteSpace
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    CompleteSpace data.projection.ker :=
  inferInstance

/-- Relative heat data strengthened to an explicit summable rank-one
presentation. -/
structure FiniteDefectReducedRelativeTraceData
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) where
  referenceOperator : data.projection.ker →L[Real] data.projection.ker
  reference_selfAdjoint : IsSelfAdjoint referenceOperator
  referenceGap : Real
  referenceGap_pos : 0 < referenceGap
  reference_lowerBound : ∀ vector,
    referenceGap * ‖vector‖ ≤ ‖referenceOperator vector‖
  relativeRankOneExpansion : ∀ time : HeatTime,
    SummableRankOneOperatorExpansion
      (finiteDefectReducedRelativeHeatDifference operator data referenceOperator
        time)

/-- Forget the trace presentation while retaining the valid compact relative
heat packet. -/
def FiniteDefectReducedRelativeTraceData.toRelativeHeatData
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedRelativeTraceData operator data) :
    FiniteDefectReducedRelativeHeatData operator data where
  referenceOperator := relative.referenceOperator
  reference_selfAdjoint := relative.reference_selfAdjoint
  referenceGap := relative.referenceGap
  referenceGap_pos := relative.referenceGap_pos
  reference_lowerBound := relative.reference_lowerBound
  relativeExpansion := fun time =>
    (relative.relativeRankOneExpansion time).toCompactExpansion

/-- Positive-time scalar trace series of the relative heat difference. -/
def finiteDefectReducedRelativeHeatTrace
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedRelativeTraceData operator data)
    (time : HeatTime) : Real :=
  (relative.relativeRankOneExpansion time).expansionTrace

/-- The relative heat difference is compact. -/
theorem FiniteDefectReducedRelativeTraceData.relativeHeat_compact
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedRelativeTraceData operator data)
    (time : HeatTime) :
    IsCompactOperator
      (finiteDefectReducedRelativeHeatDifference operator data
        relative.referenceOperator time) :=
  (relative.relativeRankOneExpansion time).operator_compact

/-- The explicit scalar trace family is summable at each positive time. -/
theorem FiniteDefectReducedRelativeTraceData.relativeTrace_summable
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedRelativeTraceData operator data)
    (time : HeatTime) :
    Summable (fun index =>
      (relative.relativeRankOneExpansion time).coefficient index *
        inner Real
          ((relative.relativeRankOneExpansion time).leftVector index)
          ((relative.relativeRankOneExpansion time).rightVector index)) :=
  (relative.relativeRankOneExpansion time).trace_summable

/-- The trace series converges to the declared relative heat trace. -/
theorem FiniteDefectReducedRelativeTraceData.hasSum_relativeHeatTrace
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedRelativeTraceData operator data)
    (time : HeatTime) :
    HasSum
      (fun index =>
        (relative.relativeRankOneExpansion time).coefficient index *
          inner Real
            ((relative.relativeRankOneExpansion time).leftVector index)
            ((relative.relativeRankOneExpansion time).rightVector index))
      (finiteDefectReducedRelativeHeatTrace operator data relative time) :=
  (relative.relativeRankOneExpansion time).hasSum_expansionTrace

/-- Public relative trace-series checkpoint. -/
theorem finite_defect_reduced_relative_trace_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedRelativeTraceData operator data) :
    (∀ time : HeatTime,
      IsCompactOperator
        (finiteDefectReducedRelativeHeatDifference operator data
          relative.referenceOperator time)) ∧
      (∀ time : HeatTime,
        Summable (fun index =>
          (relative.relativeRankOneExpansion time).coefficient index *
            inner Real
              ((relative.relativeRankOneExpansion time).leftVector index)
              ((relative.relativeRankOneExpansion time).rightVector index))) :=
  ⟨relative.relativeHeat_compact operator data,
    relative.relativeTrace_summable operator data⟩

end
end P0EFTJanusProgramPFiniteDefectReducedRelativeTrace4D
end JanusFormal
