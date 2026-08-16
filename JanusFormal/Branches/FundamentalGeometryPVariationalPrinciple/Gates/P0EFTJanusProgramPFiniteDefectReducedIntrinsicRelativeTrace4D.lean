import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedRelativeTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Intrinsic relative heat trace on the finite-defect complement

The presentation-level relative trace packet is strengthened by requiring the
rank-one trace uniqueness theorem at every positive time.  The resulting heat
trace is a canonical scalar function of the actual-minus-reference operator,
not of one chosen nuclear decomposition.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectReducedIntrinsicRelativeTrace4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectReducedRelativeHeat4D
open P0EFTJanusProgramPFiniteDefectReducedRelativeTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

local instance finiteDefectReducedIntrinsicRelativeTraceCompleteSpace
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    CompleteSpace data.projection.ker :=
  inferInstance

/-- Relative heat data whose nuclear trace is presentation-independent at each
positive time. -/
structure FiniteDefectReducedIntrinsicRelativeTraceData
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) where
  referenceOperator : data.projection.ker →L[Real] data.projection.ker
  reference_selfAdjoint : IsSelfAdjoint referenceOperator
  referenceGap : Real
  referenceGap_pos : 0 < referenceGap
  reference_lowerBound : ∀ vector,
    referenceGap * ‖vector‖ ≤ ‖referenceOperator vector‖
  relativeTraceClass : ∀ time : HeatTime,
    IntrinsicNuclearTraceData
      (finiteDefectReducedRelativeHeatDifference operator data referenceOperator
        time)

/-- Forget uniqueness while retaining one explicit trace presentation. -/
def FiniteDefectReducedIntrinsicRelativeTraceData.toRelativeTraceData
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedIntrinsicRelativeTraceData operator data) :
    FiniteDefectReducedRelativeTraceData operator data where
  referenceOperator := relative.referenceOperator
  reference_selfAdjoint := relative.reference_selfAdjoint
  referenceGap := relative.referenceGap
  referenceGap_pos := relative.referenceGap_pos
  reference_lowerBound := relative.reference_lowerBound
  relativeRankOneExpansion := fun time =>
    (relative.relativeTraceClass time).expansion

/-- Canonical positive-time relative heat trace. -/
def finiteDefectReducedIntrinsicRelativeHeatTrace
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedIntrinsicRelativeTraceData operator data)
    (time : HeatTime) : Real :=
  intrinsicNuclearTrace (relative.relativeTraceClass time)

/-- The old presentation-level trace obtained by forgetting uniqueness agrees
with the intrinsic scalar. -/
theorem finiteDefectReducedRelativeHeatTrace_toRelativeTraceData
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedIntrinsicRelativeTraceData operator data)
    (time : HeatTime) :
    finiteDefectReducedRelativeHeatTrace operator data
        (relative.toRelativeTraceData operator data) time =
      finiteDefectReducedIntrinsicRelativeHeatTrace operator data relative time :=
  rfl

/-- Every certified expansion of the same relative heat difference computes
exactly the canonical trace. -/
theorem FiniteDefectReducedIntrinsicRelativeTraceData.expansionTrace_eq
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedIntrinsicRelativeTraceData operator data)
    (time : HeatTime)
    (expansion : SummableRankOneOperatorExpansion
      (finiteDefectReducedRelativeHeatDifference operator data
        relative.referenceOperator time)) :
    expansion.expansionTrace =
      finiteDefectReducedIntrinsicRelativeHeatTrace operator data relative time :=
  (relative.relativeTraceClass time).expansionTrace_eq expansion

/-- Every positive-time relative heat difference is compact. -/
theorem FiniteDefectReducedIntrinsicRelativeTraceData.relativeHeat_compact
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedIntrinsicRelativeTraceData operator data)
    (time : HeatTime) :
    IsCompactOperator
      (finiteDefectReducedRelativeHeatDifference operator data
        relative.referenceOperator time) :=
  (relative.relativeTraceClass time).operator_compact

/-- Public intrinsic relative-trace checkpoint. -/
theorem finite_defect_reduced_intrinsic_relative_trace_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedIntrinsicRelativeTraceData operator data) :
    (∀ time : HeatTime,
      IsCompactOperator
        (finiteDefectReducedRelativeHeatDifference operator data
          relative.referenceOperator time)) ∧
      (∀ time : HeatTime,
        ∀ expansion : SummableRankOneOperatorExpansion
          (finiteDefectReducedRelativeHeatDifference operator data
            relative.referenceOperator time),
          expansion.expansionTrace =
            finiteDefectReducedIntrinsicRelativeHeatTrace operator data relative
              time) :=
  ⟨relative.relativeHeat_compact operator data,
    relative.expansionTrace_eq operator data⟩

end
end P0EFTJanusProgramPFiniteDefectReducedIntrinsicRelativeTrace4D
end JanusFormal
