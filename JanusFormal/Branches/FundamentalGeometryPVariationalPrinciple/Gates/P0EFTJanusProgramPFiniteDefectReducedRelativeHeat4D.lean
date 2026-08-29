import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleDiracHeatTraceCancellation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedExponentialCompactNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSummableCompactOperatorExpansion4D

/-!
# Relative heat input on the finite-defect complement

The bounded reduced exponential itself is invertible and therefore cannot be
compact in an infinite-dimensional realization.  The correct bounded object
for determinant comparison is a *relative* heat difference.

This file fixes a self-adjoint, coercive reference operator on the same exact
zero-mode complement and asks for a norm-summable compact expansion of

`exp (-t H_red) - exp (-t H_ref)`

at every positive time.  Compactness of the relative heat difference is then a
theorem, not an extra field.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectReducedRelativeHeat4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectReducedExponential4D
open P0EFTJanusProgramPFiniteDefectReducedExponentialCompactNoGo4D
open P0EFTJanusProgramPSummableCompactOperatorExpansion4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

local instance finiteDefectReducedRelativeHeatCompleteSpace
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    CompleteSpace data.projection.ker :=
  inferInstance

/-- Bounded exponential of a reference operator on the same reduced space. -/
noncomputable def finiteDefectReducedReferenceExponential
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (referenceOperator : data.projection.ker →L[Real] data.projection.ker)
    (time : HeatTime) :
    data.projection.ker →L[Real] data.projection.ker :=
  NormedSpace.exp ((-time.1) • referenceOperator)

/-- Exact relative heat difference. -/
def finiteDefectReducedRelativeHeatDifference
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (referenceOperator : data.projection.ker →L[Real] data.projection.ker)
    (time : HeatTime) :
    data.projection.ker →L[Real] data.projection.ker :=
  finiteDefectReducedExponential operator data time.1 -
    finiteDefectReducedReferenceExponential operator data referenceOperator time

/-- Minimal determinant-level analytic packet on the bounded reduced space.
The reference operator has its own positive gap, while the actual-versus-
reference heat difference is given by an explicit nuclear-style compact
expansion. -/
structure FiniteDefectReducedRelativeHeatData
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) where
  referenceOperator : data.projection.ker →L[Real] data.projection.ker
  reference_selfAdjoint : IsSelfAdjoint referenceOperator
  referenceGap : Real
  referenceGap_pos : 0 < referenceGap
  reference_lowerBound : ∀ vector,
    referenceGap * ‖vector‖ ≤ ‖referenceOperator vector‖
  relativeExpansion : ∀ time : HeatTime,
    SummableCompactOperatorExpansion
      (finiteDefectReducedRelativeHeatDifference operator data referenceOperator
        time)

/-- The relative heat difference is compact at every positive time. -/
theorem FiniteDefectReducedRelativeHeatData.relativeHeat_compact
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedRelativeHeatData operator data)
    (time : HeatTime) :
    IsCompactOperator
      (finiteDefectReducedRelativeHeatDifference operator data
        relative.referenceOperator time) :=
  (relative.relativeExpansion time).operator_compact

/-- Absolute compactness of the actual bounded exponential still forces finite
dimension, independently of the valid relative heat expansion. -/
theorem FiniteDefectReducedRelativeHeatData.absoluteHeat_compact_implies_finiteDimensional
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (_relative : FiniteDefectReducedRelativeHeatData operator data)
    (time : HeatTime)
    (hCompact : IsCompactOperator
      (finiteDefectReducedExponential operator data time.1)) :
    FiniteDimensional Real data.projection.ker :=
  finiteDimensional_of_compact_finiteDefectReducedExponential operator data
    time.1 hCompact

/-- Public relative-heat checkpoint. -/
theorem finite_defect_reduced_relative_heat_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (relative : FiniteDefectReducedRelativeHeatData operator data) :
    (∀ time : HeatTime,
      IsCompactOperator
        (finiteDefectReducedRelativeHeatDifference operator data
          relative.referenceOperator time)) ∧
      0 < relative.referenceGap ∧
      (∀ vector,
        relative.referenceGap * ‖vector‖ ≤
          ‖relative.referenceOperator vector‖) :=
  ⟨relative.relativeHeat_compact operator data,
    relative.referenceGap_pos,
    relative.reference_lowerBound⟩

end
end P0EFTJanusProgramPFiniteDefectReducedRelativeHeat4D
end JanusFormal
