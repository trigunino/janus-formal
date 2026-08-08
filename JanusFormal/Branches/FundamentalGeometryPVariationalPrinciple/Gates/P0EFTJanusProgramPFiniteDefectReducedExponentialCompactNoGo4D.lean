import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedExponential4D

/-!
# No-go for compactness of the bounded reduced exponential

The bounded reduced Riesz operator has an everywhere invertible exponential.
A compact invertible operator on a Banach space forces the identity to be
compact and hence forces the space to be finite-dimensional.

Therefore the exact bounded exponential constructed for the reduced Hessian
cannot be the nuclear elliptic heat operator in an infinite-dimensional
realization.  Determinant and Quillen work must use the underlying unbounded
elliptic realization, or a relative/compact-resolvent construction, rather
than declaring the bounded Riesz exponential nuclear.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectReducedExponentialCompactNoGo4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectReducedExponential4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

local instance finiteDefectReducedExponentialNoGoCompleteSpace
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    CompleteSpace data.projection.ker :=
  inferInstance

/-- Compactness of one bounded reduced exponential forces finite dimension of
the exact zero-mode complement. -/
theorem finiteDimensional_of_compact_finiteDefectReducedExponential
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (time : Real)
    (hCompact : IsCompactOperator
      (finiteDefectReducedExponential operator data time)) :
    FiniteDimensional Real data.projection.ker := by
  let forward := finiteDefectReducedExponential operator data time
  let backward := finiteDefectReducedExponential operator data (-time)
  have hComposition : IsCompactOperator (backward.comp forward) :=
    hCompact.clm_comp backward
  have hIdentity : backward.comp forward =
      ContinuousLinearMap.id Real data.projection.ker := by
    apply ContinuousLinearMap.ext
    intro vector
    have hMul := congrArg
      (fun map : data.projection.ker →L[Real] data.projection.ker => map vector)
      (finiteDefectReducedExponential_neg_mul operator data time)
    simpa [forward, backward] using hMul
  rw [hIdentity] at hComposition
  have hId : IsCompactOperator (id : data.projection.ker →
      data.projection.ker) := by
    simpa using hComposition
  exact FiniteDimensional.of_isCompactOperator_id hId

/-- In a genuinely infinite-dimensional reduced realization, no bounded
reduced exponential is compact. -/
theorem finiteDefectReducedExponential_not_compact_of_not_finiteDimensional
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (hInfinite : ¬ FiniteDimensional Real data.projection.ker)
    (time : Real) :
    ¬ IsCompactOperator (finiteDefectReducedExponential operator data time) := by
  intro hCompact
  exact hInfinite
    (finiteDimensional_of_compact_finiteDefectReducedExponential operator data
      time hCompact)

/-- The same obstruction applies to any summable compact expansion, since such
an expansion would make the exponential compact. -/
theorem finite_defect_reduced_bounded_heat_no_go_gate
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (time : Real)
    (hCompact : IsCompactOperator
      (finiteDefectReducedExponential operator data time)) :
    FiniteDimensional Real data.projection.ker :=
  finiteDimensional_of_compact_finiteDefectReducedExponential operator data
    time hCompact

end
end P0EFTJanusProgramPFiniteDefectReducedExponentialCompactNoGo4D
end JanusFormal
