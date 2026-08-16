import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D

/-!
# Differential operator/geometric Bismut--Freed comparison

Both sides of the multidimensional comparison now carry actual differentiable
one-forms:

* the operator side is the intrinsic nuclear trace covector
  `-Tr(G_b DH_b[·])`;
* the geometric side is a complex continuous-linear BF covector.

Once their values and first derivatives agree, equality of their curvatures is
a theorem.  The local families-index two-form is then compared with that
derived curvature; no independent BF curvature function is accepted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D
open P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D
open P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D
open P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D

variable {Base E : Type*}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Full differential comparison before applying the local families-index
formula.  The derivative agreement is the typed infinitesimal version of the
one-form comparison. -/
structure DifferentiableOperatorGeometricBismutFreedComparisonData
    (actual reference : Base → E →L[Real] E) where
  operator : DifferentiableRelativeIntrinsicTraceOneFormData actual reference
  geometric : DifferentiableLinearGeometricBismutFreedOneFormData Base
  oneForm_agreement : ∀ base direction,
    geometric.geometry.oneForm base direction =
      ((operator.trace.bismutFreedRealOneForm base direction : Real) : Complex)
  derivative_agreement : ∀ base first second,
    geometric.derivative base first second =
      ((operator.bismutFreedOneFormDerivative base first second : Real) : Complex)

namespace DifferentiableOperatorGeometricBismutFreedComparisonData

/-- Equality of the two derived curvatures.  The operator side is real for the
self-adjoint logarithmic-trace sector and is embedded canonically in `Complex`. -/
theorem curvature_eq_operatorTrace
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableOperatorGeometricBismutFreedComparisonData
      actual reference)
    (base first second : Base) :
    data.geometric.curvature base first second =
      ((data.operator.bismutFreedTraceCurvature base first second : Real) :
        Complex) := by
  unfold DifferentiableLinearGeometricBismutFreedOneFormData.curvature
    DifferentiableRelativeIntrinsicTraceOneFormData.bismutFreedTraceCurvature
  rw [data.derivative_agreement base first second,
    data.derivative_agreement base second first]
  norm_cast

/-- The geometric BF curvature is therefore antisymmetric without a supplied
antisymmetry premise. -/
theorem geometricCurvature_antisymm
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableOperatorGeometricBismutFreedComparisonData
      actual reference)
    (base first second : Base) :
    data.geometric.curvature base first second =
      -data.geometric.curvature base second first :=
  data.geometric.curvature_antisymm base first second

/-- Along any actual differentiable path, the geometric coefficient is the
intrinsic operator trace coefficient in the path velocity. -/
theorem pathCoefficient_eq_operatorTrace
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableOperatorGeometricBismutFreedComparisonData
      actual reference)
    (path : DifferentiableGeometricFamilyPathData Base)
    (parameter : Real) :
    pulledLinearGeometricCoefficient data.geometric.geometry path parameter =
      ((data.operator.trace.bismutFreedRealOneForm
        (path.point parameter) (path.velocity parameter) : Real) : Complex) :=
  data.oneForm_agreement (path.point parameter) (path.velocity parameter)

/-- Public differential operator/geometric BF comparison checkpoint. -/
theorem differentiable_operator_geometric_bismut_freed_comparison_gate
    (actual reference : Base → E →L[Real] E)
    (data : DifferentiableOperatorGeometricBismutFreedComparisonData
      actual reference) :
    (∀ base direction,
      data.geometric.geometry.oneForm base direction =
        ((data.operator.trace.bismutFreedRealOneForm base direction : Real) :
          Complex)) ∧
    (∀ base first second,
      data.geometric.curvature base first second =
        ((data.operator.bismutFreedTraceCurvature base first second : Real) :
          Complex)) ∧
    (∀ base first second,
      data.geometric.curvature base first second =
        -data.geometric.curvature base second first) :=
  ⟨data.oneForm_agreement, data.curvature_eq_operatorTrace,
    data.geometricCurvature_antisymm⟩

end DifferentiableOperatorGeometricBismutFreedComparisonData

/-- Final differential families-index comparison: the local index two-form is
identified with the BF curvature already derived from the connection one-form. -/
structure DifferentialFamiliesIndexComparisonData
    (actual reference : Base → E →L[Real] E) where
  comparison : DifferentiableOperatorGeometricBismutFreedComparisonData
    actual reference
  localIndex : LocalFamiliesIndexTwoFormData Base
  familiesIndex_agreement : ∀ base first second,
    comparison.geometric.curvature base first second =
      localIndex.twoForm base first second

namespace DifferentialFamiliesIndexComparisonData

/-- The local index two-form equals the intrinsic operator trace curvature. -/
theorem localIndex_eq_operatorTraceCurvature
    {actual reference : Base → E →L[Real] E}
    (data : DifferentialFamiliesIndexComparisonData actual reference)
    (base first second : Base) :
    data.localIndex.twoForm base first second =
      ((data.comparison.operator.bismutFreedTraceCurvature
        base first second : Real) : Complex) := by
  rw [← data.familiesIndex_agreement base first second]
  exact data.comparison.curvature_eq_operatorTrace base first second

/-- Public non-circular families-index checkpoint. -/
theorem differential_families_index_comparison_gate
    (actual reference : Base → E →L[Real] E)
    (data : DifferentialFamiliesIndexComparisonData actual reference) :
    (∀ base first second,
      data.comparison.geometric.curvature base first second =
        data.localIndex.twoForm base first second) ∧
    (∀ base first second,
      data.localIndex.twoForm base first second =
        ((data.comparison.operator.bismutFreedTraceCurvature
          base first second : Real) : Complex)) :=
  ⟨data.familiesIndex_agreement,
    data.localIndex_eq_operatorTraceCurvature⟩

end DifferentialFamiliesIndexComparisonData

end
end P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D
end JanusFormal
