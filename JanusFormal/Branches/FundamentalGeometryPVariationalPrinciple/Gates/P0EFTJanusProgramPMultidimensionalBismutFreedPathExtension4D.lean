import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D

/-!
# Multidimensional Bismut--Freed extension of an existing one-parameter family

The established Candidate-A determinant route is a genuine one-parameter
operator family.  A higher-dimensional families-index theorem must extend that
family, not silently replace it.

This file records the exact compatibility required of a multidimensional base
family:

* its actual and reference operators restrict to the existing path operators;
* their Frechet derivatives in the true path velocity restrict to the existing
  one-parameter derivatives;
* its intrinsic BF trace one-form evaluates on the path velocity to the
  established relative logarithmic trace coefficient.

The new geometric one-form then pulls back to exactly the old operator-defined
Bismut--Freed coefficient.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPMultidimensionalBismutFreedPathExtension4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D
open P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D
open P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D
open P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D

variable {Base E : Type*}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- A multidimensional differential BF/families-index package whose restriction
to one differentiable path is the already existing one-parameter operator
family and trace connection. -/
structure MultidimensionalBismutFreedPathExtensionData
    (pathActual pathReference : Real → E →L[Real] E)
    (baseActual baseReference : Base → E →L[Real] E) where
  pathTrace : RelativeIntrinsicLogarithmicDerivativeTraceData
    pathActual pathReference
  differential : DifferentialFamiliesIndexComparisonData
    baseActual baseReference
  path : DifferentiableGeometricFamilyPathData Base
  actual_operator_restriction : ∀ parameter,
    baseActual (path.point parameter) = pathActual parameter
  reference_operator_restriction : ∀ parameter,
    baseReference (path.point parameter) = pathReference parameter
  actual_derivative_restriction : ∀ parameter,
    differential.comparison.operator.trace.actualTrace.family.derivative
        (path.point parameter) (path.velocity parameter) =
      pathTrace.actualTrace.family.derivative parameter
  reference_derivative_restriction : ∀ parameter,
    differential.comparison.operator.trace.referenceTrace.family.derivative
        (path.point parameter) (path.velocity parameter) =
      pathTrace.referenceTrace.family.derivative parameter
  trace_one_form_restriction : ∀ parameter,
    differential.comparison.operator.trace.bismutFreedRealOneForm
        (path.point parameter) (path.velocity parameter) =
      -pathTrace.trace parameter

namespace MultidimensionalBismutFreedPathExtensionData

/-- The multidimensional geometric BF one-form pulls back to the exact existing
one-parameter operator-defined coefficient. -/
theorem geometric_path_coefficient_eq_existing
    {pathActual pathReference : Real → E →L[Real] E}
    {baseActual baseReference : Base → E →L[Real] E}
    (data : MultidimensionalBismutFreedPathExtensionData
      pathActual pathReference baseActual baseReference)
    (parameter : Real) :
    pulledLinearGeometricCoefficient
        data.differential.comparison.geometric.geometry data.path parameter =
      data.pathTrace.bismutFreedCoefficient parameter := by
  rw [data.differential.comparison.oneForm_agreement
    (data.path.point parameter) (data.path.velocity parameter)]
  rw [data.trace_one_form_restriction parameter]
  rfl

/-- The actual operator directional derivative on the extension restricts to
exactly the established path derivative. -/
theorem actual_directionalDerivative_eq_existing
    {pathActual pathReference : Real → E →L[Real] E}
    {baseActual baseReference : Base → E →L[Real] E}
    (data : MultidimensionalBismutFreedPathExtensionData
      pathActual pathReference baseActual baseReference)
    (parameter : Real) :
    data.differential.comparison.operator.trace.actualTrace.family.derivative
        (data.path.point parameter) (data.path.velocity parameter) =
      data.pathTrace.actualTrace.family.derivative parameter :=
  data.actual_derivative_restriction parameter

/-- Same restriction theorem for the reference family. -/
theorem reference_directionalDerivative_eq_existing
    {pathActual pathReference : Real → E →L[Real] E}
    {baseActual baseReference : Base → E →L[Real] E}
    (data : MultidimensionalBismutFreedPathExtensionData
      pathActual pathReference baseActual baseReference)
    (parameter : Real) :
    data.differential.comparison.operator.trace.referenceTrace.family.derivative
        (data.path.point parameter) (data.path.velocity parameter) =
      data.pathTrace.referenceTrace.family.derivative parameter :=
  data.reference_derivative_restriction parameter

/-- The multidimensional local families-index two-form is simultaneously the
curvature derived from the geometric one-form and the complexification of the
intrinsic operator trace curvature. -/
theorem localIndex_eq_operatorTraceCurvature
    {pathActual pathReference : Real → E →L[Real] E}
    {baseActual baseReference : Base → E →L[Real] E}
    (data : MultidimensionalBismutFreedPathExtensionData
      pathActual pathReference baseActual baseReference)
    (base first second : Base) :
    data.differential.localIndex.twoForm base first second =
      ((data.differential.comparison.operator.bismutFreedTraceCurvature
        base first second : Real) : Complex) :=
  data.differential.localIndex_eq_operatorTraceCurvature base first second

/-- Public extension checkpoint. -/
theorem multidimensional_bismut_freed_path_extension_gate
    (pathActual pathReference : Real → E →L[Real] E)
    (baseActual baseReference : Base → E →L[Real] E)
    (data : MultidimensionalBismutFreedPathExtensionData
      pathActual pathReference baseActual baseReference) :
    (∀ parameter,
      baseActual (data.path.point parameter) = pathActual parameter) ∧
    (∀ parameter,
      baseReference (data.path.point parameter) = pathReference parameter) ∧
    (∀ parameter,
      pulledLinearGeometricCoefficient
          data.differential.comparison.geometric.geometry data.path parameter =
        data.pathTrace.bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      data.differential.localIndex.twoForm base first second =
        ((data.differential.comparison.operator.bismutFreedTraceCurvature
          base first second : Real) : Complex)) :=
  ⟨data.actual_operator_restriction,
    data.reference_operator_restriction,
    data.geometric_path_coefficient_eq_existing,
    data.localIndex_eq_operatorTraceCurvature⟩

end MultidimensionalBismutFreedPathExtensionData

end
end P0EFTJanusProgramPMultidimensionalBismutFreedPathExtension4D
end JanusFormal
