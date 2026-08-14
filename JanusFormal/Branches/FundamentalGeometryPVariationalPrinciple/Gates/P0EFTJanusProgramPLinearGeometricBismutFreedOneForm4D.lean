import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D

/-!
# Genuine continuous-linear geometric Bismut--Freed one-forms

The earlier geometric comparison interface used an arbitrary function
`Base → Tangent → Complex` and an arbitrary declared path velocity.  This file
replaces that weak interface on a normed parameter space by actual differential
objects:

* `oneForm b : Base →L[Real] Complex`;
* a path `gamma : Real → Base` whose stored velocity is its true derivative.

The operator comparison is now pointwise equality of two genuine one-forms:
the geometric complex covector and the complexification of the intrinsic real
trace covector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D

variable {Base E : Type*}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Genuine complex Bismut--Freed one-form on a real normed parameter space. -/
structure LinearGeometricBismutFreedOneFormData (Base : Type*)
    [NormedAddCommGroup Base] [NormedSpace Real Base] where
  oneForm : Base → Base →L[Real] Complex

/-- A differentiable real path in the parameter space, with its actual
velocity rather than an unrelated tangent field. -/
structure DifferentiableGeometricFamilyPathData (Base : Type*)
    [NormedAddCommGroup Base] [NormedSpace Real Base] where
  point : Real → Base
  velocity : Real → Base
  hasDerivAt_point : ∀ parameter,
    HasDerivAt point (velocity parameter) parameter

/-- Pullback coefficient of the genuine one-form along a differentiable path. -/
def pulledLinearGeometricCoefficient
    (geometry : LinearGeometricBismutFreedOneFormData Base)
    (path : DifferentiableGeometricFamilyPathData Base)
    (parameter : Real) : Complex :=
  geometry.oneForm (path.point parameter) (path.velocity parameter)

/-- Geometric one-form identified pointwise with the intrinsic operator-trace
Bismut--Freed covector. -/
structure LinearGeometricOperatorBismutFreedComparisonData
    (actual reference : Base → E →L[Real] E) where
  operatorTrace : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData
    actual reference
  geometry : LinearGeometricBismutFreedOneFormData Base
  oneForm_agreement : ∀ base direction,
    geometry.oneForm base direction =
      ((operatorTrace.bismutFreedRealOneForm base direction : Real) : Complex)

namespace LinearGeometricOperatorBismutFreedComparisonData

/-- The geometric covector is additive because it is an actual continuous
linear map. -/
theorem geometricOneForm_add
    {actual reference : Base → E →L[Real] E}
    (data : LinearGeometricOperatorBismutFreedComparisonData actual reference)
    (base first second : Base) :
    data.geometry.oneForm base (first + second) =
      data.geometry.oneForm base first + data.geometry.oneForm base second :=
  map_add _ _ _

/-- The geometric covector is real homogeneous. -/
theorem geometricOneForm_smul
    {actual reference : Base → E →L[Real] E}
    (data : LinearGeometricOperatorBismutFreedComparisonData actual reference)
    (base : Base) (scalar : Real) (direction : Base) :
    data.geometry.oneForm base (scalar • direction) =
      scalar • data.geometry.oneForm base direction :=
  map_smul _ _ _

/-- Pulling the geometric one-form along a differentiable path gives exactly
the directional intrinsic BF trace coefficient. -/
theorem pulledCoefficient_eq_operatorTrace
    {actual reference : Base → E →L[Real] E}
    (data : LinearGeometricOperatorBismutFreedComparisonData actual reference)
    (path : DifferentiableGeometricFamilyPathData Base)
    (parameter : Real) :
    pulledLinearGeometricCoefficient data.geometry path parameter =
      ((data.operatorTrace.bismutFreedRealOneForm
        (path.point parameter) (path.velocity parameter) : Real) : Complex) :=
  data.oneForm_agreement (path.point parameter) (path.velocity parameter)

/-- Public genuine-one-form comparison checkpoint. -/
theorem linear_geometric_operator_bismut_freed_comparison_gate
    (actual reference : Base → E →L[Real] E)
    (data : LinearGeometricOperatorBismutFreedComparisonData actual reference) :
    (∀ base direction,
      data.geometry.oneForm base direction =
        ((data.operatorTrace.bismutFreedRealOneForm base direction : Real) :
          Complex)) ∧
    (∀ base first second,
      data.geometry.oneForm base (first + second) =
        data.geometry.oneForm base first + data.geometry.oneForm base second) ∧
    (∀ base scalar direction,
      data.geometry.oneForm base (scalar • direction) =
        scalar • data.geometry.oneForm base direction) :=
  ⟨data.oneForm_agreement, data.geometricOneForm_add,
    data.geometricOneForm_smul⟩

end LinearGeometricOperatorBismutFreedComparisonData

end
end P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D
end JanusFormal
