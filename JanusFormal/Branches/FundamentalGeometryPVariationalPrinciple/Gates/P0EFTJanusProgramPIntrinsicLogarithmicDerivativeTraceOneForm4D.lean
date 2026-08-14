import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFrechetDifferentiableSelfAdjointGreenBaseFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Intrinsic logarithmic trace one-forms on a multidimensional base

For a Frechet-differentiable uniformly invertible family `H_b`, every tangent
direction `v` produces the logarithmic derivative operator

`G_b DH_b[v]`.

Nuclearity in each direction is not enough to call its trace a one-form: one
must also prove linearity and continuity in `v`.  This file records that fact as
an actual continuous linear functional

`traceOneForm b : Base →L[Real] Real`

whose value agrees with the presentation-independent nuclear trace in every
direction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D

set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option synthInstance.maxHeartbeats 2300000
noncomputable section

open P0EFTJanusProgramPFrechetDifferentiableSelfAdjointGreenBaseFamily4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D

variable {Base E : Type*}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Multidimensional logarithmic trace with a genuine continuous-linear
one-form in the parameter tangent direction. -/
structure IntrinsicLogarithmicDerivativeTraceOneFormData
    (operator : Base → E →L[Real] E) where
  family : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator
  inverse : family.GreenFrechetDifferentiabilityData
  traceClass : ∀ base direction,
    IntrinsicNuclearTraceData
      (family.logarithmicDerivativeOperator base direction)
  traceOneForm : Base → Base →L[Real] Real
  traceOneForm_agreement : ∀ base direction,
    traceOneForm base direction =
      intrinsicNuclearTrace (traceClass base direction)

namespace IntrinsicLogarithmicDerivativeTraceOneFormData

/-- Intrinsic scalar trace in one tangent direction. -/
def directionalTrace
    {operator : Base → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceOneFormData operator)
    (base direction : Base) : Real :=
  intrinsicNuclearTrace (data.traceClass base direction)

/-- The continuous-linear one-form evaluates to the intrinsic directional
trace. -/
theorem traceOneForm_eq_directionalTrace
    {operator : Base → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceOneFormData operator)
    (base direction : Base) :
    data.traceOneForm base direction = data.directionalTrace base direction :=
  data.traceOneForm_agreement base direction

/-- Every certified nuclear expansion of `G_b DH_b[v]` computes the same
one-form value. -/
theorem expansionTrace_eq_oneForm
    {operator : Base → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceOneFormData operator)
    (base direction : Base)
    (expansion : SummableRankOneOperatorExpansion
      (data.family.logarithmicDerivativeOperator base direction)) :
    expansion.expansionTrace = data.traceOneForm base direction := by
  rw [data.traceOneForm_agreement base direction]
  exact (data.traceClass base direction).expansionTrace_eq expansion

/-- Every directional logarithmic derivative is compact. -/
theorem logarithmicDerivative_compact
    {operator : Base → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceOneFormData operator)
    (base direction : Base) :
    IsCompactOperator
      (data.family.logarithmicDerivativeOperator base direction) :=
  (data.traceClass base direction).operator_compact

/-- Linearity in the tangent direction is now a theorem inherited from the
actual continuous-linear one-form. -/
theorem directionalTrace_add
    {operator : Base → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceOneFormData operator)
    (base first second : Base) :
    data.directionalTrace base (first + second) =
      data.directionalTrace base first + data.directionalTrace base second := by
  rw [← data.traceOneForm_eq_directionalTrace base (first + second),
    map_add,
    data.traceOneForm_eq_directionalTrace base first,
    data.traceOneForm_eq_directionalTrace base second]

/-- Real homogeneity in the tangent direction. -/
theorem directionalTrace_smul
    {operator : Base → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceOneFormData operator)
    (base : Base) (scalar : Real) (direction : Base) :
    data.directionalTrace base (scalar • direction) =
      scalar * data.directionalTrace base direction := by
  rw [← data.traceOneForm_eq_directionalTrace base (scalar • direction),
    map_smul,
    data.traceOneForm_eq_directionalTrace base direction]
  rfl

/-- Public intrinsic trace-one-form checkpoint. -/
theorem intrinsic_logarithmic_derivative_trace_one_form_gate
    (operator : Base → E →L[Real] E)
    (data : IntrinsicLogarithmicDerivativeTraceOneFormData operator) :
    (∀ base direction,
      IsCompactOperator
        (data.family.logarithmicDerivativeOperator base direction)) ∧
    (∀ base direction,
      data.traceOneForm base direction = data.directionalTrace base direction) ∧
    (∀ base first second,
      data.directionalTrace base (first + second) =
        data.directionalTrace base first + data.directionalTrace base second) ∧
    (∀ base scalar direction,
      data.directionalTrace base (scalar • direction) =
        scalar * data.directionalTrace base direction) :=
  ⟨data.logarithmicDerivative_compact,
    data.traceOneForm_eq_directionalTrace,
    data.directionalTrace_add,
    data.directionalTrace_smul⟩

end IntrinsicLogarithmicDerivativeTraceOneFormData

/-- Relative actual-minus-reference trace one-form on one fixed reduced Hilbert
space. -/
structure RelativeIntrinsicLogarithmicDerivativeTraceOneFormData
    (actual reference : Base → E →L[Real] E) where
  actualTrace : IntrinsicLogarithmicDerivativeTraceOneFormData actual
  referenceTrace : IntrinsicLogarithmicDerivativeTraceOneFormData reference

namespace RelativeIntrinsicLogarithmicDerivativeTraceOneFormData

/-- Relative logarithmic trace as a genuine continuous linear one-form. -/
def traceOneForm
    {actual reference : Base → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData actual reference)
    (base : Base) : Base →L[Real] Real :=
  data.actualTrace.traceOneForm base - data.referenceTrace.traceOneForm base

/-- Relative directional trace. -/
def directionalTrace
    {actual reference : Base → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData actual reference)
    (base direction : Base) : Real :=
  data.actualTrace.directionalTrace base direction -
    data.referenceTrace.directionalTrace base direction

/-- The relative continuous-linear form evaluates to the relative intrinsic
trace. -/
theorem traceOneForm_eq_directionalTrace
    {actual reference : Base → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData actual reference)
    (base direction : Base) :
    data.traceOneForm base direction = data.directionalTrace base direction := by
  unfold traceOneForm directionalTrace
  rw [ContinuousLinearMap.sub_apply,
    data.actualTrace.traceOneForm_eq_directionalTrace,
    data.referenceTrace.traceOneForm_eq_directionalTrace]

/-- Real Bismut--Freed one-form in the zeta-prime sign convention. -/
def bismutFreedRealOneForm
    {actual reference : Base → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData actual reference)
    (base : Base) : Base →L[Real] Real :=
  -(data.traceOneForm base)

/-- Directional Bismut--Freed coefficient. -/
def bismutFreedDirectionalCoefficient
    {actual reference : Base → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData actual reference)
    (base direction : Base) : Real :=
  -data.directionalTrace base direction

@[simp]
theorem bismutFreedRealOneForm_apply
    {actual reference : Base → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData actual reference)
    (base direction : Base) :
    data.bismutFreedRealOneForm base direction =
      data.bismutFreedDirectionalCoefficient base direction := by
  unfold bismutFreedRealOneForm bismutFreedDirectionalCoefficient
  rw [ContinuousLinearMap.neg_apply,
    data.traceOneForm_eq_directionalTrace]

/-- Public relative BF one-form checkpoint. -/
theorem relative_intrinsic_logarithmic_derivative_trace_one_form_gate
    (actual reference : Base → E →L[Real] E)
    (data : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData actual reference) :
    (∀ base direction,
      data.traceOneForm base direction = data.directionalTrace base direction) ∧
    (∀ base direction,
      data.bismutFreedRealOneForm base direction =
        -data.directionalTrace base direction) :=
  ⟨data.traceOneForm_eq_directionalTrace,
    fun base direction => by
      rw [data.bismutFreedRealOneForm_apply]
      rfl⟩

end RelativeIntrinsicLogarithmicDerivativeTraceOneFormData

end
end P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D
end JanusFormal
