import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceZero4D

/-!
# Intrinsic logarithmic trace for a zero-derivative family

If a differentiable uniformly invertible operator family has

```text
H'_a = 0
```

at every parameter, then its logarithmic derivative operator

```text
G_a H'_a
```

is the zero operator.  A single intrinsic nuclear-trace certificate for zero
therefore supplies the entire parameterized trace-class family.  The resulting
logarithmic trace is identically zero.

This is the fixed-coordinate situation produced by the unitary D11 frame.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPZeroLogarithmicDerivativeTrace4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceZero4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- One zero trace certificate generates the full logarithmic-trace packet for
a family whose displayed derivative vanishes identically. -/
def intrinsicLogarithmicDerivativeTraceOfZeroDerivative
    {operator : Real → E →L[Real] E}
    (family : DifferentiableSelfAdjointUniformGapFamilyData operator)
    (inverse : family.GreenDifferentiabilityData)
    (hDerivative : ∀ parameter, family.derivative parameter = 0)
    (zeroTrace : IntrinsicNuclearTraceData (0 : E →L[Real] E)) :
    IntrinsicLogarithmicDerivativeTraceData operator where
  family := family
  inverse := inverse
  traceClass := by
    intro parameter
    have hLogarithmic : family.logarithmicDerivativeOperator parameter = 0 := by
      rw [DifferentiableSelfAdjointUniformGapFamilyData.logarithmicDerivativeOperator,
        hDerivative parameter]
      simp
    rw [hLogarithmic]
    exact zeroTrace

/-- The actual logarithmic trace of a zero-derivative family is zero. -/
theorem intrinsicLogarithmicDerivativeTraceOfZeroDerivative_trace
    {operator : Real → E →L[Real] E}
    (family : DifferentiableSelfAdjointUniformGapFamilyData operator)
    (inverse : family.GreenDifferentiabilityData)
    (hDerivative : ∀ parameter, family.derivative parameter = 0)
    (zeroTrace : IntrinsicNuclearTraceData (0 : E →L[Real] E))
    (parameter : Real) :
    (intrinsicLogarithmicDerivativeTraceOfZeroDerivative family inverse
      hDerivative zeroTrace).trace parameter = 0 := by
  unfold IntrinsicLogarithmicDerivativeTraceData.trace
  apply intrinsicNuclearTrace_zero

/-- The logarithmic derivative operator itself is identically zero. -/
theorem logarithmicDerivativeOperator_eq_zero
    {operator : Real → E →L[Real] E}
    (family : DifferentiableSelfAdjointUniformGapFamilyData operator)
    (hDerivative : ∀ parameter, family.derivative parameter = 0)
    (parameter : Real) :
    family.logarithmicDerivativeOperator parameter = 0 := by
  rw [DifferentiableSelfAdjointUniformGapFamilyData.logarithmicDerivativeOperator,
    hDerivative parameter]
  simp

/-- Public zero-logarithmic-trace checkpoint. -/
theorem zero_logarithmic_derivative_trace_gate
    {operator : Real → E →L[Real] E}
    (family : DifferentiableSelfAdjointUniformGapFamilyData operator)
    (inverse : family.GreenDifferentiabilityData)
    (hDerivative : ∀ parameter, family.derivative parameter = 0)
    (zeroTrace : IntrinsicNuclearTraceData (0 : E →L[Real] E)) :
    (∀ parameter,
      family.logarithmicDerivativeOperator parameter = 0) ∧
    (∀ parameter,
      (intrinsicLogarithmicDerivativeTraceOfZeroDerivative family inverse
        hDerivative zeroTrace).trace parameter = 0) :=
  ⟨logarithmicDerivativeOperator_eq_zero family hDerivative,
    intrinsicLogarithmicDerivativeTraceOfZeroDerivative_trace family inverse
      hDerivative zeroTrace⟩

end
end P0EFTJanusProgramPZeroLogarithmicDerivativeTrace4D
end JanusFormal
