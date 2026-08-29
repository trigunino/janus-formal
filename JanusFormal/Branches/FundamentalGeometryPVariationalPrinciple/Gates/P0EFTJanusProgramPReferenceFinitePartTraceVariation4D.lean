import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceZetaTraceCoefficient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-!
# Reference finite-part variation and logarithmic trace

The field `logDerivative` of a finite-part family is only a chosen name for the
actual derivative of its renormalized logarithm.  A geometric proof should
instead establish directly

```text
HasDerivAt (finitePartLogDeterminant) Tr(G H') a.
```

Uniqueness of derivatives then identifies the stored `logDerivative` with the
logarithmic operator trace.  Together with reality of `zeta'_a(0)`, this
constructs the standalone reference zeta coefficient packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceFinitePartTraceVariation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPReferenceZetaTraceCoefficient4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-- Direct finite-part variation theorem for one standalone reference family. -/
structure ReferenceFinitePartTraceVariationData
    (family : RelativeHeatMellinZetaFamilyData) where
  logarithmicTrace : Real → Real
  hasDerivAt_finitePartLog : ∀ parameter,
    HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart current))
      (logarithmicTrace parameter) parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceFinitePartTraceVariationData

/-- The named finite-part derivative is forced to equal the geometric
logarithmic trace. -/
theorem finitePartLogDerivative_eq_trace
    {family : RelativeHeatMellinZetaFamilyData}
    (data : ReferenceFinitePartTraceVariationData family)
    (parameter : Real) :
    family.finitePartFamily.logDerivative parameter =
      data.logarithmicTrace parameter := by
  exact (family.finitePartFamily.hasDerivAt_logDeterminant parameter).unique
    (data.hasDerivAt_finitePartLog parameter)

/-- Construct the preceding standalone reference coefficient packet. -/
def toReferenceZetaTraceCoefficient
    {family : RelativeHeatMellinZetaFamilyData}
    (data : ReferenceFinitePartTraceVariationData family) :
    ReferenceZetaTraceCoefficientData family where
  logarithmicTrace := data.logarithmicTrace
  finitePartLogDerivative_eq_trace :=
    data.finitePartLogDerivative_eq_trace
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- Standalone reference coefficient from the direct finite-part variation
proof. -/
theorem connectionCoefficient_eq_neg_trace
    {family : RelativeHeatMellinZetaFamilyData}
    (data : ReferenceFinitePartTraceVariationData family)
    (parameter : Real) :
    relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.logarithmicTrace parameter : Complex) :=
  data.toReferenceZetaTraceCoefficient.connectionCoefficient_eq_neg_trace
    parameter

/-- Public finite-part trace-variation checkpoint. -/
theorem reference_finite_part_trace_variation_gate
    (family : RelativeHeatMellinZetaFamilyData)
    (data : ReferenceFinitePartTraceVariationData family) :
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter =
        data.logarithmicTrace parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) :=
  ⟨data.finitePartLogDerivative_eq_trace,
    data.connectionCoefficient_eq_neg_trace⟩

end ReferenceFinitePartTraceVariationData

end
end P0EFTJanusProgramPReferenceFinitePartTraceVariation4D
end JanusFormal
