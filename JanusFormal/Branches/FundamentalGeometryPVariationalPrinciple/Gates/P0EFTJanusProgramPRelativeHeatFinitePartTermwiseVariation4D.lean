import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceFinitePartTraceVariation4D

/-!
# Termwise variation of a relative heat finite part

A finite-part logarithm is assembled from three analytically distinct pieces:

* the finite contribution of the short-time counterterm;
* the renormalized short-time integral;
* the long-time integral.

The derivative of the full logarithm should not be supplied as one opaque
premise.  This file isolates the three scalar families, their derivatives, and
the exact algebraic recombination.  The total derivative is then forced by the
ordinary sum rule.

The structure is deliberately independent of a particular choice of cutoff
notation.  A concrete finite-part construction only has to identify its three
existing terms with the displayed decomposition.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatFinitePartTermwiseVariation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPReferenceFinitePartTraceVariation4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D

/-- Three-term decomposition and differentiated contributions for one existing
finite-part family. -/
structure RelativeHeatFinitePartTermwiseVariationData
    (family : RelativeHeatFinitePartFamilyData) where
  countertermContribution : Real → Real
  shortTimeContribution : Real → Real
  longTimeContribution : Real → Real
  countertermDerivative : Real → Real
  shortTimeDerivative : Real → Real
  longTimeDerivative : Real → Real
  logDeterminant_eq : ∀ parameter,
    relativeHeatFinitePartLogDeterminant (family.finitePart parameter) =
      countertermContribution parameter +
        shortTimeContribution parameter + longTimeContribution parameter
  hasDerivAt_counterterm : ∀ parameter,
    HasDerivAt countertermContribution (countertermDerivative parameter)
      parameter
  hasDerivAt_shortTime : ∀ parameter,
    HasDerivAt shortTimeContribution (shortTimeDerivative parameter) parameter
  hasDerivAt_longTime : ∀ parameter,
    HasDerivAt longTimeContribution (longTimeDerivative parameter) parameter

namespace RelativeHeatFinitePartTermwiseVariationData

/-- Forced total derivative of the finite-part logarithm. -/
def totalDerivative
    {family : RelativeHeatFinitePartFamilyData}
    (data : RelativeHeatFinitePartTermwiseVariationData family)
    (parameter : Real) : Real :=
  data.countertermDerivative parameter +
    data.shortTimeDerivative parameter + data.longTimeDerivative parameter

/-- The three termwise derivative theorems imply the derivative of the full
finite-part logarithm. -/
theorem hasDerivAt_logDeterminant
    {family : RelativeHeatFinitePartFamilyData}
    (data : RelativeHeatFinitePartTermwiseVariationData family)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant (family.finitePart current))
      (data.totalDerivative parameter) parameter := by
  have hTerms :=
    ((data.hasDerivAt_counterterm parameter).add
      (data.hasDerivAt_shortTime parameter)).add
        (data.hasDerivAt_longTime parameter)
  convert hTerms using 1
  · funext current
    exact (data.logDeterminant_eq current).symm
  · rfl

/-- The derivative already stored in `RelativeHeatFinitePartFamilyData` is
therefore the termwise total derivative. -/
theorem namedLogDerivative_eq_totalDerivative
    {family : RelativeHeatFinitePartFamilyData}
    (data : RelativeHeatFinitePartTermwiseVariationData family)
    (parameter : Real) :
    family.logDerivative parameter = data.totalDerivative parameter :=
  (family.hasDerivAt_logDeterminant parameter).unique
    (data.hasDerivAt_logDeterminant parameter)

/-- Public termwise finite-part variation checkpoint. -/
theorem relative_heat_finite_part_termwise_variation_gate
    (family : RelativeHeatFinitePartFamilyData)
    (data : RelativeHeatFinitePartTermwiseVariationData family) :
    (∀ parameter,
      HasDerivAt
        (fun current =>
          relativeHeatFinitePartLogDeterminant (family.finitePart current))
        (data.totalDerivative parameter) parameter) ∧
    (∀ parameter,
      family.logDerivative parameter = data.totalDerivative parameter) :=
  ⟨data.hasDerivAt_logDeterminant,
    data.namedLogDerivative_eq_totalDerivative⟩

end RelativeHeatFinitePartTermwiseVariationData

/-- A termwise variation whose total derivative is the geometric logarithmic
operator trace. -/
structure ReferenceHeatFinitePartTermwiseTraceData
    (family : RelativeHeatMellinZetaFamilyData) where
  termwise : RelativeHeatFinitePartTermwiseVariationData
    family.finitePartFamily
  logarithmicTrace : Real → Real
  totalDerivative_eq_trace : ∀ parameter,
    termwise.totalDerivative parameter = logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceHeatFinitePartTermwiseTraceData

/-- Termwise heat variation constructs the direct reference finite-part trace
variation packet. -/
def toReferenceFinitePartTraceVariation
    {family : RelativeHeatMellinZetaFamilyData}
    (data : ReferenceHeatFinitePartTermwiseTraceData family) :
    ReferenceFinitePartTraceVariationData family where
  logarithmicTrace := data.logarithmicTrace
  hasDerivAt_finitePartLog := by
    intro parameter
    rw [← data.totalDerivative_eq_trace parameter]
    exact data.termwise.hasDerivAt_logDeterminant parameter
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The standalone reference coefficient follows from the three termwise
variation theorems. -/
theorem connectionCoefficient_eq_neg_trace
    {family : RelativeHeatMellinZetaFamilyData}
    (data : ReferenceHeatFinitePartTermwiseTraceData family)
    (parameter : Real) :
    P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
        relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.logarithmicTrace parameter : Complex) :=
  data.toReferenceFinitePartTraceVariation.connectionCoefficient_eq_neg_trace
    parameter

/-- Public termwise reference-trace checkpoint. -/
theorem reference_heat_finite_part_termwise_trace_gate
    (family : RelativeHeatMellinZetaFamilyData)
    (data : ReferenceHeatFinitePartTermwiseTraceData family) :
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter =
        data.logarithmicTrace parameter) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) :=
  ⟨fun parameter => by
      rw [data.termwise.namedLogDerivative_eq_totalDerivative parameter,
        data.totalDerivative_eq_trace parameter],
    data.connectionCoefficient_eq_neg_trace⟩

end ReferenceHeatFinitePartTermwiseTraceData

end
end P0EFTJanusProgramPRelativeHeatFinitePartTermwiseVariation4D
end JanusFormal
