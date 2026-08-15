import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatIntegralVariation4D

/-!
# Assemble a reference finite-part variation from Duhamel traces

The differentiated short- and long-time determinant terms are now reduced to
negative integrals of their Duhamel traces.  One reference family is therefore
controlled by

```text
countertermDerivative(a)
  - integral_short D(a,t) dt
  - integral_long  D(a,t) dt.
```

The only global spectral identity needed at this layer is that this expression
is the logarithmic inverse trace `Tr(G_a H'_a)`.  Once supplied, the complete
finite-part derivative and standalone reference zeta coefficient follow.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceHeatDuhamelFinitePartAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D
open P0EFTJanusProgramPRelativeHeatIntegralVariation4D
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

/-- Counterterm and two Duhamel time regions for one standalone reference zeta
family. -/
structure ReferenceHeatDuhamelFinitePartAssemblyData
    (family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real) where
  countertermContribution : Real → Real
  countertermDerivative : Real → Real
  hasDerivAt_counterterm : ∀ parameter,
    HasDerivAt countertermContribution (countertermDerivative parameter)
      parameter
  shortTime : DuhamelWeightedHeatTraceVariationData shortTimeRegion
  longTime : DuhamelWeightedHeatTraceVariationData longTimeRegion
  logDeterminant_eq : ∀ parameter,
    P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter +
        shortTime.weighted.contribution parameter +
          longTime.weighted.contribution parameter
  logarithmicTrace : Real → Real
  duhamel_integral_identity : ∀ parameter,
    countertermDerivative parameter -
        (∫ time in shortTimeRegion, shortTime.duhamelTrace parameter time) -
          (∫ time in longTimeRegion, longTime.duhamelTrace parameter time) =
      logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceHeatDuhamelFinitePartAssemblyData

/-- Convert Duhamel weighted integrals into the generic differentiated-integral
assembly. -/
def toIntegralAssembly
    {family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFinitePartAssemblyData family shortTimeRegion
      longTimeRegion) :
    ReferenceHeatFinitePartIntegralAssemblyData family shortTimeRegion
      longTimeRegion where
  countertermContribution := data.countertermContribution
  countertermDerivative := data.countertermDerivative
  hasDerivAt_counterterm := data.hasDerivAt_counterterm
  shortTime := data.shortTime.weighted.toParametricIntegralVariation
  longTime := data.longTime.weighted.toParametricIntegralVariation
  logDeterminant_eq := data.logDeterminant_eq
  logarithmicTrace := data.logarithmicTrace
  integratedDerivative_eq_trace := by
    intro parameter
    rw [data.shortTime.derivativeContribution_eq_neg_integral_duhamelTrace,
      data.longTime.derivativeContribution_eq_neg_integral_duhamelTrace]
    exact data.duhamel_integral_identity parameter
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- Direct finite-part logarithm derivative from Duhamel. -/
theorem hasDerivAt_finitePartLog
    {family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFinitePartAssemblyData family shortTimeRegion
      longTimeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
      (data.logarithmicTrace parameter) parameter :=
  data.toIntegralAssembly.hasDerivAt_finitePartLog parameter

/-- Standalone reference zeta coefficient from Duhamel and the integrated trace
identity. -/
theorem connectionCoefficient_eq_neg_trace
    {family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFinitePartAssemblyData family shortTimeRegion
      longTimeRegion)
    (parameter : Real) :
    P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
        relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.logarithmicTrace parameter : Complex) :=
  data.toIntegralAssembly.connectionCoefficient_eq_neg_trace parameter

/-- The named finite-part derivative is the integrated Duhamel expression. -/
theorem namedLogDerivative_eq_duhamel
    {family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceHeatDuhamelFinitePartAssemblyData family shortTimeRegion
      longTimeRegion)
    (parameter : Real) :
    family.finitePartFamily.logDerivative parameter =
      data.countertermDerivative parameter -
        (∫ time in shortTimeRegion, data.shortTime.duhamelTrace parameter time) -
          (∫ time in longTimeRegion,
            data.longTime.duhamelTrace parameter time) := by
  calc
    family.finitePartFamily.logDerivative parameter =
        data.logarithmicTrace parameter :=
      data.toIntegralAssembly.toTermwiseTraceData.
        toReferenceFinitePartTraceVariation.finitePartLogDerivative_eq_trace
          parameter
    _ = data.countertermDerivative parameter -
        (∫ time in shortTimeRegion, data.shortTime.duhamelTrace parameter time) -
          (∫ time in longTimeRegion,
            data.longTime.duhamelTrace parameter time) :=
      (data.duhamel_integral_identity parameter).symm

/-- Public Duhamel finite-part assembly checkpoint. -/
theorem reference_heat_duhamel_finite_part_assembly_gate
    (family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceHeatDuhamelFinitePartAssemblyData family shortTimeRegion
      longTimeRegion) :
    (∀ parameter,
      HasDerivAt
        (fun current =>
          P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
            relativeHeatFinitePartLogDeterminant
              (family.finitePartFamily.finitePart current))
        (data.logarithmicTrace parameter) parameter) ∧
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter =
        data.countertermDerivative parameter -
          (∫ time in shortTimeRegion,
            data.shortTime.duhamelTrace parameter time) -
            (∫ time in longTimeRegion,
              data.longTime.duhamelTrace parameter time)) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) :=
  ⟨data.hasDerivAt_finitePartLog,
    data.namedLogDerivative_eq_duhamel,
    data.connectionCoefficient_eq_neg_trace⟩

end ReferenceHeatDuhamelFinitePartAssemblyData

end
end P0EFTJanusProgramPReferenceHeatDuhamelFinitePartAssembly4D
end JanusFormal
