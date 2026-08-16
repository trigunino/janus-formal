import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceHeatDuhamelFinitePartAssembly4D

/-!
# Reference finite-part assembly from nuclear Duhamel heat data

A standalone reference family can now be specified at the operator level:

* nuclear heat operators and their nuclear parameter derivatives;
* an operator-level Duhamel identity;
* nuclear Duhamel operators;
* short- and long-time logarithmically weighted integral differentiation;
* the local counterterm variation;
* the integrated identity with the logarithmic inverse trace.

This file converts that data into the scalar Duhamel finite-part assembly and
therefore into the complete standalone reference zeta coefficient.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPReferenceHeatDuhamelFinitePartAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Operator-level reference heat variation and its finite-part assembly. -/
structure ReferenceNuclearHeatFinitePartAssemblyData
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real) where
  nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  countertermContribution : Real → Real
  countertermDerivative : Real → Real
  hasDerivAt_counterterm : ∀ parameter,
    HasDerivAt countertermContribution (countertermDerivative parameter)
      parameter
  shortTime : NuclearHeatDuhamelWeightedIntegralData nuclear shortTimeRegion
  longTime : NuclearHeatDuhamelWeightedIntegralData nuclear longTimeRegion
  logDeterminant_eq : ∀ parameter,
    relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter +
        shortTime.toWeightedHeatTraceVariation.contribution parameter +
          longTime.toWeightedHeatTraceVariation.contribution parameter
  logarithmicTrace : Real → Real
  integratedDuhamel_eq_trace : ∀ parameter,
    countertermDerivative parameter -
        (∫ time in shortTimeRegion,
          extendedDuhamelTrace nuclear parameter time) -
        (∫ time in longTimeRegion,
          extendedDuhamelTrace nuclear parameter time) =
      logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceNuclearHeatFinitePartAssemblyData

/-- Convert operator-level nuclear heat data to the scalar Duhamel assembly. -/
def toDuhamelFinitePartAssembly
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion) :
    ReferenceHeatDuhamelFinitePartAssemblyData family shortTimeRegion
      longTimeRegion where
  countertermContribution := data.countertermContribution
  countertermDerivative := data.countertermDerivative
  hasDerivAt_counterterm := data.hasDerivAt_counterterm
  shortTime := data.shortTime.toDuhamelWeightedHeatTraceVariation
  longTime := data.longTime.toDuhamelWeightedHeatTraceVariation
  logDeterminant_eq := data.logDeterminant_eq
  logarithmicTrace := data.logarithmicTrace
  duhamel_integral_identity := data.integratedDuhamel_eq_trace
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- Direct finite-part variation from the nuclear heat family. -/
theorem hasDerivAt_finitePartLog
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
      (data.logarithmicTrace parameter) parameter :=
  data.toDuhamelFinitePartAssembly.hasDerivAt_finitePartLog parameter

/-- Standalone reference coefficient generated from nuclear Duhamel data. -/
theorem connectionCoefficient_eq_neg_trace
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.logarithmicTrace parameter : Complex) :=
  data.toDuhamelFinitePartAssembly.connectionCoefficient_eq_neg_trace parameter

/-- Public nuclear reference finite-part checkpoint. -/
theorem reference_nuclear_heat_finite_part_assembly_gate
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearHeatFinitePartAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion) :
    (∀ parameter time,
      HasDerivAt (fun current => data.nuclear.heatTrace current time)
        (-(time.1) * data.nuclear.duhamelTrace parameter time) parameter) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          relativeHeatFinitePartLogDeterminant
              (family.finitePartFamily.finitePart current))
        (data.logarithmicTrace parameter) parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) :=
  ⟨data.nuclear.heatTrace_hasDerivAt,
    data.hasDerivAt_finitePartLog,
    data.connectionCoefficient_eq_neg_trace⟩

end ReferenceNuclearHeatFinitePartAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartAssembly4D
end JanusFormal
