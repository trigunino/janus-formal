import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenOperatorIdentity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartAssembly4D

/-!
# Reference finite-part assembly from an operator Duhamel--Green identity

`ReferenceNuclearHeatFinitePartAssemblyData` already derives the standalone
reference zeta coefficient from nuclear heat variation, but its final
integrated Duhamel identity was still supplied as a scalar equality.

This stronger frontend replaces that field by
`ReferenceNuclearDuhamelGreenOperatorIdentityData`.  The latter represents the
counterterm, short-time, long-time and logarithmic derivative contributions by
intrinsic nuclear operators and proves the scalar equality from their operator
identity.

Consequently the only scalar-to-operator comparison fields left here are the
three natural integration bridges:

```text
counterterm derivative = nuclear trace of the counterterm operator,
short integral          = nuclear trace of the short-time operator,
long integral           = nuclear trace of the long-time operator.
```
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartOperatorAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenOperatorIdentity4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Complete standalone reference packet whose integrated spectral identity is
operator-generated. -/
structure ReferenceNuclearHeatFinitePartOperatorAssemblyData
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real) where
  nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  countertermContribution : Real → Real
  operatorIdentity : ReferenceNuclearDuhamelGreenOperatorIdentityData.{u, v}
    nuclear shortTimeRegion longTimeRegion
  hasDerivAt_counterterm : ∀ parameter,
    HasDerivAt countertermContribution
      (operatorIdentity.countertermDerivative parameter) parameter
  shortTime : NuclearHeatDuhamelWeightedIntegralData nuclear shortTimeRegion
  longTime : NuclearHeatDuhamelWeightedIntegralData nuclear longTimeRegion
  logDeterminant_eq : ∀ parameter,
    relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter +
        shortTime.toWeightedHeatTraceVariation.contribution parameter +
          longTime.toWeightedHeatTraceVariation.contribution parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceNuclearHeatFinitePartOperatorAssemblyData

/-- Forget the operator decomposition only after deriving its scalar integrated
identity. -/
def toNuclearHeatFinitePartAssembly
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartOperatorAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion) :
    ReferenceNuclearHeatFinitePartAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  countertermDerivative := data.operatorIdentity.countertermDerivative
  hasDerivAt_counterterm := data.hasDerivAt_counterterm
  shortTime := data.shortTime
  longTime := data.longTime
  logDeterminant_eq := data.logDeterminant_eq
  logarithmicTrace := data.operatorIdentity.logarithmicTrace
  integratedDuhamel_eq_trace :=
    data.operatorIdentity.integratedDuhamel_eq_logarithmicTrace
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The finite-part logarithmic derivative is the intrinsic trace of the final
logarithmic derivative operator. -/
theorem hasDerivAt_finitePartLog
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartOperatorAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
      (data.operatorIdentity.logarithmicTrace parameter) parameter :=
  data.toNuclearHeatFinitePartAssembly.hasDerivAt_finitePartLog parameter

/-- Standalone reference coefficient obtained from the final nuclear
logarithmic derivative operator. -/
theorem connectionCoefficient_eq_neg_logarithmicTrace
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartOperatorAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.operatorIdentity.logarithmicTrace parameter : Complex) :=
  data.toNuclearHeatFinitePartAssembly.connectionCoefficient_eq_neg_trace
    parameter

/-- Public operator-generated finite-part assembly checkpoint. -/
theorem reference_nuclear_heat_finite_part_operator_assembly_gate
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearHeatFinitePartOperatorAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion) :
    (∀ parameter,
      ((data.operatorIdentity.countertermOperator parameter -
          data.operatorIdentity.shortTimeDuhamelOperator parameter) -
          data.operatorIdentity.longTimeDuhamelOperator parameter) =
        data.operatorIdentity.logarithmicDerivativeOperator parameter) ∧
    (∀ parameter,
      data.operatorIdentity.countertermDerivative parameter -
          (∫ time in shortTimeRegion,
            extendedDuhamelTrace data.nuclear parameter time) -
          (∫ time in longTimeRegion,
            extendedDuhamelTrace data.nuclear parameter time) =
        data.operatorIdentity.logarithmicTrace parameter) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          relativeHeatFinitePartLogDeterminant
              (family.finitePartFamily.finitePart current))
        (data.operatorIdentity.logarithmicTrace parameter) parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.operatorIdentity.logarithmicTrace parameter : Complex)) :=
  ⟨data.operatorIdentity.totalOperator_eq_logarithmicDerivative,
    data.operatorIdentity.integratedDuhamel_eq_logarithmicTrace,
    data.hasDerivAt_finitePartLog,
    data.connectionCoefficient_eq_neg_logarithmicTrace⟩

end ReferenceNuclearHeatFinitePartOperatorAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartOperatorAssembly4D
end JanusFormal
