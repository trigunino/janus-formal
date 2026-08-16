import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenBoundaryMatching4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartOperatorAssembly4D

/-!
# Reference finite-part assembly from short/long boundary matching

The operator-level finite-part frontend still accepted the global equality

```text
(C - D_short) - D_long = G H'.
```

This file replaces it by the local time-splitting data

```text
C - D_short = G H' + B,
D_long       = B.
```

The common boundary operator cancels, producing the global operator equality,
the intrinsic trace identity, the derivative of the finite-part logarithm and
the standalone reference zeta coefficient.  The short- and long-time weighted
integral packets are taken directly from the corresponding operator-valued
Duhamel integral certificates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartBoundaryAssembly4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenBoundaryMatching4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartOperatorAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Complete reference packet built from two locally matched time regions. -/
structure ReferenceNuclearHeatFinitePartBoundaryAssemblyData
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real) where
  nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  countertermContribution : Real → Real
  boundaryMatching :
    ReferenceNuclearDuhamelGreenBoundaryMatchingData.{u, v} nuclear
      shortTimeRegion longTimeRegion
  hasDerivAt_counterterm : ∀ parameter,
    HasDerivAt countertermContribution
      (boundaryMatching.countertermDerivative parameter) parameter
  logDeterminant_eq : ∀ parameter,
    relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter +
        boundaryMatching.shortTime.weighted.toWeightedHeatTraceVariation.contribution
          parameter +
          boundaryMatching.longTime.weighted.toWeightedHeatTraceVariation.contribution
            parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceNuclearHeatFinitePartBoundaryAssemblyData

/-- Convert the local boundary matching data to the global operator-generated
finite-part frontend. -/
def toOperatorAssembly
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartBoundaryAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion) :
    ReferenceNuclearHeatFinitePartOperatorAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  operatorIdentity := data.boundaryMatching.toOperatorIdentity
  hasDerivAt_counterterm := data.hasDerivAt_counterterm
  shortTime := data.boundaryMatching.shortTime.weighted
  longTime := data.boundaryMatching.longTime.weighted
  logDeterminant_eq := data.logDeterminant_eq
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The finite-part logarithm differentiates to the trace of the logarithmic
Green derivative operator. -/
theorem hasDerivAt_finitePartLog
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartBoundaryAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
      (data.boundaryMatching.toOperatorIdentity.logarithmicTrace parameter)
      parameter :=
  data.toOperatorAssembly.hasDerivAt_finitePartLog parameter

/-- Standalone reference zeta coefficient generated from the two matched time
regions. -/
theorem connectionCoefficient_eq_neg_logarithmicTrace
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartBoundaryAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.boundaryMatching.toOperatorIdentity.logarithmicTrace parameter :
        Complex) :=
  data.toOperatorAssembly.connectionCoefficient_eq_neg_logarithmicTrace
    parameter

/-- Public boundary-generated finite-part checkpoint. -/
theorem reference_nuclear_heat_finite_part_boundary_assembly_gate
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearHeatFinitePartBoundaryAssemblyData.{u, v}
      (E := E) family shortTimeRegion longTimeRegion) :
    (∀ parameter,
      data.boundaryMatching.countertermOperator parameter -
          data.boundaryMatching.shortTime.integratedOperator parameter =
        data.boundaryMatching.logarithmicDerivativeOperator parameter +
          data.boundaryMatching.matchingOperator parameter) ∧
    (∀ parameter,
      data.boundaryMatching.longTime.integratedOperator parameter =
        data.boundaryMatching.matchingOperator parameter) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          relativeHeatFinitePartLogDeterminant
              (family.finitePartFamily.finitePart current))
        (data.boundaryMatching.toOperatorIdentity.logarithmicTrace parameter)
        parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.boundaryMatching.toOperatorIdentity.logarithmicTrace parameter :
          Complex)) :=
  ⟨data.boundaryMatching.shortBoundaryIdentity,
    data.boundaryMatching.longBoundaryIdentity,
    data.hasDerivAt_finitePartLog,
    data.connectionCoefficient_eq_neg_logarithmicTrace⟩

end ReferenceNuclearHeatFinitePartBoundaryAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartBoundaryAssembly4D
end JanusFormal
