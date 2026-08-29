import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatDataTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeNuclearTraceFamily4D

/-!
# From relative nuclear heat operators to analytic Mellin subtraction

This file links the operator-level identity

```text
K_rel(a,t) = K_actual(a,t) - K_reference(a,t)
```

to the family-level analytic Mellin comparison.  Intrinsic nuclear trace
additivity first gives equality of scalar heat traces.  Existing finite-part
and continuation packets are transported through the resulting function
equality, after which the common-domain analytic comparison yields all zeta and
connection subtraction formulas.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeNuclearMellinDifferenceFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatDataTransport4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifference4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeNuclearTraceFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Identify the scalar heat traces stored by three Mellin families with those
coming from one actual/reference/relative nuclear operator family. -/
structure RelativeNuclearMellinTraceIdentificationData
    (nuclear : RelativeNuclearTraceFamilyData
      (Parameter := Real) (Time := HeatTime) (E := E))
    (relative actual reference : RelativeHeatMellinZetaFamilyData) where
  relativeTrace_eq : ∀ parameter,
    relative.finitePartFamily.heatTrace parameter =
      nuclear.relativeTrace parameter
  actualTrace_eq : ∀ parameter,
    actual.finitePartFamily.heatTrace parameter =
      nuclear.actualTrace parameter
  referenceTrace_eq : ∀ parameter,
    reference.finitePartFamily.heatTrace parameter =
      nuclear.referenceTrace parameter

namespace RelativeNuclearMellinTraceIdentificationData

/-- Operator-level subtraction forces the exact heat-trace equality consumed
by the analytic Mellin difference packet. -/
theorem heatTrace_eq_difference
    {nuclear : RelativeNuclearTraceFamilyData
      (Parameter := Real) (Time := HeatTime) (E := E)}
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeNuclearMellinTraceIdentificationData nuclear relative actual
      reference)
    (parameter : Real) :
    relative.finitePartFamily.heatTrace parameter =
      heatTraceDifference
        (actual.finitePartFamily.heatTrace parameter)
        (reference.finitePartFamily.heatTrace parameter) := by
  calc
    relative.finitePartFamily.heatTrace parameter =
        nuclear.relativeTrace parameter := data.relativeTrace_eq parameter
    _ = heatTraceDifference (nuclear.actualTrace parameter)
        (nuclear.referenceTrace parameter) :=
      nuclear.relativeTrace_eq_difference_function parameter
    _ = heatTraceDifference
        (actual.finitePartFamily.heatTrace parameter)
        (reference.finitePartFamily.heatTrace parameter) := by
      rw [data.actualTrace_eq parameter, data.referenceTrace_eq parameter]

end RelativeNuclearMellinTraceIdentificationData

/-- Add the common-domain analytic comparison to the nuclear trace
identification. -/
structure RelativeNuclearMellinAnalyticDifferenceFamilyData
    (nuclear : RelativeNuclearTraceFamilyData
      (Parameter := Real) (Time := HeatTime) (E := E))
    (relative actual reference : RelativeHeatMellinZetaFamilyData) where
  traceIdentification :
    RelativeNuclearMellinTraceIdentificationData nuclear relative actual
      reference
  analyticDifference : ∀ parameter,
    RelativeHeatMellinAnalyticDifferenceData
      ((relative.continuation parameter).transportHeatTrace
        (traceIdentification.heatTrace_eq_difference parameter))
      (actual.continuation parameter)
      (reference.continuation parameter)

namespace RelativeNuclearMellinAnalyticDifferenceFamilyData

/-- Forget the nuclear presentations after deriving the exact scalar trace
identity. -/
def toAnalyticDifferenceFamily
    {nuclear : RelativeNuclearTraceFamilyData
      (Parameter := Real) (Time := HeatTime) (E := E)}
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeNuclearMellinAnalyticDifferenceFamilyData nuclear relative
      actual reference) :
    RelativeHeatMellinAnalyticDifferenceFamilyData relative actual reference where
  heatTrace_eq_difference := data.traceIdentification.heatTrace_eq_difference
  analyticDifference := data.analyticDifference

/-- Relative zeta derivative at zero is actual minus reference. -/
theorem zetaPrimeAtZero_eq_difference
    {nuclear : RelativeNuclearTraceFamilyData
      (Parameter := Real) (Time := HeatTime) (E := E)}
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeNuclearMellinAnalyticDifferenceFamilyData nuclear relative
      actual reference)
    (parameter : Real) :
    relative.zetaPrimeAtZero parameter =
      actual.zetaPrimeAtZero parameter - reference.zetaPrimeAtZero parameter :=
  data.toAnalyticDifferenceFamily.zetaPrimeAtZero_eq_difference parameter

/-- Relative connection coefficient is actual minus reference. -/
theorem connectionCoefficient_eq_difference
    {nuclear : RelativeNuclearTraceFamilyData
      (Parameter := Real) (Time := HeatTime) (E := E)}
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeNuclearMellinAnalyticDifferenceFamilyData nuclear relative
      actual reference)
    (parameter : Real) :
    relativeZetaConnectionCoefficient relative.toZetaFamily parameter =
      relativeZetaConnectionCoefficient actual.toZetaFamily parameter -
        relativeZetaConnectionCoefficient reference.toZetaFamily parameter :=
  data.toAnalyticDifferenceFamily.connectionCoefficient_eq_difference parameter

/-- Public nuclear-to-Mellin comparison checkpoint. -/
theorem relative_nuclear_mellin_difference_family_gate
    (nuclear : RelativeNuclearTraceFamilyData
      (Parameter := Real) (Time := HeatTime) (E := E))
    (relative actual reference : RelativeHeatMellinZetaFamilyData)
    (data : RelativeNuclearMellinAnalyticDifferenceFamilyData nuclear relative
      actual reference) :
    (∀ parameter,
      relative.finitePartFamily.heatTrace parameter =
        heatTraceDifference
          (actual.finitePartFamily.heatTrace parameter)
          (reference.finitePartFamily.heatTrace parameter)) ∧
    (∀ parameter,
      relative.zetaPrimeAtZero parameter =
        actual.zetaPrimeAtZero parameter - reference.zetaPrimeAtZero parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient relative.toZetaFamily parameter =
        relativeZetaConnectionCoefficient actual.toZetaFamily parameter -
          relativeZetaConnectionCoefficient reference.toZetaFamily parameter) :=
  ⟨data.traceIdentification.heatTrace_eq_difference,
    data.zetaPrimeAtZero_eq_difference,
    data.connectionCoefficient_eq_difference⟩

end RelativeNuclearMellinAnalyticDifferenceFamilyData

end
end P0EFTJanusProgramPRelativeNuclearMellinDifferenceFamily4D
end JanusFormal
