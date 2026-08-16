import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D

/-!
# Operator origin of the integrated Duhamel--Green trace identity

The preceding reference finite-part packet still accepted the scalar equality

```text
C'(a)
  - integral_short Tr(D_a(t)) dt
  - integral_long  Tr(D_a(t)) dt
    = Tr(G_a H'_a)
```

as one indivisible input.  This file replaces it by an operator identity.
The counterterm contribution, the two integrated Duhamel contributions and the
logarithmic derivative are represented by intrinsic nuclear operators.  The
only scalar bridges are the identifications of the counterterm derivative and
the two time integrals with the traces of their corresponding operators.

Trace additivity under subtraction and transport through the final operator
equality then force the displayed scalar formula.  In particular, equality of
the final scalar traces is no longer a separate premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelGreenOperatorIdentity4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
open P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Nuclear operator decomposition of the renormalized integrated Duhamel
identity.

The total operator is written with nested subtraction so that its intrinsic
trace follows from the already established binary subtraction theorem without
introducing a second notion of nuclear sum. -/
structure ReferenceNuclearDuhamelGreenOperatorIdentityData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (shortTimeRegion longTimeRegion : Set Real) where
  countertermOperator : Real → E →L[Real] E
  shortTimeDuhamelOperator : Real → E →L[Real] E
  longTimeDuhamelOperator : Real → E →L[Real] E
  logarithmicDerivativeOperator : Real → E →L[Real] E
  countertermTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (countertermOperator parameter)
  shortTimeTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (shortTimeDuhamelOperator parameter)
  countertermMinusShortTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v}
      (countertermOperator parameter - shortTimeDuhamelOperator parameter)
  longTimeTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (longTimeDuhamelOperator parameter)
  totalTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v}
      ((countertermOperator parameter - shortTimeDuhamelOperator parameter) -
        longTimeDuhamelOperator parameter)
  logarithmicDerivativeTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (logarithmicDerivativeOperator parameter)
  countertermDerivative : Real → Real
  countertermDerivative_eq_trace : ∀ parameter,
    countertermDerivative parameter =
      intrinsicNuclearTrace (countertermTraceClass parameter)
  shortTimeIntegral_eq_trace : ∀ parameter,
    (∫ time in shortTimeRegion,
      extendedDuhamelTrace nuclear parameter time) =
        intrinsicNuclearTrace (shortTimeTraceClass parameter)
  longTimeIntegral_eq_trace : ∀ parameter,
    (∫ time in longTimeRegion,
      extendedDuhamelTrace nuclear parameter time) =
        intrinsicNuclearTrace (longTimeTraceClass parameter)
  totalOperator_eq_logarithmicDerivative : ∀ parameter,
    ((countertermOperator parameter - shortTimeDuhamelOperator parameter) -
        longTimeDuhamelOperator parameter) =
      logarithmicDerivativeOperator parameter

namespace ReferenceNuclearDuhamelGreenOperatorIdentityData

/-- Intrinsic logarithmic trace represented by the final operator. -/
def logarithmicTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenOperatorIdentityData.{u, v} nuclear
      shortTimeRegion longTimeRegion)
    (parameter : Real) : Real :=
  intrinsicNuclearTrace (data.logarithmicDerivativeTraceClass parameter)

/-- Trace of the counterterm-minus-short-time operator. -/
theorem countertermMinusShort_trace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenOperatorIdentityData.{u, v} nuclear
      shortTimeRegion longTimeRegion)
    (parameter : Real) :
    intrinsicNuclearTrace (data.countertermMinusShortTraceClass parameter) =
      intrinsicNuclearTrace (data.countertermTraceClass parameter) -
        intrinsicNuclearTrace (data.shortTimeTraceClass parameter) :=
  intrinsicNuclearTrace_sub
    (data.countertermTraceClass parameter)
    (data.shortTimeTraceClass parameter)
    (data.countertermMinusShortTraceClass parameter)

/-- Trace of the full renormalized Duhamel operator. -/
theorem total_trace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenOperatorIdentityData.{u, v} nuclear
      shortTimeRegion longTimeRegion)
    (parameter : Real) :
    intrinsicNuclearTrace (data.totalTraceClass parameter) =
      intrinsicNuclearTrace
          (data.countertermMinusShortTraceClass parameter) -
        intrinsicNuclearTrace (data.longTimeTraceClass parameter) :=
  intrinsicNuclearTrace_sub
    (data.countertermMinusShortTraceClass parameter)
    (data.longTimeTraceClass parameter)
    (data.totalTraceClass parameter)

/-- The operator identity identifies the total intrinsic trace with the
logarithmic Green derivative trace. -/
theorem totalTrace_eq_logarithmicTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenOperatorIdentityData.{u, v} nuclear
      shortTimeRegion longTimeRegion)
    (parameter : Real) :
    intrinsicNuclearTrace (data.totalTraceClass parameter) =
      data.logarithmicTrace parameter := by
  let transported : IntrinsicNuclearTraceData.{u, v}
      (data.logarithmicDerivativeOperator parameter) :=
    P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator
      (data.totalTraceClass parameter)
      (data.totalOperator_eq_logarithmicDerivative parameter)
  calc
    intrinsicNuclearTrace (data.totalTraceClass parameter) =
        intrinsicNuclearTrace transported :=
      (P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator_intrinsicNuclearTrace
        (data.totalTraceClass parameter)
        (data.totalOperator_eq_logarithmicDerivative parameter)).symm
    _ = intrinsicNuclearTrace
        (data.logarithmicDerivativeTraceClass parameter) :=
      intrinsicNuclearTrace_unique transported
        (data.logarithmicDerivativeTraceClass parameter)
    _ = data.logarithmicTrace parameter := rfl

/-- The old scalar integrated Duhamel--Green identity is now a theorem. -/
theorem integratedDuhamel_eq_logarithmicTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenOperatorIdentityData.{u, v} nuclear
      shortTimeRegion longTimeRegion)
    (parameter : Real) :
    data.countertermDerivative parameter -
        (∫ time in shortTimeRegion,
          extendedDuhamelTrace nuclear parameter time) -
        (∫ time in longTimeRegion,
          extendedDuhamelTrace nuclear parameter time) =
      data.logarithmicTrace parameter := by
  rw [data.countertermDerivative_eq_trace parameter,
    data.shortTimeIntegral_eq_trace parameter,
    data.longTimeIntegral_eq_trace parameter]
  calc
    intrinsicNuclearTrace (data.countertermTraceClass parameter) -
          intrinsicNuclearTrace (data.shortTimeTraceClass parameter) -
        intrinsicNuclearTrace (data.longTimeTraceClass parameter) =
      intrinsicNuclearTrace
          (data.countertermMinusShortTraceClass parameter) -
        intrinsicNuclearTrace (data.longTimeTraceClass parameter) := by
      rw [data.countertermMinusShort_trace parameter]
    _ = intrinsicNuclearTrace (data.totalTraceClass parameter) :=
      (data.total_trace parameter).symm
    _ = data.logarithmicTrace parameter :=
      data.totalTrace_eq_logarithmicTrace parameter

/-- Public operator-level integrated Duhamel checkpoint. -/
theorem reference_nuclear_duhamel_green_operator_identity_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearDuhamelGreenOperatorIdentityData.{u, v} nuclear
      shortTimeRegion longTimeRegion) :
    (∀ parameter,
      ((data.countertermOperator parameter -
          data.shortTimeDuhamelOperator parameter) -
          data.longTimeDuhamelOperator parameter) =
        data.logarithmicDerivativeOperator parameter) ∧
    (∀ parameter,
      intrinsicNuclearTrace (data.totalTraceClass parameter) =
        data.logarithmicTrace parameter) ∧
    (∀ parameter,
      data.countertermDerivative parameter -
          (∫ time in shortTimeRegion,
            extendedDuhamelTrace nuclear parameter time) -
          (∫ time in longTimeRegion,
            extendedDuhamelTrace nuclear parameter time) =
        data.logarithmicTrace parameter) :=
  ⟨data.totalOperator_eq_logarithmicDerivative,
    data.totalTrace_eq_logarithmicTrace,
    data.integratedDuhamel_eq_logarithmicTrace⟩

end ReferenceNuclearDuhamelGreenOperatorIdentityData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelGreenOperatorIdentity4D
end JanusFormal
