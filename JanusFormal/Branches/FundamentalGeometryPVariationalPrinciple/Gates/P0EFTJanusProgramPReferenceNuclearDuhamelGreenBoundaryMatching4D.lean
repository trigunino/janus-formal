import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenOperatorIdentity4D

/-!
# Boundary matching for the reference Duhamel--Green identity

The global operator equality

```text
(C - D_short) - D_long = G H'
```

is naturally proved by cutting the time integral at one intermediate boundary.
The short-time renormalized piece leaves a matching operator `B`, while the
long-time integral is exactly the same `B`:

```text
C - D_short = G H' + B,
D_long       = B.
```

The boundary term cancels algebraically.  This file packages that local proof
shape and derives the global operator identity consumed by the finite-part
assembly.  Thus the remaining short- and long-time arguments may be proved
independently and meet only through one explicitly named boundary operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelGreenBoundaryMatching4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenOperatorIdentity4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Short/long operator matching data for one reference family. -/
structure ReferenceNuclearDuhamelGreenBoundaryMatchingData
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (shortTimeRegion longTimeRegion : Set Real) where
  countertermOperator : Real → E →L[Real] E
  countertermTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData (countertermOperator parameter)
  countertermDerivative : Real → Real
  countertermDerivative_eq_trace : ∀ parameter,
    countertermDerivative parameter =
      intrinsicNuclearTrace (countertermTraceClass parameter)
  shortTime : NuclearDuhamelOperatorIntegralData nuclear shortTimeRegion
  longTime : NuclearDuhamelOperatorIntegralData nuclear longTimeRegion
  countertermMinusShortTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData
      (countertermOperator parameter - shortTime.integratedOperator parameter)
  totalTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData
      ((countertermOperator parameter - shortTime.integratedOperator parameter) -
        longTime.integratedOperator parameter)
  logarithmicDerivativeOperator : Real → E →L[Real] E
  logarithmicDerivativeTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData (logarithmicDerivativeOperator parameter)
  matchingOperator : Real → E →L[Real] E
  shortBoundaryIdentity : ∀ parameter,
    countertermOperator parameter - shortTime.integratedOperator parameter =
      logarithmicDerivativeOperator parameter + matchingOperator parameter
  longBoundaryIdentity : ∀ parameter,
    longTime.integratedOperator parameter = matchingOperator parameter

namespace ReferenceNuclearDuhamelGreenBoundaryMatchingData

/-- Cancellation of the common boundary term gives the global operator
Duhamel--Green identity. -/
theorem totalOperator_eq_logarithmicDerivative
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenBoundaryMatchingData nuclear
      shortTimeRegion longTimeRegion)
    (parameter : Real) :
    ((data.countertermOperator parameter -
        data.shortTime.integratedOperator parameter) -
        data.longTime.integratedOperator parameter) =
      data.logarithmicDerivativeOperator parameter := by
  rw [data.shortBoundaryIdentity parameter,
    data.longBoundaryIdentity parameter]
  abel

/-- Convert the split-boundary proof to the global operator identity packet. -/
def toOperatorIdentity
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenBoundaryMatchingData nuclear
      shortTimeRegion longTimeRegion) :
    ReferenceNuclearDuhamelGreenOperatorIdentityData nuclear
      shortTimeRegion longTimeRegion where
  countertermOperator := data.countertermOperator
  shortTimeDuhamelOperator := data.shortTime.integratedOperator
  longTimeDuhamelOperator := data.longTime.integratedOperator
  logarithmicDerivativeOperator := data.logarithmicDerivativeOperator
  countertermTraceClass := data.countertermTraceClass
  shortTimeTraceClass := data.shortTime.integratedTraceClass
  countertermMinusShortTraceClass := data.countertermMinusShortTraceClass
  longTimeTraceClass := data.longTime.integratedTraceClass
  totalTraceClass := data.totalTraceClass
  logarithmicDerivativeTraceClass := data.logarithmicDerivativeTraceClass
  countertermDerivative := data.countertermDerivative
  countertermDerivative_eq_trace := data.countertermDerivative_eq_trace
  shortTimeIntegral_eq_trace := data.shortTime.scalarIntegral_eq_trace
  longTimeIntegral_eq_trace := data.longTime.scalarIntegral_eq_trace
  totalOperator_eq_logarithmicDerivative :=
    data.totalOperator_eq_logarithmicDerivative

/-- The renormalized integrated scalar identity follows from local boundary
matching. -/
theorem integratedDuhamel_eq_logarithmicTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenBoundaryMatchingData nuclear
      shortTimeRegion longTimeRegion)
    (parameter : Real) :
    data.countertermDerivative parameter -
        (∫ time in shortTimeRegion,
          nuclear.extendedDuhamelTrace parameter time) -
        (∫ time in longTimeRegion,
          nuclear.extendedDuhamelTrace parameter time) =
      data.toOperatorIdentity.logarithmicTrace parameter :=
  data.toOperatorIdentity.integratedDuhamel_eq_logarithmicTrace parameter

/-- Public short/long boundary-matching checkpoint. -/
theorem reference_nuclear_duhamel_green_boundary_matching_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearDuhamelGreenBoundaryMatchingData nuclear
      shortTimeRegion longTimeRegion) :
    (∀ parameter,
      data.countertermOperator parameter -
          data.shortTime.integratedOperator parameter =
        data.logarithmicDerivativeOperator parameter +
          data.matchingOperator parameter) ∧
    (∀ parameter,
      data.longTime.integratedOperator parameter =
        data.matchingOperator parameter) ∧
    (∀ parameter,
      ((data.countertermOperator parameter -
          data.shortTime.integratedOperator parameter) -
          data.longTime.integratedOperator parameter) =
        data.logarithmicDerivativeOperator parameter) ∧
    (∀ parameter,
      data.countertermDerivative parameter -
          (∫ time in shortTimeRegion,
            nuclear.extendedDuhamelTrace parameter time) -
          (∫ time in longTimeRegion,
            nuclear.extendedDuhamelTrace parameter time) =
        data.toOperatorIdentity.logarithmicTrace parameter) :=
  ⟨data.shortBoundaryIdentity,
    data.longBoundaryIdentity,
    data.totalOperator_eq_logarithmicDerivative,
    data.integratedDuhamel_eq_logarithmicTrace⟩

end ReferenceNuclearDuhamelGreenBoundaryMatchingData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelGreenBoundaryMatching4D
end JanusFormal
