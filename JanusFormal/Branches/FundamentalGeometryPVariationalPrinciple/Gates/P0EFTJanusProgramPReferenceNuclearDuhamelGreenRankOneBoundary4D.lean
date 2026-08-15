import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelRankOneIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenBoundaryMatching4D

/-!
# Reference boundary matching from rank-one Duhamel integrals

The short/long boundary packet accepted operator-valued Duhamel integrals whose
scalar trace identities were already proved.  This file supplies those
operators from common rank-one spectral expansions on the two time regions.

For each region, pointwise Duhamel operators and their integrated operator are
expressed in one time-independent spectral frame.  The equality

```text
integral Tr(D_a(t)) dt = Tr(D_region,a)
```

is generated from the rank-one expansion and the certified exchange of the
sum with the time integral.  The resulting operators then meet at the common
short/long boundary term.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelGreenRankOneBoundary4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelRankOneIntegral4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenBoundaryMatching4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Reference Green identity with rank-one constructions of both integrated
Duhamel operators. -/
structure ReferenceNuclearDuhamelGreenRankOneBoundaryData
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (shortTimeRegion longTimeRegion : Set Real) where
  countertermOperator : Real → E →L[Real] E
  countertermTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData (countertermOperator parameter)
  countertermDerivative : Real → Real
  countertermDerivative_eq_trace : ∀ parameter,
    countertermDerivative parameter =
      intrinsicNuclearTrace (countertermTraceClass parameter)
  shortTime : NuclearDuhamelRankOneIntegralData nuclear shortTimeRegion
  longTime : NuclearDuhamelRankOneIntegralData nuclear longTimeRegion
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

namespace ReferenceNuclearDuhamelGreenRankOneBoundaryData

/-- Convert the two rank-one integral packets to operator-valued boundary
matching. -/
def toBoundaryMatching
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenRankOneBoundaryData nuclear
      shortTimeRegion longTimeRegion) :
    ReferenceNuclearDuhamelGreenBoundaryMatchingData nuclear
      shortTimeRegion longTimeRegion where
  countertermOperator := data.countertermOperator
  countertermTraceClass := data.countertermTraceClass
  countertermDerivative := data.countertermDerivative
  countertermDerivative_eq_trace := data.countertermDerivative_eq_trace
  shortTime := data.shortTime.toOperatorIntegral
  longTime := data.longTime.toOperatorIntegral
  countertermMinusShortTraceClass := data.countertermMinusShortTraceClass
  totalTraceClass := data.totalTraceClass
  logarithmicDerivativeOperator := data.logarithmicDerivativeOperator
  logarithmicDerivativeTraceClass := data.logarithmicDerivativeTraceClass
  matchingOperator := data.matchingOperator
  shortBoundaryIdentity := data.shortBoundaryIdentity
  longBoundaryIdentity := data.longBoundaryIdentity

/-- Short-time scalar trace integration is derived from the spectral
expansion. -/
theorem shortTimeIntegral_eq_trace
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenRankOneBoundaryData nuclear
      shortTimeRegion longTimeRegion)
    (parameter : Real) :
    (∫ time in shortTimeRegion,
      nuclear.extendedDuhamelTrace parameter time) =
        intrinsicNuclearTrace (data.shortTime.integratedTraceClass parameter) :=
  data.shortTime.scalarIntegral_eq_intrinsicTrace parameter

/-- Long-time scalar trace integration is derived from the spectral
expansion. -/
theorem longTimeIntegral_eq_trace
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenRankOneBoundaryData nuclear
      shortTimeRegion longTimeRegion)
    (parameter : Real) :
    (∫ time in longTimeRegion,
      nuclear.extendedDuhamelTrace parameter time) =
        intrinsicNuclearTrace (data.longTime.integratedTraceClass parameter) :=
  data.longTime.scalarIntegral_eq_intrinsicTrace parameter

/-- The complete integrated Duhamel--Green trace identity follows from the two
rank-one expansions and boundary cancellation. -/
theorem integratedDuhamel_eq_logarithmicTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenRankOneBoundaryData nuclear
      shortTimeRegion longTimeRegion)
    (parameter : Real) :
    data.countertermDerivative parameter -
        (∫ time in shortTimeRegion,
          nuclear.extendedDuhamelTrace parameter time) -
        (∫ time in longTimeRegion,
          nuclear.extendedDuhamelTrace parameter time) =
      data.toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter :=
  data.toBoundaryMatching.integratedDuhamel_eq_logarithmicTrace parameter

/-- Public rank-one short/long boundary checkpoint. -/
theorem reference_nuclear_duhamel_green_rank_one_boundary_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearDuhamelGreenRankOneBoundaryData nuclear
      shortTimeRegion longTimeRegion) :
    (∀ parameter,
      (∫ time in shortTimeRegion,
        nuclear.extendedDuhamelTrace parameter time) =
          intrinsicNuclearTrace
            (data.shortTime.integratedTraceClass parameter)) ∧
    (∀ parameter,
      (∫ time in longTimeRegion,
        nuclear.extendedDuhamelTrace parameter time) =
          intrinsicNuclearTrace
            (data.longTime.integratedTraceClass parameter)) ∧
    (∀ parameter,
      data.countertermOperator parameter -
          data.shortTime.integratedOperator parameter =
        data.logarithmicDerivativeOperator parameter +
          data.matchingOperator parameter) ∧
    (∀ parameter,
      data.longTime.integratedOperator parameter =
        data.matchingOperator parameter) ∧
    (∀ parameter,
      data.countertermDerivative parameter -
          (∫ time in shortTimeRegion,
            nuclear.extendedDuhamelTrace parameter time) -
          (∫ time in longTimeRegion,
            nuclear.extendedDuhamelTrace parameter time) =
        data.toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter) :=
  ⟨data.shortTimeIntegral_eq_trace,
    data.longTimeIntegral_eq_trace,
    data.shortBoundaryIdentity,
    data.longBoundaryIdentity,
    data.integratedDuhamel_eq_logarithmicTrace⟩

end ReferenceNuclearDuhamelGreenRankOneBoundaryData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelGreenRankOneBoundary4D
end JanusFormal
