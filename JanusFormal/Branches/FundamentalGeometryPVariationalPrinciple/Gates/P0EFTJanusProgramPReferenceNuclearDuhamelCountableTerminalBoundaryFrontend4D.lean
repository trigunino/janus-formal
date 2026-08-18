import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceSmul4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelOperatorTerminalTailPrimitive4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRenormalizedNuclearDuhamelCountableRankOneBochnerFrontend4D

/-!
# Countable-short / terminal-tail operator-boundary frontend

This file joins the constructive short-time Bochner packet and the genuine
long-time terminal primitive to the signed operator-boundary assembly.  The
short integral, long boundary limit, difference trace, total trace and
logarithmic-derivative trace certificates are constructed outputs.

Two geometric identifications deliberately remain inputs: the terminal
Bochner integral is the previously certified long-time operator, and the local
signed operator equals the physical logarithmic derivative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelCountableTerminalBoundaryFrontend4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceExpansionUniqueness4D
open P0EFTJanusProgramPIntrinsicNuclearTraceSmul4D
open P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
open P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
open P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssembly4D
open P0EFTJanusProgramPReferenceNuclearDuhamelOperatorTerminalTailPrimitive4D
open P0EFTJanusProgramPRenormalizedNuclearDuhamelCountableRankOneBochnerFrontend4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

universe u v

variable {Index : Type*}
variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Minimal geometric input remaining after the constructive short and long
operator integrals have been supplied. -/
structure ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1)
    (longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))) where
  shortFrontend :
    RenormalizedNuclearDuhamelCountableRankOneBochnerFrontendData
      nuclear shortTime
  finitePartOperator : Real → E →L[Real] E
  finitePartTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (finitePartOperator parameter)
  finitePartDerivative_eq_trace : ∀ parameter,
    finitePartDerivative finiteCounterterm parameter =
      intrinsicNuclearTrace (finitePartTraceClass parameter)
  terminalTail : Real →
    ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E 1
  terminalIntegral_eq_longOperator : ∀ parameter,
    (terminalTail parameter).matchingOperator =
      longTime.integratedOperator parameter
  logarithmicDerivativeOperator : Real → E →L[Real] E
  shortBoundaryIdentity : ∀ parameter,
    (shortFrontend.toRenormalizedOperatorIntegral.integratedOperator parameter -
        finitePartOperator parameter) +
      (terminalTail parameter).matchingOperator =
        logarithmicDerivativeOperator parameter

namespace ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData

/-- The ambient uniqueness theorem already stored by the short rank-one
packet is reused for every derived presentation. -/
def traceUniqueness
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    NuclearRankOneTraceUniquenessData.{u, v} (E := E) :=
  (data.shortFrontend.rankOne parameter).traceUniqueness

/-- Difference trace certificate generated from the short and finite-part
presentations. -/
def shortMinusFinitePartTraceClass
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    IntrinsicNuclearTraceData.{u, v}
      (data.shortFrontend.toRenormalizedOperatorIntegral.integratedOperator
          parameter - data.finitePartOperator parameter) :=
  (data.traceUniqueness parameter).intrinsicTraceData
    ((data.shortFrontend.toRenormalizedOperatorIntegral.integratedTraceClass
      parameter).expansion.sub
        (data.finitePartTraceClass parameter).expansion)

/-- An intrinsic trace certificate for the algebraically equivalent
`(short - finitePart) - (-long)` presentation. -/
private def untransportedTotalTraceClass
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    IntrinsicNuclearTraceData.{u, v}
      ((data.shortFrontend.toRenormalizedOperatorIntegral.integratedOperator
          parameter - data.finitePartOperator parameter) -
        (-1 : Real) • longTime.integratedOperator parameter) :=
  (data.traceUniqueness parameter).intrinsicTraceData
    ((data.shortMinusFinitePartTraceClass parameter).expansion.sub
      ((longTime.integratedTraceClass parameter).expansion.smul (-1)))

/-- Total trace certificate generated by subtraction, scalar multiplication
and transport across the canonical additive identity. -/
def totalTraceClass
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    IntrinsicNuclearTraceData.{u, v}
      ((data.shortFrontend.toRenormalizedOperatorIntegral.integratedOperator
          parameter - data.finitePartOperator parameter) +
        longTime.integratedOperator parameter) :=
  IntrinsicNuclearTraceData.transportOperator
    (data.untransportedTotalTraceClass parameter) (by simp [sub_eq_add_neg])

/-- The long primitive identification and the physical short matching imply
the total operator identity without defining the physical operator by fiat. -/
theorem totalOperator_eq_logarithmicDerivative
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    (data.shortFrontend.toRenormalizedOperatorIntegral.integratedOperator
          parameter - data.finitePartOperator parameter) +
        longTime.integratedOperator parameter =
      data.logarithmicDerivativeOperator parameter := by
  rw [← data.terminalIntegral_eq_longOperator parameter]
  exact data.shortBoundaryIdentity parameter

/-- The logarithmic-derivative trace certificate is transported from the
constructed total trace along the genuine operator identity. -/
def logarithmicDerivativeTraceClass
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime longTime)
    (parameter : Real) :
    IntrinsicNuclearTraceData.{u, v}
      (data.logarithmicDerivativeOperator parameter) :=
  IntrinsicNuclearTraceData.transportOperator
    (data.totalTraceClass parameter)
    (data.totalOperator_eq_logarithmicDerivative parameter)

/-- Complete signed operator-boundary packet.  All analytic trace certificates
and both regional boundary packets are generated. -/
def toGreenBoundaryData
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    {longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real))}
    (data : ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime longTime) :
    ReferenceNuclearRenormalizedDuhamelGreenBoundaryData
      (atTop : Filter Real) nuclear finiteCounterterm shortTime longTime where
  finitePartOperator := data.finitePartOperator
  finitePartTraceClass := data.finitePartTraceClass
  finitePartDerivative_eq_trace := data.finitePartDerivative_eq_trace
  renormalizedShortTime :=
    data.shortFrontend.toRenormalizedOperatorIntegral
  shortMinusFinitePartTraceClass := data.shortMinusFinitePartTraceClass
  totalTraceClass := data.totalTraceClass
  logarithmicDerivativeOperator := data.logarithmicDerivativeOperator
  logarithmicDerivativeTraceClass := data.logarithmicDerivativeTraceClass
  matchingOperator := fun parameter ↦
    (data.terminalTail parameter).matchingOperator
  shortBoundaryIdentity := data.shortBoundaryIdentity
  longBoundaryLimit := fun parameter ↦
    (data.terminalTail parameter).toLongTimeBoundaryLimitOfEq
      (longTime.integratedOperator parameter)
      (data.terminalTail parameter).matchingOperator
      (data.terminalIntegral_eq_longOperator parameter) rfl

/-- Public joined-frontend checkpoint. -/
theorem reference_nuclear_duhamel_countable_terminal_boundary_frontend_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1)
    (longTime : NuclearDuhamelOperatorIntegralData.{u, v} nuclear
      (Set.Ioi (1 : Real)))
    (data : ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime longTime) :
    (∀ parameter,
      data.toGreenBoundaryData.renormalizedShortTime.integratedOperator
          parameter =
        ∫ time in Set.Ioo (0 : Real) 1,
          data.shortFrontend.operatorIntegrand parameter time) ∧
    (∀ parameter,
      longTime.integratedOperator parameter =
        data.toGreenBoundaryData.matchingOperator parameter) ∧
    (∀ parameter,
      ((data.toGreenBoundaryData.renormalizedShortTime.integratedOperator
          parameter - data.finitePartOperator parameter) +
        longTime.integratedOperator parameter) =
          data.logarithmicDerivativeOperator parameter) :=
  ⟨data.shortFrontend.integratedOperator_eq_bochnerIntegral,
    data.toGreenBoundaryData.longBoundaryIdentity,
    data.totalOperator_eq_logarithmicDerivative⟩

end ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelCountableTerminalBoundaryFrontend4D
end JanusFormal
