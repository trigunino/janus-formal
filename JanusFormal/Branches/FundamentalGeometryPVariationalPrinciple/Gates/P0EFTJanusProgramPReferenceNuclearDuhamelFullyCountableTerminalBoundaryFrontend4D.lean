import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelCountableRankOneBochnerOperatorIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelCountableTerminalBoundaryFrontend4D

/-!
# Fully countable short/long terminal-boundary frontend

The long-time operator integral and the terminal primitive are now built from
the same operator-valued integrand.  Their matching operators are therefore
definitionally equal; no separate operator identification is required.

The physical short-boundary identity remains an explicit geometric input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearDuhamelCountableRankOneBochnerOperatorIntegral4D
open P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelCountableTerminalBoundaryFrontend4D
open P0EFTJanusProgramPReferenceNuclearDuhamelOperatorTerminalTailPrimitive4D
open P0EFTJanusProgramPRenormalizedNuclearDuhamelCountableRankOneBochnerFrontend4D

universe u v

variable {Index : Type*}
variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Short and long countable rank-one data together with the remaining
finite-part and physical operator matching inputs. -/
structure ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1) where
  shortFrontend :
    RenormalizedNuclearDuhamelCountableRankOneBochnerFrontendData
      nuclear shortTime
  longFrontend :
    NuclearDuhamelCountableRankOneBochnerOperatorIntegralData
      nuclear (Set.Ioi (1 : Real))
  longIntegrand_continuousOn : ∀ parameter,
    ContinuousOn (longFrontend.operatorIntegrand parameter)
      (Set.Ici (1 : Real))
  finitePartOperator : Real → E →L[Real] E
  finitePartTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (finitePartOperator parameter)
  finitePartDerivative_eq_trace : ∀ parameter,
    finitePartDerivative finiteCounterterm parameter =
      intrinsicNuclearTrace (finitePartTraceClass parameter)
  logarithmicDerivativeOperator : Real → E →L[Real] E
  shortBoundaryIdentity : ∀ parameter,
    (shortFrontend.toRenormalizedOperatorIntegral.integratedOperator parameter -
        finitePartOperator parameter) +
      longFrontend.integratedOperator parameter =
        logarithmicDerivativeOperator parameter

namespace ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData

/-- Terminal primitive made from the exact long-time Bochner integrand. -/
def terminalTail
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime)
    (parameter : Real) :
    ReferenceNuclearDuhamelOperatorTerminalTailPrimitiveData E 1 where
  integrand := data.longFrontend.operatorIntegrand parameter
  integrand_continuousOn := data.longIntegrand_continuousOn parameter
  integrableOn_tail := data.longFrontend.operatorIntegrable parameter

/-- Because both constructions use the same integrand and region, the
terminal matching operator is definitionally the generated long operator. -/
theorem terminalIntegral_eq_longOperator
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime)
    (parameter : Real) :
    (data.terminalTail parameter).matchingOperator =
      data.longFrontend.toNuclearDuhamelOperatorIntegral.integratedOperator
        parameter :=
  rfl

/-- Adapter to the preceding joined frontend; the former long-operator
identification field is filled by reflexivity. -/
def toCountableTerminalBoundaryFrontend
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime) :
    ReferenceNuclearDuhamelCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime
        data.longFrontend.toNuclearDuhamelOperatorIntegral where
  shortFrontend := data.shortFrontend
  finitePartOperator := data.finitePartOperator
  finitePartTraceClass := data.finitePartTraceClass
  finitePartDerivative_eq_trace := data.finitePartDerivative_eq_trace
  terminalTail := data.terminalTail
  terminalIntegral_eq_longOperator := data.terminalIntegral_eq_longOperator
  logarithmicDerivativeOperator := data.logarithmicDerivativeOperator
  shortBoundaryIdentity := data.shortBoundaryIdentity

/-- Final Green-boundary packet with both regional operator integrals and all
derived nuclear trace certificates constructed. -/
def toGreenBoundaryData
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime) :=
  data.toCountableTerminalBoundaryFrontend.toGreenBoundaryData

/-- Public fully-countable terminal-boundary checkpoint. -/
theorem reference_nuclear_duhamel_fully_countable_terminal_boundary_frontend_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1)
    (data : ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime) :
    (∀ parameter,
      data.longFrontend.toNuclearDuhamelOperatorIntegral.integratedOperator
          parameter =
        ∫ time in Set.Ioi (1 : Real),
          data.longFrontend.operatorIntegrand parameter time) ∧
    (∀ parameter,
      (data.terminalTail parameter).matchingOperator =
        data.longFrontend.toNuclearDuhamelOperatorIntegral.integratedOperator
          parameter) ∧
    (∀ parameter,
      ((data.shortFrontend.toRenormalizedOperatorIntegral.integratedOperator
          parameter - data.finitePartOperator parameter) +
        data.longFrontend.toNuclearDuhamelOperatorIntegral.integratedOperator
          parameter) =
        data.logarithmicDerivativeOperator parameter) :=
  ⟨fun _ ↦ rfl, data.terminalIntegral_eq_longOperator,
    data.shortBoundaryIdentity⟩

end ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D
end JanusFormal
