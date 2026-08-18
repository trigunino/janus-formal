import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenBoundaryMatching4D

/-!
# Fully countable frontend from a proved Green operator identity

The older Green packet uses `(C - S) - L = G`; the fully countable finite-part
frontend uses the opposite signed expression `(S - C) + L = -G`.  This
adapter performs only that algebraic change of convention.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelFullyCountableGreenOperatorIdentityAdapter4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearDuhamelCountableRankOneBochnerOperatorIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenOperatorIdentity4D
open P0EFTJanusProgramPRenormalizedNuclearDuhamelCountableRankOneBochnerFrontend4D

universe u v

variable {Index : Type*}
variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Compatibility data identifying the countable short/long integrals with
the corresponding operators in an already proved Green identity. -/
structure ReferenceNuclearDuhamelFullyCountableGreenOperatorIdentityAdapterData
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
  greenIdentity : ReferenceNuclearDuhamelGreenOperatorIdentityData.{u, v}
    nuclear (Set.Ioo (0 : Real) 1) (Set.Ioi (1 : Real))
  finitePartDerivative_eq_countertermDerivative : ∀ parameter,
    finitePartDerivative finiteCounterterm parameter =
      greenIdentity.countertermDerivative parameter
  shortOperator_eq : ∀ parameter,
    shortFrontend.toRenormalizedOperatorIntegral.integratedOperator parameter =
      greenIdentity.shortTimeDuhamelOperator parameter
  longOperator_eq : ∀ parameter,
    longFrontend.integratedOperator parameter =
      greenIdentity.longTimeDuhamelOperator parameter

namespace ReferenceNuclearDuhamelFullyCountableGreenOperatorIdentityAdapterData

/-- The required fully countable signed identity is the negative of the
already proved Green identity. -/
theorem signedOperatorIdentity
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : ReferenceNuclearDuhamelFullyCountableGreenOperatorIdentityAdapterData
      nuclear finiteCounterterm shortTime)
    (parameter : Real) :
    (data.shortFrontend.toRenormalizedOperatorIntegral.integratedOperator
          parameter - data.greenIdentity.countertermOperator parameter) +
        data.longFrontend.integratedOperator parameter =
      -data.greenIdentity.logarithmicDerivativeOperator parameter := by
  rw [data.shortOperator_eq parameter, data.longOperator_eq parameter]
  calc
    (data.greenIdentity.shortTimeDuhamelOperator parameter -
          data.greenIdentity.countertermOperator parameter) +
        data.greenIdentity.longTimeDuhamelOperator parameter =
      -((data.greenIdentity.countertermOperator parameter -
          data.greenIdentity.shortTimeDuhamelOperator parameter) -
        data.greenIdentity.longTimeDuhamelOperator parameter) := by
      abel
    _ = -data.greenIdentity.logarithmicDerivativeOperator parameter := by
      rw [data.greenIdentity.totalOperator_eq_logarithmicDerivative parameter]

/-- Feed the proved Green identity into the fully countable terminal-boundary
frontend. -/
def toFullyCountableTerminalBoundaryFrontend
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : ReferenceNuclearDuhamelFullyCountableGreenOperatorIdentityAdapterData
      nuclear finiteCounterterm shortTime) :
    ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime where
  shortFrontend := data.shortFrontend
  longFrontend := data.longFrontend
  longIntegrand_continuousOn := data.longIntegrand_continuousOn
  finitePartOperator := data.greenIdentity.countertermOperator
  finitePartTraceClass := data.greenIdentity.countertermTraceClass
  finitePartDerivative_eq_trace := fun parameter =>
    (data.finitePartDerivative_eq_countertermDerivative parameter).trans
      (data.greenIdentity.countertermDerivative_eq_trace parameter)
  logarithmicDerivativeOperator := fun parameter =>
    -data.greenIdentity.logarithmicDerivativeOperator parameter
  shortBoundaryIdentity := data.signedOperatorIdentity

/-- Public adapter checkpoint. -/
theorem reference_nuclear_duhamel_fully_countable_green_operator_identity_adapter_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1)
    (data : ReferenceNuclearDuhamelFullyCountableGreenOperatorIdentityAdapterData
      nuclear finiteCounterterm shortTime) :
    ∀ parameter,
      (data.shortFrontend.toRenormalizedOperatorIntegral.integratedOperator
            parameter - data.greenIdentity.countertermOperator parameter) +
          data.longFrontend.integratedOperator parameter =
        -data.greenIdentity.logarithmicDerivativeOperator parameter :=
  data.signedOperatorIdentity

end ReferenceNuclearDuhamelFullyCountableGreenOperatorIdentityAdapterData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelFullyCountableGreenOperatorIdentityAdapter4D
end JanusFormal
