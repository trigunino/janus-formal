import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearDuhamelCountableRankOneBochnerOperatorIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D

/-!
# Product-throat fully countable terminal boundary

This adapter combines the renormalized short-time rank-one packet with the
product-generated long-time Bochner packet.  The long matching operator is the
actual Bochner integral by construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatNuclearDuhamelCountableRankOneBochnerOperatorIntegral4D
open P0EFTJanusProgramPReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D
open P0EFTJanusProgramPRenormalizedNuclearDuhamelCountableRankOneBochnerFrontend4D
open P0EFTJanusProductThroatPositiveHeatGapLongTime4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Remaining geometric operator identity after both regional integrals have
been constructed. -/
structure ProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index)
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1) where
  shortFrontend :
    RenormalizedNuclearDuhamelCountableRankOneBochnerFrontendData
      nuclear shortTime
  longTime :
    ProductThroatNuclearDuhamelCountableRankOneBochnerOperatorIntegralData
      productData fold twist nuclear 1
  longIntegrand_continuousOn : ∀ parameter,
    ContinuousOn (longTime.operatorIntegrand parameter) (Set.Ici (1 : Real))
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
      longTime.toCountableRankOneBochnerOperatorIntegral.integratedOperator
        parameter =
      logarithmicDerivativeOperator parameter

namespace ProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData

/-- Convert after retaining the product-generated weighted long-time packet. -/
def toFullyCountableTerminalBoundaryFrontend
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data :
      ProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
        Index productData fold twist nuclear finiteCounterterm shortTime) :
    ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
      nuclear finiteCounterterm shortTime where
  shortFrontend := data.shortFrontend
  longFrontend := data.longTime.toCountableRankOneBochnerOperatorIntegral
  longIntegrand_continuousOn := data.longIntegrand_continuousOn
  finitePartOperator := data.finitePartOperator
  finitePartTraceClass := data.finitePartTraceClass
  finitePartDerivative_eq_trace := data.finitePartDerivative_eq_trace
  logarithmicDerivativeOperator := data.logarithmicDerivativeOperator
  shortBoundaryIdentity := data.shortBoundaryIdentity

/-- Public ProductThroat operator-boundary checkpoint. -/
theorem product_throat_reference_nuclear_duhamel_fully_countable_terminal_boundary_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data :
      ProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
        Index productData fold twist nuclear finiteCounterterm shortTime) :
    0 < productThroatPositiveHeatGap productData ∧
    (∀ parameter,
      (data.toFullyCountableTerminalBoundaryFrontend.terminalTail parameter).matchingOperator =
        data.longTime.toCountableRankOneBochnerOperatorIntegral.integratedOperator
          parameter) ∧
    (∀ parameter,
      (data.shortFrontend.toRenormalizedOperatorIntegral.integratedOperator
          parameter - data.finitePartOperator parameter) +
        data.longTime.toCountableRankOneBochnerOperatorIntegral.integratedOperator
          parameter =
        data.logarithmicDerivativeOperator parameter) := by
  exact ⟨productThroatPositiveHeatGap_pos productData,
    data.toFullyCountableTerminalBoundaryFrontend.terminalIntegral_eq_longOperator,
    data.shortBoundaryIdentity⟩

end ProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData

end
end P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D
end JanusFormal
