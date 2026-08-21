import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHeatOperatorRealNuclearExpansion4D

/-!
# Operator-generated ProductThroat finite-counterterm frontend

Operator conjugacy and the canonical real rank-one expansion generate the
factor-two real heat-trace normalization required by the short-time frontend.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFiniteCountertermOperatorFrontend4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatNuclearHeatTrace4D
open P0EFTJanusProductThroatHeatOperatorRealNuclearExpansion4D
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontend4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
open P0EFTJanusProgramPReferenceProductThroatHeatOperatorIdentification4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- The strong short-time frontend with operator conjugacy in place of an
independent real heat-trace normalization. -/
structure ProductThroatNuclearHeatDuhamelFiniteCountertermOperatorFrontendData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  basis_continuousOn : ∀ index,
    ContinuousOn (finiteCounterterm.variation.basis index)
      (Set.Ioo (0 : Real) 1)
  operatorIdentification :
    ReferenceProductThroatHeatOperatorIdentificationData productData fold
      (fun _ => twist) nuclear
  basepoint : Real
  basepoint_integrable :
    Integrable (fun time => time⁻¹ *
      (extendedHeatTrace nuclear basepoint time -
        counterterm finiteCounterterm.variation basepoint time))
      (volume.restrict (Set.Ioo (0 : Real) 1))
  scale : Real
  derivative_norm_le :
    ∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1), ∀ parameter,
      ‖time⁻¹ *
        (extendedHeatTraceDerivative nuclear parameter time -
          countertermDerivative finiteCounterterm.variation parameter time)‖ ≤
        shortTimeQuadraticBound scale time
  longTime : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
    productData fold twist nuclear 1

namespace ProductThroatNuclearHeatDuhamelFiniteCountertermOperatorFrontendData

/-- Generate the existing strong frontend; the real trace normalization is
now a theorem of the concrete ProductThroat expansion. -/
def toFiniteCountertermSpectralBasepointFrontend
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatNuclearHeatDuhamelFiniteCountertermOperatorFrontendData
        Index productData fold twist nuclear) :
    ProductThroatNuclearHeatDuhamelFiniteCountertermSpectralBasepointFrontendData
      Index productData fold twist nuclear where
  finiteCounterterm := data.finiteCounterterm
  basis_continuousOn := data.basis_continuousOn
  realHeatTraceIdentification :=
    referenceProductThroatRealHeatTraceIdentificationData_of_operatorIdentification
      productData fold twist nuclear data.operatorIdentification
  basepoint := data.basepoint
  basepoint_integrable := data.basepoint_integrable
  scale := data.scale
  derivative_norm_le := data.derivative_norm_le
  longTime := data.longTime

/-- Exact real trace normalization generated from operator conjugacy. -/
theorem real_heat_trace_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatNuclearHeatDuhamelFiniteCountertermOperatorFrontendData
        Index productData fold twist nuclear) :
    ∀ parameter time,
      nuclear.heatTrace parameter time =
        2 * productThroatNuclearHeatTrace productData time fold twist :=
  data.toFiniteCountertermSpectralBasepointFrontend
    |>.realHeatTraceIdentification.heatTrace_eq_realProductTrace

end ProductThroatNuclearHeatDuhamelFiniteCountertermOperatorFrontendData

end
end P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFiniteCountertermOperatorFrontend4D
end JanusFormal
