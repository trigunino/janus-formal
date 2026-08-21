import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelFinitePartFamilyFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D

/-!
# Product-throat generated finite-part family

The short-time counterterm packet and the product-generated long-time packet
construct the complete differentiable finite-part family directly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFinitePartFamilyFrontend4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelFinitePartFamilyFrontend4D
open P0EFTJanusProgramPNuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Minimal ProductThroat specialization of the generated finite-part
frontend. -/
structure ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
    nuclear 1
  shortTime_counterterm_eq : ∀ parameter time,
    shortTime.counterterm parameter time =
      counterterm finiteCounterterm.variation parameter time
  longTime : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
    productData fold twist nuclear 1

namespace ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData

/-- Forget the spectral origin only after generating the weighted long-time
integral and its integrability. -/
def toNuclearHeatDuhamelFinitePartFamilyFrontend
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData
      Index productData fold twist nuclear) :
    NuclearHeatDuhamelFinitePartFamilyFrontendData Index nuclear where
  finiteCounterterm := data.finiteCounterterm
  shortTime := data.shortTime
  shortTime_counterterm_eq := data.shortTime_counterterm_eq
  longTime :=
    data.longTime.toLongTimeExponentialDominatedWeightedIntegral.toDominatedWeightedIntegral.toWeightedIntegral
  longTime_integrable := data.longTime.integrand_integrable

/-- Differentiable finite-part family generated from the ProductThroat data. -/
def toRelativeHeatFinitePartFamilyData
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData
      Index productData fold twist nuclear) :
    RelativeHeatFinitePartFamilyData :=
  data.toNuclearHeatDuhamelFinitePartFamilyFrontend.toRelativeHeatFinitePartFamilyData

/-- Public ProductThroat finite-part checkpoint. -/
theorem product_throat_nuclear_heat_duhamel_finite_part_family_frontend_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData
      Index productData fold twist nuclear) :
    let family := data.toRelativeHeatFinitePartFamilyData
    (∀ parameter,
      family.finitePart parameter =
        data.toNuclearHeatDuhamelFinitePartFamilyFrontend.toRelativeHeatFinitePartData
          parameter) ∧
    (∀ parameter,
      family.logDerivative parameter =
        data.toNuclearHeatDuhamelFinitePartFamilyFrontend.logDerivative parameter) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

end ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData

end
end P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFinitePartFamilyFrontend4D
end JanusFormal
