import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFinitePartFamilyFrontend4D

/-!
# Product-throat finite part from one short-time basepoint

One integrable short-time remainder and a uniform parameter-derivative bound
generate the complete short-time family before it is joined to the product
long-time packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontend4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFinitePartFamilyFrontend4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Product-throat finite-part input with short-time control based at one
parameter. -/
structure ProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontendData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  shortTimeBasepoint :
    NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
      nuclear 1
  shortTime_counterterm_eq : ∀ parameter time,
    shortTimeBasepoint.counterterm parameter time =
      counterterm finiteCounterterm.variation parameter time
  longTime : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
    productData fold twist nuclear 1

namespace ProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontendData

/-- Generate the full short-time packet and then the complete finite-part
family frontend. -/
def toFinitePartFamilyFrontend
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontendData
      Index productData fold twist nuclear) :
    ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData
      Index productData fold twist nuclear where
  finiteCounterterm := data.finiteCounterterm
  shortTime := data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic
  shortTime_counterterm_eq := data.shortTime_counterterm_eq
  longTime := data.longTime

/-- Public basepoint finite-part checkpoint. -/
theorem product_throat_nuclear_heat_duhamel_basepoint_finite_part_family_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontendData
      Index productData fold twist nuclear) :
    (∀ parameter,
      Integrable
        (data.shortTimeBasepoint.weightedRemainder parameter)
        (volume.restrict (Set.Ioo (0 : Real) 1))) ∧
    (∀ parameter,
      HasDerivAt
        (fun current => relativeHeatFinitePartLogDeterminant
          (data.toFinitePartFamilyFrontend.toRelativeHeatFinitePartFamilyData.finitePart
            current))
        (data.toFinitePartFamilyFrontend.toRelativeHeatFinitePartFamilyData.logDerivative
          parameter) parameter) := by
  exact ⟨data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic.integrand_integrable,
    data.toFinitePartFamilyFrontend.toRelativeHeatFinitePartFamilyData.hasDerivAt_logDeterminant⟩

end ProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontendData

end
end P0EFTJanusProgramPProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontend4D
end JanusFormal
