import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFinitePartFamilyFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceHeatDuhamelGeneratedFinitePartCompatibleAssembly4D

/-!
# Product-throat generated finite-part Mellin assembly

The product spectral long-time packet and the short-time counterterm packet
generate the finite-part family before the remaining Mellin data are supplied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelGeneratedFinitePartAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFinitePartFamilyFrontend4D
open P0EFTJanusProgramPReferenceHeatDuhamelGeneratedFinitePartCompatibleAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- The remaining analytic inputs after the product-throat finite-part family
has been generated. -/
structure ProductThroatReferenceHeatDuhamelGeneratedFinitePartAssemblyData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finitePart : ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData
    Index productData fold twist nuclear
  continuation : ∀ parameter,
    RelativeHeatMellinZetaContinuationData
      (finitePart.toNuclearHeatDuhamelFinitePartFamilyFrontend
        |>.toRelativeHeatFinitePartData parameter)
  parameterDerivative : Real → Complex
  hasDerivAt_zetaPrime : ∀ parameter,
    HasDerivAt
      (fun current ↦ (continuation current).derivativeAtZero)
      (parameterDerivative parameter) parameter
  logarithmicTrace : Real → Real
  duhamel_integral_identity : ∀ parameter,
    -finitePartDerivative finitePart.finiteCounterterm parameter +
        (∫ time in Set.Ioo (0 : Real) 1,
          finitePart.shortTime.renormalizedDuhamelTrace parameter time) +
        (∫ time in Set.Ioi (1 : Real),
          extendedDuhamelTrace nuclear parameter time) =
      logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (continuation parameter).derivativeAtZero.im = 0

namespace ProductThroatReferenceHeatDuhamelGeneratedFinitePartAssemblyData

/-- Forget the product origin only after constructing the generated
finite-part frontend. -/
def toGeneratedFinitePartCompatibleAssembly
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatReferenceHeatDuhamelGeneratedFinitePartAssemblyData
      Index productData fold twist nuclear) :
    ReferenceHeatDuhamelGeneratedFinitePartCompatibleAssemblyData
      Index nuclear where
  finitePart := data.finitePart.toNuclearHeatDuhamelFinitePartFamilyFrontend
  continuation := data.continuation
  parameterDerivative := data.parameterDerivative
  hasDerivAt_zetaPrime := data.hasDerivAt_zetaPrime
  logarithmicTrace := data.logarithmicTrace
  duhamel_integral_identity := data.duhamel_integral_identity
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- Public checkpoint: the product-throat packets now feed the complete
generated finite-part Mellin assembly. -/
theorem product_throat_reference_heat_duhamel_generated_finite_part_assembly_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatReferenceHeatDuhamelGeneratedFinitePartAssemblyData
      Index productData fold twist nuclear) :
    let generated := data.toGeneratedFinitePartCompatibleAssembly
    (∀ parameter,
      generated.toRelativeHeatMellinZetaFamilyData.finitePartFamily.logDerivative
          parameter =
        data.logarithmicTrace parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient
          generated.toRelativeHeatMellinZetaFamilyData.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) := by
  let generated := data.toGeneratedFinitePartCompatibleAssembly
  rcases
      generated.reference_heat_duhamel_generated_finite_part_compatible_assembly_gate
        Index nuclear with
    ⟨_hShort, _hLong, _hDerivative, hNamed, hConnection⟩
  refine ⟨?_, hConnection⟩
  intro parameter
  rw [hNamed parameter]
  simpa [generated, toGeneratedFinitePartCompatibleAssembly,
    ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData.toNuclearHeatDuhamelFinitePartFamilyFrontend] using
    data.duhamel_integral_identity parameter

end ProductThroatReferenceHeatDuhamelGeneratedFinitePartAssemblyData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelGeneratedFinitePartAssembly4D
end JanusFormal
