import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssembly4D

/-!
# Basepoint-generated differentiable ProductThroat assembly

The short-time family is propagated from one integrable basepoint before the
locally uniform operator and Mellin-Schwarz constructions are assembled.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontend4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundary4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Strongest generated standalone reference packet currently available. -/
structure ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssemblyData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finitePart : ProductThroatNuclearHeatDuhamelBasepointFinitePartFamilyFrontendData
    Index productData fold twist nuclear
  operatorBoundary :
    ProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundaryData
      Index productData fold twist nuclear finitePart.finiteCounterterm
        finitePart.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic
  continuation : ∀ parameter,
    RelativeHeatMellinZetaContinuationData
      (finitePart.toFinitePartFamilyFrontend
        |>.toNuclearHeatDuhamelFinitePartFamilyFrontend
        |>.toRelativeHeatFinitePartData parameter)
  canonicalSchwarz : ∀ parameter,
    RelativeHeatMellinZetaCanonicalSchwarzReflectionData
      (continuation parameter)
  zetaPrime_differentiable : Differentiable Real
    (fun parameter => (continuation parameter).derivativeAtZero)

namespace ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssemblyData

/-- Adapter to the differentiable canonical-Schwarz assembly after basepoint
propagation. -/
def toDifferentiableCanonicalSchwarzAssembly
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :
    ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssemblyData
      Index productData fold twist nuclear where
  finitePart := data.finitePart.toFinitePartFamilyFrontend
  operatorBoundary := data.operatorBoundary
  continuation := data.continuation
  canonicalSchwarz := data.canonicalSchwarz
  zetaPrime_differentiable := data.zetaPrime_differentiable

/-- Public basepoint-to-zeta checkpoint. -/
theorem product_throat_reference_heat_duhamel_basepoint_differentiable_canonical_schwarz_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :
    (∀ parameter,
      Integrable (data.finitePart.shortTimeBasepoint.weightedRemainder parameter)
        (volume.restrict (Set.Ioo (0 : Real) 1))) ∧
    Differentiable Real
      (fun parameter => (data.continuation parameter).derivativeAtZero) ∧
    (∀ parameter,
      (data.continuation parameter).derivativeAtZero.im = 0) := by
  exact
    ⟨data.finitePart.toFinitePartFamilyFrontend.shortTime.integrand_integrable,
      data.zetaPrime_differentiable,
      data.toDifferentiableCanonicalSchwarzAssembly.product_throat_reference_heat_duhamel_differentiable_canonical_schwarz_gate.2.1⟩

end ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssemblyData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssembly4D
end JanusFormal
