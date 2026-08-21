import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundary4D

/-!
# Locally uniform operator-generated Schwarz assembly

The long operator continuity required by the terminal primitive is generated
from the locally uniform countable rank-one expansion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFinitePartFamilyFrontend4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundary4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Canonical Schwarz assembly with long-time continuity generated from a
uniformly summable operator series. -/
structure ProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssemblyData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finitePart : ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData
    Index productData fold twist nuclear
  operatorBoundary :
    ProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundaryData
      Index productData fold twist nuclear finitePart.finiteCounterterm
        finitePart.shortTime
  continuation : ∀ parameter,
    RelativeHeatMellinZetaContinuationData
      (finitePart.toNuclearHeatDuhamelFinitePartFamilyFrontend
        |>.toRelativeHeatFinitePartData parameter)
  canonicalSchwarz : ∀ parameter,
    RelativeHeatMellinZetaCanonicalSchwarzReflectionData
      (continuation parameter)
  parameterDerivative : Real → Complex
  hasDerivAt_zetaPrime : ∀ parameter,
    HasDerivAt
      (fun current ↦ (continuation current).derivativeAtZero)
      (parameterDerivative parameter) parameter

namespace ProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssemblyData

/-- Adapter to the canonical Schwarz terminal after deriving operator
continuity. -/
def toOperatorGeneratedCanonicalSchwarzAssembly
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :
    ProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssemblyData
      Index productData fold twist nuclear where
  finitePart := data.finitePart
  operatorBoundary := data.operatorBoundary.toFullyCountableTerminalBoundary
  continuation := data.continuation
  canonicalSchwarz := data.canonicalSchwarz
  parameterDerivative := data.parameterDerivative
  hasDerivAt_zetaPrime := data.hasDerivAt_zetaPrime

/-- Public checkpoint retaining the derived long-time continuity and the
canonical real connection coefficient. -/
theorem product_throat_reference_heat_duhamel_locally_uniform_operator_generated_canonical_schwarz_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :
    (∀ parameter,
      ContinuousOn (data.operatorBoundary.longTime.operatorIntegrand parameter)
        (Set.Ici (1 : Real))) ∧
    (∀ parameter,
      (data.continuation parameter).derivativeAtZero.im = 0) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.relativeZetaConnectionCoefficient
          data.toOperatorGeneratedCanonicalSchwarzAssembly.toRelativeHeatMellinZetaFamilyData.toZetaFamily
          parameter =
        -(data.toOperatorGeneratedCanonicalSchwarzAssembly.logarithmicTrace
          parameter : Complex)) := by
  exact ⟨data.operatorBoundary.longIntegrand_continuousOn,
    data.toOperatorGeneratedCanonicalSchwarzAssembly.product_throat_reference_heat_duhamel_operator_generated_canonical_schwarz_gate⟩

end ProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssemblyData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssembly4D
end JanusFormal
