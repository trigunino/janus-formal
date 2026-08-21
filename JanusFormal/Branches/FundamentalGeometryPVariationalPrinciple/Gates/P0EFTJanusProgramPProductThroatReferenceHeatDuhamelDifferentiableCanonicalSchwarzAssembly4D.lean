import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssembly4D

/-!
# Differentiable ProductThroat canonical-Schwarz assembly

The parameter derivative of `zeta'(0)` is now defined canonically by `deriv`
from differentiability of the continuation family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFinitePartFamilyFrontend4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundary4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Product-throat terminal data with an honestly differentiable family of
regularized zeta derivatives. -/
structure ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssemblyData
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
  zetaPrime_differentiable : Differentiable Real
    (fun parameter => (continuation parameter).derivativeAtZero)

namespace ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssemblyData

/-- The derivative field and its `HasDerivAt` certificate are generated from
the differentiable continuation family. -/
def toLocallyUniformOperatorGeneratedCanonicalSchwarzAssembly
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :
    ProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssemblyData
      Index productData fold twist nuclear where
  finitePart := data.finitePart
  operatorBoundary := data.operatorBoundary
  continuation := data.continuation
  canonicalSchwarz := data.canonicalSchwarz
  parameterDerivative := fun parameter =>
    deriv (fun current => (data.continuation current).derivativeAtZero)
      parameter
  hasDerivAt_zetaPrime := fun parameter =>
    (data.zetaPrime_differentiable parameter).hasDerivAt

/-- Public differentiable-family checkpoint. -/
theorem product_throat_reference_heat_duhamel_differentiable_canonical_schwarz_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :
    Differentiable Real
        (fun parameter => (data.continuation parameter).derivativeAtZero) ∧
    (∀ parameter,
      (data.continuation parameter).derivativeAtZero.im = 0) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.relativeZetaConnectionCoefficient
          data.toLocallyUniformOperatorGeneratedCanonicalSchwarzAssembly.toOperatorGeneratedCanonicalSchwarzAssembly.toRelativeHeatMellinZetaFamilyData.toZetaFamily
          parameter =
        -(data.toLocallyUniformOperatorGeneratedCanonicalSchwarzAssembly.toOperatorGeneratedCanonicalSchwarzAssembly.logarithmicTrace
          parameter : Complex)) := by
  exact ⟨data.zetaPrime_differentiable,
    data.toLocallyUniformOperatorGeneratedCanonicalSchwarzAssembly.product_throat_reference_heat_duhamel_locally_uniform_operator_generated_canonical_schwarz_gate.2⟩

end ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssemblyData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssembly4D
end JanusFormal
