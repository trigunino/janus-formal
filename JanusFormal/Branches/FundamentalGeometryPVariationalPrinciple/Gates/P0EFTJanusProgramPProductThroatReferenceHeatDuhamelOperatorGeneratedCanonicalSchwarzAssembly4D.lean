import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelOperatorGeneratedFinitePartAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D

/-!
# Canonical-Schwarz product-throat operator assembly

Analytic Schwarz reflection now derives reality of the regularized zeta
derivative; it is no longer a separate input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFinitePartFamilyFrontend4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelOperatorGeneratedFinitePartAssembly4D
open P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Operator-generated finite part plus a genuine analytic continuation and
its canonical Schwarz domain. -/
structure ProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssemblyData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finitePart : ProductThroatNuclearHeatDuhamelFinitePartFamilyFrontendData
    Index productData fold twist nuclear
  operatorBoundary :
    ProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData
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

namespace ProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssemblyData

/-- Canonical Schwarz reflection fills the reality field of the preceding
operator-generated assembly. -/
def toOperatorGeneratedFinitePartAssembly
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :
    ProductThroatReferenceHeatDuhamelOperatorGeneratedFinitePartAssemblyData
      Index productData fold twist nuclear where
  finitePart := data.finitePart
  operatorBoundary := data.operatorBoundary
  continuation := data.continuation
  parameterDerivative := data.parameterDerivative
  hasDerivAt_zetaPrime := data.hasDerivAt_zetaPrime
  zetaPrimeAtZero_real := fun parameter =>
    (data.canonicalSchwarz parameter).derivativeAtZero_im_eq_zero

/-- Generated Mellin-zeta family. -/
def toRelativeHeatMellinZetaFamilyData
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :=
  data.toOperatorGeneratedFinitePartAssembly.toGeneratedFinitePartAssembly
    |>.toGeneratedFinitePartCompatibleAssembly.toRelativeHeatMellinZetaFamilyData

/-- Intrinsic trace of the constructed logarithmic derivative. -/
def logarithmicTrace
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) : Real → Real :=
  data.operatorBoundary.toFullyCountableTerminalBoundaryFrontend.toGreenBoundaryData.logarithmicTrace

/-- Public checkpoint exposing both Schwarz symmetry and the resulting real
zeta connection coefficient. -/
theorem product_throat_reference_heat_duhamel_operator_generated_canonical_schwarz_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :
    (∀ parameter,
      (data.continuation parameter).derivativeAtZero.im = 0) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.relativeZetaConnectionCoefficient
          data.toRelativeHeatMellinZetaFamilyData.toZetaFamily
          parameter =
        -(data.logarithmicTrace parameter : Complex)) := by
  exact ⟨fun parameter =>
      (data.canonicalSchwarz parameter).derivativeAtZero_im_eq_zero,
    data.toOperatorGeneratedFinitePartAssembly.product_throat_reference_heat_duhamel_operator_generated_finite_part_gate⟩

end ProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssemblyData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelOperatorGeneratedCanonicalSchwarzAssembly4D
end JanusFormal
