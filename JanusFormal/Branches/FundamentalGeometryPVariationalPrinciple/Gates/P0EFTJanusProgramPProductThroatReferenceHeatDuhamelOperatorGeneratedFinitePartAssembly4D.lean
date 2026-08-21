import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelGeneratedFinitePartAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D

/-!
# Operator-generated product-throat finite-part assembly

The fully countable short/long operator boundary generates the integrated
Duhamel identity required by the Mellin finite-part assembly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelOperatorGeneratedFinitePartAssembly4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelFinitePartFamilyFrontend4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelGeneratedFinitePartAssembly4D
open P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D
open P0EFTJanusProgramPReferenceNuclearDuhamelCountableTerminalBoundaryFrontend4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Only the Mellin continuation family remains analytic input after the
finite-part and operator-boundary constructions. -/
structure ProductThroatReferenceHeatDuhamelOperatorGeneratedFinitePartAssemblyData
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
  parameterDerivative : Real → Complex
  hasDerivAt_zetaPrime : ∀ parameter,
    HasDerivAt
      (fun current ↦ (continuation current).derivativeAtZero)
      (parameterDerivative parameter) parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (continuation parameter).derivativeAtZero.im = 0

namespace ProductThroatReferenceHeatDuhamelOperatorGeneratedFinitePartAssemblyData

/-- The scalar integrated Duhamel identity is obtained by tracing the
constructed operator boundary. -/
def toGeneratedFinitePartAssembly
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelOperatorGeneratedFinitePartAssemblyData
        Index productData fold twist nuclear) :
    ProductThroatReferenceHeatDuhamelGeneratedFinitePartAssemblyData
      Index productData fold twist nuclear where
  finitePart := data.finitePart
  continuation := data.continuation
  parameterDerivative := data.parameterDerivative
  hasDerivAt_zetaPrime := data.hasDerivAt_zetaPrime
  logarithmicTrace :=
    data.operatorBoundary.toFullyCountableTerminalBoundaryFrontend.toGreenBoundaryData.logarithmicTrace
  duhamel_integral_identity :=
    data.operatorBoundary.toFullyCountableTerminalBoundaryFrontend.toGreenBoundaryData.duhamel_integral_identity
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- Public terminal: the connection coefficient is the negative intrinsic
trace of the constructed logarithmic-derivative operator. -/
theorem product_throat_reference_heat_duhamel_operator_generated_finite_part_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelOperatorGeneratedFinitePartAssemblyData
        Index productData fold twist nuclear) :
    let assembly := data.toGeneratedFinitePartAssembly
    ∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.relativeZetaConnectionCoefficient
          assembly.toGeneratedFinitePartCompatibleAssembly.toRelativeHeatMellinZetaFamilyData.toZetaFamily
          parameter =
        -(data.operatorBoundary.toFullyCountableTerminalBoundaryFrontend.toGreenBoundaryData.logarithmicTrace
          parameter : Complex) := by
  exact
    data.toGeneratedFinitePartAssembly.product_throat_reference_heat_duhamel_generated_finite_part_assembly_gate.2

end ProductThroatReferenceHeatDuhamelOperatorGeneratedFinitePartAssemblyData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelOperatorGeneratedFinitePartAssembly4D
end JanusFormal
