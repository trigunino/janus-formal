import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D

/-!
# Continuous-basepoint differentiable ProductThroat assembly

Time continuity and one basepoint majorant generate the short-time finite-part
family before the differentiable Mellin-Schwarz assembly is formed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceIsometricEquivalenceTransport4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelContinuousBasepointFinitePartFamilyFrontend4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPReferenceProductThroatHeatOperatorIdentification4D
open P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D
open P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundary4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Differentiable Mellin-Schwarz data generated from continuous short-time
basepoint input. -/
structure ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssemblyData
    (Index : Type*)
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finitePart :
    ProductThroatNuclearHeatDuhamelFiniteCountertermSpectralBasepointFrontendData
      Index productData fold twist nuclear
  operatorBoundary :
    ProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundaryData
      Index productData fold twist nuclear finitePart.finiteCounterterm
        (finitePart.toCanonicalWeightContinuousBasepointFinitePartFamilyFrontend
          |>.toContinuousBasepointFinitePartFamilyFrontend.shortTime
          |>.toContinuousBasepoint.toBasepointQuadratic
          |>.toCountertermSubtractedShortTimeQuadratic)
  continuation : ∀ parameter,
    RelativeHeatMellinZetaContinuationData
      (finitePart.toCanonicalWeightContinuousBasepointFinitePartFamilyFrontend
        |>.toContinuousBasepointFinitePartFamilyFrontend
        |>.toBasepointFinitePartFamilyFrontend
        |>.toFinitePartFamilyFrontend
        |>.toNuclearHeatDuhamelFinitePartFamilyFrontend
        |>.toRelativeHeatFinitePartData parameter)
  canonicalSchwarz : ∀ parameter,
    RelativeHeatMellinZetaCanonicalSchwarzReflectionData
      (continuation parameter)
  zetaPrime_differentiable : Differentiable Real
    (fun parameter => (continuation parameter).derivativeAtZero)

namespace ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssemblyData

/-- Forget the continuity presentation after it has generated the basepoint
finite-part packet. -/
def toBasepointDifferentiableCanonicalSchwarzAssembly
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :
    ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssemblyData
      Index productData fold twist nuclear where
  finitePart := data.finitePart.toCanonicalWeightContinuousBasepointFinitePartFamilyFrontend
    |>.toContinuousBasepointFinitePartFamilyFrontend
    |>.toBasepointFinitePartFamilyFrontend
  operatorBoundary := data.operatorBoundary
  continuation := data.continuation
  canonicalSchwarz := data.canonicalSchwarz
  zetaPrime_differentiable := data.zetaPrime_differentiable

/-- The abstract reference heat operator and its intrinsic nuclear trace are
exactly the concrete product-throat operator and trace. -/
theorem heat_operator_identification_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear)
    (parameter : Real) (time : HeatTime) :
    isometricEquivalenceConjugatedOperator
        data.finitePart.realHeatTraceIdentification.operatorIdentification.coordinates
        (nuclear.heatOperator parameter time) =
        productThroatHeatOperatorReal productData time fold twist ∧
    intrinsicNuclearTrace
        (data.finitePart.realHeatTraceIdentification.operatorIdentification.productHeatTraceClass
          parameter time) =
      nuclear.heatTrace parameter time :=
  data.finitePart.realHeatTraceIdentification.operatorIdentification.reference_product_throat_heat_operator_identification_gate
    parameter time

/-- Time continuity of the short heat trace is generated by the explicit
product spectral trace. -/
theorem short_heat_trace_continuousOn
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear)
    (parameter : Real) :
    ContinuousOn (fun time => extendedHeatTrace nuclear parameter time)
      (Set.Ioo (0 : Real) 1) :=
  data.finitePart.realHeatTraceIdentification.extendedHeatTrace_continuousOn_Ioo
    parameter 1

/-- Public continuity-to-differentiable-Schwarz checkpoint. -/
theorem product_throat_reference_heat_duhamel_continuous_basepoint_differentiable_canonical_schwarz_gate
    {Index : Type*}
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssemblyData
        Index productData fold twist nuclear) :
    (∀ parameter,
      ContinuousOn
        (fun time => time⁻¹ *
          (extendedHeatTrace nuclear parameter time -
            counterterm data.finitePart.finiteCounterterm.variation
              parameter time))
        (Set.Ioo (0 : Real) 1)) ∧
    Differentiable Real
      (fun parameter => (data.continuation parameter).derivativeAtZero) ∧
    (∀ parameter,
      (data.continuation parameter).derivativeAtZero.im = 0) := by
  exact
    ⟨data.finitePart.toCanonicalWeightContinuousBasepointFinitePartFamilyFrontend
        |>.toContinuousBasepointFinitePartFamilyFrontend.shortTime
        |>.toContinuousBasepoint.weightedRemainder_continuousOn,
      data.zetaPrime_differentiable,
      data.toBasepointDifferentiableCanonicalSchwarzAssembly.product_throat_reference_heat_duhamel_basepoint_differentiable_canonical_schwarz_gate.2.2⟩

end ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssemblyData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssembly4D
end JanusFormal
