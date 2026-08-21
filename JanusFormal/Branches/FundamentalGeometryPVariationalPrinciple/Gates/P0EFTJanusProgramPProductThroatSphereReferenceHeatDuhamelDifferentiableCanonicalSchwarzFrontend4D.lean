import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereNuclearFiniteCountertermSpectralBasepointFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelRealTraceLongTimeExponential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegral4D

/-!
# Spherical ProductThroat differentiable Schwarz frontend

This frontend packages the proved spherical short-time basepoint with the
operator boundary, Mellin continuation and Schwarz data of the generated
reference assembly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereReferenceHeatDuhamelDifferentiableCanonicalSchwarzFrontend4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelRealTraceLongTimeExponential4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
open P0EFTJanusProgramPProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegral4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPProductThroatReferenceNuclearDuhamelLocallyUniformFullyCountableTerminalBoundary4D
open P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D
open P0EFTJanusProgramPProductThroatSphereNuclearFiniteCountertermSpectralBasepointFrontend4D
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
open P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Spherical analytic inputs that canonically generate the finite-part
frontend. -/
structure ProductThroatSphereReferenceHeatDuhamelSourceData
    (sphereData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  shortTime : ProductThroatSphereNuclearShortTimeBasepointQuadraticData
    sphereData nuclear
  shortTime_counterterm_eq : ∀ parameter time,
    shortTime.counterterm parameter time =
      P0EFTJanusProgramPFiniteHeatCountertermVariation4D.counterterm
        (reducedSphereFiniteCountertermVariation sphereData).variation
          parameter time
  longTime : ProductThroatNuclearHeatDuhamelRealTraceLongTimeExponentialData
    sphereData fold twist nuclear

namespace ProductThroatSphereReferenceHeatDuhamelSourceData

/-- Generated finite-part input with no additional short-time estimates. -/
def toFinitePartFrontend
    {sphereData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (source : ProductThroatSphereReferenceHeatDuhamelSourceData
      sphereData fold twist nuclear) :=
  productThroatReducedSphereSpectralBasepointFrontend
    source.longTime.realHeatTraceIdentification source.shortTime
      source.shortTime_counterterm_eq source.longTime.toLongTimeExponential

end ProductThroatSphereReferenceHeatDuhamelSourceData

/-- Remaining operator/Mellin data over the generated spherical finite-part
source. -/
structure ProductThroatSphereReferenceHeatDuhamelDifferentiableCanonicalSchwarzFrontendData
    (sphereData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  source : ProductThroatSphereReferenceHeatDuhamelSourceData
    sphereData fold twist nuclear
  operatorBoundary :
    ProductThroatReferenceNuclearDuhamelGeneratedBochnerTerminalBoundaryData
      ReducedSphereCountertermProfile sphereData fold twist nuclear
        source.toFinitePartFrontend.finiteCounterterm
        (source.toFinitePartFrontend
          |>.toCanonicalWeightContinuousBasepointFinitePartFamilyFrontend
          |>.toContinuousBasepointFinitePartFamilyFrontend.shortTime
          |>.toContinuousBasepoint.toBasepointQuadratic
          |>.toCountertermSubtractedShortTimeQuadratic)
  continuation : ∀ parameter,
    RelativeHeatMellinZetaContinuationData
      (source.toFinitePartFrontend
        |>.toCanonicalWeightContinuousBasepointFinitePartFamilyFrontend
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

namespace ProductThroatSphereReferenceHeatDuhamelDifferentiableCanonicalSchwarzFrontendData

/-- Adapter to the strongest generated ProductThroat assembly. -/
def toContinuousBasepointDifferentiableCanonicalSchwarzAssembly
    {sphereData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatSphereReferenceHeatDuhamelDifferentiableCanonicalSchwarzFrontendData
        sphereData fold twist nuclear) :
    ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssemblyData
      ReducedSphereCountertermProfile sphereData fold twist nuclear where
  finitePart := data.source.toFinitePartFrontend
  operatorBoundary :=
    data.operatorBoundary.toLocallyUniformFullyCountableTerminalBoundary
  continuation := data.continuation
  canonicalSchwarz := data.canonicalSchwarz
  zetaPrime_differentiable := data.zetaPrime_differentiable

/-- Public spherical generated-assembly checkpoint. -/
theorem product_throat_sphere_reference_heat_duhamel_differentiable_canonical_schwarz_gate
    {sphereData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatSphereReferenceHeatDuhamelDifferentiableCanonicalSchwarzFrontendData
        sphereData fold twist nuclear) :
    Integrable
      (fun time => time⁻¹ *
        (P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData.extendedHeatTrace
            nuclear data.source.shortTime.basepoint time -
          P0EFTJanusProgramPFiniteHeatCountertermVariation4D.counterterm
            (reducedSphereFiniteCountertermVariation sphereData).variation
              data.source.shortTime.basepoint time))
      (volume.restrict (Set.Ioo (0 : Real) 1)) ∧
    Differentiable Real
      (fun parameter => (data.continuation parameter).derivativeAtZero) ∧
    (∀ parameter,
      (data.continuation parameter).derivativeAtZero.im = 0) ∧
    (∀ parameter,
      Integrable (data.operatorBoundary.longTime.operatorIntegrand parameter)
        (volume.restrict (Set.Ioi (1 : Real)))) := by
  exact
    ⟨data.source.toFinitePartFrontend.basepoint_integrable,
      data.zetaPrime_differentiable,
      data.toContinuousBasepointDifferentiableCanonicalSchwarzAssembly.product_throat_reference_heat_duhamel_continuous_basepoint_differentiable_canonical_schwarz_gate.2.2,
      data.operatorBoundary.longTime.operatorIntegrable⟩

end ProductThroatSphereReferenceHeatDuhamelDifferentiableCanonicalSchwarzFrontendData

end
end P0EFTJanusProgramPProductThroatSphereReferenceHeatDuhamelDifferentiableCanonicalSchwarzFrontend4D
end JanusFormal
