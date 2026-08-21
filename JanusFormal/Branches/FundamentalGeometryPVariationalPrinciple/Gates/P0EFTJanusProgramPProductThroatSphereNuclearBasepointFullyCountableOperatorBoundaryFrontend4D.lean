import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegral4D

/-!
# Fully countable spherical-basepoint operator-boundary frontend

This frontend replaces the manual `operatorBoundary` field of the spherical
basepoint assembly by the constructive short and long countable-rank-one
Bochner packets.  The terminal primitive shares the long integrand, while the
only remaining signed operator identity is the physical short-boundary
matching statement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereNuclearBasepointFullyCountableOperatorBoundaryFrontend4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearDuhamelCountableRankOneBochnerOperatorIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssembly4D
open P0EFTJanusProgramPProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegral4D
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
open P0EFTJanusProgramPReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontend4D
open P0EFTJanusProgramPRenormalizedNuclearDuhamelCountableRankOneBochnerFrontend4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Spherical-basepoint input with constructive short and long operator
integrals.  No preassembled Green boundary packet is supplied. -/
structure ProductThroatSphereNuclearBasepointFullyCountableOperatorBoundaryFrontendData
    (Index : Type*)
    (sphereData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  shortTimeBasepoint :
    ProductThroatSphereNuclearShortTimeBasepointQuadraticData sphereData nuclear
  shortFrontend :
    RenormalizedNuclearDuhamelCountableRankOneBochnerFrontendData nuclear
      shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic
  longFrontend :
    ProductThroatNuclearDuhamelLocallyUniformBochnerOperatorIntegralData
      sphereData fold twist nuclear 1
  finitePartOperator : Real → E →L[Real] E
  finitePartTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (finitePartOperator parameter)
  finitePartDerivative_eq_trace : ∀ parameter,
    finitePartDerivative finiteCounterterm parameter =
      intrinsicNuclearTrace (finitePartTraceClass parameter)
  logarithmicDerivativeOperator : Real → E →L[Real] E
  shortBoundaryIdentity : ∀ parameter,
    (shortFrontend.toRenormalizedOperatorIntegral.integratedOperator parameter -
        finitePartOperator parameter) +
      (longFrontend.toCountableRankOneBochnerOperatorIntegral
        |>.toCountableRankOneBochnerOperatorIntegral
        |>.toNuclearDuhamelOperatorIntegral).integratedOperator parameter =
        logarithmicDerivativeOperator parameter
  familyHeatTrace_eq : ∀ parameter time,
    family.finitePartFamily.heatTrace parameter time =
      nuclear.heatTrace parameter time
  familyCounterterm_eq : ∀ parameter time,
    (family.finitePartFamily.finitePart parameter).counterterm time =
      counterterm finiteCounterterm.variation parameter time
  rawCountertermFinitePart_eq : ∀ parameter,
    (family.finitePartFamily.finitePart parameter).countertermFinitePart =
      finitePartContribution finiteCounterterm parameter
  shortTime_counterterm_eq : ∀ parameter time,
    shortTimeBasepoint.counterterm parameter time =
      counterterm finiteCounterterm.variation parameter time
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ProductThroatSphereNuclearBasepointFullyCountableOperatorBoundaryFrontendData

/-- Canonical generated product-throat terminal boundary. -/
def toGeneratedBochnerTerminalBoundary
    {Index : Type*}
    {sphereData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatSphereNuclearBasepointFullyCountableOperatorBoundaryFrontendData
        Index sphereData fold twist family nuclear) :
    ProductThroatReferenceNuclearDuhamelGeneratedBochnerTerminalBoundaryData
      Index sphereData fold twist nuclear data.finiteCounterterm
        data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic where
  shortFrontend := data.shortFrontend
  longTime := data.longFrontend
  finitePartOperator := data.finitePartOperator
  finitePartTraceClass := data.finitePartTraceClass
  finitePartDerivative_eq_trace := data.finitePartDerivative_eq_trace
  logarithmicDerivativeOperator := data.logarithmicDerivativeOperator
  shortBoundaryIdentity := data.shortBoundaryIdentity

/-- Fully countable Green-boundary frontend generated from the two regional
operator integrands. -/
def toFullyCountableTerminalBoundaryFrontend
    {Index : Type*}
    {sphereData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatSphereNuclearBasepointFullyCountableOperatorBoundaryFrontendData
        Index sphereData fold twist family nuclear) :
    ReferenceNuclearDuhamelFullyCountableTerminalBoundaryFrontendData nuclear
      data.finiteCounterterm
      data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic :=
  data.toGeneratedBochnerTerminalBoundary
    |>.toLocallyUniformFullyCountableTerminalBoundary
    |>.toFullyCountableTerminalBoundary
    |>.toFullyCountableTerminalBoundaryFrontend

/-- Canonical spherical operator-boundary assembly. -/
def toOperatorBoundaryFinitePartAssembly
    {Index : Type*}
    {sphereData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatSphereNuclearBasepointFullyCountableOperatorBoundaryFrontendData
        Index sphereData fold twist family nuclear) :
    ProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssemblyData
      Index (atTop : Filter Real) sphereData family nuclear where
  finiteCounterterm := data.finiteCounterterm
  shortTimeBasepoint := data.shortTimeBasepoint
  longTime := data.longFrontend.toCountableRankOneBochnerOperatorIntegral
    |>.toCountableRankOneBochnerOperatorIntegral
    |>.toNuclearDuhamelOperatorIntegral
  operatorBoundary :=
    data.toFullyCountableTerminalBoundaryFrontend.toGreenBoundaryData
  familyHeatTrace_eq := data.familyHeatTrace_eq
  familyCounterterm_eq := data.familyCounterterm_eq
  rawCountertermFinitePart_eq := data.rawCountertermFinitePart_eq
  shortTime_counterterm_eq := data.shortTime_counterterm_eq
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- Public logarithmic-derivative and Duhamel checkpoint generated by the
canonical operator-boundary assembly. -/
theorem product_throat_sphere_nuclear_basepoint_fully_countable_operator_boundary_frontend_gate
    (Index : Type*)
    (sphereData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data :
      ProductThroatSphereNuclearBasepointFullyCountableOperatorBoundaryFrontendData
        Index sphereData fold twist family nuclear) :
    (∀ parameter,
      ((data.shortFrontend.toRenormalizedOperatorIntegral.integratedOperator
          parameter - data.finitePartOperator parameter) +
        (data.longFrontend.toCountableRankOneBochnerOperatorIntegral
          |>.toCountableRankOneBochnerOperatorIntegral
          |>.toNuclearDuhamelOperatorIntegral).integratedOperator
          parameter) =
        data.logarithmicDerivativeOperator parameter) ∧
    (∀ parameter,
      -finitePartDerivative data.finiteCounterterm parameter +
          (∫ time in Set.Ioo (0 : Real) 1,
            (data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic).renormalizedDuhamelTrace
              parameter time) +
          (∫ time in Set.Ioi (1 : Real),
            extendedDuhamelTrace nuclear parameter time) =
        (data.toOperatorBoundaryFinitePartAssembly.operatorBoundary).logarithmicTrace
          parameter) ∧
    (∀ parameter,
      HasDerivAt
        (fun current ↦
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
        ((data.toOperatorBoundaryFinitePartAssembly.operatorBoundary).logarithmicTrace
          parameter) parameter) ∧
    (∀ parameter,
      Integrable (data.longFrontend.operatorIntegrand parameter)
        (volume.restrict (Set.Ioi (1 : Real)))) := by
  have hAssembly :=
    ProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssemblyData.product_throat_sphere_nuclear_basepoint_operator_boundary_finite_part_assembly_gate
        Index (atTop : Filter Real) sphereData family nuclear
          data.toOperatorBoundaryFinitePartAssembly
  exact ⟨hAssembly.2.1, hAssembly.2.2.1, hAssembly.2.2.2,
    data.longFrontend.operatorIntegrable⟩

end ProductThroatSphereNuclearBasepointFullyCountableOperatorBoundaryFrontendData

end
end P0EFTJanusProgramPProductThroatSphereNuclearBasepointFullyCountableOperatorBoundaryFrontend4D
end JanusFormal
