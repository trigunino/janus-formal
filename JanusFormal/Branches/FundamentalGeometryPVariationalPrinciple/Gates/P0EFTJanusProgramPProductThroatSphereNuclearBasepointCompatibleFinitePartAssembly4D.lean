import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssembly4D

/-!
# Spherical-basepoint compatible finite-part assembly

The short-time remainder of a parameter-dependent nuclear family is anchored
at the reduced product-throat sphere and propagated by its uniformly
quadratic parameter derivative.  Exact scalar compatibility then inserts the
resulting packet into the canonical finite-part Duhamel assembly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereNuclearBasepointCompatibleFinitePartAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D.ProductThroatSphereNuclearShortTimeBasepointQuadraticData
open P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssembly4D
open P0EFTJanusProgramPReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssembly4D.ReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssemblyData
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

universe u v

variable {Index : Type*}
variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Data reducing the complete compatible assembly to a spherical basepoint
and a uniform quadratic derivative estimate at short time. -/
structure ProductThroatSphereNuclearBasepointCompatibleFinitePartAssemblyData
    (Index : Type*)
    (sphereData : ProductThroatSpectralData)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  finiteCounterterm : FiniteHeatCountertermFinitePartVariationData Index
  shortTimeBasepoint :
    ProductThroatSphereNuclearShortTimeBasepointQuadraticData sphereData nuclear
  longTime : NuclearHeatDuhamelWeightedIntegralData nuclear
    (Set.Ioi (1 : Real))
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
  logarithmicTrace : Real → Real
  duhamel_integral_identity : ∀ parameter,
    -finitePartDerivative finiteCounterterm parameter +
        (∫ time in Set.Ioo (0 : Real) 1,
          (shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic).renormalizedDuhamelTrace
            parameter time) +
        (∫ time in Set.Ioi (1 : Real),
          extendedDuhamelTrace nuclear parameter time) =
      logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ProductThroatSphereNuclearBasepointCompatibleFinitePartAssemblyData

/-- Convert the spherical-basepoint packet to the exact compatible assembly. -/
def toCompatibleFinitePartAssembly
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearBasepointCompatibleFinitePartAssemblyData
      Index sphereData family nuclear) :
    ReferenceHeatDuhamelFiniteCountertermCompatibleFinitePartAssemblyData
      Index family nuclear where
  finiteCounterterm := data.finiteCounterterm
  shortTime :=
    data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic
  longTime := data.longTime
  familyHeatTrace_eq := data.familyHeatTrace_eq
  familyCounterterm_eq := data.familyCounterterm_eq
  rawCountertermFinitePart_eq := data.rawCountertermFinitePart_eq
  shortTime_counterterm_eq := data.shortTime_counterterm_eq
  logarithmicTrace := data.logarithmicTrace
  duhamel_integral_identity := data.duhamel_integral_identity
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The finite-part short-time contribution at the basepoint is exactly the
already proved reduced-sphere contribution. -/
theorem familyBasepointShortTime_eq_sphere
    {sphereData : ProductThroatSpectralData}
    {family : RelativeHeatMellinZetaFamilyData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearBasepointCompatibleFinitePartAssemblyData
      Index sphereData family nuclear) :
    relativeHeatShortTimeFinitePart
        (family.finitePartFamily.finitePart
          data.shortTimeBasepoint.basepoint) =
      relativeHeatShortTimeFinitePart
        (reducedSphereFinitePartData sphereData) := by
  rw [data.toCompatibleFinitePartAssembly.toReferenceHeatDuhamelFiniteCountertermCompatibilityData.shortTimeContribution_eq]
  exact data.shortTimeBasepoint.basepoint_contribution_eq

/-- Public spherical-basepoint assembly checkpoint. -/
theorem product_throat_sphere_nuclear_basepoint_compatible_finite_part_assembly_gate
    (Index : Type*)
    (sphereData : ProductThroatSpectralData)
    (family : RelativeHeatMellinZetaFamilyData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearBasepointCompatibleFinitePartAssemblyData
      Index sphereData family nuclear) :
    (relativeHeatShortTimeFinitePart
        (family.finitePartFamily.finitePart
          data.shortTimeBasepoint.basepoint) =
      relativeHeatShortTimeFinitePart
        (reducedSphereFinitePartData sphereData)) ∧
    (∀ parameter,
      Integrable
        (fun time =>
          (data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic).weight
              time *
            (data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic).subtractedHeatTrace
              parameter time)
        (volume.restrict (Set.Ioo (0 : Real) 1))) ∧
    (∀ parameter,
      HasDerivAt
        (fun current ↦
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
        (data.logarithmicTrace parameter) parameter) ∧
    (∀ parameter,
      family.finitePartFamily.logDerivative parameter =
        -finitePartDerivative data.finiteCounterterm parameter +
          (∫ time in Set.Ioo (0 : Real) 1,
            (data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic).renormalizedDuhamelTrace
              parameter time) +
          (∫ time in Set.Ioi (1 : Real),
            extendedDuhamelTrace nuclear parameter time)) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) := by
  let shortTime :=
    data.shortTimeBasepoint.toCountertermSubtractedShortTimeQuadratic
  rcases
      reference_heat_duhamel_finite_counterterm_compatible_finite_part_assembly_gate
        Index family nuclear data.toCompatibleFinitePartAssembly with
    ⟨_, _, _, hDerivative, _, hNamed, hConnection⟩
  exact ⟨data.familyBasepointShortTime_eq_sphere,
    fun parameter ↦ shortTime.integrand_integrable parameter,
    hDerivative, hNamed, hConnection⟩

end ProductThroatSphereNuclearBasepointCompatibleFinitePartAssemblyData

end
end P0EFTJanusProgramPProductThroatSphereNuclearBasepointCompatibleFinitePartAssembly4D
end JanusFormal
