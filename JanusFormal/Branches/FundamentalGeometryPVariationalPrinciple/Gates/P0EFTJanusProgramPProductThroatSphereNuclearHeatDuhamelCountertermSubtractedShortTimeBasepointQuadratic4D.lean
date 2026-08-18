import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereCountertermFinitePartLimit4D

/-!
# Product-throat sphere basepoint for a non-isospectral nuclear family

This module anchors a genuinely parameter-dependent nuclear heat family at
the reduced product-throat sphere.  The proved spherical short-time remainder
is transported from that basepoint by a uniform quadratic derivative bound.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D.NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D.NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
open P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatSphereCountertermFinitePartLimit4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Minimal compatibility between a non-isospectral nuclear family and the
reduced-sphere remainder at one parameter. -/
structure ProductThroatSphereNuclearShortTimeBasepointQuadraticData
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  basepoint : Real
  counterterm : Real → Real → Real
  countertermDerivative : Real → Real → Real
  counterterm_hasDerivAt : ∀ parameter time,
    HasDerivAt (fun current => counterterm current time)
      (countertermDerivative parameter time) parameter
  basepoint_extendedHeatTrace_eq :
    ∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1),
      extendedHeatTrace nuclear basepoint time =
        positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace sphereData) time
  basepoint_counterterm_eq :
    ∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1),
      counterterm basepoint time = reducedSphereCounterterm sphereData time
  integrand_aeStronglyMeasurable : ∀ parameter,
    AEStronglyMeasurable
      (fun time => time⁻¹ *
        (extendedHeatTrace nuclear parameter time - counterterm parameter time))
      (volume.restrict (Set.Ioo (0 : Real) 1))
  scale : Real
  derivative_norm_le :
    ∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1), ∀ parameter,
      ‖time⁻¹ *
        (extendedHeatTraceDerivative nuclear parameter time -
          countertermDerivative parameter time)‖ ≤
        shortTimeQuadraticBound scale time

namespace ProductThroatSphereNuclearShortTimeBasepointQuadraticData

/-- The actual family remainder is integrable at the spherical basepoint. -/
theorem basepoint_integrable
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatSphereNuclearShortTimeBasepointQuadraticData
        sphereData nuclear) :
    Integrable
      (fun time => time⁻¹ *
        (extendedHeatTrace nuclear data.basepoint time -
          data.counterterm data.basepoint time))
      (volume.restrict (Set.Ioo (0 : Real) 1)) := by
  refine (positiveTimeReducedSphere_shortTimeIntegrable_Ioo sphereData).congr ?_
  filter_upwards [data.basepoint_extendedHeatTrace_eq,
    data.basepoint_counterterm_eq] with time hHeat hCounterterm
  rw [hHeat, hCounterterm]

/-- Adapter to the generic basepoint-propagation packet. -/
def toBasepointQuadratic
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatSphereNuclearShortTimeBasepointQuadraticData
        sphereData nuclear) :
    NuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadraticData
      nuclear 1 where
  weight := fun time => time⁻¹
  weight_mul_time_eq_one := shortTimeInvWeight_mul_time_eq_one
  counterterm := data.counterterm
  countertermDerivative := data.countertermDerivative
  counterterm_hasDerivAt := data.counterterm_hasDerivAt
  integrand_aeStronglyMeasurable := data.integrand_aeStronglyMeasurable
  basepoint := data.basepoint
  basepoint_integrable := data.basepoint_integrable
  scale := data.scale
  derivative_norm_le := data.derivative_norm_le

/-- Direct complete short-time packet for the non-isospectral family. -/
def toCountertermSubtractedShortTimeQuadratic
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatSphereNuclearShortTimeBasepointQuadraticData
        sphereData nuclear) :
    NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData nuclear 1 :=
  data.toBasepointQuadratic.toCountertermSubtractedShortTimeQuadratic

/-- The transported packet retains the already certified spherical
short-time finite part at its basepoint. -/
theorem basepoint_contribution_eq
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data :
      ProductThroatSphereNuclearShortTimeBasepointQuadraticData
        sphereData nuclear) :
    data.toCountertermSubtractedShortTimeQuadratic.toWeightedHeatTraceVariation.contribution
        data.basepoint =
      relativeHeatShortTimeFinitePart
        (reducedSphereFinitePartData sphereData) := by
  change
    (∫ time in Set.Ioo (0 : Real) 1,
      time⁻¹ *
        (extendedHeatTrace nuclear data.basepoint time -
          data.counterterm data.basepoint time)) = _
  rw [integral_congr_ae (by
    filter_upwards [data.basepoint_extendedHeatTrace_eq,
      data.basepoint_counterterm_eq] with time hHeat hCounterterm
    rw [hHeat, hCounterterm])]
  exact positiveTimeReducedSphere_shortTimeIntegral_Ioo_eq sphereData

/-- Public non-isospectral spherical-basepoint checkpoint. -/
theorem product_throat_sphere_nuclear_short_time_basepoint_quadratic_gate
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data :
      ProductThroatSphereNuclearShortTimeBasepointQuadraticData
        sphereData nuclear) :
    let shortTime := data.toCountertermSubtractedShortTimeQuadratic
    (∀ parameter,
      ∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1),
        ‖data.toBasepointQuadratic.weightedRemainder parameter time -
          data.toBasepointQuadratic.weightedRemainder data.basepoint time‖ ≤
        shortTimeQuadraticBound data.scale time *
          ‖parameter - data.basepoint‖) ∧
    (∀ parameter, Integrable
      (fun time => shortTime.weight time *
        shortTime.subtractedHeatTrace parameter time)
      (volume.restrict (Set.Ioo (0 : Real) 1))) ∧
    (∀ parameter, Integrable
      (fun time => shortTime.weight time *
        shortTime.subtractedHeatTraceDerivative parameter time)
      (volume.restrict (Set.Ioo (0 : Real) 1))) ∧
    (∀ parameter, Integrable
      (shortTime.renormalizedDuhamelTrace parameter)
      (volume.restrict (Set.Ioo (0 : Real) 1))) ∧
    (∀ parameter, HasDerivAt
      (fun current =>
        ∫ time in Set.Ioo (0 : Real) 1,
          shortTime.weight time *
            shortTime.subtractedHeatTrace current time)
      (-∫ time in Set.Ioo (0 : Real) 1,
        shortTime.renormalizedDuhamelTrace parameter time) parameter) ∧
    shortTime.toWeightedHeatTraceVariation.contribution data.basepoint =
      relativeHeatShortTimeFinitePart
        (reducedSphereFinitePartData sphereData) := by
  dsimp only
  rcases
      nuclear_heat_duhamel_counterterm_subtracted_short_time_basepoint_quadratic_gate
        nuclear 1 data.toBasepointQuadratic with
    ⟨hDifference, hValue, hDerivative, hRenormalized, hVariation⟩
  exact
    ⟨hDifference, hValue, hDerivative, hRenormalized, hVariation,
      data.basepoint_contribution_eq⟩

end ProductThroatSphereNuclearShortTimeBasepointQuadraticData

end
end P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeBasepointQuadratic4D
end JanusFormal
