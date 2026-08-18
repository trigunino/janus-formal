import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D

/-!
# Reduced-sphere nuclear long-time Duhamel packet

The fixed reduced-sphere scalar heat trace is logarithmically integrable on
`(1, ∞)`.  Its parameter derivative vanishes, and the scalar Duhamel formula
then forces the extended Duhamel trace to vanish on this region.  These facts
construct the complete nuclear weighted-integral packet with weight `t⁻¹`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelWeightedIntegralData
open P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

namespace ProductThroatSphereNuclearShortTimeQuadraticData

/-- Constancy of the scalar heat trace forces the extended Duhamel trace to
vanish at every strictly positive time. -/
theorem extendedDuhamelTrace_eq_zero
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter time : Real) (hTime : 0 < time) :
    extendedDuhamelTrace nuclear parameter time = 0 := by
  have hProduct := extendedHeatTraceDerivative_eq nuclear parameter time
  rw [data.extendedHeatTraceDerivative_eq_zero] at hProduct
  exact (mul_eq_zero.mp hProduct.symm).resolve_left
    (neg_ne_zero.mpr (ne_of_gt hTime))

/-- The fixed reduced-sphere heat family gives a logarithmically weighted
nuclear Duhamel packet on `(1, ∞)`. -/
def toLongTimeWeightedIntegral
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear) :
    NuclearHeatDuhamelWeightedIntegralData nuclear (Set.Ioi (1 : Real)) where
  weight := fun time => time⁻¹
  weight_mul_time_eq_one := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    exact inv_mul_cancel₀ (ne_of_gt ((by norm_num : (0 : Real) < 1).trans hTime))
  hasDerivAt_integral := by
    intro parameter
    have hFunction :
        (fun current =>
          ∫ time in Set.Ioi (1 : Real),
            time⁻¹ * extendedHeatTrace nuclear current time) =
          fun _ =>
            ∫ time in Set.Ioi (1 : Real),
              time⁻¹ * positiveTimeTraceExtension
                (dimensionlessReducedSphereHeatTrace sphereData) time := by
      funext current
      apply integral_congr_ae
      filter_upwards [] with time
      rw [data.extendedHeatTrace_eq]
    have hDerivative :
        (∫ time in Set.Ioi (1 : Real),
          time⁻¹ * extendedHeatTraceDerivative nuclear parameter time) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [] with time
      rw [data.extendedHeatTraceDerivative_eq_zero]
      exact mul_zero _
    rw [hFunction, hDerivative]
    exact hasDerivAt_const parameter _

/-- The long-time weighted heat kernel is integrable. -/
theorem weightedHeatTrace_longTimeIntegrable
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter : Real) :
    Integrable
      (fun time =>
        (toLongTimeWeightedIntegral data).weight time *
          extendedHeatTrace nuclear parameter time)
      (volume.restrict (Set.Ioi (1 : Real))) := by
  change Integrable
    (fun time => time⁻¹ * extendedHeatTrace nuclear parameter time)
    (volume.restrict (Set.Ioi (1 : Real)))
  refine (positiveTimeReducedSphere_longTimeIntegrable sphereData).congr ?_
  filter_upwards [] with time
  rw [data.extendedHeatTrace_eq]
  simp only [div_eq_mul_inv, mul_comm]

/-- The extended Duhamel trace is integrable on the long-time region. -/
theorem extendedDuhamelTrace_longTimeIntegrable
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter : Real) :
    Integrable (extendedDuhamelTrace nuclear parameter)
      (volume.restrict (Set.Ioi (1 : Real))) := by
  refine (integrable_zero Real Real
    (volume.restrict (Set.Ioi (1 : Real)))).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact (extendedDuhamelTrace_eq_zero data parameter time
    ((by norm_num : (0 : Real) < 1).trans hTime)).symm

/-- The generated contribution is exactly the certified spherical long-time
integral. -/
theorem contribution_eq
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter : Real) :
    (toLongTimeWeightedIntegral data).toWeightedHeatTraceVariation.contribution
        parameter =
      relativeHeatLongTimeIntegral (reducedSphereFinitePartData sphereData) := by
  change
    (∫ time in Set.Ioi (1 : Real),
      time⁻¹ * extendedHeatTrace nuclear parameter time) =
      ∫ time in Set.Ioi (1 : Real),
        positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace sphereData) time / time
  apply integral_congr_ae
  filter_upwards [] with time
  rw [data.extendedHeatTrace_eq]
  simp only [div_eq_mul_inv, mul_comm]

/-- Public reduced-sphere nuclear long-time checkpoint. -/
theorem product_throat_sphere_nuclear_long_time_weighted_integral_gate
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear) :
    let longTime := toLongTimeWeightedIntegral data
    (∀ parameter, Integrable
      (fun time => longTime.weight time *
        extendedHeatTrace nuclear parameter time)
      (volume.restrict (Set.Ioi (1 : Real)))) ∧
    (∀ parameter, Integrable
      (extendedDuhamelTrace nuclear parameter)
      (volume.restrict (Set.Ioi (1 : Real)))) ∧
    (∀ parameter, HasDerivAt
      longTime.toWeightedHeatTraceVariation.contribution
      (-(∫ time in Set.Ioi (1 : Real),
        extendedDuhamelTrace nuclear parameter time)) parameter) ∧
    (∀ parameter,
      longTime.toWeightedHeatTraceVariation.contribution parameter =
        relativeHeatLongTimeIntegral
          (reducedSphereFinitePartData sphereData)) := by
  dsimp only
  exact ⟨weightedHeatTrace_longTimeIntegrable data,
    extendedDuhamelTrace_longTimeIntegrable data,
    (toLongTimeWeightedIntegral data).toDuhamelWeightedHeatTraceVariation.hasDerivAt_contribution,
    contribution_eq data⟩

end ProductThroatSphereNuclearShortTimeQuadraticData

end
end P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelLongTimeWeightedIntegral4D
end JanusFormal
