import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D

/-!
# Reduced-sphere nuclear short-time packet

An intrinsic nuclear family whose scalar heat trace is the fixed reduced
product-throat sphere trace inherits the proved spherical UV subtraction and
Euler--Maclaurin majorant.  Its scalar parameter derivative vanishes, so the
quadratic derivative bound is generated with scale zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D.NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
open P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatSphereCountertermFinitePartLimit4D
open P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- The sole spectral compatibility needed for the fixed reduced-sphere
reference family. -/
structure ProductThroatSphereNuclearShortTimeQuadraticData
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  heatTrace_eq : ∀ parameter time,
    nuclear.heatTrace parameter time =
      dimensionlessReducedSphereHeatTrace sphereData time

namespace ProductThroatSphereNuclearShortTimeQuadraticData

theorem extendedHeatTrace_eq
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter time : Real) :
    extendedHeatTrace nuclear parameter time =
      positiveTimeTraceExtension
        (dimensionlessReducedSphereHeatTrace sphereData) time := by
  by_cases hTime : 0 < time
  · simp [extendedHeatTrace, positiveTimeTraceExtension, hTime,
      data.heatTrace_eq]
  · simp [extendedHeatTrace, positiveTimeTraceExtension, hTime]

/-- Constancy of the scalar heat trace forces its declared parameter
derivative to vanish. -/
theorem extendedHeatTraceDerivative_eq_zero
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter time : Real) :
    extendedHeatTraceDerivative nuclear parameter time = 0 := by
  have hNuclear := extendedHeatTrace_hasDerivAt nuclear parameter time
  have hConstant :
      HasDerivAt
        (fun _ : Real => positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace sphereData) time)
        0 parameter :=
    hasDerivAt_const parameter _
  have hFunctions :
      (fun current => extendedHeatTrace nuclear current time) =
        (fun _ : Real => positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace sphereData) time) := by
    funext current
    exact data.extendedHeatTrace_eq current time
  rw [hFunctions] at hNuclear
  exact hNuclear.unique hConstant

/-- The logarithmically weighted reduced-sphere remainder is bounded by the
proved Euler--Maclaurin majorant. -/
theorem weightedRemainder_norm_le
    {sphereData : ProductThroatSpectralData}
    {time : Real} (hTime : time ∈ Set.Ioo (0 : Real) 1) :
    ‖time⁻¹ *
        (positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace sphereData) time -
          reducedSphereCounterterm sphereData time)‖ ≤
      sphereShortTimeMajorant sphereData time := by
  have hBound := sphereShortTimeMajorant_bound sphereData
    (show time ∈ Set.Ioc (0 : Real) 1 from ⟨hTime.1, hTime.2.le⟩)
  simpa [positiveTimeTraceExtension, hTime.1,
    dimensionlessReducedSphereHeatTrace, dimensionlessSphereHeatTrace,
    reducedSphereCounterterm, div_eq_mul_inv, mul_comm] using hBound

/-- Complete counterterm-subtracted short-time packet on `(0,1)`. -/
def toCountertermSubtractedShortTimeQuadratic
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear) :
    NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData nuclear 1 where
  weight := fun time => time⁻¹
  weight_mul_time_eq_one := shortTimeInvWeight_mul_time_eq_one
  counterterm := fun _ time => reducedSphereCounterterm sphereData time
  countertermDerivative := fun _ _ => 0
  counterterm_hasDerivAt := by
    intro parameter time
    exact hasDerivAt_const parameter _
  parameterDomain := fun _ => Set.univ
  parameterDomain_mem_nhds := fun _ => Filter.univ_mem
  integrand_aeStronglyMeasurable := by
    intro parameter
    filter_upwards [] with current
    simpa only [data.extendedHeatTrace_eq] using
      (positiveTimeReducedSphere_shortTimeIntegrable_Ioo sphereData).aestronglyMeasurable
  integrandMajorant := fun _ => sphereShortTimeMajorant sphereData
  integrandMajorant_integrable := by
    intro parameter
    exact (sphereShortTimeMajorant_integrableOn sphereData).mono_set
      (fun _ hTime => ⟨hTime.1, hTime.2.le⟩)
  integrand_norm_le := by
    intro parameter
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    rw [data.extendedHeatTrace_eq]
    exact weightedRemainder_norm_le hTime
  scale := fun _ => 0
  derivative_norm_le := by
    intro parameter
    filter_upwards [] with time
    intro current hCurrent
    rw [data.extendedHeatTraceDerivative_eq_zero]
    simp [shortTimeQuadraticBound]

/-- The generated density is the density of the finite spherical
counterterm packet. -/
theorem counterterm_eq_finiteCounterterm
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter time : Real) :
    data.toCountertermSubtractedShortTimeQuadratic.counterterm parameter time =
      P0EFTJanusProgramPFiniteHeatCountertermVariation4D.counterterm
        (reducedSphereCountertermVariation sphereData) parameter time := by
  exact (reducedSphereCountertermVariation_counterterm_eq
    sphereData parameter time).symm

/-- The weighted contribution is exactly the already certified spherical
short-time finite part. -/
theorem contribution_eq
    {sphereData : ProductThroatSpectralData}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear)
    (parameter : Real) :
    data.toCountertermSubtractedShortTimeQuadratic.toWeightedHeatTraceVariation.contribution
        parameter =
      relativeHeatShortTimeFinitePart
        (reducedSphereFinitePartData sphereData) := by
  change
    (∫ time in Set.Ioo (0 : Real) 1,
      time⁻¹ *
        (extendedHeatTrace nuclear parameter time -
          reducedSphereCounterterm sphereData time)) = _
  simpa only [data.extendedHeatTrace_eq] using
    positiveTimeReducedSphere_shortTimeIntegral_Ioo_eq sphereData

/-- Public reduced-sphere nuclear short-time checkpoint. -/
theorem product_throat_sphere_nuclear_short_time_quadratic_gate
    (sphereData : ProductThroatSpectralData)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (data : ProductThroatSphereNuclearShortTimeQuadraticData sphereData nuclear) :
    let shortTime := data.toCountertermSubtractedShortTimeQuadratic
    (∀ parameter, Integrable
      (fun time => shortTime.weight time *
        shortTime.subtractedHeatTrace parameter time)
      (volume.restrict (Set.Ioo 0 1))) ∧
    (∀ parameter, Integrable
      (fun time => shortTime.weight time *
        shortTime.subtractedHeatTraceDerivative parameter time)
      (volume.restrict (Set.Ioo 0 1))) ∧
    (∀ parameter, Integrable
      (shortTime.renormalizedDuhamelTrace parameter)
      (volume.restrict (Set.Ioo 0 1))) ∧
    (∀ parameter, HasDerivAt
      (fun current =>
        ∫ time in Set.Ioo 0 1,
          shortTime.weight time *
            shortTime.subtractedHeatTrace current time)
      (-(∫ time in Set.Ioo 0 1,
        shortTime.renormalizedDuhamelTrace parameter time)) parameter) ∧
    (∀ parameter,
      shortTime.toWeightedHeatTraceVariation.contribution parameter =
        relativeHeatShortTimeFinitePart
          (reducedSphereFinitePartData sphereData)) := by
  dsimp only
  rcases nuclear_heat_duhamel_counterterm_subtracted_short_time_quadratic_gate
      nuclear 1 data.toCountertermSubtractedShortTimeQuadratic with
    ⟨hValue, hDerivative, hRenormalized, hVariation⟩
  exact
    ⟨hValue, hDerivative, hRenormalized, hVariation, data.contribution_eq⟩

end ProductThroatSphereNuclearShortTimeQuadraticData

end
end P0EFTJanusProgramPProductThroatSphereNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
end JanusFormal
