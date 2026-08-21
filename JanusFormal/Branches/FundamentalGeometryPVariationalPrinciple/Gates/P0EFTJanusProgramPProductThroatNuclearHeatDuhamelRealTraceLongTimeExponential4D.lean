import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D

/-!
# Real-trace generated ProductThroat long-time packet

The exact real trace normalization supplies continuity and integrability of
the long-time heat integrand.  The only remaining analytic inputs are
measurability and the product-trace estimate for the inserted Duhamel trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatNuclearHeatDuhamelRealTraceLongTimeExponential4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatNuclearHeatTrace4D
open P0EFTJanusProductThroatNuclearHeatTraceSmooth4D
open P0EFTJanusProductThroatPositiveHeatGapLongTime4D
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
open P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- The canonically weighted real product trace is integrable on `(1,∞)`. -/
theorem canonicalWeightedHeatTrace_integrable
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (identification : ReferenceProductThroatRealHeatTraceIdentificationData
      productData fold twist nuclear)
    (parameter : Real) :
    Integrable (fun time => time⁻¹ * extendedHeatTrace nuclear parameter time)
      (volume.restrict (Set.Ioi (1 : Real))) := by
  apply (integrableOn_longTimeExponentialBound
    (2 * productThroatLongTimeScale productData fold twist)
    (productThroatPositiveHeatGap_pos productData) 1).mono'
  · exact
      ((continuousOn_id.inv₀ (fun time hTime =>
          ne_of_gt (zero_lt_one.trans hTime))).mul
        ((identification.extendedHeatTrace_continuousOn_Ioi parameter).mono
          (Set.Ioi_subset_Ioi (by norm_num)))).aestronglyMeasurable
            measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    have hOne : 1 ≤ time := hTime.le
    have hPositive : 0 < time := zero_lt_one.trans hTime
    have hTraceNonnegative :
        0 ≤ productThroatNuclearHeatTraceReal productData time fold twist := by
      calc
        0 ≤ productThroatNuclearHeatTrace productData ⟨time, hPositive⟩
            fold twist := productThroatNuclearHeatTrace_nonnegative
              productData ⟨time, hPositive⟩ fold twist
        _ = productThroatNuclearHeatTraceReal productData time fold twist :=
          (productThroatNuclearHeatTraceReal_of_heatTime
            productData ⟨time, hPositive⟩ fold twist).symm
    rw [identification.extendedHeatTrace_eq_realProductTrace
      parameter time hPositive, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hPositive.le)
        (mul_nonneg (by norm_num) hTraceNonnegative))]
    calc
      time⁻¹ *
          (2 * productThroatNuclearHeatTraceReal productData time fold twist) ≤
          2 * productThroatNuclearHeatTraceReal productData time fold twist := by
        exact mul_le_of_le_one_left
          (mul_nonneg (by norm_num) hTraceNonnegative)
          (inv_le_one_of_one_le₀ hOne)
      _ ≤ 2 * longTimeExponentialBound
          (productThroatLongTimeScale productData fold twist)
          (productThroatPositiveHeatGap productData) time :=
        mul_le_mul_of_nonneg_left
          (calc
            productThroatNuclearHeatTraceReal productData time fold twist =
                productThroatNuclearHeatTrace productData ⟨time, hPositive⟩
                  fold twist :=
              productThroatNuclearHeatTraceReal_of_heatTime
                productData ⟨time, hPositive⟩ fold twist
            _ ≤ longTimeExponentialBound
                (productThroatLongTimeScale productData fold twist)
                (productThroatPositiveHeatGap productData) time :=
              productThroatNuclearHeatTrace_le_longTimeExponentialBound
                productData ⟨time, hPositive⟩ hOne fold twist)
          (by norm_num)
      _ = longTimeExponentialBound
          (2 * productThroatLongTimeScale productData fold twist)
          (productThroatPositiveHeatGap productData) time := by
        unfold longTimeExponentialBound
        ring

/-- Minimal long-time data after generating all scalar heat regularity from
the real product trace. -/
structure ProductThroatNuclearHeatDuhamelRealTraceLongTimeExponentialData
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  realHeatTraceIdentification :
    ReferenceProductThroatRealHeatTraceIdentificationData productData fold
      twist nuclear
  parameterDomain : Real → Set Real
  parameterDomain_mem_nhds : ∀ parameter,
    parameterDomain parameter ∈ 𝓝 parameter
  duhamel_aeStronglyMeasurable : ∀ parameter,
    AEStronglyMeasurable (extendedDuhamelTrace nuclear parameter)
      (volume.restrict (Set.Ioi (1 : Real)))
  insertionScale : Real → Real
  insertionScale_nonnegative : ∀ parameter, 0 ≤ insertionScale parameter
  duhamelTrace_norm_le : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioi (1 : Real)),
      ∀ current ∈ parameterDomain parameter,
        ‖extendedDuhamelTrace nuclear current time‖ ≤
          insertionScale parameter *
            extendedProductThroatNuclearHeatTrace productData fold twist time

namespace ProductThroatNuclearHeatDuhamelRealTraceLongTimeExponentialData

/-- Generate the complete product-spectral long-time packet. -/
def toLongTimeExponential
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatNuclearHeatDuhamelRealTraceLongTimeExponentialData
      productData fold twist nuclear) :
    ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      productData fold twist nuclear 1 where
  start_ge_one := le_rfl
  weight := fun time => time⁻¹
  weight_mul_time_eq_one := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    exact inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans hTime))
  parameterDomain := data.parameterDomain
  parameterDomain_mem_nhds := data.parameterDomain_mem_nhds
  integrand_aeStronglyMeasurable := by
    intro parameter
    filter_upwards [] with current
    exact
      ((continuousOn_id.inv₀ (fun time hTime =>
          ne_of_gt (zero_lt_one.trans hTime))).mul
        ((data.realHeatTraceIdentification.extendedHeatTrace_continuousOn_Ioi
          current).mono (Set.Ioi_subset_Ioi (by norm_num)))).aestronglyMeasurable
            measurableSet_Ioi
  integrand_integrable :=
    canonicalWeightedHeatTrace_integrable data.realHeatTraceIdentification
  derivative_aeStronglyMeasurable := by
    intro parameter
    refine (data.duhamel_aeStronglyMeasurable parameter).neg.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    rw [extendedHeatTraceDerivative_eq]
    have hTimePositive : 0 < time := zero_lt_one.trans hTime
    change -extendedDuhamelTrace nuclear parameter time =
      time⁻¹ * (-time * extendedDuhamelTrace nuclear parameter time)
    calc
      -extendedDuhamelTrace nuclear parameter time =
          -(time⁻¹ * time) * extendedDuhamelTrace nuclear parameter time := by
        rw [inv_mul_cancel₀ (ne_of_gt hTimePositive)]
        ring
      _ = time⁻¹ * (-time * extendedDuhamelTrace nuclear parameter time) := by
        ring
  insertionScale := data.insertionScale
  insertionScale_nonnegative := data.insertionScale_nonnegative
  duhamelTrace_norm_le := data.duhamelTrace_norm_le

/-- Public real-trace-generated long-time checkpoint. -/
theorem product_throat_nuclear_heat_duhamel_real_trace_long_time_gate
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ProductThroatNuclearHeatDuhamelRealTraceLongTimeExponentialData
      productData fold twist nuclear) :
    (∀ parameter,
      Integrable
        (fun time => time⁻¹ * extendedHeatTrace nuclear parameter time)
        (volume.restrict (Set.Ioi (1 : Real)))) ∧
    (∀ parameter,
      data.toLongTimeExponential.toLongTimeExponentialDominatedWeightedIntegral.rate
          parameter = productThroatPositiveHeatGap productData) := by
  exact ⟨canonicalWeightedHeatTrace_integrable
      data.realHeatTraceIdentification,
    fun _ => rfl⟩

end ProductThroatNuclearHeatDuhamelRealTraceLongTimeExponentialData

end
end P0EFTJanusProgramPProductThroatNuclearHeatDuhamelRealTraceLongTimeExponential4D
end JanusFormal
