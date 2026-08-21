import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceProductThroatHeatOperatorIdentification4D

/-!
# Product-throat Duhamel domination through the heat trace

The direct insertion/product-trace estimate is generated from an insertion
bound relative to the reference heat trace and a separate comparison of that
heat trace with the concrete product spectrum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatNuclearHeatDuhamelRelativeTraceLongTimeExponential4D

set_option autoImplicit false
noncomputable section

open Filter Set MeasureTheory
open scoped Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatPositiveHeatGapLongTime4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D

universe e i

variable {E : Type e}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Long-time input split into an operator insertion estimate and an
independent product-spectral heat-trace comparison. -/
structure ProductThroatNuclearHeatDuhamelRelativeTraceLongTimeExponentialData
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (start : Real) where
  start_ge_one : 1 ≤ start
  weight : Real → Real
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict (Set.Ioi start), weight time * time = 1
  parameterDomain : Real → Set Real
  parameterDomain_mem_nhds : ∀ parameter,
    parameterDomain parameter ∈ 𝓝 parameter
  integrand_aeStronglyMeasurable : ∀ parameter,
    ∀ᶠ current in 𝓝 parameter,
      AEStronglyMeasurable
        (fun time => weight time * extendedHeatTrace nuclear current time)
        (volume.restrict (Set.Ioi start))
  integrand_integrable : ∀ parameter,
    Integrable
      (fun time => weight time * extendedHeatTrace nuclear parameter time)
      (volume.restrict (Set.Ioi start))
  derivative_aeStronglyMeasurable : ∀ parameter,
    AEStronglyMeasurable
      (fun time => weight time * extendedHeatTraceDerivative nuclear parameter time)
      (volume.restrict (Set.Ioi start))
  insertionScale : Real → Real
  insertionScale_nonnegative : ∀ parameter, 0 ≤ insertionScale parameter
  duhamelTrace_norm_le_heatTrace : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioi start),
      ∀ current ∈ parameterDomain parameter,
        ‖extendedDuhamelTrace nuclear current time‖ ≤
          insertionScale parameter * ‖extendedHeatTrace nuclear current time‖
  heatTrace_norm_le_productTrace : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioi start),
      ∀ current ∈ parameterDomain parameter,
        ‖extendedHeatTrace nuclear current time‖ ≤
          extendedProductThroatNuclearHeatTrace productData fold twist time

namespace ProductThroatNuclearHeatDuhamelRelativeTraceLongTimeExponentialData

/-- Assemble the direct product-trace domination packet. -/
def toProductThroatNuclearHeatDuhamelLongTimeExponential
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelRelativeTraceLongTimeExponentialData
      productData fold twist nuclear start) :
    ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      productData fold twist nuclear start where
  start_ge_one := data.start_ge_one
  weight := data.weight
  weight_mul_time_eq_one := data.weight_mul_time_eq_one
  parameterDomain := data.parameterDomain
  parameterDomain_mem_nhds := data.parameterDomain_mem_nhds
  integrand_aeStronglyMeasurable := data.integrand_aeStronglyMeasurable
  integrand_integrable := data.integrand_integrable
  derivative_aeStronglyMeasurable := data.derivative_aeStronglyMeasurable
  insertionScale := data.insertionScale
  insertionScale_nonnegative := data.insertionScale_nonnegative
  duhamelTrace_norm_le := by
    intro parameter
    filter_upwards [data.duhamelTrace_norm_le_heatTrace parameter,
      data.heatTrace_norm_le_productTrace parameter] with time hDuhamel hHeat
    intro current hCurrent
    exact (hDuhamel current hCurrent).trans
      (mul_le_mul_of_nonneg_left (hHeat current hCurrent)
        (data.insertionScale_nonnegative parameter))

/-- Derived direct insertion estimate. -/
theorem duhamelTrace_norm_le_productTrace
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelRelativeTraceLongTimeExponentialData
      productData fold twist nuclear start)
    (parameter : Real) :
    ∀ᵐ time ∂volume.restrict (Set.Ioi start),
      ∀ current ∈ data.parameterDomain parameter,
        ‖extendedDuhamelTrace nuclear current time‖ ≤
          data.insertionScale parameter *
            extendedProductThroatNuclearHeatTrace productData fold twist time :=
  data.toProductThroatNuclearHeatDuhamelLongTimeExponential.duhamelTrace_norm_le
    parameter

/-- Public relative-trace domination checkpoint. -/
theorem product_throat_nuclear_heat_duhamel_relative_trace_long_time_gate
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelRelativeTraceLongTimeExponentialData
      productData fold twist nuclear start) :
    (∀ parameter,
      ∀ᵐ time ∂volume.restrict (Set.Ioi start),
        ∀ current ∈ data.parameterDomain parameter,
          ‖extendedDuhamelTrace nuclear current time‖ ≤
            data.insertionScale parameter *
              extendedProductThroatNuclearHeatTrace productData fold twist time) ∧
    (∀ parameter, 0 ≤ data.insertionScale parameter) :=
  ⟨data.duhamelTrace_norm_le_productTrace,
    data.insertionScale_nonnegative⟩

end ProductThroatNuclearHeatDuhamelRelativeTraceLongTimeExponentialData

end
end P0EFTJanusProgramPProductThroatNuclearHeatDuhamelRelativeTraceLongTimeExponential4D
end JanusFormal
