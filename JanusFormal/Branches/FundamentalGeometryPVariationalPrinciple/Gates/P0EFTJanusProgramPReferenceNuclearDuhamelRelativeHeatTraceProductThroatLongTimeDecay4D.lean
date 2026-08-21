import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelProductThroatLongTimeDecay4D

/-!
# Product-throat terminal decay through a reference heat trace

The terminal primitive estimate is split into a bound by a reference heat
trace and a separate comparison of that trace with the product spectrum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelRelativeHeatTraceProductThroatLongTimeDecay4D

set_option autoImplicit false
noncomputable section

open Filter Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatPositiveHeatGapLongTime4D
open P0EFTJanusProgramPReferenceNuclearDuhamelProductThroatLongTimeDecay4D

variable {Cutoff E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Terminal boundary data whose product estimate is factored through a
reference heat trace. -/
structure ReferenceNuclearDuhamelRelativeHeatTraceProductThroatLongTimeDecayData
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (cutoffFilter : Filter Cutoff) [NeBot cutoffFilter]
    (integratedOperator matchingOperator : E) where
  partialIntegral : Cutoff → E
  terminalPrimitive : Cutoff → E
  cutoffTime : Cutoff → Real
  referenceHeatTrace : Cutoff → Real
  boundaryScale : Real
  boundaryScale_nonnegative : 0 ≤ boundaryScale
  cutoffTime_tendsto_atTop : Tendsto cutoffTime cutoffFilter atTop
  terminalPrimitive_norm_le_referenceHeatTrace : ∀ᶠ cutoff in cutoffFilter,
    ‖terminalPrimitive cutoff‖ ≤
      boundaryScale * ‖referenceHeatTrace cutoff‖
  referenceHeatTrace_norm_le_productTrace : ∀ᶠ cutoff in cutoffFilter,
    ‖referenceHeatTrace cutoff‖ ≤
      extendedProductThroatNuclearHeatTrace productData fold twist
        (cutoffTime cutoff)
  partialIntegral_tendsto :
    Tendsto partialIntegral cutoffFilter (𝓝 integratedOperator)
  finiteBoundaryIdentity : ∀ cutoff,
    partialIntegral cutoff + terminalPrimitive cutoff = matchingOperator

namespace ReferenceNuclearDuhamelRelativeHeatTraceProductThroatLongTimeDecayData

/-- Assemble the direct terminal/product-trace decay packet. -/
def toReferenceNuclearDuhamelProductThroatLongTimeDecay
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data :
      ReferenceNuclearDuhamelRelativeHeatTraceProductThroatLongTimeDecayData
        productData fold twist cutoffFilter integratedOperator matchingOperator) :
    ReferenceNuclearDuhamelProductThroatLongTimeDecayData
      productData fold twist cutoffFilter integratedOperator matchingOperator where
  partialIntegral := data.partialIntegral
  terminalPrimitive := data.terminalPrimitive
  cutoffTime := data.cutoffTime
  boundaryScale := data.boundaryScale
  boundaryScale_nonnegative := data.boundaryScale_nonnegative
  cutoffTime_tendsto_atTop := data.cutoffTime_tendsto_atTop
  terminalPrimitive_norm_le_heatTrace := by
    filter_upwards [data.terminalPrimitive_norm_le_referenceHeatTrace,
      data.referenceHeatTrace_norm_le_productTrace] with cutoff hTerminal hHeat
    exact hTerminal.trans
      (mul_le_mul_of_nonneg_left hHeat data.boundaryScale_nonnegative)
  partialIntegral_tendsto := data.partialIntegral_tendsto
  finiteBoundaryIdentity := data.finiteBoundaryIdentity

/-- Derived terminal/product-trace estimate. -/
theorem terminalPrimitive_norm_le_productTrace
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data :
      ReferenceNuclearDuhamelRelativeHeatTraceProductThroatLongTimeDecayData
        productData fold twist cutoffFilter integratedOperator matchingOperator) :
    ∀ᶠ cutoff in cutoffFilter,
      ‖data.terminalPrimitive cutoff‖ ≤
        data.boundaryScale *
          extendedProductThroatNuclearHeatTrace productData fold twist
            (data.cutoffTime cutoff) :=
  data.toReferenceNuclearDuhamelProductThroatLongTimeDecay.terminalPrimitive_norm_le_heatTrace

/-- Public relative-heat-trace terminal-decay checkpoint. -/
theorem reference_nuclear_duhamel_relative_heat_trace_product_throat_long_time_decay_gate
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data :
      ReferenceNuclearDuhamelRelativeHeatTraceProductThroatLongTimeDecayData
        productData fold twist cutoffFilter integratedOperator matchingOperator) :
    (∀ᶠ cutoff in cutoffFilter,
      ‖data.terminalPrimitive cutoff‖ ≤
        data.boundaryScale *
          extendedProductThroatNuclearHeatTrace productData fold twist
            (data.cutoffTime cutoff)) ∧
    Tendsto data.partialIntegral cutoffFilter (𝓝 integratedOperator) :=
  ⟨data.terminalPrimitive_norm_le_productTrace,
    data.partialIntegral_tendsto⟩

end ReferenceNuclearDuhamelRelativeHeatTraceProductThroatLongTimeDecayData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelRelativeHeatTraceProductThroatLongTimeDecay4D
end JanusFormal
