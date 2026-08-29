import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatPositiveHeatGapLongTime4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelLongTimeExponentialDecay4D

/-!
# Product-throat spectral decay of the terminal Duhamel primitive

The generic long-time endpoint packet accepts an exponential norm estimate for
its terminal primitive.  Here that estimate is generated from the same
circle-times-monopole-sphere heat trace used for the Duhamel integrand.

Given

```text
‖terminalPrimitive(R)‖
  ≤ B · Tr(exp(-T(R) H_product)),
```

and `T(R) → +∞`, the concrete product heat gap yields

```text
‖terminalPrimitive(R)‖
  ≤ B C_product exp(-(1 / R_sphere^2) T(R)).
```

Thus both the integrand domination and the endpoint decay use one genuine
reference spectrum and one positive rate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelProductThroatLongTimeDecay4D

set_option autoImplicit false
noncomputable section

open Filter Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatPositiveHeatGapLongTime4D
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
open P0EFTJanusProgramPReferenceNuclearDuhamelLongTimeExponentialDecay4D

variable {Cutoff E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Finite-boundary data whose terminal primitive is controlled by the
concrete product-throat heat trace. -/
structure ReferenceNuclearDuhamelProductThroatLongTimeDecayData
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (cutoffFilter : Filter Cutoff) [NeBot cutoffFilter]
    (integratedOperator matchingOperator : E) where
  partialIntegral : Cutoff → E
  terminalPrimitive : Cutoff → E
  cutoffTime : Cutoff → Real
  boundaryScale : Real
  boundaryScale_nonnegative : 0 ≤ boundaryScale
  cutoffTime_tendsto_atTop : Tendsto cutoffTime cutoffFilter atTop
  terminalPrimitive_norm_le_heatTrace : ∀ᶠ cutoff in cutoffFilter,
    ‖terminalPrimitive cutoff‖ ≤
      boundaryScale *
        extendedProductThroatNuclearHeatTrace productData fold twist
          (cutoffTime cutoff)
  partialIntegral_tendsto :
    Tendsto partialIntegral cutoffFilter (𝓝 integratedOperator)
  finiteBoundaryIdentity : ∀ cutoff,
    partialIntegral cutoff + terminalPrimitive cutoff = matchingOperator

namespace ReferenceNuclearDuhamelProductThroatLongTimeDecayData

/-- Scale of the generated terminal exponential envelope. -/
def longTimeScale
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelProductThroatLongTimeDecayData
      productData fold twist cutoffFilter integratedOperator matchingOperator) :
    Real :=
  data.boundaryScale * productThroatLongTimeScale productData fold twist

/-- The generated terminal scale is nonnegative. -/
theorem longTimeScale_nonnegative
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelProductThroatLongTimeDecayData
      productData fold twist cutoffFilter integratedOperator matchingOperator) :
    0 ≤ data.longTimeScale := by
  unfold longTimeScale
  exact mul_nonneg data.boundaryScale_nonnegative
    (productThroatLongTimeScale_nonnegative productData fold twist)

/-- The product heat estimate generates the required exponential norm bound. -/
theorem terminalPrimitive_norm_le_exponential
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelProductThroatLongTimeDecayData
      productData fold twist cutoffFilter integratedOperator matchingOperator) :
    ∀ᶠ cutoff in cutoffFilter,
      ‖data.terminalPrimitive cutoff‖ ≤
        longTimeExponentialBound data.longTimeScale
          (productThroatPositiveHeatGap productData)
          (data.cutoffTime cutoff) := by
  have hEventuallyOne :
      ∀ᶠ cutoff in cutoffFilter, 1 ≤ data.cutoffTime cutoff :=
    data.cutoffTime_tendsto_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [data.terminalPrimitive_norm_le_heatTrace,
    hEventuallyOne] with cutoff hTerminal hTime
  have hProduct :=
    extendedProductThroatNuclearHeatTrace_le_longTimeExponentialBound
      productData fold twist (data.cutoffTime cutoff) hTime
  calc
    ‖data.terminalPrimitive cutoff‖ ≤
        data.boundaryScale *
          extendedProductThroatNuclearHeatTrace productData fold twist
            (data.cutoffTime cutoff) :=
      hTerminal
    _ ≤ data.boundaryScale *
        longTimeExponentialBound
          (productThroatLongTimeScale productData fold twist)
          (productThroatPositiveHeatGap productData)
          (data.cutoffTime cutoff) :=
      mul_le_mul_of_nonneg_left hProduct data.boundaryScale_nonnegative
    _ = longTimeExponentialBound data.longTimeScale
        (productThroatPositiveHeatGap productData)
        (data.cutoffTime cutoff) := by
      unfold longTimeExponentialBound longTimeScale
      ring

/-- Convert the product spectral estimate to the generic endpoint-decay
packet. -/
def toLongTimeExponentialDecay
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelProductThroatLongTimeDecayData
      productData fold twist cutoffFilter integratedOperator matchingOperator) :
    ReferenceNuclearDuhamelLongTimeExponentialDecayData cutoffFilter
      integratedOperator matchingOperator where
  partialIntegral := data.partialIntegral
  terminalPrimitive := data.terminalPrimitive
  cutoffTime := data.cutoffTime
  scale := data.longTimeScale
  rate := productThroatPositiveHeatGap productData
  scale_nonneg := data.longTimeScale_nonnegative
  rate_pos := productThroatPositiveHeatGap_pos productData
  cutoffTime_tendsto_atTop := data.cutoffTime_tendsto_atTop
  terminalPrimitive_norm_le := data.terminalPrimitive_norm_le_exponential
  partialIntegral_tendsto := data.partialIntegral_tendsto
  finiteBoundaryIdentity := data.finiteBoundaryIdentity

/-- The terminal primitive tends to zero at the concrete product rate. -/
theorem terminalPrimitive_tendsto_zero
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelProductThroatLongTimeDecayData
      productData fold twist cutoffFilter integratedOperator matchingOperator) :
    Tendsto data.terminalPrimitive cutoffFilter (𝓝 0) :=
  data.toLongTimeExponentialDecay.terminalPrimitive_tendsto_zero

/-- The long-time integrated operator equals the matching operator. -/
theorem boundaryIdentity
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelProductThroatLongTimeDecayData
      productData fold twist cutoffFilter integratedOperator matchingOperator) :
    integratedOperator = matchingOperator :=
  data.toLongTimeExponentialDecay.boundaryIdentity

/-- Public product-throat terminal-decay checkpoint. -/
theorem reference_nuclear_duhamel_product_throat_long_time_decay_gate
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (cutoffFilter : Filter Cutoff) [NeBot cutoffFilter]
    (integratedOperator matchingOperator : E)
    (data : ReferenceNuclearDuhamelProductThroatLongTimeDecayData
      productData fold twist cutoffFilter integratedOperator matchingOperator) :
    0 < productThroatPositiveHeatGap productData ∧
    (∀ᶠ cutoff in cutoffFilter,
      ‖data.terminalPrimitive cutoff‖ ≤
        longTimeExponentialBound data.longTimeScale
          (productThroatPositiveHeatGap productData)
          (data.cutoffTime cutoff)) ∧
    Tendsto data.terminalPrimitive cutoffFilter (𝓝 0) ∧
    integratedOperator = matchingOperator :=
  ⟨productThroatPositiveHeatGap_pos productData,
    data.terminalPrimitive_norm_le_exponential,
    data.terminalPrimitive_tendsto_zero,
    data.boundaryIdentity⟩

end ReferenceNuclearDuhamelProductThroatLongTimeDecayData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelProductThroatLongTimeDecay4D
end JanusFormal
