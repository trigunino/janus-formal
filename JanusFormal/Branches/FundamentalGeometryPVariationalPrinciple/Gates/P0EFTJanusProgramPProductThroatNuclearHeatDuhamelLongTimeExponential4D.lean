import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatPositiveHeatGapLongTime4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D

/-!
# Product-throat spectral domination of the long-time Duhamel variation

The concrete product spectrum supplies the positive rate

```text
c_product = 1 / R^2
```

and a canonical heat-trace scale.  If the insertion trace is bounded by a
locally uniform scalar multiple of that heat trace, this module generates the
`C exp (-c_product t)` field required by the long-time dominated Duhamel
interface.

Thus the reference-side long-time differentiation theorem no longer receives
an unrelated abstract rate: its rate and heat scale are forced by the genuine
circle-times-monopole-sphere spectrum.  The remaining input is the natural
operator estimate comparing the inserted Duhamel trace with the positive heat
trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatNuclearHeatTrace4D
open P0EFTJanusProductThroatPositiveHeatGapLongTime4D
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPNuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegral4D

universe e i s

variable {E : Type e}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Analytic long-time heat data together with a product-spectral bound for the
inserted Duhamel trace. -/
structure ProductThroatNuclearHeatDuhamelLongTimeExponentialData
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
      (fun time =>
        weight time * extendedHeatTraceDerivative nuclear parameter time)
      (volume.restrict (Set.Ioi start))
  insertionScale : Real → Real
  insertionScale_nonnegative : ∀ parameter, 0 ≤ insertionScale parameter
  duhamelTrace_norm_le : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioi start),
      ∀ current ∈ parameterDomain parameter,
        ‖extendedDuhamelTrace nuclear current time‖ ≤
          insertionScale parameter *
            extendedProductThroatNuclearHeatTrace productData fold twist time

namespace ProductThroatNuclearHeatDuhamelLongTimeExponentialData

/-- Total long-time scale: insertion bound times the canonical unit-time
product heat scale. -/
def longTimeScale
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      productData fold twist nuclear start)
    (parameter : Real) : Real :=
  data.insertionScale parameter *
    productThroatLongTimeScale productData fold twist

/-- The generated total scale is nonnegative. -/
theorem longTimeScale_nonnegative
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      productData fold twist nuclear start)
    (parameter : Real) :
    0 ≤ data.longTimeScale parameter := by
  unfold longTimeScale
  exact mul_nonneg (data.insertionScale_nonnegative parameter)
    (productThroatLongTimeScale_nonnegative productData fold twist)

/-- The product spectrum generates the complete exponential domination packet
consumed by the weighted long-time Duhamel integral. -/
def toLongTimeExponentialDominatedWeightedIntegral
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      productData fold twist nuclear start) :
    NuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegralData
      nuclear start where
  weight := data.weight
  weight_mul_time_eq_one := data.weight_mul_time_eq_one
  parameterDomain := data.parameterDomain
  parameterDomain_mem_nhds := data.parameterDomain_mem_nhds
  integrand_aeStronglyMeasurable := data.integrand_aeStronglyMeasurable
  integrand_integrable := data.integrand_integrable
  derivative_aeStronglyMeasurable := data.derivative_aeStronglyMeasurable
  scale := data.longTimeScale
  rate := fun _ => productThroatPositiveHeatGap productData
  rate_pos := fun _ => productThroatPositiveHeatGap_pos productData
  derivative_norm_le := by
    intro parameter
    have hTimeGeOne :
        ∀ᵐ time ∂volume.restrict (Set.Ioi start), 1 ≤ time :=
      (ae_restrict_mem measurableSet_Ioi).mono fun time hTime =>
        data.start_ge_one.trans hTime.le
    filter_upwards [data.weight_mul_time_eq_one,
      data.duhamelTrace_norm_le parameter, hTimeGeOne] with
      time hWeight hTrace hTime
    intro current hCurrent
    have hDerivative :
        data.weight time *
            extendedHeatTraceDerivative nuclear current time =
          -extendedDuhamelTrace nuclear current time := by
      rw [extendedHeatTraceDerivative_eq]
      calc
        data.weight time *
            (-time * extendedDuhamelTrace nuclear current time) =
          -(data.weight time * time) *
            extendedDuhamelTrace nuclear current time := by ring
        _ = -extendedDuhamelTrace nuclear current time := by
          rw [hWeight]
          ring
    have hProduct :=
      extendedProductThroatNuclearHeatTrace_le_longTimeExponentialBound
        productData fold twist time hTime
    calc
      ‖data.weight time *
          extendedHeatTraceDerivative nuclear current time‖ =
          ‖extendedDuhamelTrace nuclear current time‖ := by
        rw [hDerivative, norm_neg]
      _ ≤ data.insertionScale parameter *
          extendedProductThroatNuclearHeatTrace productData fold twist time :=
        hTrace current hCurrent
      _ ≤ data.insertionScale parameter *
          longTimeExponentialBound
            (productThroatLongTimeScale productData fold twist)
            (productThroatPositiveHeatGap productData) time :=
        mul_le_mul_of_nonneg_left hProduct
          (data.insertionScale_nonnegative parameter)
      _ = longTimeExponentialBound
          (data.longTimeScale parameter)
          (productThroatPositiveHeatGap productData) time := by
        unfold longTimeExponentialBound longTimeScale
        ring

/-- The generated decay rate is exactly the concrete product heat gap. -/
@[simp] theorem generatedRate_eq_productThroatPositiveHeatGap
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      productData fold twist nuclear start)
    (parameter : Real) :
    data.toLongTimeExponentialDominatedWeightedIntegral.rate parameter =
      productThroatPositiveHeatGap productData :=
  rfl

/-- The generated majorant is integrable on the selected long-time half-line. -/
theorem bound_integrable
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      productData fold twist nuclear start)
    (parameter : Real) :
    Integrable
      (longTimeExponentialBound (data.longTimeScale parameter)
        (productThroatPositiveHeatGap productData))
      (volume.restrict (Set.Ioi start)) :=
  data.toLongTimeExponentialDominatedWeightedIntegral.bound_integrable parameter

/-- Differentiation of the weighted long-time heat integral now uses the
concrete product spectral rate. -/
theorem hasDerivAt_integral
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      productData fold twist nuclear start)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        ∫ time in Set.Ioi start,
          data.weight time * extendedHeatTrace nuclear current time)
      (-(∫ time in Set.Ioi start,
        extendedDuhamelTrace nuclear parameter time)) parameter :=
  P0EFTJanusProgramPNuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegral4D.NuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegralData.hasDerivAt_integral
    data.toLongTimeExponentialDominatedWeightedIntegral parameter

/-- Public product-spectral Duhamel long-time checkpoint. -/
theorem product_throat_nuclear_heat_duhamel_long_time_exponential_gate
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (start : Real)
    (data : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
      productData fold twist nuclear start) :
    0 < productThroatPositiveHeatGap productData ∧
    (∀ parameter, 0 ≤ data.longTimeScale parameter) ∧
    (∀ parameter,
      Integrable
        (longTimeExponentialBound (data.longTimeScale parameter)
          (productThroatPositiveHeatGap productData))
        (volume.restrict (Set.Ioi start))) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          ∫ time in Set.Ioi start,
            data.weight time * extendedHeatTrace nuclear current time)
        (-(∫ time in Set.Ioi start,
          extendedDuhamelTrace nuclear parameter time)) parameter) :=
  ⟨productThroatPositiveHeatGap_pos productData,
    data.longTimeScale_nonnegative,
    data.bound_integrable,
    data.hasDerivAt_integral⟩

end ProductThroatNuclearHeatDuhamelLongTimeExponentialData

open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D

variable {Slice : Type s} [MeasurableSpace Slice]
  [CompleteSpace E]

/-- The product-throat Duhamel bound generated from a nuclear expansion of
the full heat operator and an operator-norm bound on the insertion `H'_a`. -/
structure ProductThroatNuclearHeatDuhamelExpansionBoundData
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (start : Real) where
  semigroup :
    NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear
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
      (fun time =>
        weight time * extendedHeatTraceDerivative nuclear parameter time)
      (volume.restrict (Set.Ioi start))
  insertionScale : Real → Real
  insertionScale_nonnegative : ∀ parameter, 0 ≤ insertionScale parameter
  fullHeatExpansion : ∀ parameter time,
    SummableRankOneOperatorExpansion.{i, e}
      (semigroup.fullHeat parameter time)
  fullHeat_nuclearNormSum_le : ∀ parameter time,
    (∑' index,
      |(fullHeatExpansion parameter time).coefficient index| *
        ‖(fullHeatExpansion parameter time).leftVector index‖ *
          ‖(fullHeatExpansion parameter time).rightVector index‖) ≤
      productThroatNuclearHeatTrace productData time fold twist
  insertion_norm_le : ∀ parameter time, start < time.1 →
    ∀ current ∈ parameterDomain parameter,
      ‖semigroup.insertion current time‖ ≤ insertionScale parameter

namespace ProductThroatNuclearHeatDuhamelExpansionBoundData

/-- Nuclear bounded composition proves the inserted Duhamel trace estimate;
it is no longer an independent long-time hypothesis. -/
theorem duhamelTrace_norm_le
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelExpansionBoundData
      productData fold twist sliceMeasure nuclear start)
    (parameter : Real) :
    ∀ᵐ time ∂volume.restrict (Set.Ioi start),
      ∀ current ∈ data.parameterDomain parameter,
        ‖extendedDuhamelTrace nuclear current time‖ ≤
          data.insertionScale parameter *
            extendedProductThroatNuclearHeatTrace
              productData fold twist time := by
  have hPositive :
      ∀ᵐ time ∂volume.restrict (Set.Ioi start), 0 < time :=
    (ae_restrict_mem measurableSet_Ioi).mono fun time hTime =>
      (zero_lt_one.trans_le data.start_ge_one).trans hTime
  filter_upwards [hPositive, ae_restrict_mem measurableSet_Ioi] with
    time hTime hStart
  intro current hCurrent
  let positiveTime : HeatTime := ⟨time, hTime⟩
  have hTrace :
      |nuclear.duhamelTrace current positiveTime| ≤
        data.insertionScale parameter *
          productThroatNuclearHeatTrace productData positiveTime fold twist := by
    rw [data.semigroup.duhamelTrace_eq_insertionFullHeatTrace]
    exact
      P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D.SummableRankOneOperatorExpansion.intrinsicNuclearTrace_compLeft_abs_le_heatTrace
            (data.fullHeatExpansion current positiveTime)
            (data.semigroup.insertion current positiveTime)
            (data.semigroup.collapsedTraceClass current positiveTime)
            (productThroatNuclearHeatTrace productData positiveTime fold twist)
            (data.insertionScale parameter)
            (data.fullHeat_nuclearNormSum_le current positiveTime)
            (productThroatNuclearHeatTrace_nonnegative
              productData positiveTime fold twist)
            (data.insertion_norm_le parameter positiveTime hStart current hCurrent)
  simpa [extendedDuhamelTrace,
    extendedProductThroatNuclearHeatTrace, hTime, positiveTime,
    Real.norm_eq_abs] using hTrace

/-- Build the existing product-spectral long-time packet from the expansion
and the norm bound on `H'_a`. -/
def toLongTimeExponentialData
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data : ProductThroatNuclearHeatDuhamelExpansionBoundData
      productData fold twist sliceMeasure nuclear start) :
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
  duhamelTrace_norm_le := data.duhamelTrace_norm_le

/-- Public checkpoint: `|Tr D_a(t)| ≤ B_a Tr K(t)` follows from `H'_a`,
the nuclear heat expansion and semigroup cyclicity. -/
theorem product_throat_nuclear_heat_duhamel_expansion_bound_gate
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (start : Real)
    (data : ProductThroatNuclearHeatDuhamelExpansionBoundData
      productData fold twist sliceMeasure nuclear start) :
    (∀ parameter,
      ∀ᵐ time ∂volume.restrict (Set.Ioi start),
        ∀ current ∈ data.parameterDomain parameter,
          ‖extendedDuhamelTrace nuclear current time‖ ≤
            data.insertionScale parameter *
              extendedProductThroatNuclearHeatTrace
                productData fold twist time) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          ∫ time in Set.Ioi start,
            data.weight time * extendedHeatTrace nuclear current time)
        (-(∫ time in Set.Ioi start,
          extendedDuhamelTrace nuclear parameter time)) parameter) :=
  ⟨data.duhamelTrace_norm_le,
    data.toLongTimeExponentialData.hasDerivAt_integral⟩

end ProductThroatNuclearHeatDuhamelExpansionBoundData

end
end P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
end JanusFormal
