import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatNuclearHeatTraceSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceProductThroatHeatOperatorIdentification4D

/-!
# Real product-throat heat-trace continuity

The complex product heat operator is used as a real operator in the reference
family.  Its real trace is therefore twice its complex trace.  Once that exact
scalar identification is supplied, smoothness of the explicit spectral series
generates time continuity of the abstract nuclear heat trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatNuclearHeatTrace4D
open P0EFTJanusProductThroatNuclearHeatTraceSmooth4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPReferenceProductThroatHeatOperatorIdentification4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Operator identification together with the exact real/complex trace
normalization. -/
structure ReferenceProductThroatRealHeatTraceIdentificationData
    (productData : ProductThroatSpectralData) (fold : Fold)
    (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)) where
  operatorIdentification :
    ReferenceProductThroatHeatOperatorIdentificationData productData fold
      (fun _ => twist) nuclear
  heatTrace_eq_realProductTrace : ∀ parameter time,
    nuclear.heatTrace parameter time =
      2 * productThroatNuclearHeatTrace productData time fold twist

namespace ReferenceProductThroatRealHeatTraceIdentificationData

/-- Equality of zero-extended traces at every positive real time. -/
theorem extendedHeatTrace_eq_realProductTrace
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceProductThroatRealHeatTraceIdentificationData
      productData fold twist nuclear)
    (parameter time : Real) (hTime : 0 < time) :
    extendedHeatTrace nuclear parameter time =
      2 * productThroatNuclearHeatTraceReal productData time fold twist := by
  rw [extendedHeatTrace, dif_pos hTime,
    data.heatTrace_eq_realProductTrace parameter ⟨time, hTime⟩,
    ← productThroatNuclearHeatTraceReal_of_heatTime]

/-- Product spectral smoothness generates time continuity of the abstract
nuclear heat trace on every positive short-time interval. -/
theorem extendedHeatTrace_continuousOn_Ioo
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceProductThroatRealHeatTraceIdentificationData
      productData fold twist nuclear)
    (parameter cutoff : Real) :
    ContinuousOn (fun time => extendedHeatTrace nuclear parameter time)
      (Set.Ioo 0 cutoff) := by
  have hProduct : ContinuousOn
      (fun time : Real => 2 *
        productThroatNuclearHeatTraceReal productData time fold twist)
      (Set.Ioo 0 cutoff) :=
    continuousOn_const.mul
      ((productThroatNuclearHeatTraceReal_contDiffOn_infty
        productData fold twist).continuousOn.mono Set.Ioo_subset_Ioi_self)
  exact hProduct.congr fun time hTime =>
    data.extendedHeatTrace_eq_realProductTrace parameter time hTime.1

/-- Time continuity on the full positive long-time half-line. -/
theorem extendedHeatTrace_continuousOn_Ioi
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceProductThroatRealHeatTraceIdentificationData
      productData fold twist nuclear)
    (parameter : Real) :
    ContinuousOn (fun time => extendedHeatTrace nuclear parameter time)
      (Set.Ioi 0) := by
  have hProduct : ContinuousOn
      (fun time : Real => 2 *
        productThroatNuclearHeatTraceReal productData time fold twist)
      (Set.Ioi 0) :=
    continuousOn_const.mul
      (productThroatNuclearHeatTraceReal_contDiffOn_infty
        productData fold twist).continuousOn
  exact hProduct.congr fun time hTime =>
    data.extendedHeatTrace_eq_realProductTrace parameter time hTime

/-- Public operator, trace-normalization and continuity checkpoint. -/
theorem reference_product_throat_real_heat_trace_continuity_gate
    {productData : ProductThroatSpectralData} {fold : Fold}
    {twist : CircleTwist}
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (data : ReferenceProductThroatRealHeatTraceIdentificationData
      productData fold twist nuclear) :
    (∀ parameter time,
      nuclear.heatTrace parameter time =
        2 * productThroatNuclearHeatTrace productData time fold twist) ∧
    (∀ parameter cutoff,
      ContinuousOn (fun time => extendedHeatTrace nuclear parameter time)
        (Set.Ioo 0 cutoff)) ∧
    (∀ parameter,
      ContinuousOn (fun time => extendedHeatTrace nuclear parameter time)
        (Set.Ioi 0)) :=
  ⟨data.heatTrace_eq_realProductTrace,
    data.extendedHeatTrace_continuousOn_Ioo,
    data.extendedHeatTrace_continuousOn_Ioi⟩

end ReferenceProductThroatRealHeatTraceIdentificationData

end
end P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D
end JanusFormal
