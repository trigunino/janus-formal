import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinLLActualActionEulerHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonCompleteSectorD9Variation4D

/-!
# Common variation bridge for the matter + Robin + LL action

The common `IndependentFieldVariation` has no Robin junction slot.  This gate
adds exactly that direction while retaining the complete common packet, then
transports the genuine first- and second-variation theorems of the already
assembled matter + Robin + LL action.  Metric, gauge, ghost and auxiliary
directions are retained faithfully but this action does not depend on them.
No complete Candidate-A action is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLActionVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusMatterRobinLLActualActionEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Complete common directions plus the junction direction absent from
`IndependentFieldVariation`. -/
structure MatterRobinLLEnrichedDirections where
  common : CommonSectorDirections period hPeriod
  robin : SmoothThroatField period hPeriod Real

/-- Faithful realization as the common variation paired with its Robin slot. -/
def enrichedCommonVariation
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    IndependentFieldVariation period hPeriod ×
      SmoothThroatField period hPeriod Real :=
  (combinedIndependentVariation period hPeriod direction.common,
    direction.robin)

theorem enrichedCommonVariation_injective :
    Function.Injective (enrichedCommonVariation period hPeriod) := by
  intro first second hEqual
  have hCommon := congrArg Prod.fst hEqual
  have hRobin := congrArg Prod.snd hEqual
  change first.robin = second.robin at hRobin
  have hCommon' : first.common = second.common :=
    combinedIndependentVariation_injective period hPeriod hCommon
  cases first with
  | mk firstCommon firstRobin =>
      cases second with
      | mk secondCommon secondRobin =>
          change firstCommon = secondCommon at hCommon'
          change firstRobin = secondRobin at hRobin
          subst secondCommon
          subst secondRobin
          rfl

/-- Euler pairing of the same assembled action on an enriched common
direction. -/
def commonMatterRobinLLEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : MatterRobinLLEnrichedDirections period hPeriod) : Real :=
  matterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure
    (independentMatterComponentFamily period hPeriod fields)
    (matterVariationComponentFamily period hPeriod direction.common.matter)
    junction direction.robin fields direction.common.ll

/-- Genuine derivative of the existing assembled action along the enriched
common direction. -/
theorem commonMatterRobinLLAction_hasDerivAt
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : MatterRobinLLEnrichedDirections period hPeriod) :
    HasDerivAt
      (fun epsilon : Real => matterRobinLLAction period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        (matterMultipletAffineCurve period hPeriod
          (independentMatterComponentFamily period hPeriod fields)
          (matterVariationComponentFamily period hPeriod direction.common.matter)
          epsilon)
        (junctionAffineCurve period hPeriod junction direction.robin epsilon)
        (differentialLLFluxCurve period hPeriod fields direction.common.ll epsilon))
      (commonMatterRobinLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction) 0 := by
  exact matterRobinLLAction_hasDerivAt period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure
    (independentMatterComponentFamily period hPeriod fields)
    (matterVariationComponentFamily period hPeriod direction.common.matter)
    junction direction.robin fields direction.common.ll

/-- Hessian transported to two enriched common directions. -/
def commonMatterRobinLLHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : MatterRobinLLEnrichedDirections period hPeriod) : Real :=
  matterRobinLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
    llMeasure
    (matterVariationComponentFamily period hPeriod first.common.matter)
    (matterVariationComponentFamily period hPeriod second.common.matter)
    first.robin second.robin fields first.common.ll second.common.ll

/-- The transported Euler pairing has the transported genuine Hessian as its
derivative. -/
theorem commonMatterRobinLLEuler_hasDerivAt
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (first second : MatterRobinLLEnrichedDirections period hPeriod) :
    HasDerivAt
      (fun epsilon : Real => matterRobinLLEuler period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        (matterMultipletAffineCurve period hPeriod
          (independentMatterComponentFamily period hPeriod fields)
          (matterVariationComponentFamily period hPeriod first.common.matter)
          epsilon)
        (matterVariationComponentFamily period hPeriod second.common.matter)
        (junctionAffineCurve period hPeriod junction first.robin epsilon)
        second.robin
        (differentialLLFluxCurve period hPeriod fields first.common.ll epsilon)
        second.common.ll)
      (commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second) 0 := by
  exact matterRobinLLEuler_hasDerivAt period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure
    (independentMatterComponentFamily period hPeriod fields)
    (matterVariationComponentFamily period hPeriod first.common.matter)
    (matterVariationComponentFamily period hPeriod second.common.matter)
    junction first.robin second.robin fields first.common.ll second.common.ll

end

end P0EFTJanusCommonMatterRobinLLActionVariation4D
end JanusFormal
