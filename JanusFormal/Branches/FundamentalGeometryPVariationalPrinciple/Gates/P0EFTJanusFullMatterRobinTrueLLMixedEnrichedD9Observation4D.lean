import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9HessianCongruence4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLMixedEnrichedD9Observation4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9HessianCongruence4D
open P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- The genuine mixed coefficient of the assembled action is exactly the
active Hessian evaluated on the two global-matter-enriched D9 observations. -/
theorem fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus
        kMinus robinMeasure frame llMeasure fields first second =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := by
  rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
    fullHessian_eq_enrichedD9ActiveHessian]

/-- Replacing both directions by observations with the same active readings
in their respective slots leaves the assembled mixed coefficient unchanged. -/
theorem fullMatterRobinTrueLLMixedTaylorCoefficient_eq_of_enrichedD9ActiveReadings
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first first' second second' : FullMatterRobinLLDirections period hPeriod)
    (hFirst : toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point) =
      toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields first' sector column point))
    (hSecond : toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) =
      toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields second' sector column point)) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus
        kMinus robinMeasure frame llMeasure fields first second =
      fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData
        kPlus kMinus robinMeasure frame llMeasure fields first' second' := by
  rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian
      period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      sector column point first second,
    fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian
      period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      sector column point first' second']
  rw [enrichedD9ActiveHessian_congr_left period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields _ _ _ hFirst,
    enrichedD9ActiveHessian_congr_right period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields _ _ _ hSecond]

end
end P0EFTJanusFullMatterRobinTrueLLMixedEnrichedD9Observation4D
end JanusFormal
