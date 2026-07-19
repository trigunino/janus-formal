import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Stationarity4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLTaylorC1EnrichedD9Observation4D

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
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Euler4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Stationarity4D
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

/-- The integrated linear Taylor coefficient of the true assembled action is
exactly its active Euler functional read from the enriched D9 observation. -/
theorem fullMatterRobinTrueLLTaylorC1_eq_enrichedD9ActiveEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction direction =
      enrichedD9ActiveEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction
        (globalMatterEnrichedD9Projection period hPeriod fields direction sector
          column point) := by
  rw [fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler,
    trueEuler_eq_enrichedD9ActiveEuler]

/-- Equal active readings of two enriched D9 observations give equal true
linear Taylor coefficients. -/
theorem fullMatterRobinTrueLLTaylorC1_eq_of_enrichedD9ActiveReading
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hActive : toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point) =
      toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point)) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction first =
      fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction second := by
  rw [fullMatterRobinTrueLLTaylorC1_eq_enrichedD9ActiveEuler period hPeriod
      matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
      fields junction sector column point first,
    fullMatterRobinTrueLLTaylorC1_eq_enrichedD9ActiveEuler period hPeriod
      matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
      fields junction sector column point second]
  exact enrichedD9ActiveEuler_eq_of_toActiveDirection_eq period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    _ _ hActive

end
end P0EFTJanusFullMatterRobinTrueLLTaylorC1EnrichedD9Observation4D
end JanusFormal
