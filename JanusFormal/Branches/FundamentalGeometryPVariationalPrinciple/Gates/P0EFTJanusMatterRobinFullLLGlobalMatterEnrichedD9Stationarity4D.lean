import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Euler4D

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Stationarity4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Euler4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem trueEuler_stationary_iff_enrichedD9ActiveEuler_stationary
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    P0EFTJanusFullMatterRobinTrueLLActionVariation4D.fullMatterRobinTrueLLEuler period hPeriod
        matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction = 0 ↔
      enrichedD9ActiveEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
        frame llMeasure fields junction
          (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point) = 0 := by
  rw [trueEuler_eq_enrichedD9ActiveEuler]

theorem enrichedD9ActiveEuler_eq_of_toActiveDirection_eq
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (first second : GlobalMatterEnrichedD9Projection period hPeriod)
    (hActive : toActiveDirection period hPeriod first = toActiveDirection period hPeriod second) :
    enrichedD9ActiveEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction first =
      enrichedD9ActiveEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction second := by
  unfold enrichedD9ActiveEuler
  rw [hActive]

theorem enrichedD9ActiveEuler_independent_of_inactive_components
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hActive : P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D.activeProjection period hPeriod first =
      P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D.activeProjection period hPeriod second) :
    enrichedD9ActiveEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point) =
      enrichedD9ActiveEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := by
  apply enrichedD9ActiveEuler_eq_of_toActiveDirection_eq
  simpa using hActive

end
end P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Stationarity4D
end JanusFormal
