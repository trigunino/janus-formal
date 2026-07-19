import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9HessianCongruence4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem enrichedD9ActiveHessian_congr_left
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (first first' second : GlobalMatterEnrichedD9Projection period hPeriod)
    (h : toActiveDirection period hPeriod first = toActiveDirection period hPeriod first') :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first' second := by
  unfold enrichedD9ActiveHessian
  rw [h]

theorem enrichedD9ActiveHessian_congr_right
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (first second second' : GlobalMatterEnrichedD9Projection period hPeriod)
    (h : toActiveDirection period hPeriod second = toActiveDirection period hPeriod second') :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second' := by
  unfold enrichedD9ActiveHessian
  rw [h]

theorem inactive_components_kernel_left
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first first' second : FullMatterRobinLLDirections period hPeriod)
    (h : activeProjection period hPeriod first = activeProjection period hPeriod first') :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first' sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := by
  apply enrichedD9ActiveHessian_congr_left
  simpa using h

theorem inactive_components_kernel_right
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second second' : FullMatterRobinLLDirections period hPeriod)
    (h : activeProjection period hPeriod second = activeProjection period hPeriod second') :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second' sector column point) := by
  apply enrichedD9ActiveHessian_congr_right
  simpa using h

end
end P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9HessianCongruence4D
end JanusFormal
