import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinLLAuxiliaryEnrichedD9Projection4D

/-! Exact comparison between the active action projection and enriched D9 data. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLActiveD9Comparison4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusCommonCompleteSectorD9ProjectionKernel4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullMatterRobinLLAuxiliaryEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Robin and all three LL slots of the action-active projection are recovered
definitionally by the enriched D9 packet. -/
theorem enrichedD9_recovers_robin_fullLL
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    (fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields direction
        sector column point).robin =
        (activeProjection period hPeriod direction).robin ∧
    (fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields direction
        sector column point).llField =
        (activeProjection period hPeriod direction).llField ∧
    (fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields direction
        sector column point).llAuxMetric =
        (activeProjection period hPeriod direction).llAuxMetric ∧
    (fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields direction
        sector column point).llMeasure =
        (activeProjection period hPeriod direction).llMeasure := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Equality of enriched D9 packets recovers the four complete active slots,
but in the matter slot gives only the selected throat value. -/
theorem enrichedD9_equal_recovers_complete_slots_and_matter_trace
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (hEqual : fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields first
      sector column point =
      fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields second
        sector column point) :
    first.robin = second.robin ∧
    first.common.ll = second.common.ll ∧
    first.llAuxMetric = second.llAuxMetric ∧
    first.llMeasure = second.llMeasure ∧
    d9MatterCoefficient period hPeriod
        (combinedIndependentVariation period hPeriod first.common) sector point =
      d9MatterCoefficient period hPeriod
        (combinedIndependentVariation period hPeriod second.common) sector point := by
  have hRobin := congrArg FullRobinLLAuxiliaryVisibleD9Projection.robin hEqual
  have hField := congrArg FullRobinLLAuxiliaryVisibleD9Projection.llField hEqual
  have hMetric := congrArg FullRobinLLAuxiliaryVisibleD9Projection.llAuxMetric hEqual
  have hMeasure := congrArg FullRobinLLAuxiliaryVisibleD9Projection.llMeasure hEqual
  have hVisible := congrArg FullRobinLLAuxiliaryVisibleD9Projection.visible hEqual
  have hMatter := congrArg VisibleD9Projection.matter hVisible
  exact ⟨hRobin, hField, hMetric, hMeasure, hMatter⟩

private def unitMatterField : SmoothQuotientField period hPeriod MatterFiber where
  toFun := fun _ => EuclideanSpace.single 0 (1 : Real)
  contMDiff_toFun := contMDiff_const

private def replaceMatter
    (direction : FullMatterRobinLLDirections period hPeriod)
    (matter : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber) :
    FullMatterRobinLLDirections period hPeriod :=
  { direction with common := { direction.common with matter := matter } }

/-- Concrete no-go at a fixed plus-sector D9 observation: changing the whole
minus matter field is invisible, although it changes the action-active class. -/
theorem enrichedD9_plus_not_complete_for_active_matter
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (column : Fin 2) (point : EffectiveThroat period hPeriod) :
    let first := replaceMatter period hPeriod direction (0, 0)
    let second := replaceMatter period hPeriod direction (0, unitMatterField period hPeriod)
    fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields first
        .plus column point =
      fullRobinLLAuxiliaryVisibleD9Projection period hPeriod fields second
        .plus column point ∧
    activeProjection period hPeriod first ≠ activeProjection period hPeriod second := by
  dsimp only
  constructor
  · rfl
  · intro h
    have hMatter := congrArg ActiveDirection.matter h
    have hMinus := congrArg (fun pair => pair.2) hMatter
    have hValue := congrArg (fun field => field
      (fixedThroatQuotientInclusion period hPeriod point) 0) hMinus
    change (0 : Real) = 1 at hValue
    norm_num at hValue

end
end P0EFTJanusMatterRobinFullLLActiveD9Comparison4D
end JanusFormal
