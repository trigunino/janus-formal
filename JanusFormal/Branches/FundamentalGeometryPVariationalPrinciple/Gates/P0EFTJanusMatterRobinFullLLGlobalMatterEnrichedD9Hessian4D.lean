import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D

/-! The true active Hessian evaluated on the complete global-matter-enriched D9 observation. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
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
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def enrichedD9ActiveHessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (first second : GlobalMatterEnrichedD9Projection period hPeriod) : Real :=
  activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
    (toActiveDirection period hPeriod first) (toActiveDirection period hPeriod second)

theorem enrichedD9ActiveHessian_activeEmbedding
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second : ActiveDirection period hPeriod) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeEmbedding period hPeriod fields sector column point first)
        (activeEmbedding period hPeriod fields sector column point second) =
      activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second := by
  simp [enrichedD9ActiveHessian]

theorem fullHessian_eq_enrichedD9ActiveHessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    P0EFTJanusMatterRobinFullLLActualHessian4D.globalMatterRobinFullLLHessian period hPeriod matterData
        kPlus kMinus robinMeasure frame llMeasure fields first second =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := by
  rw [fullHessian_factors_active]
  rfl

end
end P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
end JanusFormal
