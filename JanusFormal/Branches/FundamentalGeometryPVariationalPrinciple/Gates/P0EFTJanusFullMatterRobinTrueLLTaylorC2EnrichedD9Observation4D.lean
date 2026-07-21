import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9HessianCongruence4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLTaylorC2EnrichedD9Observation4D

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
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9HessianCongruence4D
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

/-- The integrated diagonal quadratic Taylor coefficient is one half of the
enriched-D9 active Hessian evaluated twice on the observation of the same
direction. -/
theorem fullMatterRobinTrueLLTaylorC2_eq_half_enrichedD9ActiveHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields direction =
      (1 / 2 : Real) * enrichedD9ActiveHessian period hPeriod matterData kPlus
        kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields direction sector
          column point)
        (globalMatterEnrichedD9Projection period hPeriod fields direction sector
          column point) := by
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    fullHessian_eq_enrichedD9ActiveHessian]

/-- Equal active readings of two enriched observations give equal diagonal
quadratic coefficients. -/
theorem fullMatterRobinTrueLLTaylorC2_eq_of_enrichedD9ActiveReading
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hActive : toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point) =
      toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point)) :
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first =
      fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields second := by
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_enrichedD9ActiveHessian period hPeriod
      matterData kPlus kMinus robinMeasure frame llMeasure fields sector column
      point first,
    fullMatterRobinTrueLLTaylorC2_eq_half_enrichedD9ActiveHessian period hPeriod
      matterData kPlus kMinus robinMeasure frame llMeasure fields sector column
      point second]
  congr 1
  unfold enrichedD9ActiveHessian
  rw [hActive]

end
end P0EFTJanusFullMatterRobinTrueLLTaylorC2EnrichedD9Observation4D
end JanusFormal
