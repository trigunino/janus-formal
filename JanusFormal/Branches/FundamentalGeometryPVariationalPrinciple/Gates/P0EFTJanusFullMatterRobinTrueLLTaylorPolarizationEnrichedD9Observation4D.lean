import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorPolarization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorC2EnrichedD9Observation4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLTaylorPolarizationEnrichedD9Observation4D

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
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusFullLLHessianExplicitPolarization4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLTaylorPolarization4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusFullMatterRobinTrueLLTaylorC2EnrichedD9Observation4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- The mixed Hessian is reconstructed from the two diagonal quadratic
Taylor coefficients, and each coefficient is read on the corresponding
global-matter-enriched D9 observation.  No injectivity of that observation is used. -/
theorem mixedHessian_eq_difference_enrichedD9_diagonal_C2
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (x y : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields x y =
      (1 / 4 : Real) *
        (enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure
            frame llMeasure fields
            (globalMatterEnrichedD9Projection period hPeriod fields
              (addDirection period hPeriod x y) sector column point)
            (globalMatterEnrichedD9Projection period hPeriod fields
              (addDirection period hPeriod x y) sector column point) -
         enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure
            frame llMeasure fields
            (globalMatterEnrichedD9Projection period hPeriod fields
              (subDirection period hPeriod x y) sector column point)
            (globalMatterEnrichedD9Projection period hPeriod fields
              (subDirection period hPeriod x y) sector column point)) := by
  rw [assembledHessian_eq_difference_C2 period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields x y]
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_enrichedD9ActiveHessian period hPeriod
      matterData kPlus kMinus robinMeasure frame llMeasure fields sector column point,
    fullMatterRobinTrueLLTaylorC2_eq_half_enrichedD9ActiveHessian period hPeriod
      matterData kPlus kMinus robinMeasure frame llMeasure fields sector column point]
  ring

end
end P0EFTJanusFullMatterRobinTrueLLTaylorPolarizationEnrichedD9Observation4D
end JanusFormal
