import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveMixedDerivatives4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedEnrichedD9Observation4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveQuotientD9Kernel4D

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
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLMixedActiveQuotient4D
open P0EFTJanusFullMatterRobinTrueLLInactiveMixedDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLMixedEnrichedD9Observation4D
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

theorem quotientHessian_eq_zero_of_inactive_first
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod first = zeroActiveDirection period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦first⟧ ⟦second⟧ = 0 := by
  rw [← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_quotientHessian]
  exact mixedTaylorCoefficient_eq_zero_of_inactive_first period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields first second hInactive

theorem quotientHessian_eq_zero_of_inactive_second
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod second = zeroActiveDirection period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      ⟦first⟧ ⟦second⟧ = 0 := by
  rw [← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_quotientHessian]
  exact mixedTaylorCoefficient_eq_zero_of_inactive_second period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields first second hInactive

theorem enrichedD9ActiveHessian_eq_zero_of_inactive_first
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod first = zeroActiveDirection period hPeriod) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) = 0 := by
  rw [← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian]
  exact mixedTaylorCoefficient_eq_zero_of_inactive_first period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields first second hInactive

theorem enrichedD9ActiveHessian_eq_zero_of_inactive_second
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod second = zeroActiveDirection period hPeriod) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) = 0 := by
  rw [← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian]
  exact mixedTaylorCoefficient_eq_zero_of_inactive_second period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields first second hInactive

end
end P0EFTJanusFullMatterRobinTrueLLInactiveQuotientD9Kernel4D
end JanusFormal
