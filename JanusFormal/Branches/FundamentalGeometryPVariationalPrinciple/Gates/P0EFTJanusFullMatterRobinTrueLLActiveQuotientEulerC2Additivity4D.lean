import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActiveQuotientHessianAdditivity4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLActiveQuotientEulerC2Additivity4D

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
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientTaylor4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2Polarization4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2InversePolarization4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientHessianAdditivity4D
open P0EFTJanusFullMatterRobinTrueLLInactiveToActiveQuotientStationarity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem activeQuotientC2_add_exact_cross
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second : ActiveQuotient period hPeriod) :
    activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientAdd period hPeriod first second) =
      activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first +
        activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields second +
        quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
          first second := by
  rw [activeQuotientC2_eq_half_Hessian,
    quotientHessian_activeQuotientAdd_first,
    quotientHessian_activeQuotientAdd_second,
    quotientHessian_activeQuotientAdd_second,
    P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D.quotientHessian_symmetric
      period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields second first,
    quotientHessian_diagonal_eq_two_activeQuotientC2,
    quotientHessian_diagonal_eq_two_activeQuotientC2]
  ring

end
end P0EFTJanusFullMatterRobinTrueLLActiveQuotientEulerC2Additivity4D
end JanusFormal
