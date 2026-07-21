import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLMixedClairaut4D

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
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Concrete Clairaut/Helmholtz identity: the `s*t` coefficient of the same
assembled matter, Robin, and full LL action is independent of the order of
the two synchronized directions. -/
theorem fullMatterRobinTrueLLMixedTaylorCoefficient_comm
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (llFields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus
        kMinus robinMeasure frame llMeasure llFields first second =
      fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData
        kPlus kMinus robinMeasure frame llMeasure llFields second first := by
  rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
    fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian]
  exact globalMatterRobinFullLLHessian_symmetric period hPeriod matterData
    kPlus kMinus robinMeasure frame llMeasure llFields first second

/-- The two effective mixed derivatives of the true assembled action agree,
not merely their algebraically named coefficients. -/
theorem fullMatterRobinTrueLL_effectiveMixedDeriv_comm
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    deriv (fullMatterRobinTrueLLFirstCoefficientAlongSecond period hPeriod
        matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        matter junction llFields first second) 0 =
      deriv (fullMatterRobinTrueLLFirstCoefficientAlongSecond period hPeriod
        matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        matter junction llFields second first) 0 := by
  have hFirst := fullMatterRobinTrueLLFirstCoefficientAlongSecond_hasDerivAt
    period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure matter junction llFields first second
  have hSecond := fullMatterRobinTrueLLFirstCoefficientAlongSecond_hasDerivAt
    period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure matter junction llFields second first
  rw [hFirst.deriv, hSecond.deriv]
  exact fullMatterRobinTrueLLMixedTaylorCoefficient_comm period hPeriod
    matterData kPlus kMinus robinMeasure frame llMeasure llFields first second

end
end P0EFTJanusFullMatterRobinTrueLLMixedClairaut4D
end JanusFormal
