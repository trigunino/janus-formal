import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActualHessian4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D

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
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusMatterRobinFullLLActualHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- The coefficient of the first parameter, evaluated after moving the same
assembled fields along a second synchronized direction. -/
def fullMatterRobinTrueLLFirstCoefficientAlongSecond
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) (t : Real) : Real :=
  globalMatterRobinFullLLFirstVariation period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure
    (matterMultipletAffineCurve period hPeriod matter
      (matterVariationComponentFamily period hPeriod second.common.matter) t)
    (junctionAffineCurve period hPeriod junction second.robin t)
    (fullLLCurve period hPeriod llFields
      (fullDirectionLLVariation period hPeriod second) second.llAuxMetric t)
    first

/-- Genuine sectorwise `s*t` coefficient. Each summand is the mixed Hessian
of the same matter, Robin, or full three-slot LL action. -/
def fullMatterRobinTrueLLMixedTaylorCoefficient
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (llFields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) : Real :=
  globalMatterMultipletHessian period hPeriod matterData
      (matterVariationComponentFamily period hPeriod first.common.matter)
      (matterVariationComponentFamily period hPeriod second.common.matter) +
    robinHessian period hPeriod kPlus kMinus first.robin second.robin robinMeasure +
    globalPTFullLLHessianForm period hPeriod frame llFields first second llMeasure

theorem fullMatterRobinTrueLLFirstCoefficientAlongSecond_hasDerivAt
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
    HasDerivAt
      (fullMatterRobinTrueLLFirstCoefficientAlongSecond period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter
        junction llFields first second)
      (fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData
        kPlus kMinus robinMeasure frame llMeasure llFields first second) 0 := by
  unfold fullMatterRobinTrueLLFirstCoefficientAlongSecond
    fullMatterRobinTrueLLMixedTaylorCoefficient
  exact globalMatterRobinFullLLFirstVariation_second_direction_hasDerivAt
    period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure matter junction llFields first second

theorem fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (llFields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus
        kMinus robinMeasure frame llMeasure llFields first second =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure llFields first second := by
  rfl

end
end P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
end JanusFormal
