import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedCoefficientActiveQuotientDerivatives4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveMixedDerivatives4D

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
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
open P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
open P0EFTJanusFullMatterRobinTrueLLMixedCoefficientActiveQuotientDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLTaylorPolarization4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem mixedTaylorCoefficient_eq_zero_of_inactive_first
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod first = zeroActiveDirection period hPeriod) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields first second = 0 := by
  rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian]
  exact globalMatterRobinFullLLHessian_inactive_left period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields first second hInactive

theorem mixedTaylorCoefficient_eq_zero_of_inactive_second
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod second = zeroActiveDirection period hPeriod) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields first second = 0 := by
  rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian]
  exact globalMatterRobinFullLLHessian_inactive_right period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields first second hInactive

theorem representativeEulerCurve_hasDerivAt_zero_of_inactive_first
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod first = zeroActiveDirection period hPeriod) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first second) 0 0 := by
  have hZero := mixedTaylorCoefficient_eq_zero_of_inactive_first period hPeriod matterData
    kPlus kMinus robinMeasure frame llMeasure fields first second hInactive
  have h := representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first second
  simpa [hZero] using h

theorem representativeEulerCurve_hasDerivAt_zero_of_inactive_second
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod second = zeroActiveDirection period hPeriod) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first second) 0 0 := by
  have hZero := mixedTaylorCoefficient_eq_zero_of_inactive_second period hPeriod matterData
    kPlus kMinus robinMeasure frame llMeasure fields first second hInactive
  have h := representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first second
  simpa [hZero] using h

end
end P0EFTJanusFullMatterRobinTrueLLInactiveMixedDerivatives4D
end JanusFormal
