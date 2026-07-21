import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedActiveQuotient4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLMixedCoefficientActiveQuotientDerivatives4D

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
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
open P0EFTJanusFullMatterRobinTrueLLMixedActiveQuotient4D

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

theorem representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first second)
      (fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second) 0 := by
  exact fullMatterRobinTrueLLFirstCoefficientAlongSecond_hasDerivAt period hPeriod
    matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter junction
    fields first second

theorem mixedTaylorCoefficient_eq_activeQuotientHessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ((activeQuotientEquiv period hPeriod).symm (activeProjection period hPeriod first))
        ((activeQuotientEquiv period hPeriod).symm (activeProjection period hPeriod second)) := by
  have hFirst :
      (activeQuotientEquiv period hPeriod).symm (activeProjection period hPeriod first) =
        (⟦first⟧ : ActiveQuotient period hPeriod) := by
    apply (activeQuotientEquiv period hPeriod).injective
    simp
  have hSecond :
      (activeQuotientEquiv period hPeriod).symm (activeProjection period hPeriod second) =
        (⟦second⟧ : ActiveQuotient period hPeriod) := by
    apply (activeQuotientEquiv period hPeriod).injective
    simp
  rw [hFirst, hSecond]
  exact fullMatterRobinTrueLLMixedTaylorCoefficient_eq_quotientHessian period hPeriod
    matterData kPlus kMinus robinMeasure frame llMeasure fields first second

theorem swappedRepresentativeEulerCurve_hasDerivAt_mixedTaylorCoefficient
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields second first)
      (fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second) 0 := by
  have h := representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod
    matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter junction
    fields second first
  have hc :
      fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
          robinMeasure frame llMeasure fields first second =
        fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus
          robinMeasure frame llMeasure fields second first := by
    rw [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
      fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian,
      P0EFTJanusMatterRobinFullLLActualHessian4D.globalMatterRobinFullLLHessian_symmetric]
  rw [hc]
  exact h

end
end P0EFTJanusFullMatterRobinTrueLLMixedCoefficientActiveQuotientDerivatives4D
end JanusFormal
