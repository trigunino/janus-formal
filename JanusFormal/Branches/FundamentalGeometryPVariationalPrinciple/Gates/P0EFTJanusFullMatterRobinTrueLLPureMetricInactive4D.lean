import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLPureGaugeInactive4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMetricD9Variation4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLPureMetricInactive4D

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
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusCommonMetricD9Variation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Exact injection of a genuine diagonal metric direction from the common
Program-P variation space. -/
def pureMetricFullDirection (metric : SmoothDiagonalMetricVariation period hPeriod) :
    FullMatterRobinLLDirections period hPeriod where
  common := { metric := metric, matter := 0, gauge := 0, ghost := 0, auxiliary := 0, ll := 0 }
  robin := 0
  llAuxMetric := 0
  llMeasure := 0

theorem pureMetricFullDirection_realizes_common_metricOnly
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    fullMatterRobinLLVariation period hPeriod (pureMetricFullDirection period hPeriod metric) =
      (metricOnlyIndependentVariation period hPeriod metric, 0) := by
  rfl

theorem pureMetricFullDirection_activeProjection_zero
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    activeProjection period hPeriod (pureMetricFullDirection period hPeriod metric) =
      zeroActiveDirection period hPeriod := by
  rfl

/-- Sectorial constancy only: the Einstein--Hilbert action is absent, hence
this is not invariance of the complete Candidate A action. -/
theorem pureMetricFullDirection_sectorial_action_constant
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (metric : SmoothDiagonalMetricVariation period hPeriod) (t : Real) :
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction (pureMetricFullDirection period hPeriod metric) t =
      fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction := by
  exact fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    (pureMetricFullDirection period hPeriod metric)
    (pureMetricFullDirection_activeProjection_zero period hPeriod metric) t

theorem pureMetricFullDirection_sectorial_Euler_zero
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction (pureMetricFullDirection period hPeriod metric) = 0 := by
  exact fullMatterRobinTrueLLEuler_eq_zero_of_activeProjection_zero period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    (pureMetricFullDirection period hPeriod metric)
    (pureMetricFullDirection_activeProjection_zero period hPeriod metric)

theorem pureMetricFullDirection_sectorial_Hessian_zero_left
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (metric : SmoothDiagonalMetricVariation period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields (pureMetricFullDirection period hPeriod metric) direction = 0 := by
  exact globalMatterRobinFullLLHessian_inactive_left period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields (pureMetricFullDirection period hPeriod metric) direction
    (pureMetricFullDirection_activeProjection_zero period hPeriod metric)

theorem pureMetricFullDirection_sectorial_Hessian_zero_right
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (metric : SmoothDiagonalMetricVariation period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields direction (pureMetricFullDirection period hPeriod metric) = 0 := by
  exact globalMatterRobinFullLLHessian_inactive_right period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields direction (pureMetricFullDirection period hPeriod metric)
    (pureMetricFullDirection_activeProjection_zero period hPeriod metric)

end
end P0EFTJanusFullMatterRobinTrueLLPureMetricInactive4D
end JanusFormal
