import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveCharacterization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveFirstOrderQuotientD94D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonGaugeD9Variation4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLPureGaugeInactive4D

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
open P0EFTJanusCommonGaugeD9Variation4D
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

/-- Injection of the already existing common gauge-only direction into the
full matter--Robin--LL direction space. All non-gauge slots are zero. -/
def pureGaugeFullDirection
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric := P0EFTJanusProgramPCommonLLActionVariation4D.zeroSmoothDiagonalMetricVariation
        period hPeriod
      matter := 0
      gauge := gauge
      ghost := 0
      auxiliary := 0
      ll := 0 }
  robin := 0
  llAuxMetric := 0
  llMeasure := 0

theorem pureGaugeFullDirection_realizes_common_gaugeOnly
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    fullMatterRobinLLVariation period hPeriod (pureGaugeFullDirection period hPeriod gauge) =
      (gaugeOnlyIndependentVariation period hPeriod gauge, 0) := by
  rfl

theorem pureGaugeFullDirection_activeProjection_zero
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    activeProjection period hPeriod (pureGaugeFullDirection period hPeriod gauge) =
      zeroActiveDirection period hPeriod := by
  rfl

/-- This is constancy only of the assembled matter + Robin + LL action.
The Maxwell action is not a summand of this functional, so this theorem is
not invariance of the complete Candidate A action. -/
theorem pureGaugeFullDirection_matterRobinLL_action_constant
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) (t : Real) :
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction (pureGaugeFullDirection period hPeriod gauge) t =
      fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction := by
  exact fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    (pureGaugeFullDirection period hPeriod gauge)
    (pureGaugeFullDirection_activeProjection_zero period hPeriod gauge) t

theorem pureGaugeFullDirection_matterRobinLL_Euler_zero
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction (pureGaugeFullDirection period hPeriod gauge) = 0 := by
  exact fullMatterRobinTrueLLEuler_eq_zero_of_activeProjection_zero period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    (pureGaugeFullDirection period hPeriod gauge)
    (pureGaugeFullDirection_activeProjection_zero period hPeriod gauge)

theorem pureGaugeFullDirection_matterRobinLL_Hessian_zero_left
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields (pureGaugeFullDirection period hPeriod gauge) direction = 0 := by
  exact globalMatterRobinFullLLHessian_inactive_left period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields (pureGaugeFullDirection period hPeriod gauge) direction
    (pureGaugeFullDirection_activeProjection_zero period hPeriod gauge)

theorem pureGaugeFullDirection_matterRobinLL_Hessian_zero_right
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields direction (pureGaugeFullDirection period hPeriod gauge) = 0 := by
  exact globalMatterRobinFullLLHessian_inactive_right period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields direction (pureGaugeFullDirection period hPeriod gauge)
    (pureGaugeFullDirection_activeProjection_zero period hPeriod gauge)

end
end P0EFTJanusFullMatterRobinTrueLLPureGaugeInactive4D
end JanusFormal
