import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorPolarization4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D

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
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLTaylorPolarization4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

private theorem activeHessian_zero_left
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (second : ActiveDirection period hPeriod) :
    activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields (zeroActiveDirection period hPeriod) second = 0 := by
  let zeroFull := activeRepresentative period hPeriod
    (zeroActiveDirection period hPeriod)
  let secondFull := activeRepresentative period hPeriod second
  have hId : addDirection period hPeriod zeroFull zeroFull = zeroFull := by
    simp [zeroFull, addDirection, activeRepresentative, zeroActiveDirection,
      P0EFTJanusProgramPCommonLLActionVariation4D.zeroSmoothDiagonalMetricVariation]
  have hAdd := assembledHessian_add_first period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields zeroFull zeroFull secondFull
  rw [hId] at hAdd
  change globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields zeroFull secondFull = 0
  linarith

/-- Any direction with zero active projection is in the left kernel of the
genuine assembled Hessian. -/
theorem globalMatterRobinFullLLHessian_inactive_left
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod first =
      zeroActiveDirection period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields first second = 0 := by
  rw [fullHessian_factors_active, hInactive]
  exact activeHessian_zero_left period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields (activeProjection period hPeriod second)

/-- The corresponding right-kernel statement follows from the true Hessian
symmetry. -/
theorem globalMatterRobinFullLLHessian_inactive_right
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod second =
      zeroActiveDirection period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields first second = 0 := by
  rw [globalMatterRobinFullLLHessian_symmetric]
  exact globalMatterRobinFullLLHessian_inactive_left period hPeriod matterData
    kPlus kMinus robinMeasure frame llMeasure fields second first hInactive

end
end P0EFTJanusFullMatterRobinTrueLLInactiveHessianKernel4D
end JanusFormal
