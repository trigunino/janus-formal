import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientKernelReconstruction4D

/-! Left and right kernels of the symmetric active quotient Hessian. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLActiveQuotientTwoSidedKernel4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
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
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusMatterRobinFullLLActiveQuotientKernelReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem quotientHessian_rightKernel_iff_activeHessian_rightKernel
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (second : ActiveQuotient period hPeriod) :
    (∀ first, quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second = 0) ↔
      (∀ active, activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        active (activeQuotientEquiv period hPeriod second) = 0) := by
  constructor
  · intro h active
    have hh := h ((activeQuotientEquiv period hPeriod).symm active)
    rw [quotientHessian_eq_activeHessian_equiv period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields ((activeQuotientEquiv period hPeriod).symm active) second] at hh
    simpa using hh
  · intro h first
    rw [quotientHessian_eq_activeHessian_equiv period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields first second]
    exact h _

theorem quotientHessian_leftKernel_iff_rightKernel
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (direction : ActiveQuotient period hPeriod) :
    (∀ other, quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields direction other = 0) ↔
      (∀ other, quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields other direction = 0) := by
  constructor <;> intro h other
  · rw [quotientHessian_eq_activeHessian_equiv, activeHessian_symmetric]
    rw [← quotientHessian_eq_activeHessian_equiv]
    exact h other
  · rw [quotientHessian_eq_activeHessian_equiv, activeHessian_symmetric]
    rw [← quotientHessian_eq_activeHessian_equiv]
    exact h other

end
end P0EFTJanusMatterRobinFullLLActiveQuotientTwoSidedKernel4D
end JanusFormal
