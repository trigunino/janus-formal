import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D

/-! Reconstruction of the descended Hessian and its left kernel on the exact active quotient. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLActiveQuotientKernelReconstruction4D
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

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem quotientHessian_eq_activeHessian_equiv
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (first second : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second =
      activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientEquiv period hPeriod first) (activeQuotientEquiv period hPeriod second) := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      rw [quotientHessian_mk, fullHessian_factors_active]
      rfl

theorem quotientHessian_leftKernel_iff_activeHessian_leftKernel
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (first : ActiveQuotient period hPeriod) :
    (∀ second, quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields first second = 0) ↔
      (∀ active, activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (activeQuotientEquiv period hPeriod first) active = 0) := by
  constructor
  · intro h active
    have hh := h ((activeQuotientEquiv period hPeriod).symm active)
    rw [quotientHessian_eq_activeHessian_equiv period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields first ((activeQuotientEquiv period hPeriod).symm active)] at hh
    simpa using hh
  · intro h second
    rw [quotientHessian_eq_activeHessian_equiv period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields first second]
    exact h _

end
end P0EFTJanusMatterRobinFullLLActiveQuotientKernelReconstruction4D
end JanusFormal
