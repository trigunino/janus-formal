import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveTranslationStationarityHelmholtz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientTwoSidedKernel4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveTranslationHessianKernels4D

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
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientKernelReconstruction4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationQuotient4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationDescents4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationStationarityHelmholtz4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem inactiveQuotientHessian_eq_activeHessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : InactiveTranslationQuotient period hPeriod) :
    inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
        fields first second =
      activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (inactiveTranslationQuotientEquivActiveDirection period hPeriod first)
        (inactiveTranslationQuotientEquivActiveDirection period hPeriod second) := rfl

theorem inactiveQuotientHessian_eq_activeQuotientHessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : InactiveTranslationQuotient period hPeriod) :
    inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
        fields first second =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (inactiveTranslationQuotientEquivActiveQuotient period hPeriod first)
        (inactiveTranslationQuotientEquivActiveQuotient period hPeriod second) := by
  rw [quotientHessian_eq_activeHessian_equiv]
  simp [inactiveQuotientHessian, inactiveTranslationQuotientEquivActiveQuotient]

theorem inactiveQuotientHessian_leftKernel_iff_activeHessian_leftKernel
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first : InactiveTranslationQuotient period hPeriod) :
    (∀ second, inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first second = 0) ↔
      (∀ active, activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
        fields (inactiveTranslationQuotientEquivActiveDirection period hPeriod first) active = 0) := by
  constructor
  · intro h active
    have hh := h ((inactiveTranslationQuotientEquivActiveDirection period hPeriod).symm active)
    simpa [inactiveQuotientHessian] using hh
  · intro h second
    rw [inactiveQuotientHessian_eq_activeHessian]
    exact h _

theorem inactiveQuotientHessian_rightKernel_iff_activeHessian_rightKernel
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (second : InactiveTranslationQuotient period hPeriod) :
    (∀ first, inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first second = 0) ↔
      (∀ active, activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
        fields active (inactiveTranslationQuotientEquivActiveDirection period hPeriod second) = 0) := by
  constructor
  · intro h active
    have hh := h ((inactiveTranslationQuotientEquivActiveDirection period hPeriod).symm active)
    simpa [inactiveQuotientHessian] using hh
  · intro h first
    rw [inactiveQuotientHessian_eq_activeHessian]
    exact h _

theorem inactiveQuotientHessian_leftKernel_iff_rightKernel
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (direction : InactiveTranslationQuotient period hPeriod) :
    (∀ other, inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields direction other = 0) ↔
      (∀ other, inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields other direction = 0) := by
  constructor <;> intro h other
  · rw [inactiveQuotientHessian_symmetric]
    exact h other
  · rw [inactiveQuotientHessian_symmetric]
    exact h other

end
end P0EFTJanusFullMatterRobinTrueLLInactiveTranslationHessianKernels4D
end JanusFormal
