import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveTranslationNondegeneracy4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveTranslationTwoSidedNondegeneracy4D

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
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationQuotient4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationDescents4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationStationarityHelmholtz4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationNondegeneracy4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def inactiveQuotientHessianRightNondegenerate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) : Prop :=
  ∀ second, (∀ first, inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields first second = 0) →
    second = (inactiveTranslationQuotientEquivActiveDirection period hPeriod).symm
      (zeroActiveDirection period hPeriod)

def activeHessianRightNondegenerate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) : Prop :=
  ∀ second, (∀ first, activeHessian period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields first second = 0) → second = zeroActiveDirection period hPeriod

theorem inactiveQuotientHessianLeftNondegenerate_iff_right
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    inactiveQuotientHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields ↔
      inactiveQuotientHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields := by
  constructor <;> intro h direction hKernel
  · apply h direction
    intro other
    rw [inactiveQuotientHessian_symmetric]
    exact hKernel other
  · apply h direction
    intro other
    rw [inactiveQuotientHessian_symmetric]
    exact hKernel other

theorem activeHessianLeftNondegenerate_iff_right
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    activeHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields ↔
      activeHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields := by
  constructor <;> intro h direction hKernel
  · apply h direction
    intro other
    rw [activeHessian_symmetric]
    exact hKernel other
  · apply h direction
    intro other
    rw [activeHessian_symmetric]
    exact hKernel other

theorem inactiveQuotientHessianRightNondegenerate_iff_active
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    inactiveQuotientHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields ↔
      activeHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields := by
  rw [← inactiveQuotientHessianLeftNondegenerate_iff_right,
    inactiveQuotientHessianLeftNondegenerate_iff_active,
    activeHessianLeftNondegenerate_iff_right]

def inactiveQuotientHessianTwoSidedNondegenerate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) : Prop :=
  inactiveQuotientHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields ∧
    inactiveQuotientHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields

def activeHessianTwoSidedNondegenerate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) : Prop :=
  activeHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields ∧
    activeHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields

theorem inactiveQuotientHessianTwoSidedNondegenerate_iff_active
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    inactiveQuotientHessianTwoSidedNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields ↔
      activeHessianTwoSidedNondegenerate period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields := by
  exact and_congr
    (inactiveQuotientHessianLeftNondegenerate_iff_active period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields)
    (inactiveQuotientHessianRightNondegenerate_iff_active period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields)

end
end P0EFTJanusFullMatterRobinTrueLLInactiveTranslationTwoSidedNondegeneracy4D
end JanusFormal
