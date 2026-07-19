import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveTranslationTwoSidedNondegeneracy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientTwoSidedKernel4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveToActiveQuotientNondegeneracy4D

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
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientKernelReconstruction4D
open P0EFTJanusMatterRobinFullLLActiveQuotientTwoSidedKernel4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationNondegeneracy4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationTwoSidedNondegeneracy4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def zeroActiveQuotient : ActiveQuotient period hPeriod :=
  (activeQuotientEquiv period hPeriod).symm (zeroActiveDirection period hPeriod)

def activeQuotientHessianLeftNondegenerate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) : Prop :=
  ∀ first, (∀ second, quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields first second = 0) → first = zeroActiveQuotient period hPeriod

def activeQuotientHessianRightNondegenerate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) : Prop :=
  ∀ second, (∀ first, quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields first second = 0) → second = zeroActiveQuotient period hPeriod

theorem activeQuotientHessianLeftNondegenerate_iff_active
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    activeQuotientHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields ↔
      activeHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields := by
  constructor
  · intro h active hKernel
    let quotient := (activeQuotientEquiv period hPeriod).symm active
    have hQuotientKernel : ∀ second, quotientHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields quotient second = 0 :=
      (quotientHessian_leftKernel_iff_activeHessian_leftKernel period hPeriod matterData kPlus
        kMinus robinMeasure frame llMeasure fields quotient).2 (by simpa [quotient] using hKernel)
    have hZero := h quotient hQuotientKernel
    apply (activeQuotientEquiv period hPeriod).symm.injective
    simpa [quotient, zeroActiveQuotient] using hZero
  · intro h quotient hKernel
    apply (activeQuotientEquiv period hPeriod).injective
    simp only [zeroActiveQuotient, Equiv.apply_symm_apply]
    apply h
    exact (quotientHessian_leftKernel_iff_activeHessian_leftKernel period hPeriod matterData
      kPlus kMinus robinMeasure frame llMeasure fields quotient).1 hKernel

theorem activeQuotientHessianRightNondegenerate_iff_active
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    activeQuotientHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields ↔
      activeHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields := by
  constructor
  · intro h active hKernel
    let quotient := (activeQuotientEquiv period hPeriod).symm active
    have hQuotientKernel : ∀ first, quotientHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first quotient = 0 :=
      (quotientHessian_rightKernel_iff_activeHessian_rightKernel period hPeriod matterData kPlus
        kMinus robinMeasure frame llMeasure fields quotient).2 (by simpa [quotient] using hKernel)
    have hZero := h quotient hQuotientKernel
    apply (activeQuotientEquiv period hPeriod).symm.injective
    simpa [quotient, zeroActiveQuotient] using hZero
  · intro h quotient hKernel
    apply (activeQuotientEquiv period hPeriod).injective
    simp only [zeroActiveQuotient, Equiv.apply_symm_apply]
    apply h
    exact (quotientHessian_rightKernel_iff_activeHessian_rightKernel period hPeriod matterData
      kPlus kMinus robinMeasure frame llMeasure fields quotient).1 hKernel

def activeQuotientHessianTwoSidedNondegenerate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) : Prop :=
  activeQuotientHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields ∧
    activeQuotientHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields

theorem inactiveQuotientHessianLeftNondegenerate_iff_activeQuotient
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    inactiveQuotientHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields ↔
      activeQuotientHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields := by
  rw [inactiveQuotientHessianLeftNondegenerate_iff_active,
    activeQuotientHessianLeftNondegenerate_iff_active]

theorem inactiveQuotientHessianRightNondegenerate_iff_activeQuotient
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    inactiveQuotientHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields ↔
      activeQuotientHessianRightNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields := by
  rw [inactiveQuotientHessianRightNondegenerate_iff_active,
    activeQuotientHessianRightNondegenerate_iff_active]

theorem inactiveQuotientHessianTwoSidedNondegenerate_iff_activeQuotient
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    inactiveQuotientHessianTwoSidedNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields ↔
      activeQuotientHessianTwoSidedNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields := by
  exact and_congr
    (inactiveQuotientHessianLeftNondegenerate_iff_activeQuotient period hPeriod matterData
      kPlus kMinus robinMeasure frame llMeasure fields)
    (inactiveQuotientHessianRightNondegenerate_iff_activeQuotient period hPeriod matterData
      kPlus kMinus robinMeasure frame llMeasure fields)

end
end P0EFTJanusFullMatterRobinTrueLLInactiveToActiveQuotientNondegeneracy4D
end JanusFormal
