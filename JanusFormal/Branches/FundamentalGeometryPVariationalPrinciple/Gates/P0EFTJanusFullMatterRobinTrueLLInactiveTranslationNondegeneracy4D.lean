import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveTranslationHessianKernels4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveTranslationNondegeneracy4D

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
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationHessianKernels4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem inactiveQuotientStationary_iff_activeEuler
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real) :
    inactiveQuotientStationary period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction ↔
      ∀ active : ActiveDirection period hPeriod,
        activeEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
          llMeasure fields junction active = 0 := by
  constructor
  · intro h active
    exact h ((inactiveTranslationQuotientEquivActiveDirection period hPeriod).symm active)
  · intro h direction
    exact h (inactiveTranslationQuotientEquivActiveDirection period hPeriod direction)

def inactiveQuotientHessianLeftNondegenerate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) : Prop :=
  ∀ first, (∀ second, inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields first second = 0) →
    first = (inactiveTranslationQuotientEquivActiveDirection period hPeriod).symm
      (zeroActiveDirection period hPeriod)

def activeHessianLeftNondegenerate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) : Prop :=
  ∀ first, (∀ second, activeHessian period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields first second = 0) → first = zeroActiveDirection period hPeriod

theorem inactiveQuotientHessianLeftNondegenerate_iff_active
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    inactiveQuotientHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields ↔
      activeHessianLeftNondegenerate period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields := by
  constructor
  · intro h active hKernel
    let quotient := (inactiveTranslationQuotientEquivActiveDirection period hPeriod).symm active
    have hQuotientKernel : ∀ second, inactiveQuotientHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields quotient second = 0 :=
      (inactiveQuotientHessian_leftKernel_iff_activeHessian_leftKernel period hPeriod matterData
        kPlus kMinus robinMeasure frame llMeasure fields quotient).2 (by simpa [quotient] using hKernel)
    have hZero := h quotient hQuotientKernel
    apply (inactiveTranslationQuotientEquivActiveDirection period hPeriod).symm.injective
    simpa [quotient] using hZero
  · intro h quotient hKernel
    apply (inactiveTranslationQuotientEquivActiveDirection period hPeriod).injective
    apply h
    exact (inactiveQuotientHessian_leftKernel_iff_activeHessian_leftKernel period hPeriod matterData
      kPlus kMinus robinMeasure frame llMeasure fields quotient).1 hKernel

end
end P0EFTJanusFullMatterRobinTrueLLInactiveTranslationNondegeneracy4D
end JanusFormal
