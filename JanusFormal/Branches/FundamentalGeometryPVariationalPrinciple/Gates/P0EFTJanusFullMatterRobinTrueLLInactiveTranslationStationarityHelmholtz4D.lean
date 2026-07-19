import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveTranslationHigherDescents4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveTranslationStationarityHelmholtz4D

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
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationQuotient4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationDescents4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Stationarity of the assembled action against every direction modulo its
four inactive translation slots. This is only a proposition on a set quotient. -/
def inactiveQuotientStationary
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real) : Prop :=
  ∀ direction : InactiveTranslationQuotient period hPeriod,
    inactiveQuotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction direction = 0

theorem inactiveQuotientStationary_iff_fullEuler
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real) :
    inactiveQuotientStationary period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction ↔
      ∀ direction : FullMatterRobinLLDirections period hPeriod,
        fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
          robinMeasure frame llMeasure fields junction direction = 0 := by
  constructor
  · intro h direction
    simpa only [inactiveQuotientEuler_mk] using
      h (inactiveTranslationMk period hPeriod direction)
  · intro h
    intro direction
    induction direction using Quotient.inductionOn with
    | _ full =>
        have hmk := inactiveQuotientEuler_mk period hPeriod matterData kPlus kMinus bulkPlus
          bulkMinus robinMeasure frame llMeasure fields junction full
        simp only [inactiveTranslationMk] at hmk
        rw [hmk]
        exact h full

/-- The Helmholtz symmetry already proved for the assembled Hessian survives
the inactive set quotient in both direction arguments. -/
theorem inactiveQuotientHessian_symmetric
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : InactiveTranslationQuotient period hPeriod) :
    inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
        fields first second =
      inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
        fields second first := by
  unfold inactiveQuotientHessian
  exact activeHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame
    llMeasure fields _ _

end
end P0EFTJanusFullMatterRobinTrueLLInactiveTranslationStationarityHelmholtz4D
end JanusFormal
