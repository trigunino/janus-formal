import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveToActiveQuotientNondegeneracy4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveToActiveQuotientStationarity4D

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
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
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

def activeQuotientEuler
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : ActiveQuotient period hPeriod) : Real :=
  activeEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure fields junction (activeQuotientEquiv period hPeriod direction)

def activeQuotientStationary
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real) : Prop :=
  ∀ direction, activeQuotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction = 0

theorem inactiveQuotientEuler_eq_activeQuotientEuler
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : InactiveTranslationQuotient period hPeriod) :
    inactiveQuotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
        frame llMeasure fields junction direction =
      activeQuotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
        frame llMeasure fields junction
          (inactiveTranslationQuotientEquivActiveQuotient period hPeriod direction) := by
  simp [inactiveQuotientEuler, activeQuotientEuler,
    inactiveTranslationQuotientEquivActiveQuotient]

theorem inactiveQuotientStationary_iff_activeQuotientStationary
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real) :
    inactiveQuotientStationary period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction ↔
      activeQuotientStationary period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction := by
  constructor
  · intro h direction
    let inactive := (inactiveTranslationQuotientEquivActiveQuotient period hPeriod).symm direction
    have hz := h inactive
    rw [inactiveQuotientEuler_eq_activeQuotientEuler] at hz
    simpa [inactive] using hz
  · intro h direction
    rw [inactiveQuotientEuler_eq_activeQuotientEuler]
    exact h _

def inactiveQuotientCritical
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : InactiveTranslationQuotient period hPeriod) : Prop :=
  inactiveQuotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction direction = 0

def activeQuotientCritical
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : ActiveQuotient period hPeriod) : Prop :=
  activeQuotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction direction = 0

theorem inactiveQuotientCritical_iff_activeQuotientCritical
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : InactiveTranslationQuotient period hPeriod) :
    inactiveQuotientCritical period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
        frame llMeasure fields junction direction ↔
      activeQuotientCritical period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
        frame llMeasure fields junction
          (inactiveTranslationQuotientEquivActiveQuotient period hPeriod direction) := by
  unfold inactiveQuotientCritical activeQuotientCritical
  rw [inactiveQuotientEuler_eq_activeQuotientEuler]

end
end P0EFTJanusFullMatterRobinTrueLLInactiveToActiveQuotientStationarity4D
end JanusFormal
