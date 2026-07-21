import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveTranslationQuotient4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveTranslationDescents4D

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
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationAction4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationInvariants4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationQuotient4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def inactiveQuotientEuler
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : InactiveTranslationQuotient period hPeriod) : Real :=
  activeEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure fields junction (inactiveTranslationQuotientEquivActiveDirection period hPeriod direction)

def inactiveQuotientC1 := inactiveQuotientEuler

def inactiveQuotientHessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : InactiveTranslationQuotient period hPeriod) : Real :=
  activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
    (inactiveTranslationQuotientEquivActiveDirection period hPeriod first)
    (inactiveTranslationQuotientEquivActiveDirection period hPeriod second)

def inactiveQuotientC2
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (direction : InactiveTranslationQuotient period hPeriod) : Real :=
  (1 / 2 : Real) * inactiveQuotientHessian period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields direction direction

@[simp] theorem inactiveQuotientEuler_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    inactiveQuotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
        frame llMeasure fields junction (inactiveTranslationMk period hPeriod direction) =
      fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction direction := by
  rw [trueEuler_factors_active]
  rfl

@[simp] theorem inactiveQuotientC1_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    inactiveQuotientC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
        frame llMeasure fields junction (inactiveTranslationMk period hPeriod direction) =
      fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction direction := by
  rw [fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler]
  exact inactiveQuotientEuler_mk period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction

@[simp] theorem inactiveQuotientHessian_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    inactiveQuotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (inactiveTranslationMk period hPeriod first) (inactiveTranslationMk period hPeriod second) =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first second := by
  rw [fullHessian_factors_active]
  rfl

@[simp] theorem inactiveQuotientC2_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    inactiveQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (inactiveTranslationMk period hPeriod direction) =
      fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields direction := by
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian]
  rfl

/-- Parametrized sectorial action curve descended directly through the
set-theoretic translation quotient. -/
def inactiveQuotientCurve
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (t : Real) (direction : InactiveTranslationQuotient period hPeriod) : Real :=
  Quotient.lift (fun full => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction full t) (by
      intro first second hOrbit
      rcases hOrbit with ⟨data, hTranslate⟩
      subst second
      exact congrFun (inactiveTranslate_curve_and_derivatives period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction data first).1 t |>.symm)
    direction

@[simp] theorem inactiveQuotientCurve_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (t : Real) (direction : FullMatterRobinLLDirections period hPeriod) :
    inactiveQuotientCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction t (inactiveTranslationMk period hPeriod direction) =
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction direction t := rfl

end
end P0EFTJanusFullMatterRobinTrueLLInactiveTranslationDescents4D
end JanusFormal
