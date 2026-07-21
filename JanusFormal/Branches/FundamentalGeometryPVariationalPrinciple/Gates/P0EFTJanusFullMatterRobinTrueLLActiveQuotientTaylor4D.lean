import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveToActiveQuotientStationarity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveTranslationHigherDescents4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLActiveQuotientTaylor4D

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
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationQuotient4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationDescents4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationHigherDescents4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def toInactive (direction : ActiveQuotient period hPeriod) :
    InactiveTranslationQuotient period hPeriod :=
  (inactiveTranslationQuotientEquivActiveQuotient period hPeriod).symm direction

theorem toInactive_mk (direction : FullMatterRobinLLDirections period hPeriod) :
    toInactive period hPeriod (⟦direction⟧ : ActiveQuotient period hPeriod) =
      inactiveTranslationMk period hPeriod direction := by
  apply (inactiveTranslationQuotientEquivActiveQuotient period hPeriod).injective
  simpa [toInactive] using
    (inactiveTranslation_projection_commutes_activeQuotient period hPeriod direction).symm

def activeQuotientCurve
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (t : Real) (direction : ActiveQuotient period hPeriod) : Real :=
  inactiveQuotientCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction t (toInactive period hPeriod direction)

def activeQuotientC1
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : ActiveQuotient period hPeriod) : Real :=
  inactiveQuotientC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure fields junction (toInactive period hPeriod direction)

def activeQuotientC2
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (direction : ActiveQuotient period hPeriod) : Real :=
  inactiveQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
    (toInactive period hPeriod direction)

def activeQuotientC3
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : ActiveQuotient period hPeriod) : Real :=
  inactiveQuotientC3 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure fields junction (toInactive period hPeriod direction)

def activeQuotientC4
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : ActiveQuotient period hPeriod) : Real :=
  inactiveQuotientC4 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure fields junction (toInactive period hPeriod direction)

@[simp] theorem activeQuotientCurve_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (t : Real) (direction : FullMatterRobinLLDirections period hPeriod) :
    activeQuotientCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction t (⟦direction⟧ : ActiveQuotient period hPeriod) =
      fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
        frame llMeasure fields junction direction t := by
  rw [activeQuotientCurve, toInactive_mk, inactiveQuotientCurve_mk]

@[simp] theorem activeQuotientC1_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure] (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) (direction : FullMatterRobinLLDirections period hPeriod) :
    activeQuotientC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction (⟦direction⟧ : ActiveQuotient period hPeriod) =
      fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction direction := by
  rw [activeQuotientC1, toInactive_mk, inactiveQuotientC1_mk]

@[simp] theorem activeQuotientC2_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure] (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (⟦direction⟧ : ActiveQuotient period hPeriod) =
      fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields direction := by
  rw [activeQuotientC2, toInactive_mk, inactiveQuotientC2_mk]

@[simp] theorem activeQuotientC3_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure] (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) (direction : FullMatterRobinLLDirections period hPeriod) :
    activeQuotientC3 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction (⟦direction⟧ : ActiveQuotient period hPeriod) =
      globalPTFullLLTaylorCubic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure := by
  rw [activeQuotientC3, toInactive_mk, inactiveQuotientC3_mk]

@[simp] theorem activeQuotientC4_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure] (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) (direction : FullMatterRobinLLDirections period hPeriod) :
    activeQuotientC4 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction (⟦direction⟧ : ActiveQuotient period hPeriod) =
      globalPTFullLLTaylorQuartic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure := by
  rw [activeQuotientC4, toInactive_mk, inactiveQuotientC4_mk]

theorem activeQuotientCurve_exact_taylor
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure] (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) (direction : ActiveQuotient period hPeriod) (t : Real) :
    activeQuotientCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction t direction =
      fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
          frame llMeasure fields junction +
        t * activeQuotientC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
          frame llMeasure fields junction direction +
        t ^ 2 * activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
          fields direction +
        t ^ 3 * activeQuotientC3 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
          frame llMeasure fields junction direction +
        t ^ 4 * activeQuotientC4 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
          frame llMeasure fields junction direction := by
  have h := inactiveQuotientCurve_exact_taylor period hPeriod matterData kPlus kMinus bulkPlus
    bulkMinus robinMeasure frame llMeasure fields junction (toInactive period hPeriod direction) t
  unfold activeQuotientCurve activeQuotientC1 activeQuotientC2 activeQuotientC3 activeQuotientC4
  unfold inactiveQuotientC2
  rw [h]
  ring

end
end P0EFTJanusFullMatterRobinTrueLLActiveQuotientTaylor4D
end JanusFormal
