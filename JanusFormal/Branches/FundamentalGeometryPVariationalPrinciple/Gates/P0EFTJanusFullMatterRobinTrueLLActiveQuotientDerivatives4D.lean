import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActiveQuotientTaylor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveTranslationHessianKernels4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLActiveQuotientDerivatives4D

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
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationQuotient4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationDescents4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationHessianKernels4D
open P0EFTJanusFullMatterRobinTrueLLInactiveToActiveQuotientStationarity4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientTaylor4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def activeQuotientIteratedDerivative
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (order : Nat) (direction : ActiveQuotient period hPeriod) : Real :=
  iteratedDeriv order (fun t => activeQuotientCurve period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction t direction) 0

@[simp] theorem activeQuotientIteratedDerivative_mk
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (order : Nat) (direction : FullMatterRobinLLDirections period hPeriod) :
    activeQuotientIteratedDerivative period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction order (⟦direction⟧ : ActiveQuotient period hPeriod) =
      iteratedDeriv order (fun t => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 := by
  unfold activeQuotientIteratedDerivative
  congr 1

theorem activeQuotientIteratedDerivative_normalized_one_to_four
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : ActiveQuotient period hPeriod) :
    activeQuotientIteratedDerivative period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction 1 direction =
          activeQuotientC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
            frame llMeasure fields junction direction ∧
    activeQuotientIteratedDerivative period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction 2 direction =
          2 * activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
            fields direction ∧
    activeQuotientIteratedDerivative period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction 3 direction =
          6 * activeQuotientC3 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
            frame llMeasure fields junction direction ∧
    activeQuotientIteratedDerivative period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction 4 direction =
          24 * activeQuotientC4 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
            frame llMeasure fields junction direction := by
  have hCurve : (fun t : Real => activeQuotientCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction t direction) = fun t =>
      fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
          robinMeasure frame llMeasure fields junction +
        t * activeQuotientC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
          frame llMeasure fields junction direction +
        t ^ 2 * activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
          fields direction +
        t ^ 3 * activeQuotientC3 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
          frame llMeasure fields junction direction +
        t ^ 4 * activeQuotientC4 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
          frame llMeasure fields junction direction := by
    funext t
    exact activeQuotientCurve_exact_taylor period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure fields junction direction t
  unfold activeQuotientIteratedDerivative
  rw [hCurve]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_mul,
    iteratedDeriv_const, iteratedDeriv_fun_id_zero, iteratedDeriv_fun_pow_zero]
  norm_num [Finset.sum_range_succ]

theorem activeQuotientC1_eq_Euler
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : ActiveQuotient period hPeriod) :
    activeQuotientC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction direction =
      activeQuotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
        frame llMeasure fields junction direction := by
  simp [activeQuotientC1, activeQuotientEuler, inactiveQuotientC1, inactiveQuotientEuler,
    P0EFTJanusFullMatterRobinTrueLLActiveQuotientTaylor4D.toInactive,
    inactiveTranslationQuotientEquivActiveQuotient]

theorem activeQuotientC2_eq_half_Hessian
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (direction : ActiveQuotient period hPeriod) :
    activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields direction =
      (1 / 2 : Real) * quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields direction direction := by
  unfold activeQuotientC2 inactiveQuotientC2
  rw [inactiveQuotientHessian_eq_activeQuotientHessian]
  simp [P0EFTJanusFullMatterRobinTrueLLActiveQuotientTaylor4D.toInactive]

end
end P0EFTJanusFullMatterRobinTrueLLActiveQuotientDerivatives4D
end JanusFormal
