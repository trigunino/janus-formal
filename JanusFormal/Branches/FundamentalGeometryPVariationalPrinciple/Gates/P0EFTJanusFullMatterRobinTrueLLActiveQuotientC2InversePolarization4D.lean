import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2Polarization4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2InversePolarization4D

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
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusFullLLHessianExplicitPolarization4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientTaylor4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2Polarization4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

@[simp] theorem activeQuotientAdd_mk
    (first second : FullMatterRobinLLDirections period hPeriod) :
    activeQuotientAdd period hPeriod (⟦first⟧ : ActiveQuotient period hPeriod) ⟦second⟧ =
      (⟦addDirection period hPeriod first second⟧ : ActiveQuotient period hPeriod) := by
  apply (activeQuotientEquiv period hPeriod).injective
  rfl

@[simp] theorem activeQuotientSub_mk
    (first second : FullMatterRobinLLDirections period hPeriod) :
    activeQuotientSub period hPeriod (⟦first⟧ : ActiveQuotient period hPeriod) ⟦second⟧ =
      (⟦subDirection period hPeriod first second⟧ : ActiveQuotient period hPeriod) := by
  apply (activeQuotientEquiv period hPeriod).injective
  rfl

theorem quotientHessian_diagonal_eq_two_activeQuotientC2
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (direction : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        direction direction =
      2 * activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
        fields direction := by
  rw [activeQuotientC2_eq_half_Hessian]
  ring

theorem activeQuotientC2_eq_quarter_polarized_diagonal
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (direction : ActiveQuotient period hPeriod) :
    activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        direction =
      (1 / 4 : Real) *
        (activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (activeQuotientAdd period hPeriod direction direction) -
         activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (activeQuotientSub period hPeriod direction direction)) := by
  rw [activeQuotientC2_eq_half_Hessian,
    quotientHessian_eq_polarized_activeQuotientC2]
  ring

end
end P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2InversePolarization4D
end JanusFormal
