import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLActiveQuotientDerivatives4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorPolarizationActiveQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2Polarization4D

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
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientTaylor4D
open P0EFTJanusFullMatterRobinTrueLLActiveQuotientDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLTaylorPolarizationActiveQuotient4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Canonical set-level sum obtained from the active representatives. -/
def activeQuotientAdd (first second : ActiveQuotient period hPeriod) :
    ActiveQuotient period hPeriod :=
  ⟦addDirection period hPeriod
    (activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod first))
    (activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod second))⟧

/-- Canonical set-level difference obtained from the active representatives. -/
def activeQuotientSub (first second : ActiveQuotient period hPeriod) :
    ActiveQuotient period hPeriod :=
  ⟦subDirection period hPeriod
    (activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod first))
    (activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod second))⟧

theorem activeRepresentative_class
    (direction : ActiveQuotient period hPeriod) :
    (⟦activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod direction)⟧ :
      ActiveQuotient period hPeriod) = direction := by
  apply (activeQuotientEquiv period hPeriod).injective
  simp

theorem quotientHessian_eq_polarized_activeQuotientC2
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second : ActiveQuotient period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        first second =
      (1 / 2 : Real) *
        (activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (activeQuotientAdd period hPeriod first second) -
         activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (activeQuotientSub period hPeriod first second)) := by
  let x := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod first)
  let y := activeRepresentative period hPeriod (activeQuotientEquiv period hPeriod second)
  have h := quotientHessian_mk_eq_difference_diagonal_C2 period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields x y
  rw [activeRepresentative_class period hPeriod first, activeRepresentative_class period hPeriod second] at h
  simpa [activeQuotientAdd, activeQuotientSub, x, y] using h

theorem polarized_activeQuotientC2_symmetric
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (first second : ActiveQuotient period hPeriod) :
    (1 / 2 : Real) *
        (activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (activeQuotientAdd period hPeriod first second) -
         activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (activeQuotientSub period hPeriod first second)) =
      (1 / 2 : Real) *
        (activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (activeQuotientAdd period hPeriod second first) -
         activeQuotientC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
            (activeQuotientSub period hPeriod second first)) := by
  rw [← quotientHessian_eq_polarized_activeQuotientC2,
    ← quotientHessian_eq_polarized_activeQuotientC2]
  exact quotientHessian_symmetric period hPeriod matterData kPlus kMinus robinMeasure frame
    llMeasure fields first second

end
end P0EFTJanusFullMatterRobinTrueLLActiveQuotientC2Polarization4D
end JanusFormal
