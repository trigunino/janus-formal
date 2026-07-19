import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveDiagonalOrderTwo4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveOrdersThreeFour4D

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
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem inactive_llField_eq_zero
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    direction.common.ll = 0 := by
  exact congrArg ActiveDirection.llField hInactive

theorem inactive_llAuxMetric_eq_zero
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    direction.llAuxMetric = 0 := by
  exact congrArg ActiveDirection.llAuxMetric hInactive

theorem inactive_llMeasure_eq_zero
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    direction.llMeasure = 0 := by
  exact congrArg ActiveDirection.llMeasure hInactive

private theorem inactive_iteratedDeriv_eq_zero
    (order : Nat)
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod)
    (hOrder : order ≠ 0) :
    iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 := by
  rw [show (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) =
      fun _ : Real => fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction by
    funext t
    exact fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
      hInactive t]
  simp (discharger := fun_prop) [iteratedDeriv_const, hOrder]

theorem fullMatterRobinTrueLLCurve_third_iteratedDeriv_eq_zero_of_inactive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    iteratedDeriv 3 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 :=
  inactive_iteratedDeriv_eq_zero period hPeriod 3 matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction hInactive (by norm_num)

theorem fullMatterRobinTrueLLCurve_fourth_iteratedDeriv_eq_zero_of_inactive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    iteratedDeriv 4 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 :=
  inactive_iteratedDeriv_eq_zero period hPeriod 4 matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction hInactive (by norm_num)

theorem globalPTFullLLTaylorCubic_eq_zero_of_inactive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    globalPTFullLLTaylorCubic period hPeriod frame fields direction.llAuxMetric
      (fullDirectionLLVariation period hPeriod direction) llMeasure = 0 := by
  have hDeriv := fullMatterRobinTrueLLCurve_third_iteratedDeriv period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
  have hZero := fullMatterRobinTrueLLCurve_third_iteratedDeriv_eq_zero_of_inactive period hPeriod
    matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    direction hInactive
  linarith

theorem globalPTFullLLTaylorQuartic_eq_zero_of_inactive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    globalPTFullLLTaylorQuartic period hPeriod frame fields direction.llAuxMetric
      (fullDirectionLLVariation period hPeriod direction) llMeasure = 0 := by
  have hDeriv := fullMatterRobinTrueLLCurve_fourth_iteratedDeriv period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
  have hZero := fullMatterRobinTrueLLCurve_fourth_iteratedDeriv_eq_zero_of_inactive period hPeriod
    matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    direction hInactive
  linarith

end
end P0EFTJanusFullMatterRobinTrueLLInactiveOrdersThreeFour4D
end JanusFormal
