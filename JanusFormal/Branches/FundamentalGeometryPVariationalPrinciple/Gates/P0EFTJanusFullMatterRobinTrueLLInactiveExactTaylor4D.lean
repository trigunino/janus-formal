import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveFirstOrderQuotientD94D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveOrdersThreeFour4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveExactTaylor4D

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
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFirstOrderQuotientD94D
open P0EFTJanusFullMatterRobinTrueLLInactiveDiagonalOrderTwo4D
open P0EFTJanusFullMatterRobinTrueLLInactiveOrdersThreeFour4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Exact Taylor certificate for a direction invisible to every active slot of
the genuine assembled action. -/
theorem inactive_exactTaylor_coefficients_and_action
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction direction = 0 ∧
      fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields direction = 0 ∧
      globalPTFullLLTaylorCubic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure = 0 ∧
      globalPTFullLLTaylorQuartic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure = 0 ∧
      ∀ t : Real, fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
          bulkMinus robinMeasure frame llMeasure fields junction direction t =
        fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
          robinMeasure frame llMeasure fields junction := by
  refine ⟨fullMatterRobinTrueLLTaylorC1_eq_zero_of_inactive period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
      hInactive, ?_⟩
  refine ⟨fullMatterRobinTrueLLTaylorC2_eq_zero_of_inactive period hPeriod matterData
      kPlus kMinus robinMeasure frame llMeasure fields direction hInactive, ?_⟩
  refine ⟨globalPTFullLLTaylorCubic_eq_zero_of_inactive period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
      hInactive, ?_⟩
  refine ⟨globalPTFullLLTaylorQuartic_eq_zero_of_inactive period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
      hInactive, ?_⟩
  exact fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction hInactive

/-- All derivatives through the quartic order vanish for the same exact
constant assembled curve. -/
theorem inactive_exactTaylor_iteratedDeriv_one_to_four
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    iteratedDeriv 1 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 ∧
      iteratedDeriv 2 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 ∧
      iteratedDeriv 3 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 ∧
      iteratedDeriv 4 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 := by
  have hCurve : (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) =
      fun _ : Real => fullMatterRobinTrueLLAction period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction := by
    funext t
    exact fullMatterRobinTrueLLCurve_eq_base_of_activeProjection_zero period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
      hInactive t
  rw [hCurve]
  simp (discharger := fun_prop) [iteratedDeriv_const]

end
end P0EFTJanusFullMatterRobinTrueLLInactiveExactTaylor4D
end JanusFormal
