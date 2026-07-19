import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveTranslationAction4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLInactiveTranslationInvariants4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLFourInactiveTranslations4D
open P0EFTJanusFullMatterRobinTrueLLActiveProjectionKernelStructure4D
open P0EFTJanusFullMatterRobinTrueLLInactiveTranslationAction4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem inactiveTranslate_eq_addFourInactive (data : ActiveProjectionKernelData period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    inactiveTranslate period hPeriod data direction = addFourInactive period hPeriod direction
      data.metric data.gauge data.ghost data.auxiliary := by rfl

theorem inactiveTranslate_curve_and_derivatives
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (data : ActiveProjectionKernelData period hPeriod) (direction : FullMatterRobinLLDirections period hPeriod) :
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction (inactiveTranslate period hPeriod data direction) t) =
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction direction t) ∧
    (∀ order ∈ ({1, 2, 3, 4} : Finset Nat),
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
          (inactiveTranslate period hPeriod data direction) t) 0 =
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0) := by
  rw [inactiveTranslate_eq_addFourInactive]
  exact ⟨addFourInactive_curve_function period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction data.metric data.gauge data.ghost data.auxiliary,
    addFourInactive_iteratedDeriv_one_to_four period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction direction data.metric data.gauge data.ghost data.auxiliary⟩

theorem inactiveTranslate_Euler_C1_C2
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure] (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) (data : ActiveProjectionKernelData period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction (inactiveTranslate period hPeriod data direction) =
      fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction direction ∧
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction (inactiveTranslate period hPeriod data direction) =
      fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
        llMeasure fields junction direction ∧
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (inactiveTranslate period hPeriod data direction) =
      fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        direction := by
  have hp := inactiveTranslate_activeProjection period hPeriod data direction
  refine ⟨?_, ?_, ?_⟩
  · rw [trueEuler_factors_active, trueEuler_factors_active, hp]
  · rw [inactiveTranslate_eq_addFourInactive]
    exact addFourInactive_C1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
      llMeasure fields junction direction data.metric data.gauge data.ghost data.auxiliary
  · rw [inactiveTranslate_eq_addFourInactive]
    exact addFourInactive_C2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      direction data.metric data.gauge data.ghost data.auxiliary

theorem inactiveTranslate_C3_C4
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure] (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) (data : ActiveProjectionKernelData period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    globalPTFullLLTaylorCubic period hPeriod frame fields (inactiveTranslate period hPeriod data direction).llAuxMetric
        (fullDirectionLLVariation period hPeriod (inactiveTranslate period hPeriod data direction)) llMeasure =
      globalPTFullLLTaylorCubic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure ∧
    globalPTFullLLTaylorQuartic period hPeriod frame fields (inactiveTranslate period hPeriod data direction).llAuxMetric
        (fullDirectionLLVariation period hPeriod (inactiveTranslate period hPeriod data direction)) llMeasure =
      globalPTFullLLTaylorQuartic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure := by
  rw [inactiveTranslate_eq_addFourInactive]
  exact addFourInactive_C3_C4 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure fields junction direction data.metric data.gauge data.ghost data.auxiliary

theorem inactiveTranslate_Hessian_quotient_D9
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod) (data : ActiveProjectionKernelData period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    (globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (inactiveTranslate period hPeriod data first) second =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        first second) ∧
    (quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦inactiveTranslate period hPeriod data first⟧ ⟦second⟧ =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields ⟦first⟧ ⟦second⟧) ∧
    (enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields
          (inactiveTranslate period hPeriod data first) sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point)) := by
  rw [inactiveTranslate_eq_addFourInactive]
  exact ⟨(addFourInactive_Hessian_three_slots period hPeriod matterData kPlus kMinus robinMeasure frame
    llMeasure fields first second data.metric data.gauge data.ghost data.auxiliary).1,
    (addFourInactive_quotientHessian_three_slots period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields first second data.metric data.gauge data.ghost data.auxiliary).1,
    (addFourInactive_enrichedD9ActiveHessian_three_slots period hPeriod matterData kPlus kMinus robinMeasure
      frame llMeasure fields sector column point first second data.metric data.gauge data.ghost data.auxiliary).1⟩

end
end P0EFTJanusFullMatterRobinTrueLLInactiveTranslationInvariants4D
end JanusFormal
