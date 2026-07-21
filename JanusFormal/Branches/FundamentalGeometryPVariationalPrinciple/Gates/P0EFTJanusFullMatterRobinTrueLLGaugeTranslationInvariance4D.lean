import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLPureGaugeSectorialCertificate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorC1EnrichedD9Observation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLGaugeTranslationInvariance4D

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
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLPureGaugeInactive4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def addPureGauge (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) : FullMatterRobinLLDirections period hPeriod :=
  addDirection period hPeriod direction (pureGaugeFullDirection period hPeriod gauge)

theorem addPureGauge_activeProjection
    (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    activeProjection period hPeriod (addPureGauge period hPeriod direction gauge) =
      activeProjection period hPeriod direction := by
  simp [addPureGauge, addDirection, pureGaugeFullDirection, activeProjection]

theorem addPureGauge_activeQuotientClass
    (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    (⟦addPureGauge period hPeriod direction gauge⟧ : ActiveQuotient period hPeriod) = ⟦direction⟧ := by
  apply (activeQuotientEquiv period hPeriod).injective
  simpa using addPureGauge_activeProjection period hPeriod direction gauge

theorem addPureGauge_enrichedD9_activeReading
    (fields : IndependentFields period hPeriod) (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod fields
      (addPureGauge period hPeriod direction gauge) sector column point) =
    toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod fields
      direction sector column point) := by
  simpa using addPureGauge_activeProjection period hPeriod direction gauge

/-- Equality for the matter + Robin + LL sector only. Maxwell is absent and
this is not a quotient by the global gauge group. -/
theorem addPureGauge_sectorial_curve
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) (t : Real) :
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction (addPureGauge period hPeriod direction gauge) t =
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction direction t := by
  simp [fullMatterRobinTrueLLCurve, addPureGauge, addDirection, pureGaugeFullDirection,
    differentialLLFullCurve]

theorem addPureGauge_TaylorC1
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction (addPureGauge period hPeriod direction gauge) =
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction direction := by
  rw [fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler,
    fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler, trueEuler_factors_active,
    trueEuler_factors_active, addPureGauge_activeProjection]

theorem addPureGauge_TaylorC2
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields (addPureGauge period hPeriod direction gauge) =
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields direction := by
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    fullHessian_factors_active, fullHessian_factors_active,
    addPureGauge_activeProjection]

theorem addPureGauge_sectorial_curve_function
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
        (addPureGauge period hPeriod direction gauge) t) =
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) := by
  funext t
  exact addPureGauge_sectorial_curve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction gauge t

theorem addPureGauge_iteratedDeriv_one_to_four
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    ∀ order ∈ ({1, 2, 3, 4} : Finset Nat),
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
          (addPureGauge period hPeriod direction gauge) t) 0 =
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 := by
  intro order _
  rw [addPureGauge_sectorial_curve_function period hPeriod matterData kPlus kMinus bulkPlus
    bulkMinus robinMeasure frame llMeasure fields junction direction gauge]

theorem addPureGauge_TaylorCubic
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    globalPTFullLLTaylorCubic period hPeriod frame fields
        (addPureGauge period hPeriod direction gauge).llAuxMetric
        (fullDirectionLLVariation period hPeriod (addPureGauge period hPeriod direction gauge)) llMeasure =
      globalPTFullLLTaylorCubic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure := by
  have hAdded := fullMatterRobinTrueLLCurve_third_iteratedDeriv period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    (addPureGauge period hPeriod direction gauge)
  have hInitial := fullMatterRobinTrueLLCurve_third_iteratedDeriv period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
  have hFunctions := addPureGauge_sectorial_curve_function period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction gauge
  rw [hFunctions] at hAdded
  linarith

theorem addPureGauge_TaylorQuartic
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    globalPTFullLLTaylorQuartic period hPeriod frame fields
        (addPureGauge period hPeriod direction gauge).llAuxMetric
        (fullDirectionLLVariation period hPeriod (addPureGauge period hPeriod direction gauge)) llMeasure =
      globalPTFullLLTaylorQuartic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure := by
  have hAdded := fullMatterRobinTrueLLCurve_fourth_iteratedDeriv period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    (addPureGauge period hPeriod direction gauge)
  have hInitial := fullMatterRobinTrueLLCurve_fourth_iteratedDeriv period hPeriod matterData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
  have hFunctions := addPureGauge_sectorial_curve_function period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction gauge
  rw [hFunctions] at hAdded
  linarith

end
end P0EFTJanusFullMatterRobinTrueLLGaugeTranslationInvariance4D
end JanusFormal
