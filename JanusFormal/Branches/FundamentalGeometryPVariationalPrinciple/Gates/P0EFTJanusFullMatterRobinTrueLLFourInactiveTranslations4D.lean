import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLGaugeTranslationInvariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLPureMetricInactive4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedCoefficientActiveQuotientDerivatives4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLMixedEnrichedD9Observation4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLFourInactiveTranslations4D

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
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Hessian4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLMixedTaylorCoefficient4D
open P0EFTJanusFullMatterRobinTrueLLMixedCoefficientActiveQuotientDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLMixedEnrichedD9Observation4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def fourInactiveDirection
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) : FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric := metric
      matter := 0
      gauge := gauge
      ghost := ghost
      auxiliary := auxiliary
      ll := 0 }
  robin := 0
  llAuxMetric := 0
  llMeasure := 0

def addFourInactive (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) : FullMatterRobinLLDirections period hPeriod :=
  addDirection period hPeriod direction
    (fourInactiveDirection period hPeriod metric gauge ghost auxiliary)

theorem addFourInactive_activeProjection (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    activeProjection period hPeriod (addFourInactive period hPeriod direction metric gauge ghost auxiliary) =
      activeProjection period hPeriod direction := by
  simp [addFourInactive, fourInactiveDirection, addDirection, activeProjection]

theorem addFourInactive_activeQuotientClass (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    (⟦addFourInactive period hPeriod direction metric gauge ghost auxiliary⟧ : ActiveQuotient period hPeriod) =
      ⟦direction⟧ := by
  apply (activeQuotientEquiv period hPeriod).injective
  simpa using addFourInactive_activeProjection period hPeriod direction metric gauge ghost auxiliary

theorem addFourInactive_D9_activeReading (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod fields
      (addFourInactive period hPeriod direction metric gauge ghost auxiliary) sector column point) =
    toActiveDirection period hPeriod
      (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point) := by
  simpa using addFourInactive_activeProjection period hPeriod direction metric gauge ghost auxiliary

theorem addFourInactive_curve (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real) (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber)
    (t : Real) :
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
      llMeasure fields junction (addFourInactive period hPeriod direction metric gauge ghost auxiliary) t =
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
      llMeasure fields junction direction t := by
  simp [fullMatterRobinTrueLLCurve, addFourInactive, fourInactiveDirection, addDirection,
    differentialLLFullCurve]

theorem addFourInactive_curve_function (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real) (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction
        (addFourInactive period hPeriod direction metric gauge ghost auxiliary) t) =
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction direction t) := by
  funext t
  exact addFourInactive_curve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure fields junction direction metric gauge ghost auxiliary t

theorem addFourInactive_C1 (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
      llMeasure fields junction (addFourInactive period hPeriod direction metric gauge ghost auxiliary) =
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
      llMeasure fields junction direction := by
  rw [fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler, fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler,
    trueEuler_factors_active, trueEuler_factors_active, addFourInactive_activeProjection]

theorem addFourInactive_C2 (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      (addFourInactive period hPeriod direction metric gauge ghost auxiliary) =
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
      direction := by
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian, fullHessian_factors_active,
    fullHessian_factors_active, addFourInactive_activeProjection]

theorem addFourInactive_iteratedDeriv_one_to_four (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real) (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real) (direction : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    ∀ order ∈ ({1, 2, 3, 4} : Finset Nat),
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
          (addFourInactive period hPeriod direction metric gauge ghost auxiliary) t) 0 =
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 := by
  intro order _
  rw [addFourInactive_curve_function period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction direction metric gauge ghost auxiliary]

theorem addFourInactive_C3_C4 (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod) (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    globalPTFullLLTaylorCubic period hPeriod frame fields
        (addFourInactive period hPeriod direction metric gauge ghost auxiliary).llAuxMetric
        (fullDirectionLLVariation period hPeriod
          (addFourInactive period hPeriod direction metric gauge ghost auxiliary)) llMeasure =
      globalPTFullLLTaylorCubic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure ∧
    globalPTFullLLTaylorQuartic period hPeriod frame fields
        (addFourInactive period hPeriod direction metric gauge ghost auxiliary).llAuxMetric
        (fullDirectionLLVariation period hPeriod
          (addFourInactive period hPeriod direction metric gauge ghost auxiliary)) llMeasure =
      globalPTFullLLTaylorQuartic period hPeriod frame fields direction.llAuxMetric
        (fullDirectionLLVariation period hPeriod direction) llMeasure := by
  have hFun := addFourInactive_curve_function period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction metric gauge ghost auxiliary
  constructor
  · have ha := fullMatterRobinTrueLLCurve_third_iteratedDeriv period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      (addFourInactive period hPeriod direction metric gauge ghost auxiliary)
    have hb := fullMatterRobinTrueLLCurve_third_iteratedDeriv period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
    rw [hFun] at ha
    linarith
  · have ha := fullMatterRobinTrueLLCurve_fourth_iteratedDeriv period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
      (addFourInactive period hPeriod direction metric gauge ghost auxiliary)
    have hb := fullMatterRobinTrueLLCurve_fourth_iteratedDeriv period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
    rw [hFun] at ha
    linarith

theorem addFourInactive_Hessian_three_slots
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields (addFourInactive period hPeriod first metric gauge ghost auxiliary) second =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first second ∧
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first (addFourInactive period hPeriod second metric gauge ghost auxiliary) =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first second ∧
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields (addFourInactive period hPeriod first metric gauge ghost auxiliary)
          (addFourInactive period hPeriod second metric gauge ghost auxiliary) =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields first second := by
  simp [fullHessian_factors_active,
    addFourInactive_activeProjection period hPeriod first metric gauge ghost auxiliary,
    addFourInactive_activeProjection period hPeriod second metric gauge ghost auxiliary]

theorem addFourInactive_mixedTaylorCoefficient_three_slots
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields (addFourInactive period hPeriod first metric gauge ghost auxiliary) second =
      fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields first second ∧
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields first (addFourInactive period hPeriod second metric gauge ghost auxiliary) =
      fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields first second ∧
    fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields (addFourInactive period hPeriod first metric gauge ghost auxiliary)
          (addFourInactive period hPeriod second metric gauge ghost auxiliary) =
      fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData kPlus kMinus robinMeasure
        frame llMeasure fields first second := by
  simp only [fullMatterRobinTrueLLMixedTaylorCoefficient_eq_actualHessian]
  exact addFourInactive_Hessian_three_slots period hPeriod matterData kPlus kMinus robinMeasure
    frame llMeasure fields first second metric gauge ghost auxiliary

theorem addFourInactive_representativeEuler_mixedDerivatives_three_slots
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    let coefficient := fullMatterRobinTrueLLMixedTaylorCoefficient period hPeriod matterData
      kPlus kMinus robinMeasure frame llMeasure fields first second
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure matter junction fields
        (addFourInactive period hPeriod first metric gauge ghost auxiliary) second) coefficient 0 ∧
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure matter junction fields first
        (addFourInactive period hPeriod second metric gauge ghost auxiliary)) coefficient 0 ∧
    HasDerivAt (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure matter junction fields
        (addFourInactive period hPeriod first metric gauge ghost auxiliary)
        (addFourInactive period hPeriod second metric gauge ghost auxiliary)) coefficient 0 := by
  dsimp only
  have hCoeff := addFourInactive_mixedTaylorCoefficient_three_slots period hPeriod matterData
    kPlus kMinus robinMeasure frame llMeasure fields first second metric gauge ghost auxiliary
  refine ⟨?_, ?_, ?_⟩
  · rw [← hCoeff.1]
    exact representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields
      (addFourInactive period hPeriod first metric gauge ghost auxiliary) second
  · rw [← hCoeff.2.1]
    exact representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields first
      (addFourInactive period hPeriod second metric gauge ghost auxiliary)
  · rw [← hCoeff.2.2]
    exact representativeEulerCurve_hasDerivAt_mixedTaylorCoefficient period hPeriod matterData
      kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure matter junction fields
      (addFourInactive period hPeriod first metric gauge ghost auxiliary)
      (addFourInactive period hPeriod second metric gauge ghost auxiliary)

/-- Quotient-active Hessian invariance under the four combined inactive
translations. This is not a quotient for the complete Candidate A action. -/
theorem addFourInactive_quotientHessian_three_slots
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦addFourInactive period hPeriod first metric gauge ghost auxiliary⟧ ⟦second⟧ =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦first⟧ ⟦second⟧ ∧
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦first⟧ ⟦addFourInactive period hPeriod second metric gauge ghost auxiliary⟧ =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦first⟧ ⟦second⟧ ∧
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦addFourInactive period hPeriod first metric gauge ghost auxiliary⟧
        ⟦addFourInactive period hPeriod second metric gauge ghost auxiliary⟧ =
      quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦first⟧ ⟦second⟧ := by
  rw [addFourInactive_activeQuotientClass period hPeriod first metric gauge ghost auxiliary,
    addFourInactive_activeQuotientClass period hPeriod second metric gauge ghost auxiliary]
  exact ⟨rfl, rfl, rfl⟩

/-- The same three-slot invariance read through the global-matter-enriched D9
observations. Candidate A terms are absent. -/
theorem addFourInactive_enrichedD9ActiveHessian_three_slots
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields
          (addFourInactive period hPeriod first metric gauge ghost auxiliary) sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) ∧
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields
          (addFourInactive period hPeriod second metric gauge ghost auxiliary) sector column point) =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) ∧
    enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields
          (addFourInactive period hPeriod first metric gauge ghost auxiliary) sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields
          (addFourInactive period hPeriod second metric gauge ghost auxiliary) sector column point) =
      enrichedD9ActiveHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        (globalMatterEnrichedD9Projection period hPeriod fields first sector column point)
        (globalMatterEnrichedD9Projection period hPeriod fields second sector column point) := by
  have hMixed := addFourInactive_mixedTaylorCoefficient_three_slots period hPeriod matterData
    kPlus kMinus robinMeasure frame llMeasure fields first second metric gauge ghost auxiliary
  constructor
  · rw [← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian period hPeriod
      matterData kPlus kMinus robinMeasure frame llMeasure fields sector column point,
      ← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian period hPeriod
        matterData kPlus kMinus robinMeasure frame llMeasure fields sector column point]
    exact hMixed.1
  constructor
  · rw [← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian period hPeriod
      matterData kPlus kMinus robinMeasure frame llMeasure fields sector column point,
      ← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian period hPeriod
        matterData kPlus kMinus robinMeasure frame llMeasure fields sector column point]
    exact hMixed.2.1
  · rw [← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian period hPeriod
      matterData kPlus kMinus robinMeasure frame llMeasure fields sector column point,
      ← fullMatterRobinTrueLLMixedTaylorCoefficient_eq_enrichedD9ActiveHessian period hPeriod
        matterData kPlus kMinus robinMeasure frame llMeasure fields sector column point]
    exact hMixed.2.2

end
end P0EFTJanusFullMatterRobinTrueLLFourInactiveTranslations4D
end JanusFormal
