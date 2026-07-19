import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGhostAuxiliaryInactiveExactCertificates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLGaugeTranslationInvariance4D

namespace JanusFormal
namespace P0EFTJanusGhostAuxiliaryTranslationInvariance4D
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
open P0EFTJanusMatterRobinFullLLActiveQuotientEquiv4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusGhostAuxiliaryInactiveSectorNoether4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def addGhost (direction : FullMatterRobinLLDirections period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber) :=
  addDirection period hPeriod direction (ghostFullDirection period hPeriod ghost)

def addAuxiliary (direction : FullMatterRobinLLDirections period hPeriod)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :=
  addDirection period hPeriod direction (auxiliaryFullDirection period hPeriod auxiliary)

@[simp] theorem addGhost_activeProjection (direction) (ghost) :
    activeProjection period hPeriod (addGhost period hPeriod direction ghost) =
      activeProjection period hPeriod direction := by
  simp [addGhost, addDirection, ghostFullDirection, activeProjection]

@[simp] theorem addAuxiliary_activeProjection (direction) (auxiliary) :
    activeProjection period hPeriod (addAuxiliary period hPeriod direction auxiliary) =
      activeProjection period hPeriod direction := by
  simp [addAuxiliary, addDirection, auxiliaryFullDirection, activeProjection]

theorem addGhost_quotient (direction) (ghost) :
    (⟦addGhost period hPeriod direction ghost⟧ : ActiveQuotient period hPeriod) = ⟦direction⟧ := by
  apply (activeQuotientEquiv period hPeriod).injective
  exact addGhost_activeProjection period hPeriod direction ghost

theorem addAuxiliary_quotient (direction) (auxiliary) :
    (⟦addAuxiliary period hPeriod direction auxiliary⟧ : ActiveQuotient period hPeriod) = ⟦direction⟧ := by
  apply (activeQuotientEquiv period hPeriod).injective
  exact addAuxiliary_activeProjection period hPeriod direction auxiliary

theorem addGhost_D9 (fields) (sector) (column) (point) (direction) (ghost) :
    toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod fields
      (addGhost period hPeriod direction ghost) sector column point) =
    toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod fields
      direction sector column point) := addGhost_activeProjection period hPeriod direction ghost

theorem addAuxiliary_D9 (fields) (sector) (column) (point) (direction) (auxiliary) :
    toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod fields
      (addAuxiliary period hPeriod direction auxiliary) sector column point) =
    toActiveDirection period hPeriod (globalMatterEnrichedD9Projection period hPeriod fields
      direction sector column point) := addAuxiliary_activeProjection period hPeriod direction auxiliary

theorem addGhost_sectorial_curve (matterData) (kPlus kMinus) (bulkPlus bulkMinus)
    (robinMeasure) (frame) (llMeasure) (fields) (junction) (direction) (ghost) (t : Real) :
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction (addGhost period hPeriod direction ghost) t =
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction direction t := by
  simp [fullMatterRobinTrueLLCurve, addGhost, addDirection, ghostFullDirection,
    P0EFTJanusDifferentialLLFullCurveActionDecomposition4D.differentialLLFullCurve]

theorem addAuxiliary_sectorial_curve (matterData) (kPlus kMinus) (bulkPlus bulkMinus)
    (robinMeasure) (frame) (llMeasure) (fields) (junction) (direction) (auxiliary) (t : Real) :
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction (addAuxiliary period hPeriod direction auxiliary) t =
    fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction direction t := by
  simp [fullMatterRobinTrueLLCurve, addAuxiliary, addDirection, auxiliaryFullDirection,
    P0EFTJanusDifferentialLLFullCurveActionDecomposition4D.differentialLLFullCurve]

theorem addGhost_C1 (matterData) (kPlus kMinus) (bulkPlus bulkMinus) (robinMeasure) (frame)
    (llMeasure) [IsFiniteMeasure llMeasure] (fields) (junction) (direction) (ghost) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction (addGhost period hPeriod direction ghost) =
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction direction := by
  rw [fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler,
    fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler,
    trueEuler_factors_active, trueEuler_factors_active,
    addGhost_activeProjection]

theorem addAuxiliary_C1 (matterData) (kPlus kMinus) (bulkPlus bulkMinus) (robinMeasure) (frame)
    (llMeasure) [IsFiniteMeasure llMeasure] (fields) (junction) (direction) (auxiliary) :
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction (addAuxiliary period hPeriod direction auxiliary) =
    fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction direction := by
  rw [fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler,
    fullMatterRobinTrueLLTaylorC1_eq_trueActionEuler,
    trueEuler_factors_active, trueEuler_factors_active,
    addAuxiliary_activeProjection]

theorem addGhost_C2 (matterData) (kPlus kMinus) (robinMeasure) (frame) (llMeasure)
    [IsFiniteMeasure llMeasure] (fields) (direction) (ghost) :
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields (addGhost period hPeriod direction ghost) =
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields direction := by
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    fullHessian_factors_active, fullHessian_factors_active,
    addGhost_activeProjection]

theorem addAuxiliary_C2 (matterData) (kPlus kMinus) (robinMeasure) (frame) (llMeasure)
    [IsFiniteMeasure llMeasure] (fields) (direction) (auxiliary) :
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields (addAuxiliary period hPeriod direction auxiliary) =
    fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure
      fields direction := by
  rw [fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    fullMatterRobinTrueLLTaylorC2_eq_half_trueActionHessian,
    fullHessian_factors_active, fullHessian_factors_active,
    addAuxiliary_activeProjection]

theorem addGhost_curve_function (matterData) (kPlus kMinus) (bulkPlus bulkMinus)
    (robinMeasure) (frame) (llMeasure) (fields) (junction) (direction) (ghost) :
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure fields junction (addGhost period hPeriod direction ghost) t) =
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure fields junction direction t) := by
  funext t
  exact addGhost_sectorial_curve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction ghost t

theorem addAuxiliary_curve_function (matterData) (kPlus kMinus) (bulkPlus bulkMinus)
    (robinMeasure) (frame) (llMeasure) (fields) (junction) (direction) (auxiliary) :
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure fields junction
        (addAuxiliary period hPeriod direction auxiliary) t) =
    (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus bulkPlus
      bulkMinus robinMeasure frame llMeasure fields junction direction t) := by
  funext t
  exact addAuxiliary_sectorial_curve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction auxiliary t

theorem addGhost_iteratedDeriv_one_to_four (matterData) (kPlus kMinus) (bulkPlus bulkMinus)
    (robinMeasure) (frame) (llMeasure) (fields) (junction) (direction) (ghost) :
    ∀ order ∈ ({1, 2, 3, 4} : Finset Nat),
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
          (addGhost period hPeriod direction ghost) t) 0 =
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 := by
  intro order _
  rw [addGhost_curve_function period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction ghost]

theorem addAuxiliary_iteratedDeriv_one_to_four (matterData) (kPlus kMinus) (bulkPlus bulkMinus)
    (robinMeasure) (frame) (llMeasure) (fields) (junction) (direction) (auxiliary) :
    ∀ order ∈ ({1, 2, 3, 4} : Finset Nat),
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
          (addAuxiliary period hPeriod direction auxiliary) t) 0 =
      iteratedDeriv order (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 := by
  intro order _
  rw [addAuxiliary_curve_function period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
    robinMeasure frame llMeasure fields junction direction auxiliary]

theorem addGhost_C3 (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber) :
    P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D.globalPTFullLLTaylorCubic
      period hPeriod frame fields (addGhost period hPeriod direction ghost).llAuxMetric
      (P0EFTJanusIntegratedPTFullLLHessianAssembly4D.fullDirectionLLVariation period hPeriod
        (addGhost period hPeriod direction ghost)) llMeasure =
    P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D.globalPTFullLLTaylorCubic
      period hPeriod frame fields direction.llAuxMetric
      (P0EFTJanusIntegratedPTFullLLHessianAssembly4D.fullDirectionLLVariation period hPeriod direction) llMeasure := by
  have ha := fullMatterRobinTrueLLCurve_third_iteratedDeriv period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction (addGhost period hPeriod direction ghost)
  have hd := fullMatterRobinTrueLLCurve_third_iteratedDeriv period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
  rw [addGhost_curve_function period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction direction ghost] at ha
  linarith

theorem addAuxiliary_C3 (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D.globalPTFullLLTaylorCubic
      period hPeriod frame fields (addAuxiliary period hPeriod direction auxiliary).llAuxMetric
      (P0EFTJanusIntegratedPTFullLLHessianAssembly4D.fullDirectionLLVariation period hPeriod
        (addAuxiliary period hPeriod direction auxiliary)) llMeasure =
    P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D.globalPTFullLLTaylorCubic
      period hPeriod frame fields direction.llAuxMetric
      (P0EFTJanusIntegratedPTFullLLHessianAssembly4D.fullDirectionLLVariation period hPeriod direction) llMeasure := by
  have ha := fullMatterRobinTrueLLCurve_third_iteratedDeriv period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction (addAuxiliary period hPeriod direction auxiliary)
  have hd := fullMatterRobinTrueLLCurve_third_iteratedDeriv period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
  rw [addAuxiliary_curve_function period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction direction auxiliary] at ha
  linarith

theorem addGhost_C4 (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber) :
    P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D.globalPTFullLLTaylorQuartic
      period hPeriod frame fields (addGhost period hPeriod direction ghost).llAuxMetric
      (P0EFTJanusIntegratedPTFullLLHessianAssembly4D.fullDirectionLLVariation period hPeriod
        (addGhost period hPeriod direction ghost)) llMeasure =
    P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D.globalPTFullLLTaylorQuartic
      period hPeriod frame fields direction.llAuxMetric
      (P0EFTJanusIntegratedPTFullLLHessianAssembly4D.fullDirectionLLVariation period hPeriod direction) llMeasure := by
  have ha := fullMatterRobinTrueLLCurve_fourth_iteratedDeriv period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction (addGhost period hPeriod direction ghost)
  have hd := fullMatterRobinTrueLLCurve_fourth_iteratedDeriv period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
  rw [addGhost_curve_function period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction direction ghost] at ha
  linarith

theorem addAuxiliary_C4 (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D.globalPTFullLLTaylorQuartic
      period hPeriod frame fields (addAuxiliary period hPeriod direction auxiliary).llAuxMetric
      (P0EFTJanusIntegratedPTFullLLHessianAssembly4D.fullDirectionLLVariation period hPeriod
        (addAuxiliary period hPeriod direction auxiliary)) llMeasure =
    P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D.globalPTFullLLTaylorQuartic
      period hPeriod frame fields direction.llAuxMetric
      (P0EFTJanusIntegratedPTFullLLHessianAssembly4D.fullDirectionLLVariation period hPeriod direction) llMeasure := by
  have ha := fullMatterRobinTrueLLCurve_fourth_iteratedDeriv period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction (addAuxiliary period hPeriod direction auxiliary)
  have hd := fullMatterRobinTrueLLCurve_fourth_iteratedDeriv period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction
  rw [addAuxiliary_curve_function period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction direction auxiliary] at ha
  linarith

end
end P0EFTJanusGhostAuxiliaryTranslationInvariance4D
end JanusFormal
