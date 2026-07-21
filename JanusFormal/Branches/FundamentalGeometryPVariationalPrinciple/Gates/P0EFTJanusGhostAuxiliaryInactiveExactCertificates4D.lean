import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGhostAuxiliaryInactiveSectorNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveExactTaylor4D

namespace JanusFormal
namespace P0EFTJanusGhostAuxiliaryInactiveExactCertificates4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9Euler4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFirstOrderQuotientD94D
open P0EFTJanusFullMatterRobinTrueLLInactiveExactTaylor4D
open P0EFTJanusGhostAuxiliaryInactiveSectorNoether4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def InactiveExactCertificate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) : Prop :=
  activeProjection period hPeriod direction = zeroActiveDirection period hPeriod ∧
  quotientEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure frame
    llMeasure fields junction ⟦direction⟧ = 0 ∧
  enrichedD9ActiveEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction
      (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point) = 0 ∧
  (fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
      robinMeasure frame llMeasure fields junction direction = 0 ∧
   fullMatterRobinTrueLLTaylorC2 period hPeriod matterData kPlus kMinus robinMeasure frame
      llMeasure fields direction = 0 ∧
   P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D.globalPTFullLLTaylorCubic
      period hPeriod frame fields direction.llAuxMetric
      (P0EFTJanusIntegratedPTFullLLHessianAssembly4D.fullDirectionLLVariation period hPeriod direction) llMeasure = 0 ∧
   P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D.globalPTFullLLTaylorQuartic
      period hPeriod frame fields direction.llAuxMetric
      (P0EFTJanusIntegratedPTFullLLHessianAssembly4D.fullDirectionLLVariation period hPeriod direction) llMeasure = 0) ∧
  (iteratedDeriv 1 (fun t => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 ∧
   iteratedDeriv 2 (fun t => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 ∧
   iteratedDeriv 3 (fun t => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 ∧
   iteratedDeriv 4 (fun t => fullMatterRobinTrueLLCurve period hPeriod matterData kPlus kMinus
      bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0)

private theorem certificate_of_inactive
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (hInactive : activeProjection period hPeriod direction = zeroActiveDirection period hPeriod) :
    InactiveExactCertificate period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction sector column point direction := by
  refine ⟨hInactive, quotientEuler_eq_zero_of_inactive period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction hInactive, ?_⟩
  refine ⟨enrichedD9ActiveEuler_eq_zero_of_inactive period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction sector column point direction hInactive, ?_⟩
  refine ⟨?_, inactive_exactTaylor_iteratedDeriv_one_to_four period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction hInactive⟩
  have hc := inactive_exactTaylor_coefficients_and_action period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction hInactive
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩

theorem ghostFullDirection_certificate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber) :
    InactiveExactCertificate period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction sector column point (ghostFullDirection period hPeriod ghost) :=
  certificate_of_inactive period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction sector column point _ rfl

theorem auxiliaryFullDirection_certificate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod) (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    InactiveExactCertificate period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
      frame llMeasure fields junction sector column point (auxiliaryFullDirection period hPeriod auxiliary) :=
  certificate_of_inactive period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    frame llMeasure fields junction sector column point _ rfl

end
end P0EFTJanusGhostAuxiliaryInactiveExactCertificates4D
end JanusFormal
