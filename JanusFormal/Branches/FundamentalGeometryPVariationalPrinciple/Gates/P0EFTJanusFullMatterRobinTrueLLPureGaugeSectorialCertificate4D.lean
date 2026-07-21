import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLPureGaugeInactive4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLInactiveExactTaylor4D

namespace JanusFormal
namespace P0EFTJanusFullMatterRobinTrueLLPureGaugeSectorialCertificate4D

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
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusFullMatterRobinTrueLLHigherDerivatives4D
open P0EFTJanusFullMatterRobinTrueLLTaylorCoefficientBridge4D
open P0EFTJanusFullMatterRobinTrueLLInactiveFiniteNoether4D
open P0EFTJanusFullMatterRobinTrueLLInactiveCharacterization4D
open P0EFTJanusFullMatterRobinTrueLLInactiveExactTaylor4D
open P0EFTJanusFullMatterRobinTrueLLPureGaugeInactive4D
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

/-- Complete certificate for the pure common gauge direction relative only to
the assembled matter + Robin + LL functional. Maxwell is absent, so this is
not a certificate for the complete Candidate A action. -/
theorem pureGauge_sectorial_quotient_D9_Taylor_certificate
    (matterData : MatterMultipletActionData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod) (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber) :
    let direction := pureGaugeFullDirection period hPeriod gauge
    (⟦direction⟧ : ActiveQuotient period hPeriod) = zeroActiveQuotientClass period hPeriod ∧
    toActiveDirection period hPeriod
      (globalMatterEnrichedD9Projection period hPeriod fields direction sector column point) =
        zeroActiveDirection period hPeriod ∧
    (fullMatterRobinTrueLLTaylorC1 period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
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
          robinMeasure frame llMeasure fields junction) ∧
    (iteratedDeriv 1 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 ∧
      iteratedDeriv 2 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 ∧
      iteratedDeriv 3 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0 ∧
      iteratedDeriv 4 (fun t : Real => fullMatterRobinTrueLLCurve period hPeriod matterData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction direction t) 0 = 0) := by
  dsimp only
  have hInactive := pureGaugeFullDirection_activeProjection_zero period hPeriod gauge
  refine ⟨(activeProjection_zero_iff_class_zero period hPeriod _).mp hInactive, ?_⟩
  refine ⟨(activeProjection_zero_iff_enrichedD9_reading_zero period hPeriod fields sector
    column point _).mp hInactive, ?_⟩
  refine ⟨inactive_exactTaylor_coefficients_and_action period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction _ hInactive, ?_⟩
  exact inactive_exactTaylor_iteratedDeriv_one_to_four period hPeriod matterData kPlus kMinus
    bulkPlus bulkMinus robinMeasure frame llMeasure fields junction _ hInactive

end
end P0EFTJanusFullMatterRobinTrueLLPureGaugeSectorialCertificate4D
end JanusFormal
