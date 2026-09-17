import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongMatterHessianOnDiagonalCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongLLHessianProjectionInvariance4D

/-! Exact H13 attachment for a strong chart centered on the supplied background. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongMatterLLSameActionBridge4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPT12StrongMatterHessianOnDiagonalCore4D
open P0EFTJanusProgramPT12StrongLLHessianProjectionInvariance4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- The actual strong chart realizes both H13 same-action attachments when its
metric center is the supplied physical background. -/
def strongMatterLLSameActionBridge
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
      period hPeriod configuration.physical plusBase minusBase hBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D period hPeriod
      configuration data analysis
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let chart := regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure
  let coreBridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart := by
    refine {
      basePoint := 0
      basePoint_mem := chart.zero_mem_domain
      baseConfiguration_fields := ?_
      tangentAnalysis := LinearMap.id
      tangentAnalysis_injective := Function.injective_id
      tangentAnalysis_denseRange := ?_ }
    · exact regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily_datumAt_zero_configuration
        period hPeriod configuration.physical couplings data plusBase
          minusBase hBase hCenter
    · apply Function.Surjective.denseRange
      intro point
      exact ⟨point, rfl⟩
  exact {
    chartBridge := coreBridge
    matter_sameAction := by
      intro base first second
      calc
        _ = diagonalExtendedBulkH13MatterGraphHessianOnCore period hPeriod
              configuration data analysis first second :=
          strong_matter_hessian_on_diagonal_core_eq_graph period hPeriod
            configuration data analysis realization plusBase minusBase hBase
              measure first second
        _ = _ := diagonalExtendedBulkH13MatterGraphHessian_eq_secondFrechet
          period hPeriod configuration data analysis base first second
    ll_sameAction := by
      intro base first second
      calc
        _ = diagonalExtendedBulkH13LLGraphHessianOnCore period hPeriod
              configuration data analysis first second :=
          strong_LL_hessian_on_diagonal_core_eq_graph period hPeriod
            configuration data analysis realization plusBase minusBase hBase
              measure first second
        _ = _ := diagonalExtendedBulkH13LLGraphHessian_eq_secondFrechet
          period hPeriod configuration data analysis base first second }

end
end P0EFTJanusProgramPT12StrongMatterLLSameActionBridge4D
end JanusFormal
