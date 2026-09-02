import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNonminimalGraphFaithfulness4D

/-!
# Faithful-coordinate capstone for the exact full-BRST residual system

The exact ten-block criticality system is combined with injectivity of every
physical augmented graph coordinate and every nonminimal graph or `L²` test
coordinate used by that system.  This is a coordinate-level capstone, not a
local PDE or Fredholm theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFaithfulResidualSystemCapstone4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphFaithfulness4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphFaithfulness4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphFaithfulness4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNonminimalGraphFaithfulness4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldFaithfulResidualCapstone :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance matterHilbertRealInnerProductSpaceFaithfulResidualCapstone :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  { InnerProductSpace.complexToReal with
    toNormedSpace := inferInstance }

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section Capstone

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

local instance fullLLGraphInnerProductSpaceFaithfulResidualCapstone :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  globalFullLLGraphInnerProductSpace period hPeriod data analysis

local instance fullLLGraphCompleteSpaceFaithfulResidualCapstone :
    CompleteSpace
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis

/-- Every test coordinate used by the exact full-BRST residual system is
injective.  The single paired gauge-Lie `L²` map is shared by the Abelian
antighost and Nakanishi--Lautrup equations. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTAllResidualTestCoordinatesFaithfulAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  Function.Injective
      (diagonalDiffeomorphismAugmentedGraphCoordinate period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        (GlobalMinimalPhysicalMetricTest period hPeriod)
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) ∧
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) ∧
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
          period hPeriod configuration data analysis chartData state)) ∧
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) ∧
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) ∧
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) ∧
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) ∧
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding period
        hPeriod configuration data analysis chartData state) ∧
    Function.Injective
      (globalPairedAbelianPureGhostGraphEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) ∧
    Function.Injective (globalPairedGaugeLieL2LinearMap period hPeriod) ∧
    Function.Injective
      (globalDiffeomorphismPureGhostGraphEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) ∧
    Function.Injective
      (globalDiffeomorphismPureAntighostGraphEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) ∧
    Function.Injective
      (globalDiffeomorphismPureNakanishiLautrupGraphEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTAllResidualTestCoordinatesFaithfulAt_proved
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTAllResidualTestCoordinatesFaithfulAt
      period hPeriod configuration data analysis chartData state := by
  exact ⟨
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphCoordinate_injective
      period hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphLinearMap_injective
      period hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphLinearMap_injective
      period hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphLinearMap_injective
      period hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphLinearMap_injective
      period hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphLinearMap_injective
      period hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphLinearMap_injective
      period hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding_injective
      period hPeriod configuration data analysis chartData state,
    globalPairedAbelianPureGhostGraphEmbedding_injective period hPeriod
      (globalCandidateAMetricBySector period hPeriod data),
    globalPairedGaugeLieL2LinearMap_injective period hPeriod,
    globalDiffeomorphismPureGhostGraphEmbedding_injective period hPeriod
      (globalCandidateAMetricBySector period hPeriod data),
    globalDiffeomorphismPureAntighostGraphEmbedding_injective period hPeriod
      (globalCandidateAMetricBySector period hPeriod data),
    globalDiffeomorphismPureNakanishiLautrupGraphEmbedding_injective period
      hPeriod (globalCandidateAMetricBySector period hPeriod data)⟩

/-- Gate 266: full-BRST criticality has an exact ten-block residual system and
every test coordinate used by that system is faithful. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_faithful_residual_system_capstone_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalPhysicalGhostL2SpinCFourierFaithfulAugmentedGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state) ∧
      GlobalCandidateAGaugeFixedNonlinearFullBRSTAllResidualTestCoordinatesFaithfulAt
        period hPeriod configuration data analysis chartData state :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalPhysicalGhostL2SpinCFourierFaithfulAugmentedGraphResidualEulerSystem
      period hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTAllResidualTestCoordinatesFaithfulAt_proved
      period hPeriod configuration data analysis chartData state⟩

end Capstone
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFaithfulResidualSystemCapstone4D
end JanusFormal
