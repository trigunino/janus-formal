import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D

/-!
# Faithfulness of the coupled Abelian-potential graph

The completed Abelian graph coordinate already present in the full-BRST
potential residual is injective on smooth paired potentials.  Its dense graph
embedding is therefore faithful.  No local Maxwell PDE is added.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphFaithfulness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldPotentialFaithfulness :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap
        period hPeriod) := by
  intro first second hEqual
  exact congrArg GlobalPairedAbelianBRSTState.potential hEqual

section PotentialGraphFaithfulness

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

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap period
        hPeriod configuration data analysis chartData state) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap_injective
      period hPeriod
  apply globalPairedAbelianOffShellSmoothEmbedding_injective period hPeriod
    (BaseMetric period hPeriod configuration data)
  simpa [globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap]
    using congrArg WithLp.fst hEqual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding period
        hPeriod configuration data analysis chartData state) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphLinearMap_injective
      period hPeriod configuration data analysis chartData state
  exact congrArg Subtype.val hEqual

/-- Gate 262: the dense smooth embedding used by the coupled potential graph
residual is injective. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_potential_graph_faithfulness_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding period
        hPeriod configuration data analysis chartData state) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphEmbedding_injective
    period hPeriod configuration data analysis chartData state

end PotentialGraphFaithfulness
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphFaithfulness4D
end JanusFormal
