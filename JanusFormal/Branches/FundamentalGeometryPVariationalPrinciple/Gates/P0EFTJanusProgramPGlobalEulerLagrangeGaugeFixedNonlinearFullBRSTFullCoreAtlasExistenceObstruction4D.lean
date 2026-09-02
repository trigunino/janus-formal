import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialAbelianBRSTBaseRegularity4D

/-!
# Full-core atlas existence obstruction

A projection-compatible atlas covering the entire algebraic full-BRST core
already entails existence of a genuine admissible action chart at every core
state. This isolates the missing analytic construction; chart surjectivity into
its graph space cannot supply domain membership.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFullCoreAtlasExistenceObstruction4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

universe v

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

section Obstruction

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)

private abbrev Core :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
    configuration

private abbrev ChartData :=
  ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
    (measure := measure) configuration data analysis

private abbrev CoveredAtlas :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas
    period hPeriod (measure := measure) configuration data analysis

/-- A full-core covered atlas necessarily contains at least one genuine
minimal-physical action chart. -/
theorem fullCoreCoveredAtlas_implies_chartData_nonempty
    (atlas : CoveredAtlas period hPeriod (measure := measure) configuration data
      analysis)
    (hFull : atlas.carrier = Set.univ) :
    Nonempty (ChartData period hPeriod (measure := measure) configuration data
      analysis) := by
  have hZero : (0 : Core period hPeriod configuration) ∈ atlas.carrier := by
    rw [hFull]
    exact Set.mem_univ _
  obtain ⟨index, _⟩ := atlas.cover 0 hZero
  exact ⟨atlas.chartData index⟩

/-- More strongly, full coverage supplies an admissible chart containing
every individual core state. -/
theorem fullCoreCoveredAtlas_implies_chartData_exists_at
    (atlas : CoveredAtlas period hPeriod (measure := measure) configuration data
      analysis)
    (hFull : atlas.carrier = Set.univ)
    (state : Core period hPeriod configuration) :
    ∃ chartData : ChartData period hPeriod (measure := measure) configuration
        data analysis,
      globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          (measure := measure) configuration data analysis chartData state ∈
        globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
          (measure := measure) configuration data analysis chartData := by
  have hState : state ∈ atlas.carrier := by
    rw [hFull]
    exact Set.mem_univ _
  obtain ⟨index, hIndex⟩ := atlas.cover state hState
  exact ⟨atlas.chartData index, hIndex⟩

/-- Gate 316: any claimed full-core atlas discharges the still-missing
pointwise analytic chart-existence obligation. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_full_core_atlas_existence_obstruction_gate
    (atlas : CoveredAtlas period hPeriod (measure := measure) configuration data
      analysis)
    (hFull : atlas.carrier = Set.univ) :
    Nonempty (ChartData period hPeriod (measure := measure) configuration data
      analysis) ∧
      ∀ state : Core period hPeriod configuration,
        ∃ chartData : ChartData period hPeriod (measure := measure)
            configuration data analysis,
          globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
              (measure := measure) configuration data analysis chartData state ∈
            globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
              (measure := measure) configuration data analysis chartData :=
  ⟨fullCoreCoveredAtlas_implies_chartData_nonempty period hPeriod
      (measure := measure) configuration data analysis atlas hFull,
    fullCoreCoveredAtlas_implies_chartData_exists_at period hPeriod
      (measure := measure) configuration data analysis atlas hFull⟩

end Obstruction
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFullCoreAtlasExistenceObstruction4D
end JanusFormal
