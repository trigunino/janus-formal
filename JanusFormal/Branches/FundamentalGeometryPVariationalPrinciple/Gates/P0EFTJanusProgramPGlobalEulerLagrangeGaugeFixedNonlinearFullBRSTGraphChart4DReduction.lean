import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4DClosure

/-!
# Exact-action reduction for the nonlinear full-BRST chart

This continuation isolates the core action identity and its zero-nonminimal reduction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 8000000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldReduction :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩


variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceReduction :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldReduction :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceReduction :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceReduction :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFiniteReduction :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section FullBRSTChart

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

private abbrev MinimalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev DiffeomorphismChart :=
  GlobalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D period
    hPeriod configuration data analysis chartData

private abbrev AbelianGraph :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

private abbrev FullAmbient :=
  DiffeomorphismChart period hPeriod configuration data analysis chartData ×
    AbelianGraph period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartNormedAddCommGroupReduction :
    NormedAddCommGroup
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.nonlinearBRSTGraphChartNormedAddCommGroup
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartNormedSpaceReduction :
    NormedSpace Real
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.nonlinearBRSTGraphChartNormedSpace
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10002) fullDiffeomorphismChartAddCommGroupReduction :
    AddCommGroup
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedAddCommGroupReduction period hPeriod configuration data
    analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) fullDiffeomorphismChartTopologicalSpaceReduction :
    TopologicalSpace
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedAddCommGroupReduction period hPeriod configuration data
    analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartModuleReduction :
    Module Real
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedSpaceReduction period hPeriod configuration data
    analysis chartData).toModule

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphNormedAddCommGroupReduction :
    NormedAddCommGroup
      (AbelianGraph period hPeriod configuration data) :=
  @Submodule.normedAddCommGroup Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)
    inferInstance inferInstance inferInstance
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data))

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphNormedSpaceReduction :
    NormedSpace Real (AbelianGraph period hPeriod configuration data) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 10002) fullAbelianGraphAddCommGroupReduction :
    AddCommGroup (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedAddCommGroupReduction period hPeriod configuration
    data).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) fullAbelianGraphTopologicalSpaceReduction :
    TopologicalSpace (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedAddCommGroupReduction period hPeriod configuration data
    ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphModuleReduction :
    Module Real (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedSpaceReduction period hPeriod configuration data).toModule

local instance (priority := 10002) nonlinearFullAmbientModuleReduction :
    Module Real
      (FullAmbient period hPeriod configuration data analysis chartData) :=
  Prod.instModule

@[implicit_reducible]
local instance (priority := 10002) nonlinearFullBRSTChartNormedAddCommGroupReduction :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  @Submodule.normedAddCommGroup Real
    (FullAmbient period hPeriod configuration data analysis chartData)
    inferInstance inferInstance
    (nonlinearFullAmbientModuleReduction period hPeriod (measure := measure)
      configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10002) nonlinearFullBRSTChartNormedSpaceReduction :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  Submodule.normedSpace
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartModuleReduction :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedSpaceReduction period hPeriod configuration data analysis
    chartData).toModule

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartAddCommGroupReduction :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedAddCommGroupReduction period hPeriod configuration data
    analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartTopologicalSpaceReduction :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedAddCommGroupReduction period hPeriod configuration data
    analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
/-- On the core the action is exactly the nonlinear covariant action plus the
two genuine gauge-fermion BRST variations. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAction_core_eq
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration)
    (hCore :
      (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
          configuration data analysis chartData)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
            period hPeriod configuration data core) ∈
        (MinimalChart period hPeriod configuration data analysis
          chartData).family.domain) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          configuration data analysis chartData core) =
      globalCandidateACovariantAction period hPeriod
          ((MinimalChart period hPeriod configuration data analysis
            chartData).family.datumAt
            ((globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
              configuration data analysis chartData)
              (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
                period hPeriod configuration data core)) hCore).2 measure +
        globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period
          hPeriod couplings (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap
            period hPeriod configuration
            (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
              period hPeriod configuration data core)) +
        globalPairedAbelianGaugeFermionBRSTAction period hPeriod
          (BaseMetric period hPeriod configuration data) core.2.2
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  have hDiffeomorphism :=
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction_core_eq period
      hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
        period hPeriod configuration data core) hCore
  change
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTAction period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTCoreEmbedding
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
            period hPeriod configuration data core)) =
      globalCandidateACovariantAction period hPeriod
          ((MinimalChart period hPeriod configuration data analysis
            chartData).family.datumAt
            ((globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
              configuration data analysis chartData)
              (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
                period hPeriod configuration data core)) hCore).2 measure +
        globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period
          hPeriod couplings (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap
            period hPeriod configuration
            (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
              period hPeriod configuration data core)) at hDiffeomorphism
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTAction
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection_core,
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection_core,
    hDiffeomorphism,
    globalPairedAbelianOffShellGraphAction_smooth_eq_BRST]

/-- With both nonminimal sectors turned off, the full nonlinear action is
exactly the covariant physical action, while the Abelian potential remains a
genuine physical direction. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAction_zero_nonminimal_eq
    (physical : GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period
      hPeriod configuration)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod)
    (hPhysical :
      (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
          configuration data analysis chartData)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
            period hPeriod configuration data
            (globalCandidateAGaugeFixedNonlinearFullBRSTZeroNonminimalCore
              period hPeriod configuration physical potential)) ∈
        (MinimalChart period hPeriod configuration data analysis
          chartData).family.domain) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTZeroNonminimalCore period
            hPeriod configuration physical potential)) =
      globalCandidateACovariantAction period hPeriod
        ((MinimalChart period hPeriod configuration data analysis
          chartData).family.datumAt
          ((globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
            configuration data analysis chartData)
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
              period hPeriod configuration data
              (globalCandidateAGaugeFixedNonlinearFullBRSTZeroNonminimalCore
                period hPeriod configuration physical potential))) hPhysical).2
        measure := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAction_core_eq period hPeriod
    configuration data analysis chartData
    (globalCandidateAGaugeFixedNonlinearFullBRSTZeroNonminimalCore period
      hPeriod configuration physical potential) hPhysical]
  change _ +
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period
        hPeriod couplings (BaseMetric period hPeriod configuration data)
        { metricPerturbation :=
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalTangentLinearMap
              period hPeriod configuration data
              (globalCandidateAGaugeFixedNonlinearFullBRSTZeroNonminimalCore
                period hPeriod configuration physical potential)).1.completeVariation.fullMetricPerturbation
          nonminimal :=
            zeroGlobalDiffeomorphismNonminimalFields period hPeriod } +
      globalPairedAbelianGaugeFermionBRSTAction period hPeriod
        (BaseMetric period hPeriod configuration data)
        { potential := potential
          nonminimal := fun _ =>
            zeroGlobalAbelianNonminimalFields period hPeriod }
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = _
  rw [globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation_zero_nonminimal,
    globalPairedAbelianGaugeFermionBRSTAction_zero_nonminimal, add_zero,
    add_zero]

end FullBRSTChart

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
end JanusFormal
