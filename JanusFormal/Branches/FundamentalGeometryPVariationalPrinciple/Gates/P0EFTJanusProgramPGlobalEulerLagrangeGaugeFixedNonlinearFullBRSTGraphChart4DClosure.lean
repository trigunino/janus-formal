import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4DCalculus

/-!
# Closure of the nonlinear full-BRST relational chart

This continuation records the strong Riesz pairings, zero-nonminimal reduction,
and the terminal Gate 223 support theorem.
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
local instance (priority := 11000) alignedRealNontriviallyNormedFieldClosure :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩


variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceClosure :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldClosure :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceClosure :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceClosure :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFiniteClosure :
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
local instance (priority := 10001) fullDiffeomorphismChartNormedAddCommGroupClosure :
    NormedAddCommGroup
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.nonlinearBRSTGraphChartNormedAddCommGroup
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartNormedSpaceClosure :
    NormedSpace Real
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D.nonlinearBRSTGraphChartNormedSpace
    period hPeriod configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10002) fullDiffeomorphismChartAddCommGroupClosure :
    AddCommGroup
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedAddCommGroupClosure period hPeriod configuration data
    analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) fullDiffeomorphismChartTopologicalSpaceClosure :
    TopologicalSpace
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedAddCommGroupClosure period hPeriod configuration data
    analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) fullDiffeomorphismChartModuleClosure :
    Module Real
      (DiffeomorphismChart period hPeriod configuration data analysis
        chartData) :=
  (fullDiffeomorphismChartNormedSpaceClosure period hPeriod configuration data
    analysis chartData).toModule

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphNormedAddCommGroupClosure :
    NormedAddCommGroup
      (AbelianGraph period hPeriod configuration data) :=
  @Submodule.normedAddCommGroup Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)
    inferInstance inferInstance inferInstance
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data))

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphNormedSpaceClosure :
    NormedSpace Real (AbelianGraph period hPeriod configuration data) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 10002) fullAbelianGraphAddCommGroupClosure :
    AddCommGroup (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedAddCommGroupClosure period hPeriod configuration
    data).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) fullAbelianGraphTopologicalSpaceClosure :
    TopologicalSpace (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedAddCommGroupClosure period hPeriod configuration data
    ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) fullAbelianGraphModuleClosure :
    Module Real (AbelianGraph period hPeriod configuration data) :=
  (fullAbelianGraphNormedSpaceClosure period hPeriod configuration data).toModule

local instance (priority := 10002) nonlinearFullAmbientModuleClosure :
    Module Real
      (FullAmbient period hPeriod configuration data analysis chartData) :=
  Prod.instModule

@[implicit_reducible]
local instance (priority := 10002) nonlinearFullBRSTChartNormedAddCommGroupClosure :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  @Submodule.normedAddCommGroup Real
    (FullAmbient period hPeriod configuration data analysis chartData)
    inferInstance inferInstance
    (nonlinearFullAmbientModuleClosure period hPeriod (measure := measure)
      configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10002) nonlinearFullBRSTChartNormedSpaceClosure :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  Submodule.normedSpace
    (globalCandidateAGaugeFixedNonlinearFullBRSTGraphSubmodule4D period hPeriod
      configuration data analysis chartData)

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartModuleClosure :
    Module Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedSpaceClosure period hPeriod configuration data analysis
    chartData).toModule

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartAddCommGroupClosure :
    AddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedAddCommGroupClosure period hPeriod configuration data
    analysis chartData).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10003) nonlinearFullBRSTChartTopologicalSpaceClosure :
    TopologicalSpace
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :=
  (nonlinearFullBRSTChartNormedAddCommGroupClosure period hPeriod configuration data
    analysis chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
/-- The completed diffeomorphism factor retains its strong Riesz pairing on
the full relational chart. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismRieszContribution_pairing
    (state test :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :
    inner Real
        (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator period
          hPeriod couplings (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
            period hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
              period hPeriod configuration data analysis chartData state)))
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
            period hPeriod configuration data analysis chartData test)) =
      globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
            period hPeriod configuration data analysis chartData state))
        (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
            period hPeriod configuration data analysis chartData test)) :=
  globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTRieszContribution_pairing
    period hPeriod configuration data analysis chartData _ _

/-- The completed Abelian factor retains its strong Riesz pairing on the full
relational chart. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianRieszContribution_pairing
    (state test :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
        configuration data analysis chartData) :
    inner Real
        (globalPairedAbelianOffShellRieszOperator period hPeriod
          (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
            hPeriod configuration data analysis chartData state))
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData test) =
      globalPairedAbelianOffShellHessian period hPeriod
        (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData test) :=
  globalPairedAbelianOffShellRieszOperator_pairing period hPeriod
    (BaseMetric period hPeriod configuration data) _ _

private theorem zeroGlobalAbelianNakanishiLautrupField_field :
    (zeroGlobalAbelianNakanishiLautrupField period hPeriod).field = 0 :=
  rfl

private theorem zeroGlobalAbelianAntighostField_field :
    (zeroGlobalAbelianAntighostField period hPeriod).field = 0 :=
  rfl

private theorem globalGaugeLiePairingAt_zero_left
    (field : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod) :
    globalGaugeLiePairingAt period hPeriod 0 field point = 0 := by
  simpa only [zero_smul, zero_mul] using
    (globalGaugeLiePairingAt_smul_first period hPeriod 0
      (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra) field point)

/-- The Abelian gauge-fixing action vanishes when its `c/cbar/B` fields are
zero, without constraining the physical potential. -/
theorem globalPairedAbelianGaugeFermionBRSTAction_zero_nonminimal
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
        { potential := potential
          nonminimal := fun _ =>
            zeroGlobalAbelianNonminimalFields period hPeriod }
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0 := by
  unfold globalPairedAbelianGaugeFermionBRSTAction
    globalPairedAbelianGaugeFermionBRSTDensity
    zeroGlobalAbelianNonminimalFields
  simp only [zeroGlobalAbelianNakanishiLautrupField_field,
    zeroGlobalAbelianAntighostField_field,
    globalGaugeLiePairingAt_zero_left, mul_zero, zero_sub, neg_zero, add_zero,
    Finset.sum_const_zero, integral_zero]

/-- Canonical core slice with both nonminimal BRST sectors fixed at zero. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTZeroNonminimalCore
    (physical : GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period
      hPeriod configuration)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration :=
  (physical,
    (zeroGlobalDiffeomorphismNonminimalFields period hPeriod,
      { potential := potential
        nonminimal := fun _ =>
          zeroGlobalAbelianNonminimalFields period hPeriod }))

end FullBRSTChart

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
end JanusFormal
