import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupSmoothLorenzBBridge4D

/-!
# Resolved two-equation Abelian strong subsystem

The paired Abelian antighost and Nakanishi--Lautrup equations are packaged as
one exact strong subsystem. The unresolved ghost covector is deliberately not
included.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianResolvedTwoEquationStrongSystem4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianAntighostSmoothFPBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupSmoothLorenzBBridge4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldAbelianResolvedTwoEquationStrongSystem :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceAbelianResolvedTwoEquationStrongSystem :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldAbelianResolvedTwoEquationStrongSystem :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceAbelianResolvedTwoEquationStrongSystem :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceAbelianResolvedTwoEquationStrongSystem :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section AbelianResolvedTwoEquationStrongSystem

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

/-- The two Abelian nonminimal equations with currently available separating
strong residuals. The ghost covector is intentionally outside this predicate. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianResolvedStrongSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) : Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual
      period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
      period hPeriod configuration data analysis chartData state = 0

/-- The two weak covectors vanish exactly when the resolved strong subsystem
vanishes. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianResolvedCovectors_eq_zero_iff_strongSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalAntighostBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
          period hPeriod configuration data analysis chartData state = 0) ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianResolvedStrongSystemAt
        period hPeriod configuration data analysis chartData state := by
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianResolvedStrongSystemAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostBRSTCovector_eq_zero_iff_l2Residual,
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_eq_zero_iff_l2Residual]

/-- Full-BRST criticality forces the resolved strong subsystem at every
completed graph state. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianResolvedStrongSystem
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianResolvedStrongSystemAt
      period hPeriod configuration data analysis chartData state := by
  constructor
  · exact
      globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianAntighostL2Residual_eq_zero
        period hPeriod configuration data analysis chartData state hCritical
  · exact
      globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianNakanishiLautrupL2Residual_eq_zero
        period hPeriod configuration data analysis chartData state hCritical

/-- On embedded smooth cores, the resolved completed subsystem is precisely
the genuine paired FP and Lorenz-minus-field `L²` system. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianResolvedStrongSystem_core_iff
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianResolvedStrongSystemAt
        period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          configuration data analysis chartData core) ↔
      (globalPairedAbelianFPL2LinearMap period hPeriod
          (BaseMetric period hPeriod configuration data)
          (fun sector => (core.2.2.nonminimal sector).ghost.field) = 0 ∧
        globalPairedAbelianLorenzL2LinearMap period hPeriod
              (BaseMetric period hPeriod configuration data) core.2.2.potential -
            globalPairedGaugeLieL2LinearMap period hPeriod
              (fun sector =>
                (core.2.2.nonminimal sector).nakanishiLautrup.field) = 0) := by
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianResolvedStrongSystemAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual_core,
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual_core]

/-- On smooth cores, the two weak covectors are exactly equivalent to the
genuine paired FP and Lorenz-minus-field equations. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianResolvedCovectors_core_eq_zero_iff
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalAntighostBRSTCovector
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
            configuration data analysis chartData core) = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
            configuration data analysis chartData core) = 0) ↔
      (globalPairedAbelianFPL2LinearMap period hPeriod
          (BaseMetric period hPeriod configuration data)
          (fun sector => (core.2.2.nonminimal sector).ghost.field) = 0 ∧
        globalPairedAbelianLorenzL2LinearMap period hPeriod
              (BaseMetric period hPeriod configuration data) core.2.2.potential -
            globalPairedGaugeLieL2LinearMap period hPeriod
              (fun sector =>
                (core.2.2.nonminimal sector).nakanishiLautrup.field) = 0) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostBRSTCovector_core_eq_zero_iff_fpL2,
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_core_eq_zero_iff_lorenzB]

/-- Gate 243: full-BRST criticality at a smooth core forces the resolved
two-equation Abelian strong subsystem. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_abelian_resolved_twoEquation_strong_system_gate
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
        configuration data analysis chartData core)) :
    globalPairedAbelianFPL2LinearMap period hPeriod
        (BaseMetric period hPeriod configuration data)
        (fun sector => (core.2.2.nonminimal sector).ghost.field) = 0 ∧
      globalPairedAbelianLorenzL2LinearMap period hPeriod
            (BaseMetric period hPeriod configuration data) core.2.2.potential -
          globalPairedGaugeLieL2LinearMap period hPeriod
            (fun sector =>
              (core.2.2.nonminimal sector).nakanishiLautrup.field) = 0 := by
  exact ⟨
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_core_imp_abelianFPL2_eq_zero
      period hPeriod configuration data analysis chartData core hCritical,
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_core_imp_abelianLorenzB_eq_zero
      period hPeriod configuration data analysis chartData core hCritical⟩

end AbelianResolvedTwoEquationStrongSystem

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianResolvedTwoEquationStrongSystem4D
end JanusFormal
