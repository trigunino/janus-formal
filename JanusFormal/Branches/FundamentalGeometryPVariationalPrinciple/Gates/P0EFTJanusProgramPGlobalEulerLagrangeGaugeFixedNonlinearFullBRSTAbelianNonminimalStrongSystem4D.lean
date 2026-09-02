import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual4D

/-!
# Strong paired Abelian nonminimal system

The three fieldwise Abelian nonminimal covectors are replaced exactly by the
ghost graph-Riesz, antighost `L²`, and Nakanishi--Lautrup `L²` residuals.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem4D

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
open P0EFTJanusMappingTorusSmoothFieldDescent4D
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
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianAntighostSmoothFPBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupSmoothLorenzBBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldAbelianNonminimalStrongSystem :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceAbelianNonminimalStrongSystem :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldAbelianNonminimalStrongSystem :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceAbelianNonminimalStrongSystem :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceAbelianNonminimalStrongSystem :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section AbelianNonminimalStrongSystem

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

/-- Exact strong system for all three paired Abelian nonminimal fields. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) : Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual
          period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
        period hPeriod configuration data analysis chartData state = 0

/-- The aggregated weak Abelian nonminimal covector vanishes exactly when all
three strong residuals vanish. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector_eq_zero_iff_strongSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
        period hPeriod configuration data analysis chartData state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector_eq_zero_iff_components]
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostBRSTCovector_eq_zero_iff_graphResidual,
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostBRSTCovector_eq_zero_iff_l2Residual,
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_eq_zero_iff_l2Residual]

/-- Full-BRST criticality forces the complete strong Abelian nonminimal
system. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianNonminimalStrongSystem
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
      period hPeriod configuration data analysis chartData state := by
  exact ⟨
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianGhostGraphResidual_eq_zero
      period hPeriod configuration data analysis chartData state hCritical,
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianAntighostL2Residual_eq_zero
      period hPeriod configuration data analysis chartData state hCritical,
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianNakanishiLautrupL2Residual_eq_zero
      period hPeriod configuration data analysis chartData state hCritical⟩

/-- On embedded smooth cores, the two `L²` entries become their genuine FP
and Lorenz-minus-field equations; the ghost entry remains its exact graph
residual. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem_core_iff
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
        period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          configuration data analysis chartData core) ↔
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
            period hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period
              hPeriod configuration data analysis chartData core) = 0 ∧
        globalPairedAbelianFPL2LinearMap period hPeriod
              (BaseMetric period hPeriod configuration data)
              (fun sector => (core.2.2.nonminimal sector).ghost.field) = 0 ∧
          globalPairedAbelianLorenzL2LinearMap period hPeriod
                (BaseMetric period hPeriod configuration data) core.2.2.potential -
              globalPairedGaugeLieL2LinearMap period hPeriod
                (fun sector =>
                  (core.2.2.nonminimal sector).nakanishiLautrup.field) = 0) := by
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual_core,
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual_core]

/-- Gate 245: all three paired Abelian nonminimal weak equations are exactly
replaced by their separating strong residual system. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_abelian_nonminimal_strong_system_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector_eq_zero_iff_strongSystem
    period hPeriod configuration data analysis chartData state

end AbelianNonminimalStrongSystem

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem4D
end JanusFormal
