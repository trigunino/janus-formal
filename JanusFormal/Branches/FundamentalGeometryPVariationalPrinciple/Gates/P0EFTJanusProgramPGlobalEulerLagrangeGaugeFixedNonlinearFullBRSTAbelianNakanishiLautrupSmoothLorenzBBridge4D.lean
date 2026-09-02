import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianAntighostSmoothFPBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonAnalyticDomainClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

/-!
# Smooth-core Abelian Nakanishi--Lautrup Lorenz bridge

The completed auxiliary-field residual is identified with the genuine paired
Lorenz-minus-field `L²` expression on embedded algebraic smooth cores.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupSmoothLorenzBBridge4D

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
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D
open P0EFTJanusProgramPGlobalCandidateACommonAnalyticDomainClosure4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCMatterEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreeComponentEquiv4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTComponentEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldAbelianNakanishiLautrupSmoothLorenzBBridge :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpaceAbelianNakanishiLautrupSmoothLorenzBBridge :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldAbelianNakanishiLautrupSmoothLorenzBBridge :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceAbelianNakanishiLautrupSmoothLorenzBBridge :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceAbelianNakanishiLautrupSmoothLorenzBBridge :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceAbelianNakanishiLautrupSmoothLorenzBBridge :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldAbelianNakanishiLautrupSmoothLorenzBBridge :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceAbelianNakanishiLautrupSmoothLorenzBBridge :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldAbelianNakanishiLautrupSmoothLorenzBBridge :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteAbelianNakanishiLautrupSmoothLorenzBBridge :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroupAbelianNakanishiLautrupSmoothLorenzBBridge :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModuleAbelianNakanishiLautrupSmoothLorenzBBridge :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroupAbelianNakanishiLautrupSmoothLorenzBBridge
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModuleAbelianNakanishiLautrupSmoothLorenzBBridge
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

section AbelianNakanishiLautrupSmoothLorenzBBridge

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

private abbrev GaugeFreePhysical :=
  GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period hPeriod
    configuration

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupAbelianNakanishiLautrupSmoothLorenzBBridge :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleAbelianNakanishiLautrupSmoothLorenzBBridge :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupAbelianNakanishiLautrupSmoothLorenzBBridge :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-! ## Smooth-core identification -/

/-- On an embedded algebraic smooth core, the completed auxiliary-field
residual is exactly the paired Lorenz coordinate minus the paired smooth
Nakanishi--Lautrup field. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual_core
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
        period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
          configuration data analysis chartData core) =
      globalPairedAbelianLorenzL2LinearMap period hPeriod
          (BaseMetric period hPeriod configuration data) core.2.2.potential -
        globalPairedGaugeLieL2LinearMap period hPeriod
          (fun sector =>
            (core.2.2.nonminimal sector).nakanishiLautrup.field) := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection_core,
    globalPairedAbelianOffShellLorenzProjection_smooth,
    globalPairedAbelianOffShellBProjection_smooth]

/-- On smooth cores, auxiliary-field stationarity is exactly the genuine
paired Lorenz-minus-field `L²` equation. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_core_eq_zero_iff_lorenzB
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period
            hPeriod configuration data analysis chartData core) = 0 ↔
      globalPairedAbelianLorenzL2LinearMap period hPeriod
            (BaseMetric period hPeriod configuration data) core.2.2.potential -
          globalPairedGaugeLieL2LinearMap period hPeriod
            (fun sector =>
              (core.2.2.nonminimal sector).nakanishiLautrup.field) = 0 := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_eq_zero_iff_l2Residual,
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual_core]

/-- Full-BRST criticality at an embedded smooth core forces the genuine paired
Lorenz-minus-field `L²` equation. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_core_imp_abelianLorenzB_eq_zero
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
        configuration data analysis chartData core)) :
    globalPairedAbelianLorenzL2LinearMap period hPeriod
          (BaseMetric period hPeriod configuration data) core.2.2.potential -
        globalPairedGaugeLieL2LinearMap period hPeriod
          (fun sector =>
            (core.2.2.nonminimal sector).nakanishiLautrup.field) = 0 := by
  have hResidual :=
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianNakanishiLautrupL2Residual_eq_zero
      period hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period hPeriod
        configuration data analysis chartData core) hCritical
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual_core]
    at hResidual
  exact hResidual

/-- Gate 242: the strong auxiliary-field residual becomes the genuine paired
Lorenz-minus-Nakanishi--Lautrup `L²` equation on embedded smooth cores. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_abelian_nakanishiLautrup_smooth_lorenzB_bridge_gate
    (core : GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
      configuration) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEmbedding period
            hPeriod configuration data analysis chartData core) = 0 ↔
      globalPairedAbelianLorenzL2LinearMap period hPeriod
            (BaseMetric period hPeriod configuration data) core.2.2.potential -
          globalPairedGaugeLieL2LinearMap period hPeriod
            (fun sector =>
              (core.2.2.nonminimal sector).nakanishiLautrup.field) = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_core_eq_zero_iff_lorenzB
    period hPeriod configuration data analysis chartData core

end AbelianNakanishiLautrupSmoothLorenzBBridge

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupSmoothLorenzBBridge4D
end JanusFormal
