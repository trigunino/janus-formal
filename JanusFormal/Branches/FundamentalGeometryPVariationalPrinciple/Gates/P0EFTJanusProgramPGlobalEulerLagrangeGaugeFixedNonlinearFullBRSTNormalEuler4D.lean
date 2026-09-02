import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalRobinNormalCrossBlockDecomposition4D

/-!
# Full-BRST normal Euler equation

Pure normal tests have zero metric and Abelian components.  Their full-BRST
equation is therefore the physical Robin block plus its named cross-block.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalEuler4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
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
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalRobinNormalCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldNormalEuler :
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

local instance effectiveQuotientChartedSpaceNormalEuler :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldNormalEuler :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceNormalEuler :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceNormalEuler :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceNormalEuler :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldNormalEuler :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceNormalEuler :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldNormalEuler :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteNormalEuler :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroupNormalEuler :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModuleNormalEuler :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroupNormalEuler
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModuleNormalEuler
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

section NormalEuler

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

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupNormalEuler :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleNormalEuler :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupNormalEuler :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Pure normal directions in the corrected minimal physical tangent. -/
private def normalMinimalPhysicalLinearMap :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical :=
  (globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration.physical).symm.toLinearMap.comp
    ((productFirstInclusion
      (GlobalMinimalPhysicalBulkTangent period hPeriod)
      (Sector → D9PrimitiveSpinCSmoothSection period hPeriod
        .positiveQuarter)).comp
      ((globalMinimalPhysicalSevenBulkEquiv period hPeriod).symm.toLinearMap.comp
        (globalMinimalPhysicalNormalTestInclusion period hPeriod)))

/-- Pure normal directions regarded as gauge-free physical directions. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalGaugeFreeLinearMap :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real]
      GaugeFreePhysical period hPeriod configuration where
  toFun normal :=
    ⟨normalMinimalPhysicalLinearMap period hPeriod configuration normal, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (normalMinimalPhysicalLinearMap period hPeriod configuration).map_add
      first second
  map_smul' scalar normal := by
    apply Subtype.ext
    exact (normalMinimalPhysicalLinearMap period hPeriod configuration).map_smul
      scalar normal

/-- Full-BRST Euler covector restricted to pure normal tests. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalGaugeFreeLinearMap
        period hPeriod configuration)

/-- The physical part of a pure normal test is the existing normal Euler
covector. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalPhysicalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalGaugeFreeLinearMap
          period hPeriod configuration) =
      globalCandidateAMinimalPhysicalNormalEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state) := by
  apply LinearMap.ext
  intro normal
  rfl

/-- A pure normal test has zero metric component, so its diagonal
diffeomorphism-BRST response vanishes. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalDiffeomorphismBRSTCovector_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalGaugeFreeLinearMap
          period hPeriod configuration) = 0 := by
  apply LinearMap.ext
  intro normal
  have hState :
      globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap
          period hPeriod configuration
          (globalCandidateAGaugeFixedNonlinearFullBRSTNormalGaugeFreeLinearMap
            period hPeriod configuration normal) = 0 := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext <;> rfl
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [hState, map_zero, map_zero]

/-- Exact normal equation: authentic Robin block plus the named physical
cross-block. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period hPeriod
        configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
    LinearMap.add_comp,
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPhysicalEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalDiffeomorphismBRSTCovector_eq_zero,
    add_zero,
    globalCandidateAMinimalPhysicalNormalEulerCovector_decomposition]

/-- Full criticality forces the coupled weak Robin normal equation. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_normalEuler_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state) :
    globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) = 0 := by
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq]
  have hCoupled :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_coupledCoreEulerSystem
      period hPeriod configuration data analysis chartData state).mp hCritical
  apply LinearMap.ext
  intro normal
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
        period hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalGaugeFreeLinearMap
          period hPeriod configuration normal) = 0
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
    hCoupled.1]
  rfl

/-- Gate 231: the full-BRST normal equation is the honest coupled Robin
equation. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_normal_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period hPeriod
        configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq period hPeriod
    configuration data analysis chartData state

end NormalEuler

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalEuler4D
