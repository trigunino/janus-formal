import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCMatterEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D

/-!
# Full-BRST physical diffeomorphism-ghost Euler equation

The corrected minimal physical diffeomorphism-ghost coordinate has zero metric
and Abelian components.  Its full-BRST equation is exactly the existing
minimal-physical covector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D

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
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldPhysicalDiffeomorphismGhost :
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

local instance effectiveQuotientChartedSpacePhysicalDiffeomorphismGhost :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldPhysicalDiffeomorphismGhost :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpacePhysicalDiffeomorphismGhost :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpacePhysicalDiffeomorphismGhost :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpacePhysicalDiffeomorphismGhost :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldPhysicalDiffeomorphismGhost :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpacePhysicalDiffeomorphismGhost :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldPhysicalDiffeomorphismGhost :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFinitePhysicalDiffeomorphismGhost :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroupPhysicalDiffeomorphismGhost :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModulePhysicalDiffeomorphismGhost :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroupPhysicalDiffeomorphismGhost
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModulePhysicalDiffeomorphismGhost
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

section PhysicalDiffeomorphismGhostEuler

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
local instance (priority := 10003) fullChartAddCommGroupPhysicalDiffeomorphismGhost :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModulePhysicalDiffeomorphismGhost :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupPhysicalDiffeomorphismGhost :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Pure corrected diffeomorphism-ghost directions in the minimal tangent. -/
private def physicalDiffeomorphismGhostMinimalPhysicalLinearMap :
    GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical :=
  (globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration.physical).symm.toLinearMap.comp
    ((productFirstInclusion
      (GlobalMinimalPhysicalBulkTangent period hPeriod)
      (Sector → D9PrimitiveSpinCSmoothSection period hPeriod
        .positiveQuarter)).comp
      ((globalMinimalPhysicalSevenBulkEquiv period hPeriod).symm.toLinearMap.comp
        (globalMinimalPhysicalDiffeomorphismGhostTestInclusion period hPeriod)))

/-- Pure corrected diffeomorphism-ghost tests as gauge-free directions. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostGaugeFreeLinearMap :
    GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod →ₗ[Real]
      GaugeFreePhysical period hPeriod configuration where
  toFun ghost :=
    ⟨physicalDiffeomorphismGhostMinimalPhysicalLinearMap period hPeriod
      configuration ghost, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (physicalDiffeomorphismGhostMinimalPhysicalLinearMap period hPeriod
      configuration).map_add first second
  map_smul' scalar ghost := by
    apply Subtype.ext
    exact (physicalDiffeomorphismGhostMinimalPhysicalLinearMap period hPeriod
      configuration).map_smul scalar ghost

/-- Full-BRST Euler covector on the corrected physical ghost coordinate. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostGaugeFreeLinearMap
        period hPeriod configuration)

/-- Its physical part is exactly the existing minimal-physical ghost
covector. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostPhysicalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostGaugeFreeLinearMap
          period hPeriod configuration) =
      globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt period
        hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state) := by
  apply LinearMap.ext
  intro ghost
  rfl

/-- Its metric component is zero, so the diagonal diffeomorphism-BRST response
vanishes. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostBRSTCovector_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostGaugeFreeLinearMap
          period hPeriod configuration) = 0 := by
  apply LinearMap.ext
  intro ghost
  have hState :
      globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap
          period hPeriod configuration
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostGaugeFreeLinearMap
            period hPeriod configuration ghost) = 0 := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext <;> rfl
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [hState, map_zero, map_zero]

/-- Exact full-BRST physical diffeomorphism-ghost equation. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
        period hPeriod configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt period
        hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state) := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
    LinearMap.add_comp,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostPhysicalEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostBRSTCovector_eq_zero,
    add_zero]

/-- Full criticality forces the weak corrected physical ghost equation. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_physicalDiffeomorphismGhostEuler_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state) :
    globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt period
        hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state) = 0 := by
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector_eq]
  have hCoupled :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_coupledCoreEulerSystem
      period hPeriod configuration data analysis chartData state).mp hCritical
  apply LinearMap.ext
  intro ghost
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
        period hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostGaugeFreeLinearMap
          period hPeriod configuration ghost) = 0
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
    hCoupled.1]
  rfl

/-- Gate 234: the corrected physical diffeomorphism-ghost equation is exposed
without an artificial BRST remainder. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_physical_diffeomorphism_ghost_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
        period hPeriod configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt period
        hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector_eq
    period hPeriod configuration data analysis chartData state

end PhysicalDiffeomorphismGhostEuler

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D
