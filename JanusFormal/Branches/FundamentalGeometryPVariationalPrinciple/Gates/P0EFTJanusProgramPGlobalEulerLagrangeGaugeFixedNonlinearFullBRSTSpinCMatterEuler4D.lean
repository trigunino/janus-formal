import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSpinCMatterGraphResidualBridge4D

/-!
# Full-BRST primitive SpinC Euler equation

Pure primitive SpinC tests have zero bulk metric and Abelian components.  The
full-BRST equation is the authentic matter block plus its named cross-block.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCMatterEuler4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSpinCMatterGraphResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldSpinCEuler :
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

local instance effectiveQuotientChartedSpaceSpinCEuler :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldSpinCEuler :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceSpinCEuler :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceSpinCEuler :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceSpinCEuler :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldSpinCEuler :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceSpinCEuler :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldSpinCEuler :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteSpinCEuler :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroupSpinCEuler :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModuleSpinCEuler :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroupSpinCEuler
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModuleSpinCEuler
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

section SpinCEuler

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

private abbrev SpinCTest :=
  Sector → D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

private abbrev GaugeFreePhysical :=
  GlobalCandidateAMinimalPhysicalGaugeFreeTangent4D period hPeriod
    configuration

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupSpinCEuler :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleSpinCEuler :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupSpinCEuler :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Pure primitive SpinC directions in the corrected minimal tangent. -/
private def spinCMinimalPhysicalLinearMap :
    SpinCTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical :=
  (globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration.physical).symm.toLinearMap.comp
    (productSecondInclusion
      (GlobalMinimalPhysicalBulkTangent period hPeriod)
      (SpinCTest period hPeriod))

/-- Pure primitive SpinC tests regarded as gauge-free physical directions. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCGaugeFreeLinearMap :
    SpinCTest period hPeriod →ₗ[Real]
      GaugeFreePhysical period hPeriod configuration where
  toFun spinC :=
    ⟨spinCMinimalPhysicalLinearMap period hPeriod configuration spinC, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (spinCMinimalPhysicalLinearMap period hPeriod configuration).map_add
      first second
  map_smul' scalar spinC := by
    apply Subtype.ext
    exact (spinCMinimalPhysicalLinearMap period hPeriod configuration).map_smul
      scalar spinC

/-- Full-BRST Euler covector restricted to primitive SpinC tests. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SpinCTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCGaugeFreeLinearMap
        period hPeriod configuration)

/-- The physical part of a pure SpinC test is the existing complete SpinC
Euler covector. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCPhysicalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCGaugeFreeLinearMap
          period hPeriod configuration) =
      globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state) := by
  apply LinearMap.ext
  intro spinC
  rfl

/-- Pure SpinC tests have zero metric component, so their diagonal
diffeomorphism-BRST response vanishes. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCDiffeomorphismBRSTCovector_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCGaugeFreeLinearMap
          period hPeriod configuration) = 0 := by
  apply LinearMap.ext
  intro spinC
  have hState :
      globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap
          period hPeriod configuration
          (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCGaugeFreeLinearMap
            period hPeriod configuration spinC) = 0 := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext <;> rfl
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [hState, map_zero, map_zero]

/-- Exact SpinC equation: authentic matter block plus the named physical
cross-block. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector period hPeriod
        configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalMatterBlockSpinCEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalSpinCCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
    LinearMap.add_comp,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCPhysicalEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCDiffeomorphismBRSTCovector_eq_zero,
    add_zero,
    globalCandidateAMinimalPhysicalSpinCEulerCovector_decomposition]

/-- Full criticality forces the coupled weak SpinC matter equation. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_spinCEuler_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state) :
    globalCandidateAMinimalPhysicalMatterBlockSpinCEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalSpinCCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) = 0 := by
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq]
  have hCoupled :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_coupledCoreEulerSystem
      period hPeriod configuration data analysis chartData state).mp hCritical
  apply LinearMap.ext
  intro spinC
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
        period hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCGaugeFreeLinearMap
          period hPeriod configuration spinC) = 0
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
    hCoupled.1]
  rfl

/-- Gate 233: the full-BRST primitive SpinC equation is the honest coupled
matter equation. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_spinC_matter_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector period hPeriod
        configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalMatterBlockSpinCEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalSpinCCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq period hPeriod
    configuration data analysis chartData state

end SpinCEuler

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCMatterEuler4D
