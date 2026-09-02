import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLThreeSlotCrossBlockDecomposition4D

/-!
# Full-BRST LL three-slot Euler equations

The LL auxiliary-metric, measure and field tests have zero physical metric and
Abelian components.  Their full-BRST equations are the corresponding LL block
covectors plus the named physical cross-blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotEuler4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalLLThreeSlotCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldLLThreeSlot :
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

local instance effectiveQuotientChartedSpaceLLThreeSlot :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldLLThreeSlot :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceLLThreeSlot :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceLLThreeSlot :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceLLThreeSlot :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldLLThreeSlot :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceLLThreeSlot :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldLLThreeSlot :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteLLThreeSlot :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroupLLThreeSlot :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModuleLLThreeSlot :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroupLLThreeSlot
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModuleLLThreeSlot
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

section LLThreeSlotEuler

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
local instance (priority := 10003) fullChartAddCommGroupLLThreeSlot :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleLLThreeSlot :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupLLThreeSlot :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Insert any seven-bulk test coordinate into the corrected minimal tangent. -/
private def sevenBulkTestMinimalPhysicalLinearMap
    {Test : Type*} [AddCommMonoid Test] [Module Real Test]
    (inclusion : Test →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod) :
    Test →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical :=
  (globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration.physical).symm.toLinearMap.comp
    ((productFirstInclusion
      (GlobalMinimalPhysicalBulkTangent period hPeriod)
      (Sector → D9PrimitiveSpinCSmoothSection period hPeriod
        .positiveQuarter)).comp
      ((globalMinimalPhysicalSevenBulkEquiv period hPeriod).symm.toLinearMap.comp
        inclusion))

/-- LL auxiliary-metric tests as gauge-free physical directions. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricGaugeFreeLinearMap :
    GlobalMinimalPhysicalLLAuxMetricTest period hPeriod →ₗ[Real]
      GaugeFreePhysical period hPeriod configuration where
  toFun variation :=
    ⟨sevenBulkTestMinimalPhysicalLinearMap period hPeriod configuration
      (globalMinimalPhysicalLLAuxMetricTestInclusion period hPeriod) variation,
      rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (sevenBulkTestMinimalPhysicalLinearMap period hPeriod configuration
      (globalMinimalPhysicalLLAuxMetricTestInclusion period hPeriod)).map_add
        first second
  map_smul' scalar variation := by
    apply Subtype.ext
    exact (sevenBulkTestMinimalPhysicalLinearMap period hPeriod configuration
      (globalMinimalPhysicalLLAuxMetricTestInclusion period hPeriod)).map_smul
        scalar variation

/-- LL measure tests as gauge-free physical directions. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureGaugeFreeLinearMap :
    GlobalMinimalPhysicalLLMeasureTest period hPeriod →ₗ[Real]
      GaugeFreePhysical period hPeriod configuration where
  toFun variation :=
    ⟨sevenBulkTestMinimalPhysicalLinearMap period hPeriod configuration
      (globalMinimalPhysicalLLMeasureTestInclusion period hPeriod) variation,
      rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (sevenBulkTestMinimalPhysicalLinearMap period hPeriod configuration
      (globalMinimalPhysicalLLMeasureTestInclusion period hPeriod)).map_add
        first second
  map_smul' scalar variation := by
    apply Subtype.ext
    exact (sevenBulkTestMinimalPhysicalLinearMap period hPeriod configuration
      (globalMinimalPhysicalLLMeasureTestInclusion period hPeriod)).map_smul
        scalar variation

/-- LL field tests as gauge-free physical directions. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldGaugeFreeLinearMap :
    GlobalMinimalPhysicalLLFieldTest period hPeriod →ₗ[Real]
      GaugeFreePhysical period hPeriod configuration where
  toFun variation :=
    ⟨sevenBulkTestMinimalPhysicalLinearMap period hPeriod configuration
      (globalMinimalPhysicalLLFieldTestInclusion period hPeriod) variation,
      rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (sevenBulkTestMinimalPhysicalLinearMap period hPeriod configuration
      (globalMinimalPhysicalLLFieldTestInclusion period hPeriod)).map_add
        first second
  map_smul' scalar variation := by
    apply Subtype.ext
    exact (sevenBulkTestMinimalPhysicalLinearMap period hPeriod configuration
      (globalMinimalPhysicalLLFieldTestInclusion period hPeriod)).map_smul
        scalar variation

/-- Full-BRST Euler covector on the LL auxiliary-metric slot. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalMinimalPhysicalLLAuxMetricTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricGaugeFreeLinearMap
        period hPeriod configuration)

/-- Full-BRST Euler covector on the LL measure slot. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalMinimalPhysicalLLMeasureTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureGaugeFreeLinearMap
        period hPeriod configuration)

/-- Full-BRST Euler covector on the LL field slot. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalMinimalPhysicalLLFieldTest period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldGaugeFreeLinearMap
        period hPeriod configuration)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricPhysicalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricGaugeFreeLinearMap
          period hPeriod configuration) =
      globalCandidateAMinimalPhysicalLLAuxMetricEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state) := by
  apply LinearMap.ext
  intro variation
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasurePhysicalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureGaugeFreeLinearMap
          period hPeriod configuration) =
      globalCandidateAMinimalPhysicalLLMeasureEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state) := by
  apply LinearMap.ext
  intro variation
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldPhysicalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalActionEulerCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldGaugeFreeLinearMap
          period hPeriod configuration) =
      globalCandidateAMinimalPhysicalLLFieldEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state) := by
  apply LinearMap.ext
  intro variation
  rfl

private theorem gaugeFreeDiffeomorphismBRSTCovector_apply_eq_zero_of_state_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (physical : GaugeFreePhysical period hPeriod configuration)
    (hState :
      globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismStateLinearMap
        period hPeriod configuration physical = 0) :
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
        period hPeriod configuration data analysis chartData state physical = 0 := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
  simp only [LinearMap.comp_apply]
  rw [hState, map_zero, map_zero]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricDiffeomorphismBRSTCovector_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricGaugeFreeLinearMap
          period hPeriod configuration) = 0 := by
  apply LinearMap.ext
  intro variation
  apply gaugeFreeDiffeomorphismBRSTCovector_apply_eq_zero_of_state_eq_zero
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext <;> rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureDiffeomorphismBRSTCovector_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureGaugeFreeLinearMap
          period hPeriod configuration) = 0 := by
  apply LinearMap.ext
  intro variation
  apply gaugeFreeDiffeomorphismBRSTCovector_apply_eq_zero_of_state_eq_zero
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext <;> rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldDiffeomorphismBRSTCovector_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeDiffeomorphismBRSTCovector
      period hPeriod configuration data analysis chartData state).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldGaugeFreeLinearMap
          period hPeriod configuration) = 0 := by
  apply LinearMap.ext
  intro variation
  apply gaugeFreeDiffeomorphismBRSTCovector_apply_eq_zero_of_state_eq_zero
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext <;> rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector period
        hPeriod configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalLLAuxMetricCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
    LinearMap.add_comp,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricPhysicalEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricDiffeomorphismBRSTCovector_eq_zero,
    add_zero,
    globalCandidateAMinimalPhysicalLLAuxMetricEulerCovector_decomposition]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector period
        hPeriod configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt period hPeriod
          configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalLLMeasureCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
    LinearMap.add_comp,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasurePhysicalEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureDiffeomorphismBRSTCovector_eq_zero,
    add_zero,
    globalCandidateAMinimalPhysicalLLMeasureEulerCovector_decomposition]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector period hPeriod
        configuration data analysis chartData state =
      globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt period hPeriod
          configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalLLFieldCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
    LinearMap.add_comp,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldPhysicalEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldDiffeomorphismBRSTCovector_eq_zero,
    add_zero,
    globalCandidateAMinimalPhysicalLLFieldEulerCovector_decomposition]

/-- Full criticality forces all three coupled weak LL equations. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_llThreeSlotEuler_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state) :
    (globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) +
        globalCandidateAMinimalPhysicalLLAuxMetricCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
            configuration data analysis chartData state) = 0) ∧
      (globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt period hPeriod
            configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
              hPeriod configuration data analysis chartData state) +
          globalCandidateAMinimalPhysicalLLMeasureCrossBlockEulerCovectorAt period
            hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
              hPeriod configuration data analysis chartData state) = 0) ∧
        globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt period hPeriod
              configuration data analysis chartData
              (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
                hPeriod configuration data analysis chartData state) +
            globalCandidateAMinimalPhysicalLLFieldCrossBlockEulerCovectorAt period
              hPeriod configuration data analysis chartData
              (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
                hPeriod configuration data analysis chartData state) = 0 := by
  have hCoupled :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_coupledCoreEulerSystem
      period hPeriod configuration data analysis chartData state).mp hCritical
  have hGaugeFree :
      globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
          period hPeriod configuration data analysis chartData state = 0 := by
    rw [globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector_eq,
      hCoupled.1]
  have hAux :
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector period
        hPeriod configuration data analysis chartData state = 0 := by
    unfold globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector
    rw [hGaugeFree, LinearMap.zero_comp]
  have hMeasure :
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector period
        hPeriod configuration data analysis chartData state = 0 := by
    unfold globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector
    rw [hGaugeFree, LinearMap.zero_comp]
  have hField :
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector period
        hPeriod configuration data analysis chartData state = 0 := by
    unfold globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector
    rw [hGaugeFree, LinearMap.zero_comp]
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq] at hAux
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq] at hMeasure
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq] at hField
  exact ⟨hAux, hMeasure, hField⟩

/-- Gate 232: all three full-BRST LL equations reduce exactly to their
physical LL block and named cross-block. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_ll_three_slot_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector period
          hPeriod configuration data analysis chartData state =
        globalCandidateAMinimalPhysicalLLAuxMetricBlockEulerCovectorAt period
            hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
              hPeriod configuration data analysis chartData state) +
          globalCandidateAMinimalPhysicalLLAuxMetricCrossBlockEulerCovectorAt
            period hPeriod configuration data analysis chartData
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
              hPeriod configuration data analysis chartData state)) ∧
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector period
            hPeriod configuration data analysis chartData state =
          globalCandidateAMinimalPhysicalLLMeasureBlockEulerCovectorAt period
              hPeriod configuration data analysis chartData
              (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
                hPeriod configuration data analysis chartData state) +
            globalCandidateAMinimalPhysicalLLMeasureCrossBlockEulerCovectorAt
              period hPeriod configuration data analysis chartData
              (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
                hPeriod configuration data analysis chartData state)) ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector period
              hPeriod configuration data analysis chartData state =
            globalCandidateAMinimalPhysicalLLFieldBlockEulerCovectorAt period
                hPeriod configuration data analysis chartData
                (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
                  hPeriod configuration data analysis chartData state) +
              globalCandidateAMinimalPhysicalLLFieldCrossBlockEulerCovectorAt
                period hPeriod configuration data analysis chartData
                (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period
                  hPeriod configuration data analysis chartData state) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq period
      hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq period
      hPeriod configuration data analysis chartData state,
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq period
      hPeriod configuration data analysis chartData state⟩

end LLThreeSlotEuler

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotEuler4D
