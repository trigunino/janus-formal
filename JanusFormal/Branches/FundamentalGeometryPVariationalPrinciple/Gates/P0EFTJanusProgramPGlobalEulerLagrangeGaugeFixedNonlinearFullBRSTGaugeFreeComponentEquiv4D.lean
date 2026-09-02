import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D

/-!
# Gauge-free physical component equivalence

The gauge-free physical tangent is exactly the product of metric, normal,
corrected diffeomorphism-ghost, three LL and primitive SpinC test spaces.  This
closes component exhaustion inside the gauge-free factor.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreeComponentEquiv4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCMatterEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldGaugeFreeComponent :
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

local instance effectiveQuotientChartedSpaceGaugeFreeComponent :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldGaugeFreeComponent :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceGaugeFreeComponent :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceGaugeFreeComponent :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceGaugeFreeComponent :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldGaugeFreeComponent :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceGaugeFreeComponent :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldGaugeFreeComponent :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteGaugeFreeComponent :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroupGaugeFreeComponent :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModuleGaugeFreeComponent :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroupGaugeFreeComponent
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModuleGaugeFreeComponent
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

/-- The seven independent component families of a gauge-free physical test. -/
abbrev GlobalCandidateAGaugeFreePhysicalComponentTests4D :=
  GlobalMinimalPhysicalMetricTest period hPeriod ×
    (GlobalMinimalPhysicalNormalTest period hPeriod ×
      (GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod ×
        (GlobalMinimalPhysicalLLAuxMetricTest period hPeriod ×
          (GlobalMinimalPhysicalLLMeasureTest period hPeriod ×
            (GlobalMinimalPhysicalLLFieldTest period hPeriod ×
              (Sector → D9PrimitiveSpinCSmoothSection period hPeriod
                .positiveQuarter))))))

section GaugeFreeComponentEquiv

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

private abbrev Components :=
  GlobalCandidateAGaugeFreePhysicalComponentTests4D period hPeriod

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupGaugeFreeComponent :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleGaugeFreeComponent :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupGaugeFreeComponent :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Exact linear coordinates on the gauge-free physical tangent. -/
def globalCandidateAGaugeFreePhysicalComponentLinearEquiv :
    GaugeFreePhysical period hPeriod configuration ≃ₗ[Real]
      Components period hPeriod where
  toFun physical :=
    let sectors := globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration.physical physical.1
    let bulk := globalMinimalPhysicalSevenBulkEquiv period hPeriod sectors.1
    (bulk.1,
      (bulk.2.2.1,
        (bulk.2.2.2.1,
          (bulk.2.2.2.2.1,
            (bulk.2.2.2.2.2.1,
              (bulk.2.2.2.2.2.2, sectors.2))))))
  invFun components :=
    let bulkCoordinates : GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod :=
      (components.1,
        (0,
          (components.2.1,
            (components.2.2.1,
              (components.2.2.2.1,
                (components.2.2.2.2.1,
                  components.2.2.2.2.2.1))))))
    let spinC := components.2.2.2.2.2.2
    ⟨(globalMinimalPhysicalTangentSectorEquiv period hPeriod
        configuration.physical).symm
      ((globalMinimalPhysicalSevenBulkEquiv period hPeriod).symm
        bulkCoordinates, spinC), rfl⟩
  left_inv physical := by
    have hGauge :
        (globalMinimalPhysicalSevenBulkEquiv period hPeriod
          (globalMinimalPhysicalTangentSectorEquiv period hPeriod
            configuration.physical physical.1).1).2.1 = 0 := by
      change
        (GlobalPhysicalFieldTangent.completeVariation period hPeriod
          physical.1.1).independent.gauge = 0
      exact LinearMap.mem_ker.mp physical.2
    apply Subtype.ext
    apply (globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration.physical).injective
    apply Prod.ext
    · apply (globalMinimalPhysicalSevenBulkEquiv period hPeriod).injective
      simp only [LinearEquiv.apply_symm_apply]
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact hGauge.symm
        · rfl
    · rfl
  right_inv components := by
    ext <;> rfl
  map_add' first second := by
    ext <;> rfl
  map_smul' scalar physical := by
    ext <;> rfl

/-- Gauge-free Euler covector in the exact seven component coordinates. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeComponentEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Components period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalCandidateAGaugeFreePhysicalComponentLinearEquiv period hPeriod
        configuration).symm.toLinearMap

/-- Vanishing of the gauge-free equation is exactly the seven component
equations. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeEulerCovector_eq_zero_iff_components
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period
            hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period
            hPeriod configuration data analysis chartData state = 0 ∧
          globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
              period hPeriod configuration data analysis chartData state = 0 ∧
            globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector
                period hPeriod configuration data analysis chartData state = 0 ∧
              globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector
                  period hPeriod configuration data analysis chartData state = 0 ∧
                globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector
                    period hPeriod configuration data analysis chartData state = 0 ∧
                  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector
                    period hPeriod configuration data analysis chartData state = 0 := by
  let covector :=
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
      period hPeriod configuration data analysis chartData state
  let componentCovector :=
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeComponentEulerCovector
      period hPeriod configuration data analysis chartData state
  change covector = 0 ↔ _
  rw [← covector_comp_equiv_symm_eq_zero_iff
    (globalCandidateAGaugeFreePhysicalComponentLinearEquiv period hPeriod
      configuration) covector]
  change componentCovector = 0 ↔ _
  rw [productCovector_eq_zero_iff componentCovector]
  rw [productCovector_eq_zero_iff (productCovectorSecond componentCovector)]
  rw [productCovector_eq_zero_iff
    (productCovectorSecond (productCovectorSecond componentCovector))]
  rw [productCovector_eq_zero_iff
    (productCovectorSecond (productCovectorSecond
      (productCovectorSecond componentCovector)))]
  rw [productCovector_eq_zero_iff
    (productCovectorSecond (productCovectorSecond
      (productCovectorSecond (productCovectorSecond componentCovector))))]
  rw [productCovector_eq_zero_iff
    (productCovectorSecond (productCovectorSecond
      (productCovectorSecond (productCovectorSecond
        (productCovectorSecond componentCovector)))))]
  rfl

/-- Gate 235: the gauge-free tangent and equation are exhausted by the seven
canonical component families. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_gaugeFree_component_equiv_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period
            hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period
            hPeriod configuration data analysis chartData state = 0 ∧
          globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
              period hPeriod configuration data analysis chartData state = 0 ∧
            globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector
                period hPeriod configuration data analysis chartData state = 0 ∧
              globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector
                  period hPeriod configuration data analysis chartData state = 0 ∧
                globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector
                    period hPeriod configuration data analysis chartData state = 0 ∧
                  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector
                    period hPeriod configuration data analysis chartData state = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreeEulerCovector_eq_zero_iff_components
    period hPeriod configuration data analysis chartData state

end GaugeFreeComponentEquiv

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGaugeFreeComponentEquiv4D
