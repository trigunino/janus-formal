import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTComponentEulerSystem4D

/-!
# Diffeomorphism-nonminimal component Euler equations

The aggregated diffeomorphism-nonminimal BRST covector is split exactly into
ghost, antighost and Nakanishi--Lautrup component covectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentEuler4D

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

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldDiffeomorphismComponent :
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

local instance effectiveQuotientChartedSpaceDiffeomorphismComponent :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldDiffeomorphismComponent :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceDiffeomorphismComponent :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceDiffeomorphismComponent :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceDiffeomorphismComponent :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldDiffeomorphismComponent :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceDiffeomorphismComponent :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldDiffeomorphismComponent :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteDiffeomorphismComponent :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroupDiffeomorphismComponent :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModuleDiffeomorphismComponent :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroupDiffeomorphismComponent
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModuleDiffeomorphismComponent
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

/-- Linear product coordinates of the three diffeomorphism-nonminimal fields. -/
def globalDiffeomorphismNonminimalFieldsLinearEquiv :
    GlobalDiffeomorphismNonminimalFields period hPeriod ≃ₗ[Real]
      GlobalDiffeomorphismGhostField period hPeriod ×
        (GlobalDiffeomorphismAntighostField period hPeriod ×
          GlobalDiffeomorphismNakanishiLautrupField period hPeriod) where
  toFun state :=
    (state.ghost, (state.antighost, state.nakanishiLautrup))
  invFun fields :=
    ⟨fields.1, fields.2.1, fields.2.2⟩
  left_inv state := by cases state; rfl
  right_inv fields := by cases fields; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section DiffeomorphismNonminimalComponent

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

private abbrev DiffeomorphismComponents :=
  GlobalDiffeomorphismGhostField period hPeriod ×
    (GlobalDiffeomorphismAntighostField period hPeriod ×
      GlobalDiffeomorphismNakanishiLautrupField period hPeriod)

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupDiffeomorphismComponent :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleDiffeomorphismComponent :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupDiffeomorphismComponent :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Diffeomorphism-nonminimal BRST covector in its three field coordinates. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    DiffeomorphismComponents period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalDiffeomorphismNonminimalFieldsLinearEquiv period hPeriod).symm.toLinearMap

/-- Pure diffeomorphism ghost component covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalGhostBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real] Real :=
  productCovectorFirst
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentBRSTCovector
      period hPeriod configuration data analysis chartData state)

/-- Pure diffeomorphism antighost component covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalAntighostBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalDiffeomorphismAntighostField period hPeriod →ₗ[Real] Real :=
  productCovectorFirst (productCovectorSecond
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentBRSTCovector
      period hPeriod configuration data analysis chartData state))

/-- Pure diffeomorphism Nakanishi--Lautrup component covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalNakanishiLautrupBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalDiffeomorphismNakanishiLautrupField period hPeriod →ₗ[Real] Real :=
  productCovectorSecond (productCovectorSecond
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentBRSTCovector
      period hPeriod configuration data analysis chartData state))

/-- The aggregated diffeomorphism-nonminimal equation vanishes exactly when its
three field equations vanish. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector_eq_zero_iff_components
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalGhostBRSTCovector
            period hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalAntighostBRSTCovector
              period hPeriod configuration data analysis chartData state = 0 ∧
          globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalNakanishiLautrupBRSTCovector
            period hPeriod configuration data analysis chartData state = 0 := by
  let covector :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
      period hPeriod configuration data analysis chartData state
  let componentCovector :=
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentBRSTCovector
      period hPeriod configuration data analysis chartData state
  change covector = 0 ↔ _
  rw [← covector_comp_equiv_symm_eq_zero_iff
    (globalDiffeomorphismNonminimalFieldsLinearEquiv period hPeriod) covector]
  change componentCovector = 0 ↔ _
  rw [productCovector_eq_zero_iff componentCovector]
  rw [productCovector_eq_zero_iff (productCovectorSecond componentCovector)]
  rfl

/-- Full-BRST weak component system with the diffeomorphism nonminimal triplet
resolved field by field. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismComponentEulerSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period hPeriod
        configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period hPeriod
        configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
          period hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector
            period hPeriod configuration data analysis chartData state = 0 ∧
          globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector
              period hPeriod configuration data analysis chartData state = 0 ∧
            globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector
                period hPeriod configuration data analysis chartData state = 0 ∧
              globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector
                  period hPeriod configuration data analysis chartData state = 0 ∧
                globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalGhostBRSTCovector
                    period hPeriod configuration data analysis chartData state = 0 ∧
                  globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalAntighostBRSTCovector
                      period hPeriod configuration data analysis chartData state = 0 ∧
                    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalNakanishiLautrupBRSTCovector
                        period hPeriod configuration data analysis chartData state = 0 ∧
                      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector
                          period hPeriod configuration data analysis chartData state = 0 ∧
                        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
                          period hPeriod configuration data analysis chartData state = 0

/-- Exact criticality is equivalent to the fieldwise-resolved weak system. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_diffeomorphismComponentEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismComponentEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_componentEulerSystem]
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTComponentEulerSystemAt
    GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismComponentEulerSystemAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector_eq_zero_iff_components]
  simp only [and_assoc]

/-- Gate 237: the diffeomorphism nonminimal triplet is resolved field by field
inside the exact weak full-BRST Euler system. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_diffeomorphism_nonminimal_component_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismComponentEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_diffeomorphismComponentEulerSystem
    period hPeriod configuration data analysis chartData state

end DiffeomorphismNonminimalComponent

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentEuler4D
end JanusFormal
