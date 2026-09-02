import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentEuler4D

/-!
# Abelian-nonminimal component Euler equations

The paired Abelian nonminimal BRST covector is split exactly into its typed
ghost, antighost and Nakanishi--Lautrup family covectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentEuler4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldAbelianComponent :
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

local instance effectiveQuotientChartedSpaceAbelianComponent :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldAbelianComponent :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceAbelianComponent :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceAbelianComponent :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceAbelianComponent :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldAbelianComponent :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceAbelianComponent :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldAbelianComponent :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteAbelianComponent :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroupAbelianComponent :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModuleAbelianComponent :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroupAbelianComponent
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModuleAbelianComponent
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

/-- Linear product coordinates of the paired typed Abelian nonminimal fields. -/
def globalPairedAbelianNonminimalFieldsLinearEquiv :
    (Sector → GlobalAbelianNonminimalFields period hPeriod) ≃ₗ[Real]
      (Sector → GlobalAbelianGhostField period hPeriod) ×
        ((Sector → GlobalAbelianAntighostField period hPeriod) ×
          (Sector → GlobalAbelianNakanishiLautrupField period hPeriod)) where
  toFun states :=
    (fun sector => (states sector).ghost,
      (fun sector => (states sector).antighost,
        fun sector => (states sector).nakanishiLautrup))
  invFun fields := fun sector =>
    ⟨fields.1 sector, fields.2.1 sector, fields.2.2 sector⟩
  left_inv states := by
    funext sector
    apply GlobalAbelianNonminimalFields.ext <;> rfl
  right_inv fields := by
    apply Prod.ext
    · funext sector
      rfl
    · apply Prod.ext
      · funext sector
        rfl
      · funext sector
        rfl
  map_add' first second := by
    apply Prod.ext
    · funext sector
      rfl
    · apply Prod.ext
      · funext sector
        rfl
      · funext sector
        rfl
  map_smul' scalar states := by
    apply Prod.ext
    · funext sector
      rfl
    · apply Prod.ext
      · funext sector
        rfl
      · funext sector
        rfl

section AbelianNonminimalComponent

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

private abbrev AbelianComponents :=
  (Sector → GlobalAbelianGhostField period hPeriod) ×
    ((Sector → GlobalAbelianAntighostField period hPeriod) ×
      (Sector → GlobalAbelianNakanishiLautrupField period hPeriod))

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupAbelianComponent :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleAbelianComponent :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupAbelianComponent :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Abelian-nonminimal BRST covector in its three typed field coordinates. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    AbelianComponents period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
    period hPeriod configuration data analysis chartData state).comp
      (globalPairedAbelianNonminimalFieldsLinearEquiv period hPeriod).symm.toLinearMap

/-- Pure paired Abelian ghost-family component covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalGhostBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (Sector → GlobalAbelianGhostField period hPeriod) →ₗ[Real] Real :=
  productCovectorFirst
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentBRSTCovector
      period hPeriod configuration data analysis chartData state)

/-- Pure paired Abelian antighost-family component covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalAntighostBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (Sector → GlobalAbelianAntighostField period hPeriod) →ₗ[Real] Real :=
  productCovectorFirst (productCovectorSecond
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentBRSTCovector
      period hPeriod configuration data analysis chartData state))

/-- Pure paired Abelian Nakanishi--Lautrup-family component covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (Sector → GlobalAbelianNakanishiLautrupField period hPeriod) →ₗ[Real] Real :=
  productCovectorSecond (productCovectorSecond
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentBRSTCovector
      period hPeriod configuration data analysis chartData state))

/-- The aggregated Abelian-nonminimal equation vanishes exactly when its three
typed family equations vanish. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector_eq_zero_iff_components
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalGhostBRSTCovector
            period hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalAntighostBRSTCovector
              period hPeriod configuration data analysis chartData state = 0 ∧
          globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
            period hPeriod configuration data analysis chartData state = 0 := by
  let covector :=
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
      period hPeriod configuration data analysis chartData state
  let componentCovector :=
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentBRSTCovector
      period hPeriod configuration data analysis chartData state
  change covector = 0 ↔ _
  rw [← covector_comp_equiv_symm_eq_zero_iff
    (globalPairedAbelianNonminimalFieldsLinearEquiv period hPeriod) covector]
  change componentCovector = 0 ↔ _
  rw [productCovector_eq_zero_iff componentCovector]
  rw [productCovector_eq_zero_iff (productCovectorSecond componentCovector)]
  rfl

/-- Exact weak full-BRST system with both nonminimal triplets resolved field by
field. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTFieldwiseComponentEulerSystemAt
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
                        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalGhostBRSTCovector
                            period hPeriod configuration data analysis chartData state = 0 ∧
                          globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalAntighostBRSTCovector
                              period hPeriod configuration data analysis chartData state = 0 ∧
                            globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
                              period hPeriod configuration data analysis chartData state = 0

/-- Exact criticality is equivalent to the fully fieldwise weak component
system. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_fieldwiseComponentEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFieldwiseComponentEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_diffeomorphismComponentEulerSystem]
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismComponentEulerSystemAt
    GlobalCandidateAGaugeFixedNonlinearFullBRSTFieldwiseComponentEulerSystemAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector_eq_zero_iff_components]

/-- Gate 238: both nonminimal triplets are resolved field by field inside the
exact weak full-BRST Euler system. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_abelian_nonminimal_component_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFieldwiseComponentEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_fieldwiseComponentEulerSystem
    period hPeriod configuration data analysis chartData state

end AbelianNonminimalComponent

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentEuler4D
end JanusFormal
