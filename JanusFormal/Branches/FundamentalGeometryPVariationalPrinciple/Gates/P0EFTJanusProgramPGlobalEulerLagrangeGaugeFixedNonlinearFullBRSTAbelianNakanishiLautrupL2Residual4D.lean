import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalComponentEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonAnalyticDomainClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

/-!
# Strong paired Abelian Nakanishi--Lautrup residual

The weak Nakanishi--Lautrup component is represented and separated by the
authentic `L²` residual `Lorenz - B` on the completed paired Abelian graph.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D

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

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldAbelianBResidual :
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

local instance effectiveQuotientChartedSpaceAbelianBResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldAbelianBResidual :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceAbelianBResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceAbelianBResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceAbelianBResidual :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldAbelianBResidual :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceAbelianBResidual :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldAbelianBResidual :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteAbelianBResidual :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroupAbelianBResidual :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModuleAbelianBResidual :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroupAbelianBResidual
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModuleAbelianBResidual
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

/-- Smooth paired gauge-Lie fields are dense in the existing paired `L²`
carrier. -/
theorem globalPairedGaugeLieL2LinearMap_denseRange :
    DenseRange (globalPairedGaugeLieL2LinearMap period hPeriod) := by
  rw [DenseRange]
  have hRange :
      Set.range (globalPairedGaugeLieL2LinearMap period hPeriod) =
        Set.range (globalPairedAbelianLorenzAdjointTestInclusion period
          hPeriod) := by
    ext value
    constructor
    · rintro ⟨field, rfl⟩
      refine ⟨fun index => ghostComponent period hPeriod
        (field index.1) index.2, ?_⟩
      apply PiLp.ext
      intro index
      rfl
    · rintro ⟨field, rfl⟩
      refine ⟨globalPairedGaugeLieSmoothOfComponents period hPeriod field, ?_⟩
      apply PiLp.ext
      intro index
      change
        smoothToCanonicalPhysicalBulkL2 period hPeriod
            (ghostComponent period hPeriod
              (globalPairedGaugeLieSmoothOfComponents period hPeriod field
                index.1) index.2) =
          smoothToCanonicalPhysicalBulkL2 period hPeriod (field index)
      rw [ghostComponent_globalPairedGaugeLieSmoothOfComponents]
  rw [hRange]
  exact globalPairedAbelianLorenzAdjointTestInclusion_denseRange period hPeriod

section AbelianBResidual

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
local instance (priority := 10003) fullChartAddCommGroupAbelianBResidual :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleAbelianBResidual :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) gaugeFreePhysicalAddCommGroupAbelianBResidual :
    AddCommGroup (GaugeFreePhysical period hPeriod configuration) :=
  Module.addCommMonoidToAddCommGroup Real

/-- Authentic strong `L²` residual of the Abelian Nakanishi--Lautrup equation. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalPairedGaugeLieL2 period hPeriod :=
  globalPairedAbelianOffShellLorenzProjection period hPeriod
        (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData state) -
    globalPairedAbelianOffShellBProjection period hPeriod
      (BaseMetric period hPeriod configuration data)
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
        hPeriod configuration data analysis chartData state)

/-- Pair the strong residual with a smooth typed Nakanishi--Lautrup test. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualPairing
    (residual : GlobalPairedGaugeLieL2 period hPeriod)
    (test : Sector → GlobalAbelianNakanishiLautrupField period hPeriod) : Real :=
  inner Real residual
    (globalPairedGaugeLieL2LinearMap period hPeriod
      (fun sector => (test sector).field))

/-- The weak component covector is exactly pairing with `Lorenz - B`. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_apply_eq_l2ResidualPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : Sector → GlobalAbelianNakanishiLautrupField period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
        period hPeriod configuration data analysis chartData state test =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualPairing
        period hPeriod
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
          period hPeriod configuration data analysis chartData state) test := by
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state
        (fun sector => ⟨⟨0⟩, ⟨0⟩, test sector⟩) = _
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
  simp only [LinearMap.comp_apply]
  change
    globalPairedAbelianOffShellHessian period hPeriod
        (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData state)
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (BaseMetric period hPeriod configuration data)
          { potential := 0
            nonminimal := fun sector => ⟨⟨0⟩, ⟨0⟩, test sector⟩ }) = _
  rw [globalPairedAbelianOffShellHessian_apply]
  simp only [globalPairedAbelianOffShellLorenzProjection_smooth,
    globalPairedAbelianOffShellBProjection_smooth,
    globalPairedAbelianOffShellAntighostProjection_smooth,
    globalPairedAbelianOffShellFPProjection_smooth,
    map_zero, inner_zero_right, zero_add]
  have hZeroGaugeLieField :
      (fun _ : Sector =>
        (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra)) = 0 := rfl
  rw [hZeroGaugeLieField]
  simp only [map_zero, inner_zero_right, add_zero]
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualPairing
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
  rw [inner_sub_left]

/-- Smooth typed tests separate the authentic `L²` residual. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualPairing_separates
    (residual : GlobalPairedGaugeLieL2 period hPeriod) :
    (∀ test : Sector → GlobalAbelianNakanishiLautrupField period hPeriod,
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualPairing
          period hPeriod residual test = 0) ↔ residual = 0 := by
  constructor
  · intro hPairing
    apply (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod
      ).eq_zero_of_inner_left (𝕜 := Real)
    intro test
    exact hPairing (fun sector => ⟨test sector⟩)
  · rintro rfl test
    simp [globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualPairing]

/-- Concrete separating representation of the strong Abelian
Nakanishi--Lautrup residual. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualRepresentation
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
        period hPeriod configuration data analysis chartData state) where
  Residual := GlobalPairedGaugeLieL2 period hPeriod
  zeroResidual := 0
  residual :=
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
      period hPeriod configuration data analysis chartData state
  pairing :=
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualPairing
      period hPeriod
  represents := fun test =>
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_apply_eq_l2ResidualPairing
      period hPeriod configuration data analysis chartData state test
  separates :=
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualPairing_separates
      period hPeriod
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
          period hPeriod configuration data analysis chartData state)

/-- Weak Nakanishi--Lautrup stationarity is equivalent to the authentic strong
`L²` residual equation. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_eq_zero_iff_l2Residual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
        period hPeriod configuration data analysis chartData state = 0 :=
  separatingPDEResidualRepresentation_covector_eq_zero_iff
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualRepresentation
      period hPeriod configuration data analysis chartData state)

/-- Full-BRST criticality forces the strong Abelian auxiliary-field residual. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianNakanishiLautrupL2Residual_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
        period hPeriod configuration data analysis chartData state = 0 := by
  have hSystem :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_fieldwiseComponentEulerSystem
      period hPeriod configuration data analysis chartData state).mp hCritical
  rcases hSystem with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hNakanishiLautrup⟩
  exact
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_eq_zero_iff_l2Residual
      period hPeriod configuration data analysis chartData state).mp
        hNakanishiLautrup

/-- Gate 239: the Abelian Nakanishi--Lautrup weak equation has its authentic
separating strong `L²` residual. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_abelian_nakanishiLautrup_l2_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalNakanishiLautrupBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
        period hPeriod configuration data analysis chartData state = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupBRSTCovector_eq_zero_iff_l2Residual
    period hPeriod configuration data analysis chartData state

end AbelianBResidual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
end JanusFormal
