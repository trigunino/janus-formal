import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTProjectionCompatibleCoveredAtlas4D

/-!
# Regularity of the authentic Abelian L2 residual coordinates

The antighost Faddeev--Popov and Nakanishi--Lautrup `Lorenz - B`
coordinates of the fixed full-BRST residual are bounded linear functions of
the full chart state.  Hence these two coordinates are globally smooth.  No
regularity of the other twelve, partly state-dependent graph/Riesz
coordinates is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianL2ResidualRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section Regularity

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
    (measure := measure) configuration data analysis chartData

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev RegularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedAddCommGroup
    period hPeriod (measure := measure) configuration data analysis chartData

private abbrev RegularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedSpace
    period hPeriod (measure := measure) configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 11000) regularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 11000) regularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedSpace period hPeriod configuration data analysis chartData

/-- The Abelian antighost residual as one bounded linear map. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2ResidualCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      GlobalPairedGaugeLieL2 period hPeriod :=
  (globalPairedAbelianOffShellFPProjection period hPeriod
    (BaseMetric period hPeriod configuration data)).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
        hPeriod configuration data analysis chartData)

/-- The Abelian auxiliary-field residual as one bounded linear map. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      GlobalPairedGaugeLieL2 period hPeriod := by
  let lorenz :=
    (globalPairedAbelianOffShellLorenzProjection period hPeriod
      (BaseMetric period hPeriod configuration data)).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData)
  let auxiliary :=
    (globalPairedAbelianOffShellBProjection period hPeriod
      (BaseMetric period hPeriod configuration data)).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData)
  exact
    { toFun := fun state => lorenz state - auxiliary state
      map_add' := by
        intro first second
        rw [lorenz.map_add, auxiliary.map_add]
        abel
      map_smul' := by
        intro scalar state
        rw [lorenz.map_smul, auxiliary.map_smul, smul_sub]
        simp only [RingHom.id_apply]
      cont := lorenz.continuous.sub auxiliary.continuous }

theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual_eq_clm
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2ResidualCLM
        period hPeriod configuration data analysis chartData state :=
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual_eq_clm
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualCLM
        period hPeriod configuration data analysis chartData state :=
  rfl

/-- The authentic Abelian antighost residual is globally smooth. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual_contDiff :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (GlobalPairedGaugeLieL2 period hPeriod) inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual
        period hPeriod configuration data analysis chartData) := by
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data
      analysis chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (GlobalPairedGaugeLieL2 period hPeriod) inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2ResidualCLM
      period hPeriod configuration data analysis chartData)
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (GlobalPairedGaugeLieL2 period hPeriod)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data
      analysis chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData) inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2ResidualCLM
      period hPeriod configuration data analysis chartData)

/-- The authentic Abelian auxiliary-field residual is globally smooth. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual_contDiff :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (GlobalPairedGaugeLieL2 period hPeriod) inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
        period hPeriod configuration data analysis chartData) := by
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data
      analysis chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (GlobalPairedGaugeLieL2 period hPeriod) inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualCLM
      period hPeriod configuration data analysis chartData)
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (GlobalPairedGaugeLieL2 period hPeriod)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data
      analysis chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData) inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualCLM
      period hPeriod configuration data analysis chartData)

/-- The two authentic Abelian `L²` residuals as one bounded linear map. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianL2ResidualCoordinatesCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      (GlobalPairedGaugeLieL2 period hPeriod ×
        GlobalPairedGaugeLieL2 period hPeriod) :=
  { toFun := fun state =>
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2ResidualCLM
          period hPeriod configuration data analysis chartData state,
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualCLM
          period hPeriod configuration data analysis chartData state)
    map_add' := by
      intro first second
      apply Prod.ext
      · exact
          (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2ResidualCLM
            period hPeriod configuration data analysis chartData).map_add
              first second
      · exact
          (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualCLM
            period hPeriod configuration data analysis chartData).map_add
              first second
    map_smul' := by
      intro scalar state
      apply Prod.ext
      · exact
          (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2ResidualCLM
            period hPeriod configuration data analysis chartData).map_smul
              scalar state
      · exact
          (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualCLM
            period hPeriod configuration data analysis chartData).map_smul
              scalar state
    cont :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2ResidualCLM
        period hPeriod configuration data analysis chartData).continuous.prodMk
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2ResidualCLM
          period hPeriod configuration data analysis chartData).continuous }

/-- The two authentic `L²` coordinates extracted from the fixed residual. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientAbelianL2Coordinates
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalPairedGaugeLieL2 period hPeriod ×
      GlobalPairedGaugeLieL2 period hPeriod :=
  ((globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
      period hPeriod configuration data analysis chartData state).abelianAntighost,
    (globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
      period hPeriod configuration data analysis chartData
        state).abelianNakanishiLautrup)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientAbelianL2Coordinates_apply
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientAbelianL2Coordinates
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianL2ResidualCoordinatesCLM
        period hPeriod configuration data analysis chartData state :=
  rfl

/-- The corresponding two-coordinate projection of the fixed ambient
residual is globally smooth. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientAbelianL2Coordinates_contDiff :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (GlobalPairedGaugeLieL2 period hPeriod ×
        GlobalPairedGaugeLieL2 period hPeriod) inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientAbelianL2Coordinates
        period hPeriod configuration data analysis chartData) := by
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data
      analysis chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (GlobalPairedGaugeLieL2 period hPeriod ×
      GlobalPairedGaugeLieL2 period hPeriod) inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianL2ResidualCoordinatesCLM
      period hPeriod configuration data analysis chartData)
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (GlobalPairedGaugeLieL2 period hPeriod ×
      GlobalPairedGaugeLieL2 period hPeriod)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data
      analysis chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData) inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianL2ResidualCoordinatesCLM
      period hPeriod configuration data analysis chartData)

/-- Gate 273: two authentic coordinates of the fixed fourteen-component
full-BRST residual are bounded linear, hence globally smooth. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_abelian_l2_residual_regularity_gate :
    @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (GlobalPairedGaugeLieL2 period hPeriod) inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual
          period hPeriod configuration data analysis chartData) ∧
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (GlobalPairedGaugeLieL2 period hPeriod) inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
          period hPeriod configuration data analysis chartData) ∧
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (GlobalPairedGaugeLieL2 period hPeriod ×
          GlobalPairedGaugeLieL2 period hPeriod) inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientAbelianL2Coordinates
          period hPeriod configuration data analysis chartData) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual_contDiff
      period hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual_contDiff
      period hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientAbelianL2Coordinates_contDiff
      period hPeriod configuration data analysis chartData⟩

end Regularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianL2ResidualRegularity4D
end JanusFormal
