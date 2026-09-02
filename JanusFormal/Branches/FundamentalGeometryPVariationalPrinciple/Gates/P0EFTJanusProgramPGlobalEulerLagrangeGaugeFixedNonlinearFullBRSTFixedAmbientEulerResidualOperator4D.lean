import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLAuthenticDenseSeparation4D

/-!
# Fixed-ambient full-BRST Euler residual operator

The fourteen separated full-BRST residuals are projected from their closed
graph subspaces to fixed ambient spaces and assembled into one genuine map
from the nonlinear chart to a state-independent target.  Its zero is exactly
full-BRST criticality.  No continuity, atlas gluing or local PDE identification
is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2Faithfulness4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldFixedAmbientEulerResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section FixedOperator

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
    configuration data analysis chartData

/-- Fixed two-sheet normal `L²` coordinate. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedPairedNormalL2 :=
  WithLp 2
    (ThroatScalarL2
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (intrinsicCanonicalThroatVolumeMeasure
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) ×
      ThroatScalarL2
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (intrinsicCanonicalThroatVolumeMeasure
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)))

/-- Fixed base used by the augmented normal residual. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormalL2RobinBase :=
  WithLp 2
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedPairedNormalL2 period
        hPeriod × Real)

/-- Fixed two-sector physical-ghost `L²` coordinate. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedPairedPhysicalGhostL2 :=
  WithLp 2
    (PhysicalGhostFiniteFrameL2 period hPeriod ×
      PhysicalGhostFiniteFrameL2 period hPeriod)

/-- Fixed base used by the augmented physical-ghost residual. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedPhysicalGhostL2EulerBase :=
  WithLp 2
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedPairedPhysicalGhostL2
        period hPeriod × Real)

/-- State-independent codomain containing the fourteen full-BRST residual
coordinates. -/
@[ext]
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualTarget4D where
  metric :
    WithLp 2
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) × Real)
  normal :
    WithLp 2
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormalL2RobinBase period
          hPeriod × Real)
  physicalGhost :
    WithLp 2
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedPhysicalGhostL2EulerBase
          period hPeriod × Real)
  llAuxMetric : WithLp 2
    (GlobalFullLLGraphHilbert period hPeriod data analysis × Real)
  llMeasure : WithLp 2
    (GlobalFullLLGraphHilbert period hPeriod data analysis × Real)
  llField : WithLp 2
    (GlobalFullLLGraphHilbert period hPeriod data analysis × Real)
  spinC : WithLp 2
    (WithLp 2
        (ProgramPPrimitiveSpinCMatterHilbert ×
          ProgramPPrimitiveSpinCMatterHilbert) × Real)
  diffeomorphismGhost :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
  diffeomorphismAntighost :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
  diffeomorphismNakanishiLautrup :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
  potential : WithLp 2
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) × Real)
  abelianGhost : GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
  abelianAntighost : GlobalPairedGaugeLieL2 period hPeriod
  abelianNakanishiLautrup : GlobalPairedGaugeLieL2 period hPeriod

instance fixedResidualTargetZero : Zero
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualTarget4D period
      hPeriod configuration data analysis) where
  zero :=
    { metric := 0
      normal := 0
      physicalGhost := 0
      llAuxMetric := 0
      llMeasure := 0
      llField := 0
      spinC := 0
      diffeomorphismGhost := 0
      diffeomorphismAntighost := 0
      diffeomorphismNakanishiLautrup := 0
      potential := 0
      abelianGhost := 0
      abelianAntighost := 0
      abelianNakanishiLautrup := 0 }

theorem globalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualTarget_eq_zero_iff
    (target :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualTarget4D period
        hPeriod configuration data analysis) :
    target = 0 ↔
      target.metric = 0 ∧
      target.normal = 0 ∧
      target.physicalGhost = 0 ∧
      target.llAuxMetric = 0 ∧
      target.llMeasure = 0 ∧
      target.llField = 0 ∧
      target.spinC = 0 ∧
      (target.diffeomorphismGhost = 0 ∧
       target.diffeomorphismAntighost = 0 ∧
       target.diffeomorphismNakanishiLautrup = 0) ∧
      target.potential = 0 ∧
      (target.abelianGhost = 0 ∧
       target.abelianAntighost = 0 ∧
       target.abelianNakanishiLautrup = 0) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨rfl, rfl, rfl⟩, rfl, ⟨rfl, rfl, rfl⟩⟩
  · rintro ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure,
      hLLField, hSpinC, ⟨hDiffGhost, hDiffAnti, hDiffB⟩, hPotential,
      ⟨hAbelianGhost, hAbelianAnti, hAbelianB⟩⟩
    apply GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualTarget4D.ext <;>
      assumption

/-- A genuine nonlinear operator from the full-BRST chart to one fixed ambient
residual target. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualTarget4D period
      hPeriod configuration data analysis where
  metric :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  normal :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  physicalGhost :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  llAuxMetric :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  llMeasure :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  llField :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  spinC :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  diffeomorphismGhost :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  diffeomorphismAntighost :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  diffeomorphismNakanishiLautrup :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  potential :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual period
      hPeriod configuration data analysis chartData state).1
  abelianGhost :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual
      period hPeriod configuration data analysis chartData state).1
  abelianAntighost :=
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual period
      hPeriod configuration data analysis chartData state
  abelianNakanishiLautrup :=
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
      period hPeriod configuration data analysis chartData state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator_eq_zero_iff_residualSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
          period hPeriod configuration data analysis chartData state = 0 ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalPhysicalGhostL2SpinCFourierFaithfulAugmentedGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualTarget_eq_zero_iff]
  simp [globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator,
    GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalPhysicalGhostL2SpinCFourierFaithfulAugmentedGraphResidualEulerSystemAt,
    GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystemAt,
    GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt]
  tauto

/-- Gate 268: full-BRST criticality is the zero locus of one nonlinear
fourteen-component residual operator with a fixed ambient codomain. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_ambient_euler_residual_operator_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
          configuration data analysis chartData state ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
        period hPeriod configuration data analysis chartData state = 0 := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator_eq_zero_iff_residualSystem]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalPhysicalGhostL2SpinCFourierFaithfulAugmentedGraphResidualEulerSystem
      period hPeriod configuration data analysis chartData state

end FixedOperator
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D
end JanusFormal
