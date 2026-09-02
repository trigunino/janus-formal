import Mathlib.Analysis.Normed.Lp.ProdLp
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoveredAtlasCoherentFiberTransport4D

/-!
# Normed product model of the fixed full-BRST residual target

The fourteen state-independent residual coordinates are encoded in a balanced
real normed product without changing their zero locus.  The final Abelian
antighost/Nakanishi--Lautrup pair is then an explicit bounded projection.  No
regularity of the other twelve residual coordinates is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedResidualTargetNormedSpace4D

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
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianL2ResidualRegularity4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedSpace
  P0EFTJanusProgramPGlobalFullLLGraphRiesz4D.globalFullLLC2GraphNormedSpace
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
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

section TargetNorm

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)

private abbrev FixedResidualTarget :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualTarget4D period
    hPeriod configuration data analysis

private abbrev MetricResidual :=
  WithLp 2
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) × Real)

private abbrev NormalResidual :=
  WithLp 2
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormalL2RobinBase period
        hPeriod × Real)

private abbrev PhysicalGhostResidual :=
  WithLp 2
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedPhysicalGhostL2EulerBase
        period hPeriod × Real)

private abbrev LLResidual :=
  WithLp 2 (GlobalFullLLGraphHilbert period hPeriod data analysis × Real)

private abbrev SpinCResidual :=
  WithLp 2
    (WithLp 2
        (ProgramPPrimitiveSpinCMatterHilbert ×
          ProgramPPrimitiveSpinCMatterHilbert) × Real)

private abbrev DiffeomorphismResidual :=
  GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev PotentialResidual :=
  WithLp 2
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) × Real)

private abbrev AbelianGhostResidual :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev AbelianL2Residual := GlobalPairedGaugeLieL2 period hPeriod

@[implicit_reducible]
local instance (priority := 12000) targetDiagonalGraphNormedSpace :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) :=
  diagonalGraphNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

@[implicit_reducible]
local instance (priority := 12000) targetFullLLGraphNormedSpace :
    NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  globalFullLLC2GraphNormedSpace period hPeriod data analysis

@[implicit_reducible]
local instance (priority := 12000) targetPairedAbelianGraphNormedSpace :
    NormedSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) :=
  globalPairedAbelianOffShellGraphNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

@[implicit_reducible]
local instance (priority := 13000) targetMetricResidualNormedSpace :
    NormedSpace Real (MetricResidual period hPeriod configuration data) :=
  WithLp.instProdNormedSpace 2 Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)) Real

@[implicit_reducible]
local instance (priority := 13000) targetLLResidualNormedSpace :
    NormedSpace Real
      (LLResidual period hPeriod configuration data analysis) :=
  WithLp.instProdNormedSpace 2 Real
    (GlobalFullLLGraphHilbert period hPeriod data analysis) Real

@[implicit_reducible]
local instance (priority := 13000) targetPotentialResidualNormedSpace :
    NormedSpace Real (PotentialResidual period hPeriod configuration data) :=
  WithLp.instProdNormedSpace 2 Real
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)) Real

private abbrev FixedResidualLeftCoordinates :=
  ((MetricResidual period hPeriod configuration data ×
      NormalResidual period hPeriod) ×
      (PhysicalGhostResidual period hPeriod ×
        LLResidual period hPeriod configuration data analysis)) ×
    ((LLResidual period hPeriod configuration data analysis ×
        LLResidual period hPeriod configuration data analysis) ×
      (SpinCResidual ×
        DiffeomorphismResidual period hPeriod configuration data))

private abbrev FixedResidualRightHeadCoordinates :=
  (DiffeomorphismResidual period hPeriod configuration data ×
      DiffeomorphismResidual period hPeriod configuration data) ×
    (PotentialResidual period hPeriod configuration data ×
      AbelianGhostResidual period hPeriod configuration data)

private abbrev FixedResidualAbelianL2Coordinates :=
  AbelianL2Residual period hPeriod × AbelianL2Residual period hPeriod

private abbrev FixedResidualRightCoordinates :=
  FixedResidualRightHeadCoordinates period hPeriod configuration data ×
    FixedResidualAbelianL2Coordinates period hPeriod

private abbrev FixedResidualCoordinates :=
  FixedResidualLeftCoordinates period hPeriod configuration data analysis ×
    FixedResidualRightCoordinates period hPeriod configuration data

private abbrev CheckFixedResidualLeftNormedSpace :
    NormedSpace Real
      (FixedResidualLeftCoordinates period hPeriod configuration data analysis) :=
  inferInstance

private abbrev CheckFixedResidualRightNormedSpace :
    NormedSpace Real
      (FixedResidualRightCoordinates period hPeriod configuration data) :=
  inferInstance

/-- Concrete normed product model of the fourteen fixed residual
coordinates. -/
abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D :=
  FixedResidualCoordinates period hPeriod configuration data analysis

private abbrev FixedResidualModelNormedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D
        period hPeriod configuration data analysis) :=
  @Prod.normedSpace Real
    (FixedResidualLeftCoordinates period hPeriod configuration data analysis)
    (FixedResidualRightCoordinates period hPeriod configuration data)
    inferInstance inferInstance inferInstance
    (CheckFixedResidualLeftNormedSpace period hPeriod configuration data analysis)
    (CheckFixedResidualRightNormedSpace period hPeriod configuration data)

/-- The balanced product model is a real normed space. -/
instance fixedResidualNormedModelNormedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D
        period hPeriod configuration data analysis) :=
  FixedResidualModelNormedSpace period hPeriod configuration data analysis

/-- Explicit zero-numeral bridge for the deeply nested product model. -/
instance fixedResidualNormedModelOfNatZero : OfNat
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D
      period hPeriod configuration data analysis) 0 :=
  Zero.toOfNat0

/-- Componentwise equivalence with a balanced product of the fourteen fixed
residual coordinates. -/
def fixedResidualTargetEquivCoordinates :
    FixedResidualTarget period hPeriod configuration data analysis ≃
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D
        period hPeriod configuration data analysis where
  toFun target :=
    ((((target.metric, target.normal),
        (target.physicalGhost, target.llAuxMetric)),
      ((target.llMeasure, target.llField),
        (target.spinC, target.diffeomorphismGhost))),
    (((target.diffeomorphismAntighost,
        target.diffeomorphismNakanishiLautrup),
      (target.potential, target.abelianGhost)),
      (target.abelianAntighost, target.abelianNakanishiLautrup)))
  invFun coordinates :=
    { metric := coordinates.1.1.1.1
      normal := coordinates.1.1.1.2
      physicalGhost := coordinates.1.1.2.1
      llAuxMetric := coordinates.1.1.2.2
      llMeasure := coordinates.1.2.1.1
      llField := coordinates.1.2.1.2
      spinC := coordinates.1.2.2.1
      diffeomorphismGhost := coordinates.1.2.2.2
      diffeomorphismAntighost := coordinates.2.1.1.1
      diffeomorphismNakanishiLautrup := coordinates.2.1.1.2
      potential := coordinates.2.1.2.1
      abelianGhost := coordinates.2.1.2.2
      abelianAntighost := coordinates.2.2.1
      abelianNakanishiLautrup := coordinates.2.2.2 }
  left_inv target := by cases target; rfl
  right_inv coordinates := by
    rcases coordinates with
      ⟨⟨⟨⟨metric, normal⟩, ⟨physicalGhost, llAuxMetric⟩⟩,
          ⟨⟨llMeasure, llField⟩, ⟨spinC, diffeomorphismGhost⟩⟩⟩,
        ⟨⟨⟨diffeomorphismAntighost, diffeomorphismNakanishiLautrup⟩,
            ⟨potential, abelianGhost⟩⟩,
          ⟨abelianAntighost, abelianNakanishiLautrup⟩⟩⟩
    rfl

/-- Bounded projection from the normed coordinate model onto the authentic
Abelian antighost and Nakanishi--Lautrup `L²` residuals. -/
def fixedResidualCoordinatesAbelianL2ProjectionCLM :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D
        period hPeriod configuration data analysis →L[Real]
      FixedResidualAbelianL2Coordinates period hPeriod :=
  (ContinuousLinearMap.snd Real
      (FixedResidualRightHeadCoordinates period hPeriod configuration data)
      (FixedResidualAbelianL2Coordinates period hPeriod)).comp
    (ContinuousLinearMap.snd Real
      (FixedResidualLeftCoordinates period hPeriod configuration data analysis)
      (FixedResidualRightCoordinates period hPeriod configuration data))

@[simp]
theorem fixedResidualCoordinatesAbelianL2ProjectionCLM_encode_apply
    (target : FixedResidualTarget period hPeriod configuration data analysis) :
    fixedResidualCoordinatesAbelianL2ProjectionCLM period hPeriod configuration
        data analysis
        (fixedResidualTargetEquivCoordinates period hPeriod configuration data
          analysis target) =
      (target.abelianAntighost, target.abelianNakanishiLautrup) :=
  rfl

@[simp]
theorem fixedResidualTargetEquivCoordinates_zero :
    fixedResidualTargetEquivCoordinates period hPeriod configuration data
        analysis (0 : FixedResidualTarget period hPeriod configuration data
          analysis) = 0 :=
  rfl

theorem fixedResidualTargetEquivCoordinates_eq_zero_iff
    (target : FixedResidualTarget period hPeriod configuration data analysis) :
    fixedResidualTargetEquivCoordinates period hPeriod configuration data
        analysis target = 0 ↔ target = 0 := by
  rw [← fixedResidualTargetEquivCoordinates_zero period hPeriod configuration
    data analysis]
  exact
    (fixedResidualTargetEquivCoordinates period hPeriod configuration data
      analysis).injective.eq_iff

variable
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    (measure := measure) configuration data analysis chartData

private abbrev TargetNormChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedAddCommGroup
    period hPeriod (measure := measure) configuration data analysis chartData

private abbrev TargetNormChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedSpace
    period hPeriod (measure := measure) configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 11000) targetNormChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  TargetNormChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 11000) targetNormChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  TargetNormChartNormedSpace period hPeriod configuration data analysis
    chartData

/-- The fixed residual operator encoded in the concrete normed model. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D period
      hPeriod configuration data analysis :=
  fixedResidualTargetEquivCoordinates period hPeriod configuration data analysis
    (globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
      period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator_eq_zero_iff
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
          period hPeriod configuration data analysis chartData state = 0 :=
  fixedResidualTargetEquivCoordinates_eq_zero_iff period hPeriod configuration
    data analysis _

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_fixedNormedEulerResidualOperator_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
          configuration data analysis chartData state ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
          period hPeriod configuration data analysis chartData state = 0 := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator_eq_zero_iff]
  exact
    global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_ambient_euler_residual_operator_gate
      period hPeriod configuration data analysis chartData state

theorem fixedResidualCoordinatesAbelianL2Projection_comp_operator_apply
    (state : FullChart period hPeriod configuration data analysis chartData) :
    fixedResidualCoordinatesAbelianL2ProjectionCLM period hPeriod configuration
        data analysis
        (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
          period hPeriod configuration data analysis chartData state) =
      globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientAbelianL2Coordinates
        period hPeriod configuration data analysis chartData state :=
  rfl

/-- The bounded Abelian pair projection of the normed residual model is
globally smooth. -/
theorem fixedResidualCoordinatesAbelianL2Projection_comp_operator_contDiff :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (TargetNormChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (TargetNormChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (FixedResidualAbelianL2Coordinates period hPeriod) inferInstance
      inferInstance ∞
      (fun state =>
        fixedResidualCoordinatesAbelianL2ProjectionCLM period hPeriod
          configuration data analysis
          (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
            period hPeriod configuration data analysis chartData state)) := by
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (TargetNormChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (TargetNormChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (GlobalPairedGaugeLieL2 period hPeriod ×
      GlobalPairedGaugeLieL2 period hPeriod) inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientAbelianL2Coordinates
      period hPeriod configuration data analysis chartData)
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientAbelianL2Coordinates_contDiff
      period hPeriod configuration data analysis chartData

/-- Gate 275: the fixed fourteen-component residual has a concrete normed
product model with the same critical zero locus, and its authentic Abelian
`L²` pair is a bounded projection whose composition with the nonlinear
residual operator is `C∞`. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_residual_target_normed_space_gate :
    (∀ target : FixedResidualTarget period hPeriod configuration data analysis,
      fixedResidualCoordinatesAbelianL2ProjectionCLM period hPeriod
          configuration data analysis
          (fixedResidualTargetEquivCoordinates period hPeriod configuration data
            analysis target) =
        (target.abelianAntighost, target.abelianNakanishiLautrup)) ∧
      (∀ state : FullChart period hPeriod configuration data analysis chartData,
        GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
              configuration data analysis chartData state ↔
          globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
              period hPeriod configuration data analysis chartData state = 0) ∧
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (TargetNormChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (TargetNormChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (FixedResidualAbelianL2Coordinates period hPeriod) inferInstance
        inferInstance ∞
        (fun state =>
          fixedResidualCoordinatesAbelianL2ProjectionCLM period hPeriod
            configuration data analysis
            (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
              period hPeriod configuration data analysis chartData state)) :=
  ⟨fixedResidualCoordinatesAbelianL2ProjectionCLM_encode_apply period hPeriod
      configuration data analysis,
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_fixedNormedEulerResidualOperator_eq_zero
      period hPeriod configuration data analysis chartData,
    fixedResidualCoordinatesAbelianL2Projection_comp_operator_contDiff period
      hPeriod configuration data analysis chartData⟩

end TargetNorm
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedResidualTargetNormedSpace4D
end JanusFormal
