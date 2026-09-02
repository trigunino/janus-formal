import Mathlib.Analysis.Normed.Lp.ProdLp
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedResidualTargetNormedSpace4D

/-!
# Coordinatewise regularity reduction for the normed full-BRST residual

Smoothness of the fixed normed fourteen-coordinate residual is reduced exactly
to smoothness of its fourteen coordinate maps.  The two authentic Abelian
`L²` coordinates are discharged from Gate 273; the remaining twelve are left
as explicit analytic obligations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianL2ResidualRegularity4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedResidualTargetNormedSpace4D

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

section RegularityReduction

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

@[implicit_reducible]
local instance (priority := 12000) reductionDiagonalGraphNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) :=
  diagonalGraphNormedAddCommGroupValue period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev ReductionPairedAbelianGraphNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) :=
  inferInstance

@[implicit_reducible]
local instance (priority := 12000) reductionPairedAbelianGraphNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) :=
  ReductionPairedAbelianGraphNormedAddCommGroup period hPeriod configuration
    data

@[implicit_reducible]
local instance (priority := 12000) reductionDiagonalGraphNormedSpace :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) :=
  diagonalGraphNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

@[implicit_reducible]
local instance (priority := 12000) reductionFullLLGraphNormedSpace :
    NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  globalFullLLC2GraphNormedSpace period hPeriod data analysis

@[implicit_reducible]
local instance (priority := 12000) reductionPairedAbelianGraphNormedSpace :
    NormedSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) :=
  globalPairedAbelianOffShellGraphNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

@[implicit_reducible]
local instance (priority := 13000) reductionMetricResidualNormedAddCommGroup :
    NormedAddCommGroup
      (WithLp 2
        (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period
            hPeriod (globalCandidateAMetricBySector period hPeriod data) ×
          Real)) :=
  WithLp.instProdNormedAddCommGroup 2
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)) Real

@[implicit_reducible]
local instance (priority := 13000) reductionMetricResidualNormedSpace :
    NormedSpace Real
      (WithLp 2
        (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period
            hPeriod (globalCandidateAMetricBySector period hPeriod data) ×
          Real)) :=
  WithLp.instProdNormedSpace 2 Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)) Real

@[implicit_reducible]
local instance (priority := 13000) reductionLLResidualNormedAddCommGroup :
    NormedAddCommGroup
      (WithLp 2
        (GlobalFullLLGraphHilbert period hPeriod data analysis × Real)) :=
  WithLp.instProdNormedAddCommGroup 2
    (GlobalFullLLGraphHilbert period hPeriod data analysis) Real

@[implicit_reducible]
local instance (priority := 13000) reductionLLResidualNormedSpace :
    NormedSpace Real
      (WithLp 2
        (GlobalFullLLGraphHilbert period hPeriod data analysis × Real)) :=
  WithLp.instProdNormedSpace 2 Real
    (GlobalFullLLGraphHilbert period hPeriod data analysis) Real

@[implicit_reducible]
local instance (priority := 13000) reductionPotentialResidualNormedAddCommGroup :
    NormedAddCommGroup
      (WithLp 2
        (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
            (globalCandidateAMetricBySector period hPeriod data) × Real)) :=
  WithLp.instProdNormedAddCommGroup 2
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)) Real

@[implicit_reducible]
local instance (priority := 13000) reductionPotentialResidualNormedSpace :
    NormedSpace Real
      (WithLp 2
        (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
            (globalCandidateAMetricBySector period hPeriod data) × Real)) :=
  WithLp.instProdNormedSpace 2 Real
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)) Real

private abbrev ReductionChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedAddCommGroup
    period hPeriod (measure := measure) configuration data analysis chartData

private abbrev ReductionChartSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  inferInstance

@[implicit_reducible]
local instance (priority := 12000) reductionChartSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  ReductionChartSeminormedAddCommGroup period hPeriod configuration data analysis
    chartData

private abbrev ReductionChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedSpace
    period hPeriod (measure := measure) configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 11000) reductionChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  ReductionChartNormedSpace period hPeriod configuration data analysis chartData

abbrev CoordinateContDiff
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace Real Target]
    (map : FullChart period hPeriod configuration data analysis chartData →
      Target) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    Target inferInstance inferInstance ∞ map

abbrev MetricCoordinateContDiff
    (map : FullChart period hPeriod configuration data analysis chartData →
      WithLp 2
        (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period
            hPeriod (globalCandidateAMetricBySector period hPeriod data) ×
          Real)) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (WithLp 2
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) × Real))
    (reductionMetricResidualNormedAddCommGroup period hPeriod configuration data)
    (reductionMetricResidualNormedSpace period hPeriod configuration data) ∞ map

abbrev LLCoordinateContDiff
    (map : FullChart period hPeriod configuration data analysis chartData →
      WithLp 2
        (GlobalFullLLGraphHilbert period hPeriod data analysis × Real)) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (WithLp 2
      (GlobalFullLLGraphHilbert period hPeriod data analysis × Real))
    (reductionLLResidualNormedAddCommGroup period hPeriod configuration data
      analysis)
    (reductionLLResidualNormedSpace period hPeriod configuration data analysis)
    ∞ map

abbrev PotentialCoordinateContDiff
    (map : FullChart period hPeriod configuration data analysis chartData →
      WithLp 2
        (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
            (globalCandidateAMetricBySector period hPeriod data) × Real)) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (WithLp 2
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) × Real))
    (reductionPotentialResidualNormedAddCommGroup period hPeriod configuration
      data)
    (reductionPotentialResidualNormedSpace period hPeriod configuration data) ∞
    map

private abbrev DiffeomorphismCoordinateContDiff
    (map : FullChart period hPeriod configuration data analysis chartData →
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data))
    (reductionDiagonalGraphNormedAddCommGroup period hPeriod configuration data)
    (reductionDiagonalGraphNormedSpace period hPeriod configuration data) ∞ map

private abbrev AbelianGhostCoordinateContDiff
    (map : FullChart period hPeriod configuration data analysis chartData →
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data))
    (reductionPairedAbelianGraphNormedAddCommGroup period hPeriod configuration
      data)
    (reductionPairedAbelianGraphNormedSpace period hPeriod configuration data) ∞
    map

private abbrev ReductionMetricResidual :=
  WithLp 2
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) × Real)

private abbrev ReductionNormalResidual :=
  WithLp 2
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormalL2RobinBase period
      hPeriod × Real)

private abbrev ReductionPhysicalGhostResidual :=
  WithLp 2
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedPhysicalGhostL2EulerBase
      period hPeriod × Real)

private abbrev ReductionLLResidual :=
  WithLp 2 (GlobalFullLLGraphHilbert period hPeriod data analysis × Real)

private abbrev ReductionSpinCResidual :=
  WithLp 2
    (WithLp 2
        (ProgramPPrimitiveSpinCMatterHilbert ×
          ProgramPPrimitiveSpinCMatterHilbert) × Real)

private abbrev ReductionDiffeomorphismResidual :=
  GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev ReductionPotentialResidual :=
  WithLp 2
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) × Real)

private abbrev ReductionAbelianGhostResidual :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev ReductionAbelianL2Residual :=
  GlobalPairedGaugeLieL2 period hPeriod

private abbrev ReductionResidual01 :=
  ReductionMetricResidual period hPeriod configuration data ×
    ReductionNormalResidual period hPeriod

private abbrev ReductionResidual23 :=
  ReductionPhysicalGhostResidual period hPeriod ×
    ReductionLLResidual period hPeriod configuration data analysis

private abbrev ReductionResidual45 :=
  ReductionLLResidual period hPeriod configuration data analysis ×
    ReductionLLResidual period hPeriod configuration data analysis

private abbrev ReductionResidual67 :=
  ReductionSpinCResidual ×
    ReductionDiffeomorphismResidual period hPeriod configuration data

private abbrev ReductionResidual03 :=
  ReductionResidual01 period hPeriod configuration data ×
    ReductionResidual23 period hPeriod configuration data analysis

private abbrev ReductionResidual47 :=
  ReductionResidual45 period hPeriod configuration data analysis ×
    ReductionResidual67 period hPeriod configuration data

private abbrev ReductionResidual89 :=
  ReductionDiffeomorphismResidual period hPeriod configuration data ×
    ReductionDiffeomorphismResidual period hPeriod configuration data

private abbrev ReductionResidual1011 :=
  ReductionPotentialResidual period hPeriod configuration data ×
    ReductionAbelianGhostResidual period hPeriod configuration data

private abbrev ReductionResidual811 :=
  ReductionResidual89 period hPeriod configuration data ×
    ReductionResidual1011 period hPeriod configuration data

private abbrev ReductionResidual1213 :=
  ReductionAbelianL2Residual period hPeriod ×
    ReductionAbelianL2Residual period hPeriod

private abbrev ReductionFixedResidualLeftCoordinates :=
  ReductionResidual03 period hPeriod configuration data analysis ×
    ReductionResidual47 period hPeriod configuration data analysis

private abbrev ReductionFixedResidualRightCoordinates :=
  ReductionResidual811 period hPeriod configuration data ×
    ReductionResidual1213 period hPeriod

private abbrev ReductionNormalResidualNormedAddCommGroup :
    NormedAddCommGroup (ReductionNormalResidual period hPeriod) :=
  inferInstance

private abbrev ReductionNormalResidualNormedSpace :
    NormedSpace Real (ReductionNormalResidual period hPeriod) :=
  inferInstance

private abbrev ReductionPhysicalGhostResidualNormedAddCommGroup :
    NormedAddCommGroup (ReductionPhysicalGhostResidual period hPeriod) :=
  inferInstance

private abbrev ReductionPhysicalGhostResidualNormedSpace :
    NormedSpace Real (ReductionPhysicalGhostResidual period hPeriod) :=
  inferInstance

private abbrev ReductionSpinCResidualNormedAddCommGroup :
    NormedAddCommGroup ReductionSpinCResidual :=
  inferInstance

private abbrev ReductionSpinCResidualNormedSpace :
    NormedSpace Real ReductionSpinCResidual :=
  inferInstance

private abbrev ReductionAbelianL2ResidualNormedAddCommGroup :
    NormedAddCommGroup (ReductionAbelianL2Residual period hPeriod) :=
  inferInstance

private abbrev ReductionAbelianL2ResidualNormedSpace :
    NormedSpace Real (ReductionAbelianL2Residual period hPeriod) :=
  inferInstance

private abbrev ReductionResidual01NormedAddCommGroup :
    NormedAddCommGroup
      (ReductionResidual01 period hPeriod configuration data) :=
  inferInstance

private abbrev ReductionResidual01NormedSpace :
    NormedSpace Real (ReductionResidual01 period hPeriod configuration data) :=
  @Prod.normedSpace Real
    (ReductionMetricResidual period hPeriod configuration data)
    (ReductionNormalResidual period hPeriod)
    inferInstance inferInstance inferInstance
    (reductionMetricResidualNormedSpace period hPeriod configuration data)
    (ReductionNormalResidualNormedSpace period hPeriod)

private abbrev ReductionResidual23NormedAddCommGroup :
    NormedAddCommGroup
      (ReductionResidual23 period hPeriod configuration data analysis) :=
  inferInstance

private abbrev ReductionResidual23NormedSpace :
    NormedSpace Real
      (ReductionResidual23 period hPeriod configuration data analysis) :=
  @Prod.normedSpace Real
    (ReductionPhysicalGhostResidual period hPeriod)
    (ReductionLLResidual period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance
    (ReductionPhysicalGhostResidualNormedSpace period hPeriod)
    (reductionLLResidualNormedSpace period hPeriod configuration data analysis)

private abbrev ReductionResidual45NormedAddCommGroup :
    NormedAddCommGroup
      (ReductionResidual45 period hPeriod configuration data analysis) :=
  inferInstance

private abbrev ReductionResidual45NormedSpace :
    NormedSpace Real
      (ReductionResidual45 period hPeriod configuration data analysis) :=
  @Prod.normedSpace Real
    (ReductionLLResidual period hPeriod configuration data analysis)
    (ReductionLLResidual period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance
    (reductionLLResidualNormedSpace period hPeriod configuration data analysis)
    (reductionLLResidualNormedSpace period hPeriod configuration data analysis)

private abbrev ReductionResidual67NormedAddCommGroup :
    NormedAddCommGroup
      (ReductionResidual67 period hPeriod configuration data) :=
  inferInstance

private abbrev ReductionResidual67NormedSpace :
    NormedSpace Real
      (ReductionResidual67 period hPeriod configuration data) :=
  @Prod.normedSpace Real ReductionSpinCResidual
    (ReductionDiffeomorphismResidual period hPeriod configuration data)
    inferInstance inferInstance inferInstance
    ReductionSpinCResidualNormedSpace
    (reductionDiagonalGraphNormedSpace period hPeriod configuration data)

private abbrev ReductionResidual03NormedAddCommGroup :
    NormedAddCommGroup
      (ReductionResidual03 period hPeriod configuration data analysis) :=
  inferInstance

private abbrev ReductionResidual03NormedSpace :
    NormedSpace Real
      (ReductionResidual03 period hPeriod configuration data analysis) :=
  @Prod.normedSpace Real
    (ReductionResidual01 period hPeriod configuration data)
    (ReductionResidual23 period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance
    (ReductionResidual01NormedSpace period hPeriod configuration data)
    (ReductionResidual23NormedSpace period hPeriod configuration data analysis)

private abbrev ReductionResidual47NormedAddCommGroup :
    NormedAddCommGroup
      (ReductionResidual47 period hPeriod configuration data analysis) :=
  inferInstance

private abbrev ReductionResidual47NormedSpace :
    NormedSpace Real
      (ReductionResidual47 period hPeriod configuration data analysis) :=
  @Prod.normedSpace Real
    (ReductionResidual45 period hPeriod configuration data analysis)
    (ReductionResidual67 period hPeriod configuration data)
    inferInstance inferInstance inferInstance
    (ReductionResidual45NormedSpace period hPeriod configuration data analysis)
    (ReductionResidual67NormedSpace period hPeriod configuration data)

private abbrev ReductionResidual89NormedAddCommGroup :
    NormedAddCommGroup
      (ReductionResidual89 period hPeriod configuration data) :=
  inferInstance

private abbrev ReductionResidual89NormedSpace :
    NormedSpace Real (ReductionResidual89 period hPeriod configuration data) :=
  @Prod.normedSpace Real
    (ReductionDiffeomorphismResidual period hPeriod configuration data)
    (ReductionDiffeomorphismResidual period hPeriod configuration data)
    inferInstance inferInstance inferInstance
    (reductionDiagonalGraphNormedSpace period hPeriod configuration data)
    (reductionDiagonalGraphNormedSpace period hPeriod configuration data)

private abbrev ReductionResidual1011NormedAddCommGroup :
    NormedAddCommGroup
      (ReductionResidual1011 period hPeriod configuration data) :=
  inferInstance

private abbrev ReductionResidual1011NormedSpace :
    NormedSpace Real
      (ReductionResidual1011 period hPeriod configuration data) :=
  @Prod.normedSpace Real
    (ReductionPotentialResidual period hPeriod configuration data)
    (ReductionAbelianGhostResidual period hPeriod configuration data)
    inferInstance inferInstance inferInstance
    (reductionPotentialResidualNormedSpace period hPeriod configuration data)
    (reductionPairedAbelianGraphNormedSpace period hPeriod configuration data)

private abbrev ReductionResidual811NormedAddCommGroup :
    NormedAddCommGroup
      (ReductionResidual811 period hPeriod configuration data) :=
  inferInstance

private abbrev ReductionResidual811NormedSpace :
    NormedSpace Real
      (ReductionResidual811 period hPeriod configuration data) :=
  @Prod.normedSpace Real
    (ReductionResidual89 period hPeriod configuration data)
    (ReductionResidual1011 period hPeriod configuration data)
    inferInstance inferInstance inferInstance
    (ReductionResidual89NormedSpace period hPeriod configuration data)
    (ReductionResidual1011NormedSpace period hPeriod configuration data)

private abbrev ReductionResidual1213NormedAddCommGroup :
    NormedAddCommGroup (ReductionResidual1213 period hPeriod) :=
  inferInstance

private abbrev ReductionResidual1213NormedSpace :
    NormedSpace Real (ReductionResidual1213 period hPeriod) :=
  @Prod.normedSpace Real
    (ReductionAbelianL2Residual period hPeriod)
    (ReductionAbelianL2Residual period hPeriod)
    inferInstance inferInstance inferInstance
    (ReductionAbelianL2ResidualNormedSpace period hPeriod)
    (ReductionAbelianL2ResidualNormedSpace period hPeriod)

private abbrev ReductionFixedResidualLeftNormedSpace :
    NormedSpace Real
      (ReductionFixedResidualLeftCoordinates period hPeriod configuration data
        analysis) :=
  @Prod.normedSpace Real
    (ReductionResidual03 period hPeriod configuration data analysis)
    (ReductionResidual47 period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance
    (ReductionResidual03NormedSpace period hPeriod configuration data analysis)
    (ReductionResidual47NormedSpace period hPeriod configuration data analysis)

private abbrev ReductionFixedResidualRightNormedSpace :
    NormedSpace Real
      (ReductionFixedResidualRightCoordinates period hPeriod configuration data) :=
  @Prod.normedSpace Real
    (ReductionResidual811 period hPeriod configuration data)
    (ReductionResidual1213 period hPeriod)
    inferInstance inferInstance inferInstance
    (ReductionResidual811NormedSpace period hPeriod configuration data)
    (ReductionResidual1213NormedSpace period hPeriod)

private abbrev ReductionFixedResidualLeftNormedAddCommGroup :
    NormedAddCommGroup
      (ReductionFixedResidualLeftCoordinates period hPeriod configuration data
        analysis) :=
  inferInstance

private abbrev ReductionFixedResidualRightNormedAddCommGroup :
    NormedAddCommGroup
      (ReductionFixedResidualRightCoordinates period hPeriod configuration data) :=
  inferInstance

private abbrev ReductionFixedResidualNormedModelNormedAddCommGroup :
    NormedAddCommGroup
      (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D
        period hPeriod configuration data analysis) :=
  inferInstance

abbrev FullResidualCoordinateContDiff
    (map : FullChart period hPeriod configuration data analysis chartData →
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D
        period hPeriod configuration data analysis) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D
      period hPeriod configuration data analysis)
    (ReductionFixedResidualNormedModelNormedAddCommGroup period hPeriod
      configuration data analysis)
    (fixedResidualNormedModelNormedSpace period hPeriod configuration data
      analysis) ∞ map

private theorem coordinateContDiff_fst
    {First Second : Type*}
    [firstGroup : NormedAddCommGroup First] [firstSpace : NormedSpace Real First]
    [secondGroup : NormedAddCommGroup Second] [secondSpace : NormedSpace Real Second]
    {map : FullChart period hPeriod configuration data analysis chartData →
      First × Second}
    (h : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (First × Second) inferInstance inferInstance ∞ map) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      First inferInstance inferInstance ∞ (fun state => (map state).1) :=
  @ContDiff.fst Real
    (FullChart period hPeriod configuration data analysis chartData) First Second
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞ map h

private theorem coordinateContDiff_snd
    {First Second : Type*}
    [firstGroup : NormedAddCommGroup First] [firstSpace : NormedSpace Real First]
    [secondGroup : NormedAddCommGroup Second] [secondSpace : NormedSpace Real Second]
    {map : FullChart period hPeriod configuration data analysis chartData →
      First × Second}
    (h : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (First × Second) inferInstance inferInstance ∞ map) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      Second inferInstance inferInstance ∞ (fun state => (map state).2) :=
  @ContDiff.snd Real
    (FullChart period hPeriod configuration data analysis chartData) First Second
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞ map h

private theorem coordinateContDiff_prodMk
    {First Second : Type*}
    [firstGroup : NormedAddCommGroup First] [firstSpace : NormedSpace Real First]
    [secondGroup : NormedAddCommGroup Second] [secondSpace : NormedSpace Real Second]
    {firstMap : FullChart period hPeriod configuration data analysis chartData →
      First}
    {secondMap : FullChart period hPeriod configuration data analysis chartData →
      Second}
    (hFirst : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      First inferInstance inferInstance ∞ firstMap)
    (hSecond : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      Second inferInstance inferInstance ∞ secondMap) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (First × Second) inferInstance inferInstance ∞
      (fun state => (firstMap state, secondMap state)) :=
  @ContDiff.prodMk Real
    (FullChart period hPeriod configuration data analysis chartData) First Second
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞ firstMap secondMap
    hFirst hSecond

private theorem coordinateContDiff_prod_iff
    {First Second : Type*}
    [firstGroup : NormedAddCommGroup First] [firstSpace : NormedSpace Real First]
    [secondGroup : NormedAddCommGroup Second] [secondSpace : NormedSpace Real Second]
    {map : FullChart period hPeriod configuration data analysis chartData →
      First × Second} :
    @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (ReductionChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (ReductionChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (First × Second) inferInstance inferInstance ∞ map ↔
      (@ContDiff Real
          P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
          (FullChart period hPeriod configuration data analysis chartData)
          (ReductionChartNormedAddCommGroup period hPeriod configuration data
            analysis chartData)
          (ReductionChartNormedSpace period hPeriod configuration data analysis
            chartData)
          First firstGroup firstSpace ∞ (fun state => (map state).1) ∧
        @ContDiff Real
          P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
          (FullChart period hPeriod configuration data analysis chartData)
          (ReductionChartNormedAddCommGroup period hPeriod configuration data
            analysis chartData)
          (ReductionChartNormedSpace period hPeriod configuration data analysis
            chartData)
          Second secondGroup secondSpace ∞ (fun state => (map state).2)) := by
  simpa only [Function.comp_def] using
    (@contDiff_prod_iff Real
      (FullChart period hPeriod configuration data analysis chartData)
      First Second
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
        chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      firstGroup firstSpace secondGroup secondSpace ∞ map)

private theorem fullResidualCoordinateContDiff_fst
    {map : FullChart period hPeriod configuration data analysis chartData →
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D
        period hPeriod configuration data analysis}
    (h : FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData map) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (ReductionFixedResidualLeftCoordinates period hPeriod configuration data
        analysis)
      (ReductionFixedResidualLeftNormedAddCommGroup period hPeriod configuration
        data analysis)
      (ReductionFixedResidualLeftNormedSpace period hPeriod configuration data
        analysis) ∞ (fun state => (map state).1) :=
  @ContDiff.fst Real
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionFixedResidualLeftCoordinates period hPeriod configuration data
      analysis)
    (ReductionFixedResidualRightCoordinates period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (ReductionFixedResidualLeftNormedAddCommGroup period hPeriod configuration
      data analysis)
    (ReductionFixedResidualLeftNormedSpace period hPeriod configuration data
      analysis)
    (ReductionFixedResidualRightNormedAddCommGroup period hPeriod configuration
      data)
    (ReductionFixedResidualRightNormedSpace period hPeriod configuration data) ∞
    map h

private theorem fullResidualCoordinateContDiff_snd
    {map : FullChart period hPeriod configuration data analysis chartData →
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedResidualNormedModel4D
        period hPeriod configuration data analysis}
    (h : FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData map) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (ReductionFixedResidualRightCoordinates period hPeriod configuration data)
      (ReductionFixedResidualRightNormedAddCommGroup period hPeriod configuration
        data)
      (ReductionFixedResidualRightNormedSpace period hPeriod configuration data) ∞
      (fun state => (map state).2) :=
  @ContDiff.snd Real
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionFixedResidualLeftCoordinates period hPeriod configuration data
      analysis)
    (ReductionFixedResidualRightCoordinates period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (ReductionFixedResidualLeftNormedAddCommGroup period hPeriod configuration
      data analysis)
    (ReductionFixedResidualLeftNormedSpace period hPeriod configuration data
      analysis)
    (ReductionFixedResidualRightNormedAddCommGroup period hPeriod configuration
      data)
    (ReductionFixedResidualRightNormedSpace period hPeriod configuration data) ∞
    map h

private theorem fullResidualCoordinateContDiff_prodMk
    {leftMap : FullChart period hPeriod configuration data analysis chartData →
      ReductionFixedResidualLeftCoordinates period hPeriod configuration data
        analysis}
    {rightMap : FullChart period hPeriod configuration data analysis chartData →
      ReductionFixedResidualRightCoordinates period hPeriod configuration data}
    (hLeft : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (ReductionFixedResidualLeftCoordinates period hPeriod configuration data
        analysis)
      (ReductionFixedResidualLeftNormedAddCommGroup period hPeriod configuration
        data analysis)
      (ReductionFixedResidualLeftNormedSpace period hPeriod configuration data
        analysis) ∞ leftMap)
    (hRight : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (ReductionChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (ReductionChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (ReductionFixedResidualRightCoordinates period hPeriod configuration data)
      (ReductionFixedResidualRightNormedAddCommGroup period hPeriod configuration
        data)
      (ReductionFixedResidualRightNormedSpace period hPeriod configuration data) ∞
      rightMap) :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis
      chartData (fun state => (leftMap state, rightMap state)) :=
  @ContDiff.prodMk Real
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionFixedResidualLeftCoordinates period hPeriod configuration data
      analysis)
    (ReductionFixedResidualRightCoordinates period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (ReductionFixedResidualLeftNormedAddCommGroup period hPeriod configuration
      data analysis)
    (ReductionFixedResidualLeftNormedSpace period hPeriod configuration data
      analysis)
    (ReductionFixedResidualRightNormedAddCommGroup period hPeriod configuration
      data)
    (ReductionFixedResidualRightNormedSpace period hPeriod configuration data) ∞
    leftMap rightMap hLeft hRight

private def fixedAmbientResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
    period hPeriod configuration data analysis chartData state

def fixedNormedResidualMetric
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).metric

def fixedNormedResidualNormal
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).normal

def fixedNormedResidualPhysicalGhost
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).physicalGhost

def fixedNormedResidualLLAuxMetric
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).llAuxMetric

def fixedNormedResidualLLMeasure
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).llMeasure

def fixedNormedResidualLLField
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).llField

def fixedNormedResidualSpinC
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).spinC

def fixedNormedResidualDiffeomorphismGhost
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).diffeomorphismGhost

def fixedNormedResidualDiffeomorphismAntighost
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).diffeomorphismAntighost

def fixedNormedResidualDiffeomorphismNakanishiLautrup
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).diffeomorphismNakanishiLautrup

def fixedNormedResidualPotential
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).potential

def fixedNormedResidualAbelianGhost
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).abelianGhost

def fixedNormedResidualAbelianAntighost
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).abelianAntighost

def fixedNormedResidualAbelianNakanishiLautrup
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  (fixedAmbientResidual period hPeriod configuration data analysis chartData
    state).abelianNakanishiLautrup

/-- The fourteen precise coordinatewise `C∞` obligations for the fixed normed
residual operator. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualCoordinateContDiff4D :
    Prop where
  metric : MetricCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualMetric period hPeriod configuration data analysis
      chartData)
  normal : CoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualNormal period hPeriod configuration data analysis
      chartData)
  physicalGhost : CoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualPhysicalGhost period hPeriod configuration data analysis
      chartData)
  llAuxMetric : LLCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualLLAuxMetric period hPeriod configuration data analysis
      chartData)
  llMeasure : LLCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualLLMeasure period hPeriod configuration data analysis
      chartData)
  llField : LLCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualLLField period hPeriod configuration data analysis
      chartData)
  spinC : CoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualSpinC period hPeriod configuration data analysis
      chartData)
  diffeomorphismGhost : DiffeomorphismCoordinateContDiff period hPeriod configuration data
    analysis chartData
    (fixedNormedResidualDiffeomorphismGhost period hPeriod configuration data
      analysis chartData)
  diffeomorphismAntighost : DiffeomorphismCoordinateContDiff period hPeriod configuration data
    analysis chartData
    (fixedNormedResidualDiffeomorphismAntighost period hPeriod configuration
      data analysis chartData)
  diffeomorphismNakanishiLautrup : DiffeomorphismCoordinateContDiff period hPeriod
    configuration data analysis chartData
    (fixedNormedResidualDiffeomorphismNakanishiLautrup period hPeriod
      configuration data analysis chartData)
  potential : PotentialCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualPotential period hPeriod configuration data analysis
      chartData)
  abelianGhost : AbelianGhostCoordinateContDiff period hPeriod configuration data analysis
    chartData
    (fixedNormedResidualAbelianGhost period hPeriod configuration data analysis
      chartData)
  abelianAntighost : CoordinateContDiff period hPeriod configuration data
    analysis chartData
    (fixedNormedResidualAbelianAntighost period hPeriod configuration data
      analysis chartData)
  abelianNakanishiLautrup : CoordinateContDiff period hPeriod configuration data
    analysis chartData
    (fixedNormedResidualAbelianNakanishiLautrup period hPeriod configuration
      data analysis chartData)

set_option maxHeartbeats 3600000

/-- Smoothness of the complete fixed normed residual is exactly the conjunction
of its fourteen coordinatewise smoothness obligations. -/
theorem fixedNormedEulerResidualOperator_contDiff_iff_coordinates :
    FullResidualCoordinateContDiff period hPeriod configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
          period hPeriod configuration data analysis chartData) ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualCoordinateContDiff4D
        period hPeriod configuration data analysis chartData := by
  change FullResidualCoordinateContDiff period hPeriod configuration data analysis chartData
    (fun state =>
      ((((fixedNormedResidualMetric period hPeriod configuration data analysis
              chartData state,
            fixedNormedResidualNormal period hPeriod configuration data analysis
              chartData state),
          (fixedNormedResidualPhysicalGhost period hPeriod configuration data
              analysis chartData state,
            fixedNormedResidualLLAuxMetric period hPeriod configuration data
              analysis chartData state)),
        ((fixedNormedResidualLLMeasure period hPeriod configuration data analysis
              chartData state,
            fixedNormedResidualLLField period hPeriod configuration data analysis
              chartData state),
          (fixedNormedResidualSpinC period hPeriod configuration data analysis
              chartData state,
            fixedNormedResidualDiffeomorphismGhost period hPeriod configuration
              data analysis chartData state))),
      (((fixedNormedResidualDiffeomorphismAntighost period hPeriod configuration
              data analysis chartData state,
            fixedNormedResidualDiffeomorphismNakanishiLautrup period hPeriod
              configuration data analysis chartData state),
          (fixedNormedResidualPotential period hPeriod configuration data
              analysis chartData state,
            fixedNormedResidualAbelianGhost period hPeriod configuration data
              analysis chartData state)),
        (fixedNormedResidualAbelianAntighost period hPeriod configuration data
            analysis chartData state,
          fixedNormedResidualAbelianNakanishiLautrup period hPeriod configuration
            data analysis chartData state)))) ↔ _
  constructor
  · intro h
    have hLeft := fullResidualCoordinateContDiff_fst period hPeriod configuration data
      analysis chartData h
    have hRight := fullResidualCoordinateContDiff_snd period hPeriod configuration data
      analysis chartData h
    have ⟨h03, h47⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := ReductionResidual03NormedAddCommGroup period hPeriod
          configuration data analysis)
        (firstSpace := ReductionResidual03NormedSpace period hPeriod configuration
          data analysis)
        (secondGroup := ReductionResidual47NormedAddCommGroup period hPeriod
          configuration data analysis)
        (secondSpace := ReductionResidual47NormedSpace period hPeriod configuration
          data analysis)
        period hPeriod configuration data analysis chartData).mp hLeft
    have ⟨h811, h1213⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := ReductionResidual811NormedAddCommGroup period hPeriod
          configuration data)
        (firstSpace := ReductionResidual811NormedSpace period hPeriod configuration
          data)
        (secondGroup := ReductionResidual1213NormedAddCommGroup period hPeriod)
        (secondSpace := ReductionResidual1213NormedSpace period hPeriod)
        period hPeriod configuration data analysis chartData).mp hRight
    have ⟨h01, h23⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := ReductionResidual01NormedAddCommGroup period hPeriod
          configuration data)
        (firstSpace := ReductionResidual01NormedSpace period hPeriod configuration
          data)
        (secondGroup := ReductionResidual23NormedAddCommGroup period hPeriod
          configuration data analysis)
        (secondSpace := ReductionResidual23NormedSpace period hPeriod configuration
          data analysis)
        period hPeriod configuration data analysis chartData).mp h03
    have ⟨h45, h67⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := ReductionResidual45NormedAddCommGroup period hPeriod
          configuration data analysis)
        (firstSpace := ReductionResidual45NormedSpace period hPeriod configuration
          data analysis)
        (secondGroup := ReductionResidual67NormedAddCommGroup period hPeriod
          configuration data)
        (secondSpace := ReductionResidual67NormedSpace period hPeriod configuration
          data)
        period hPeriod configuration data analysis chartData).mp h47
    have ⟨h89, h1011⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := ReductionResidual89NormedAddCommGroup period hPeriod
          configuration data)
        (firstSpace := ReductionResidual89NormedSpace period hPeriod configuration
          data)
        (secondGroup := ReductionResidual1011NormedAddCommGroup period hPeriod
          configuration data)
        (secondSpace := ReductionResidual1011NormedSpace period hPeriod
          configuration data)
        period hPeriod configuration data analysis chartData).mp h811
    have ⟨hMetric, hNormal⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := reductionMetricResidualNormedAddCommGroup period hPeriod
          configuration data)
        (firstSpace := reductionMetricResidualNormedSpace period hPeriod
          configuration data)
        (secondGroup := ReductionNormalResidualNormedAddCommGroup period hPeriod)
        (secondSpace := ReductionNormalResidualNormedSpace period hPeriod)
        period hPeriod configuration data analysis chartData).mp h01
    have ⟨hPhysicalGhost, hLLAuxMetric⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := ReductionPhysicalGhostResidualNormedAddCommGroup period
          hPeriod)
        (firstSpace := ReductionPhysicalGhostResidualNormedSpace period hPeriod)
        (secondGroup := reductionLLResidualNormedAddCommGroup period hPeriod
          configuration data analysis)
        (secondSpace := reductionLLResidualNormedSpace period hPeriod configuration
          data analysis)
        period hPeriod configuration data analysis chartData).mp h23
    have ⟨hLLMeasure, hLLField⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := reductionLLResidualNormedAddCommGroup period hPeriod
          configuration data analysis)
        (firstSpace := reductionLLResidualNormedSpace period hPeriod configuration
          data analysis)
        (secondGroup := reductionLLResidualNormedAddCommGroup period hPeriod
          configuration data analysis)
        (secondSpace := reductionLLResidualNormedSpace period hPeriod configuration
          data analysis)
        period hPeriod configuration data analysis chartData).mp h45
    have ⟨hSpinC, hDiffeomorphismGhost⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := ReductionSpinCResidualNormedAddCommGroup)
        (firstSpace := ReductionSpinCResidualNormedSpace)
        (secondGroup := reductionDiagonalGraphNormedAddCommGroup period hPeriod
          configuration data)
        (secondSpace := reductionDiagonalGraphNormedSpace period hPeriod
          configuration data)
        period hPeriod configuration data analysis chartData).mp h67
    have ⟨hDiffeomorphismAntighost, hDiffeomorphismNakanishiLautrup⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := reductionDiagonalGraphNormedAddCommGroup period hPeriod
          configuration data)
        (firstSpace := reductionDiagonalGraphNormedSpace period hPeriod
          configuration data)
        (secondGroup := reductionDiagonalGraphNormedAddCommGroup period hPeriod
          configuration data)
        (secondSpace := reductionDiagonalGraphNormedSpace period hPeriod
          configuration data)
        period hPeriod configuration data analysis chartData).mp h89
    have ⟨hPotential, hAbelianGhost⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := reductionPotentialResidualNormedAddCommGroup period hPeriod
          configuration data)
        (firstSpace := reductionPotentialResidualNormedSpace period hPeriod
          configuration data)
        (secondGroup := reductionPairedAbelianGraphNormedAddCommGroup period
          hPeriod configuration data)
        (secondSpace := reductionPairedAbelianGraphNormedSpace period hPeriod
          configuration data)
        period hPeriod configuration data analysis chartData).mp h1011
    have ⟨hAbelianAntighost, hAbelianNakanishiLautrup⟩ :=
      (coordinateContDiff_prod_iff
        (firstGroup := ReductionAbelianL2ResidualNormedAddCommGroup period hPeriod)
        (firstSpace := ReductionAbelianL2ResidualNormedSpace period hPeriod)
        (secondGroup := ReductionAbelianL2ResidualNormedAddCommGroup period hPeriod)
        (secondSpace := ReductionAbelianL2ResidualNormedSpace period hPeriod)
        period hPeriod configuration data analysis chartData).mp h1213
    exact
      { metric := hMetric
        normal := hNormal
        physicalGhost := hPhysicalGhost
        llAuxMetric := hLLAuxMetric
        llMeasure := hLLMeasure
        llField := hLLField
        spinC := hSpinC
        diffeomorphismGhost := hDiffeomorphismGhost
        diffeomorphismAntighost := hDiffeomorphismAntighost
        diffeomorphismNakanishiLautrup := hDiffeomorphismNakanishiLautrup
        potential := hPotential
        abelianGhost := hAbelianGhost
        abelianAntighost := hAbelianAntighost
        abelianNakanishiLautrup := hAbelianNakanishiLautrup }
  · intro h
    have h01 := coordinateContDiff_prodMk
      (firstGroup := reductionMetricResidualNormedAddCommGroup period hPeriod
        configuration data)
      (firstSpace := reductionMetricResidualNormedSpace period hPeriod
        configuration data)
      (secondGroup := ReductionNormalResidualNormedAddCommGroup period hPeriod)
      (secondSpace := ReductionNormalResidualNormedSpace period hPeriod)
      period hPeriod configuration data analysis chartData h.metric h.normal
    have h23 := coordinateContDiff_prodMk
      (firstGroup := ReductionPhysicalGhostResidualNormedAddCommGroup period
        hPeriod)
      (firstSpace := ReductionPhysicalGhostResidualNormedSpace period hPeriod)
      (secondGroup := reductionLLResidualNormedAddCommGroup period hPeriod
        configuration data analysis)
      (secondSpace := reductionLLResidualNormedSpace period hPeriod configuration
        data analysis)
      period hPeriod configuration data analysis chartData h.physicalGhost
        h.llAuxMetric
    have h45 := coordinateContDiff_prodMk
      (firstGroup := reductionLLResidualNormedAddCommGroup period hPeriod
        configuration data analysis)
      (firstSpace := reductionLLResidualNormedSpace period hPeriod configuration
        data analysis)
      (secondGroup := reductionLLResidualNormedAddCommGroup period hPeriod
        configuration data analysis)
      (secondSpace := reductionLLResidualNormedSpace period hPeriod configuration
        data analysis)
      period hPeriod configuration data analysis chartData h.llMeasure h.llField
    have h67 := coordinateContDiff_prodMk
      (firstGroup := ReductionSpinCResidualNormedAddCommGroup)
      (firstSpace := ReductionSpinCResidualNormedSpace)
      (secondGroup := reductionDiagonalGraphNormedAddCommGroup period hPeriod
        configuration data)
      (secondSpace := reductionDiagonalGraphNormedSpace period hPeriod
        configuration data)
      period hPeriod configuration data analysis chartData h.spinC
        h.diffeomorphismGhost
    have h89 := coordinateContDiff_prodMk
      (firstGroup := reductionDiagonalGraphNormedAddCommGroup period hPeriod
        configuration data)
      (firstSpace := reductionDiagonalGraphNormedSpace period hPeriod
        configuration data)
      (secondGroup := reductionDiagonalGraphNormedAddCommGroup period hPeriod
        configuration data)
      (secondSpace := reductionDiagonalGraphNormedSpace period hPeriod
        configuration data)
      period hPeriod configuration data analysis chartData
        h.diffeomorphismAntighost h.diffeomorphismNakanishiLautrup
    have h1011 := coordinateContDiff_prodMk
      (firstGroup := reductionPotentialResidualNormedAddCommGroup period hPeriod
        configuration data)
      (firstSpace := reductionPotentialResidualNormedSpace period hPeriod
        configuration data)
      (secondGroup := reductionPairedAbelianGraphNormedAddCommGroup period hPeriod
        configuration data)
      (secondSpace := reductionPairedAbelianGraphNormedSpace period hPeriod
        configuration data)
      period hPeriod configuration data analysis chartData h.potential
        h.abelianGhost
    have h1213 := coordinateContDiff_prodMk
      (firstGroup := ReductionAbelianL2ResidualNormedAddCommGroup period hPeriod)
      (firstSpace := ReductionAbelianL2ResidualNormedSpace period hPeriod)
      (secondGroup := ReductionAbelianL2ResidualNormedAddCommGroup period hPeriod)
      (secondSpace := ReductionAbelianL2ResidualNormedSpace period hPeriod)
      period hPeriod configuration data analysis chartData h.abelianAntighost
        h.abelianNakanishiLautrup
    have h03 := coordinateContDiff_prodMk
      (firstGroup := ReductionResidual01NormedAddCommGroup period hPeriod
        configuration data)
      (firstSpace := ReductionResidual01NormedSpace period hPeriod configuration
        data)
      (secondGroup := ReductionResidual23NormedAddCommGroup period hPeriod
        configuration data analysis)
      (secondSpace := ReductionResidual23NormedSpace period hPeriod configuration
        data analysis)
      period hPeriod configuration data analysis chartData h01 h23
    have h47 := coordinateContDiff_prodMk
      (firstGroup := ReductionResidual45NormedAddCommGroup period hPeriod
        configuration data analysis)
      (firstSpace := ReductionResidual45NormedSpace period hPeriod configuration
        data analysis)
      (secondGroup := ReductionResidual67NormedAddCommGroup period hPeriod
        configuration data)
      (secondSpace := ReductionResidual67NormedSpace period hPeriod configuration
        data)
      period hPeriod configuration data analysis chartData h45 h67
    have h811 := coordinateContDiff_prodMk
      (firstGroup := ReductionResidual89NormedAddCommGroup period hPeriod
        configuration data)
      (firstSpace := ReductionResidual89NormedSpace period hPeriod configuration
        data)
      (secondGroup := ReductionResidual1011NormedAddCommGroup period hPeriod
        configuration data)
      (secondSpace := ReductionResidual1011NormedSpace period hPeriod
        configuration data)
      period hPeriod configuration data analysis chartData h89 h1011
    have hLeft := coordinateContDiff_prodMk
      (firstGroup := ReductionResidual03NormedAddCommGroup period hPeriod
        configuration data analysis)
      (firstSpace := ReductionResidual03NormedSpace period hPeriod configuration
        data analysis)
      (secondGroup := ReductionResidual47NormedAddCommGroup period hPeriod
        configuration data analysis)
      (secondSpace := ReductionResidual47NormedSpace period hPeriod configuration
        data analysis)
      period hPeriod configuration data analysis chartData h03 h47
    have hRight := coordinateContDiff_prodMk
      (firstGroup := ReductionResidual811NormedAddCommGroup period hPeriod
        configuration data)
      (firstSpace := ReductionResidual811NormedSpace period hPeriod configuration
        data)
      (secondGroup := ReductionResidual1213NormedAddCommGroup period hPeriod)
      (secondSpace := ReductionResidual1213NormedSpace period hPeriod)
      period hPeriod configuration data analysis chartData h811 h1213
    exact fullResidualCoordinateContDiff_prodMk period hPeriod configuration data analysis
      chartData hLeft hRight

set_option maxHeartbeats 1200000

theorem fixedNormedResidualAbelianAntighost_contDiff :
    CoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualAbelianAntighost period hPeriod configuration data
        analysis chartData) := by
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    _ inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual
      period hPeriod configuration data analysis chartData)
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianAntighostL2Residual_contDiff
      period hPeriod configuration data analysis chartData

theorem fixedNormedResidualAbelianNakanishiLautrup_contDiff :
    CoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualAbelianNakanishiLautrup period hPeriod configuration
        data analysis chartData) := by
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (ReductionChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (ReductionChartNormedSpace period hPeriod configuration data analysis
      chartData)
    _ inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual
      period hPeriod configuration data analysis chartData)
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual_contDiff
      period hPeriod configuration data analysis chartData

/-- Gate 276: complete residual smoothness is reduced without loss to fourteen
coordinate obligations, of which the two authentic Abelian `L²` obligations
are already discharged. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_normed_residual_regularity_reduction_gate :
    (FullResidualCoordinateContDiff period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedEulerResidualOperator
            period hPeriod configuration data analysis chartData) ↔
        GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualCoordinateContDiff4D
          period hPeriod configuration data analysis chartData) ∧
      CoordinateContDiff period hPeriod configuration data analysis chartData
        (fixedNormedResidualAbelianAntighost period hPeriod configuration data
          analysis chartData) ∧
      CoordinateContDiff period hPeriod configuration data analysis chartData
        (fixedNormedResidualAbelianNakanishiLautrup period hPeriod configuration
          data analysis chartData) :=
  ⟨fixedNormedEulerResidualOperator_contDiff_iff_coordinates period hPeriod
      configuration data analysis chartData,
    fixedNormedResidualAbelianAntighost_contDiff period hPeriod configuration
      data analysis chartData,
    fixedNormedResidualAbelianNakanishiLautrup_contDiff period hPeriod
      configuration data analysis chartData⟩

end RegularityReduction
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D
end JanusFormal
