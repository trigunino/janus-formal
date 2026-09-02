import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszFormula4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

/-!
# Metric residual regularity from remainder data

The exact rank-one fixed-carrier formula turns smooth cross-block remainder
data into global smoothness of the authentic metric residual coordinate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricResidualRegularityFromData4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 4000000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricFixedCarrier4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricBaseRegularity4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszFormula4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

attribute [local instance 10001]
  metricFixedNormedAddCommGroup
  metricFixedInnerProductSpace
  metricFixedNormedSpace
  metricFixedModule
  diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual
  diagonalGraphNormedSpaceDiffeomorphismGhostResidual
  diagonalGraphContinuousAddDiffeomorphismGhostResidual
  diagonalGraphModuleDiffeomorphismGhostResidual
  diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual
attribute [local instance 10002]
  metricFixedSeminormedAddCommGroup
  metricFixedAddCommGroup
  metricFixedTopologicalSpace
  diagonalGraphAddCommGroupDiffeomorphismGhostResidual
  diagonalGraphTopologicalSpaceDiffeomorphismGhostResidual
attribute [local instance 10003]
  metricFixedPseudoMetricSpace
  metricFixedUniformSpace
attribute [local instance]
  diagonalGraphIsBoundedSMulDiffeomorphismGhostResidual
  diagonalGraphUniformContinuousConstSMulDiffeomorphismGhostResidual
  diagonalGraphContinuousConstSMulDiffeomorphismGhostResidual
  diagonalGraphCompleteSpaceDiffeomorphismGhostResidual

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

section ResidualRegularity

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

private abbrev MetricBase :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedAmbient period hPeriod
    configuration data

@[implicit_reducible]
local instance (priority := 15000) regularityMetricBaseNormedAddCommGroup :
    NormedAddCommGroup (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientNormedAddCommGroup period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 15001) regularityMetricBaseAddCommGroup :
    AddCommGroup (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientAddCommGroup period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 15002) regularityMetricBaseSeminormedAddCommGroup :
    SeminormedAddCommGroup (MetricBase period hPeriod configuration data) :=
  (regularityMetricBaseNormedAddCommGroup period hPeriod configuration data
    ).toSeminormedAddCommGroup

@[implicit_reducible]
local instance (priority := 15002) regularityMetricBaseAddCommMonoid :
    AddCommMonoid (MetricBase period hPeriod configuration data) :=
  (regularityMetricBaseAddCommGroup period hPeriod configuration data
    ).toAddCommMonoid

@[implicit_reducible]
local instance (priority := 15000) regularityMetricBaseNormedSpace :
    NormedSpace Real (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientNormedSpace period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 15000) regularityMetricBaseModule :
    Module Real (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientModule period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 15001) regularityMetricBaseTopologicalSpace :
    TopologicalSpace (MetricBase period hPeriod configuration data) :=
  metricFixedAmbientTopologicalSpace period hPeriod configuration data

private abbrev MetricHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert
    period hPeriod configuration data

private abbrev MetricInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedInclusionCLM period hPeriod
    configuration data

private abbrev MetricResidual :=
  WithLp 2 (MetricBase period hPeriod configuration data × Real)

@[implicit_reducible]
local instance (priority := 13000) regularityMetricResidualNormedAddCommGroup :
    NormedAddCommGroup
      (MetricResidual period hPeriod configuration data) :=
  reductionMetricResidualNormedAddCommGroup period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 13000) regularityMetricResidualNormedSpace :
    NormedSpace Real (MetricResidual period hPeriod configuration data) :=
  reductionMetricResidualNormedSpace period hPeriod configuration data

@[implicit_reducible]
local instance (priority := 13001) regularityMetricResidualSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (MetricResidual period hPeriod configuration data) :=
  (regularityMetricResidualNormedAddCommGroup period hPeriod configuration data
    ).toSeminormedAddCommGroup

@[implicit_reducible]
local instance (priority := 13001) regularityMetricResidualAddCommGroup :
    AddCommGroup (MetricResidual period hPeriod configuration data) :=
  (regularityMetricResidualNormedAddCommGroup period hPeriod configuration data
    ).toAddCommGroup

@[implicit_reducible]
local instance (priority := 13002) regularityMetricResidualAddCommMonoid :
    AddCommMonoid (MetricResidual period hPeriod configuration data) :=
  (regularityMetricResidualAddCommGroup period hPeriod configuration data
    ).toAddCommMonoid

@[implicit_reducible]
local instance (priority := 13001) regularityMetricResidualModule :
    Module Real (MetricResidual period hPeriod configuration data) :=
  (regularityMetricResidualNormedSpace period hPeriod configuration data
    ).toModule

@[implicit_reducible]
local instance (priority := 13002) regularityMetricResidualPseudoMetricSpace :
    PseudoMetricSpace (MetricResidual period hPeriod configuration data) :=
  (regularityMetricResidualNormedAddCommGroup period hPeriod configuration data
    ).toPseudoMetricSpace

@[implicit_reducible]
local instance (priority := 13002) regularityMetricResidualUniformSpace :
    UniformSpace (MetricResidual period hPeriod configuration data) :=
  (regularityMetricResidualPseudoMetricSpace period hPeriod configuration data
    ).toUniformSpace

@[implicit_reducible]
local instance (priority := 13002) regularityMetricResidualTopologicalSpace :
    TopologicalSpace (MetricResidual period hPeriod configuration data) :=
  (regularityMetricResidualUniformSpace period hPeriod configuration data
    ).toTopologicalSpace

private abbrev RegularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartNormedAddCommGroup period hPeriod configuration data
    analysis chartData

private abbrev RegularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartNormedSpace period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 12000) regularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 12000) regularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedSpace period hPeriod configuration data analysis
    chartData

private abbrev RegularityContDiff
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace Real Target]
    (map : FullChart period hPeriod configuration data analysis chartData →
      Target) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    Target inferInstance inferInstance ∞ map

local instance metricHilbertCompleteSpace :
    CompleteSpace
      (MetricHilbert period hPeriod configuration data) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedCompleteSpace
    period hPeriod configuration data

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszAmbientFormula_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (MetricResidual period hPeriod configuration data)
      (regularityMetricResidualNormedAddCommGroup period hPeriod configuration
        data)
      (regularityMetricResidualNormedSpace period hPeriod configuration data) ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity) := by
  letI sourceGroup : NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData
  letI sourceSpace : NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData
  letI metricBaseGroup :
      NormedAddCommGroup (MetricBase period hPeriod configuration data) :=
    regularityMetricBaseNormedAddCommGroup period hPeriod configuration data
  letI metricBaseSpace :
      NormedSpace Real (MetricBase period hPeriod configuration data) :=
    regularityMetricBaseNormedSpace period hPeriod configuration data
  letI metricBaseSeminormedGroup :
      SeminormedAddCommGroup (MetricBase period hPeriod configuration data) :=
    regularityMetricBaseSeminormedAddCommGroup period hPeriod configuration data
  letI metricBaseAddGroup :
      AddCommGroup (MetricBase period hPeriod configuration data) :=
    regularityMetricBaseAddCommGroup period hPeriod configuration data
  letI metricBaseAddMonoid :
      AddCommMonoid (MetricBase period hPeriod configuration data) :=
    regularityMetricBaseAddCommMonoid period hPeriod configuration data
  letI metricBaseModule :
      Module Real (MetricBase period hPeriod configuration data) :=
    regularityMetricBaseModule period hPeriod configuration data
  letI metricBaseTopology :
      TopologicalSpace (MetricBase period hPeriod configuration data) :=
    regularityMetricBaseTopologicalSpace period hPeriod configuration data
  letI metricPairGroup : NormedAddCommGroup
      (MetricBase period hPeriod configuration data × Real) := inferInstance
  letI metricPairSpace : NormedSpace Real
      (MetricBase period hPeriod configuration data × Real) := inferInstance
  letI metricPairModule : Module Real
      (MetricBase period hPeriod configuration data × Real) := inferInstance
  letI metricResidualGroup :
      NormedAddCommGroup (MetricResidual period hPeriod configuration data) :=
    regularityMetricResidualNormedAddCommGroup period hPeriod configuration data
  letI metricResidualSpace :
      NormedSpace Real (MetricResidual period hPeriod configuration data) :=
    regularityMetricResidualNormedSpace period hPeriod configuration data
  letI metricResidualModule :
      Module Real (MetricResidual period hPeriod configuration data) :=
    regularityMetricResidualModule period hPeriod configuration data
  let base :
      FullChart period hPeriod configuration data analysis chartData →
        MetricHilbert period hPeriod configuration data :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData
  let remainder :
      FullChart period hPeriod configuration data analysis chartData →
        MetricHilbert period hPeriod configuration data :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity
  let total := fun state => base state + remainder state
  let denominator := fun state => 1 + ‖remainder state‖ ^ 2
  let scale := fun state =>
    inner Real (remainder state) (total state) / denominator state
  let carrierValue := fun state => total state - scale state • remainder state
  have hBase :
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (MetricHilbert period hPeriod configuration data)
        inferInstance inferInstance ∞ base :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedBaseRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData
  have hRemainder :
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (MetricHilbert period hPeriod configuration data)
        inferInstance inferInstance ∞ remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData regularity
  have hTotal : RegularityContDiff period hPeriod configuration data analysis
      chartData total :=
    @ContDiff.add Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (MetricHilbert period hPeriod configuration data)
      inferInstance inferInstance ∞ base remainder hBase hRemainder
  have hNumerator : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state =>
      inner Real (remainder state) (total state)) :=
    @ContDiff.inner Real
      (MetricHilbert period hPeriod configuration data)
      inferInstance inferInstance inferInstance inferInstance
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      remainder total ∞ hRemainder hTotal
  have hNormSq : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state => ‖remainder state‖ ^ 2) :=
    @ContDiff.norm_sq Real
      (MetricHilbert period hPeriod configuration data)
      inferInstance inferInstance inferInstance inferInstance
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      remainder ∞ hRemainder
  have hDenominator : RegularityContDiff period hPeriod configuration data
      analysis chartData denominator :=
    @ContDiff.add Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      Real inferInstance inferInstance ∞ (fun _ => 1)
      (fun state => ‖remainder state‖ ^ 2)
      (@contDiff_const Real
        (FullChart period hPeriod configuration data analysis chartData) Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        inferInstance inferInstance ∞ (1 : Real))
      hNormSq
  have hScale : RegularityContDiff period hPeriod configuration data analysis
      chartData scale :=
    @ContDiff.div Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (fun state => inner Real (remainder state) (total state)) denominator ∞
      hNumerator hDenominator (fun state => by
        dsimp only [denominator]
        positivity)
  have hScaled : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state => scale state • remainder state) :=
    @ContDiff.smul Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (MetricHilbert period hPeriod configuration data)
      inferInstance inferInstance ∞ Real inferInstance inferInstance
      inferInstance inferInstance inferInstance scale remainder hScale hRemainder
  have hCarrierValue : RegularityContDiff period hPeriod configuration data
      analysis chartData carrierValue :=
    @ContDiff.sub Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (MetricHilbert period hPeriod configuration data)
      inferInstance inferInstance ∞ total
      (fun state => scale state • remainder state) hTotal hScaled
  have hCarrier : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state =>
      ((carrierValue state :
          MetricHilbert period hPeriod configuration data) :
        MetricBase period hPeriod configuration data)) :=
    @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (MetricHilbert period hPeriod configuration data)
      (MetricBase period hPeriod configuration data)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (MetricInclusion period hPeriod configuration data) carrierValue
      (@ContinuousLinearMap.contDiff Real
        (MetricHilbert period hPeriod configuration data)
        (MetricBase period hPeriod configuration data)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (MetricInclusion period hPeriod configuration data))
      hCarrierValue
  have hPair : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state =>
      (((carrierValue state :
          MetricHilbert period hPeriod configuration data) :
        MetricBase period hPeriod configuration data), scale state)) :=
    @ContDiff.prodMk Real
      (FullChart period hPeriod configuration data analysis chartData)
      (MetricBase period hPeriod configuration data)
      Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞ _ _ hCarrier
      hScale
  have hFormula : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state => WithLp.toLp 2
      (((carrierValue state :
          MetricHilbert period hPeriod configuration data) :
        MetricBase period hPeriod configuration data), scale state)) :=
    @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (MetricBase period hPeriod configuration data × Real)
      (MetricResidual period hPeriod configuration data)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (WithLp.prodContinuousLinearEquiv 2 Real
        (MetricBase period hPeriod configuration data) Real
        ).symm.toContinuousLinearMap _
      (@ContinuousLinearMap.contDiff Real
        (MetricBase period hPeriod configuration data × Real)
        (MetricResidual period hPeriod configuration data)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (WithLp.prodContinuousLinearEquiv 2 Real
          (MetricBase period hPeriod configuration data) Real
          ).symm.toContinuousLinearMap)
      hPair
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (MetricResidual period hPeriod configuration data)
    inferInstance inferInstance ∞
    (fun state =>
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state)
  simpa only [
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszAmbientFormula,
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularCarrierValue,
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularRieszScale,
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularTotalRepresentative,
    base, remainder, total, denominator, scale, carrierValue] using hFormula

theorem fixedNormedResidualMetric_contDiff_of_remainderRegularityData
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    MetricCoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualMetric period hPeriod configuration data analysis
        chartData) := by
  have hPointwise :
      fixedNormedResidualMetric period hPeriod configuration data analysis
          chartData =
        globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity := by
    funext state
    change
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 = _
    exact
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual_val_eq_regularFormula
        period hPeriod configuration data analysis chartData regularity state
  rw [hPointwise]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricRegularGraphRieszAmbientFormula_contDiff
      period hPeriod configuration data analysis chartData regularity

/-- Gate 302: smooth cross-block remainder data imply global smoothness of the
authentic metric residual coordinate. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_metric_residual_regularity_from_data_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    MetricCoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualMetric period hPeriod configuration data analysis
        chartData) :=
  fixedNormedResidualMetric_contDiff_of_remainderRegularityData period hPeriod
    configuration data analysis chartData regularity

end ResidualRegularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricResidualRegularityFromData4D
end JanusFormal
