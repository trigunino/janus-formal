import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricFixedCarrier4D

/-!
# Analytic remainder data for the fixed metric coordinate

The authentic diagonal-BRST base covector is already continuous on the fixed
ambient Hilbert space. This file isolates the genuinely missing input: a
globally smooth continuous extension of the scalar metric remainder to the
fixed carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricFixedCarrier4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

attribute [local instance 10001]
  diagonalGraphNormedAddCommGroupDiffeomorphismGhostResidual
  diagonalGraphNormedSpaceDiffeomorphismGhostResidual
  diagonalGraphContinuousAddDiffeomorphismGhostResidual
  diagonalGraphModuleDiffeomorphismGhostResidual
  diagonalGraphInnerProductSpaceDiffeomorphismGhostResidual
attribute [local instance 10002]
  diagonalGraphAddCommGroupDiffeomorphismGhostResidual
  diagonalGraphTopologicalSpaceDiffeomorphismGhostResidual
attribute [local instance]
  diagonalGraphIsBoundedSMulDiffeomorphismGhostResidual
  diagonalGraphUniformContinuousConstSMulDiffeomorphismGhostResidual
  diagonalGraphContinuousConstSMulDiffeomorphismGhostResidual
  diagonalGraphCompleteSpaceDiffeomorphismGhostResidual

attribute [local instance 10001]
  metricFixedNormedAddCommGroup
  metricFixedInnerProductSpace
  metricFixedNormedSpace
  metricFixedModule
attribute [local instance 10002]
  metricFixedSeminormedAddCommGroup
  metricFixedAddCommGroup
  metricFixedTopologicalSpace
attribute [local instance 10003]
  metricFixedPseudoMetricSpace
  metricFixedUniformSpace

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

section RegularityData

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

private abbrev MetricHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedHilbert period hPeriod
    configuration data

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

local instance metricHilbertCompleteSpace :
    CompleteSpace
      (MetricHilbert period hPeriod configuration data) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedCompleteSpace period
    hPeriod configuration data

local instance metricDualNormedAddCommGroup :
    NormedAddCommGroup
      (MetricHilbert period hPeriod configuration data →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance metricDualNormedSpace :
    NormedSpace Real
      (MetricHilbert period hPeriod configuration data →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

/-- Minimal missing input for fixed-carrier metric residual regularity. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D where
  covector :
    FullChart period hPeriod configuration data analysis chartData →
      MetricHilbert period hPeriod configuration data →L[Real] Real
  represents : ∀ state test,
    covector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
          period hPeriod configuration data test) =
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData
        period hPeriod configuration data analysis chartData state).remainder test
  contDiff : @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (MetricHilbert period hPeriod configuration data →L[Real] Real)
    inferInstance inferInstance ∞ covector

/-- Construct metric remainder regularity data from a smooth fixed-carrier
Riesz representative. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D.ofRieszRepresentative
    (representative :
      FullChart period hPeriod configuration data analysis chartData →
        MetricHilbert period hPeriod configuration data)
    (representativePairing : ∀ state test,
      inner Real (representative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
            period hPeriod configuration data test) =
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphData
          period hPeriod configuration data analysis chartData state).remainder
            test)
    (representativeContDiff : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (MetricHilbert period hPeriod configuration data)
      inferInstance inferInstance ∞ representative) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
      period hPeriod configuration data analysis chartData where
  covector := fun state =>
    InnerProductSpace.toDual Real
      (MetricHilbert period hPeriod configuration data) (representative state)
  represents := by
    intro state test
    change
      inner Real (representative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding
            period hPeriod configuration data test) = _
    exact representativePairing state test
  contDiff := by
    exact @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (MetricHilbert period hPeriod configuration data)
      (MetricHilbert period hPeriod configuration data →L[Real] Real)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (MetricHilbert period hPeriod configuration data))
      representative
      (@ContinuousLinearMap.contDiff Real
        (MetricHilbert period hPeriod configuration data)
        (MetricHilbert period hPeriod configuration data →L[Real] Real)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (InnerProductSpace.toDual Real
          (MetricHilbert period hPeriod configuration data
            )).toContinuousLinearEquiv.toContinuousLinearMap)
      representativeContDiff

theorem metricRemainderRegularityData_covector_unique
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.covector = second.covector := by
  funext state
  ext value
  have hFunctions :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedDenseEmbedding_denseRange
      period hPeriod configuration data).equalizer
        (first.covector state).continuous (second.covector state).continuous
        (by
          funext test
          exact (first.represents state test).trans
            (second.represents state test).symm)
  exact congrFun hFunctions value

/-- Fixed-carrier Riesz representative of the scalar metric remainder. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    MetricHilbert period hPeriod configuration data :=
  (InnerProductSpace.toDual Real
    (MetricHilbert period hPeriod configuration data)).symm
      (regularity.covector state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : MetricHilbert period hPeriod configuration data) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
          period hPeriod configuration data analysis chartData regularity state)
        test = regularity.covector state test := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
  exact InnerProductSpace.toDual_symm_apply

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative_contDiff
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
      (MetricHilbert period hPeriod configuration data)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
        period hPeriod configuration data analysis chartData regularity) := by
  exact @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (MetricHilbert period hPeriod configuration data →L[Real] Real)
    (MetricHilbert period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (InnerProductSpace.toDual Real
      (MetricHilbert period hPeriod configuration data)).symm
    regularity.covector
    (@ContinuousLinearMap.contDiff Real
      (MetricHilbert period hPeriod configuration data →L[Real] Real)
      (MetricHilbert period hPeriod configuration data)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (MetricHilbert period hPeriod configuration data
          )).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    regularity.contDiff

/-- Gate 299: the missing metric remainder covector is unique and yields a
smooth fixed Riesz representative. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_metric_remainder_regularity_data_gate
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.covector = second.covector ∧
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (MetricHilbert period hPeriod configuration data)
        inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative
          period hPeriod configuration data analysis chartData first) :=
  ⟨metricRemainderRegularityData_covector_unique period hPeriod configuration
      data analysis chartData first second,
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricFixedRemainderRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData first⟩

end RegularityData
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricRemainderRegularityData4D
end JanusFormal
