import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCarrier4D

/-!
# Robin and cross regularity data for the fixed normal carrier

This file isolates the two analytic inputs required to represent the authentic
normal Robin and cross-block covectors smoothly on the fixed paired-`L²`
carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalRobinNormalCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCarrier4D

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

local instance : IsFiniteMeasure
    (intrinsicCanonicalThroatVolumeMeasure
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

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

private abbrev PhysicalPoint
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
    configuration data analysis chartData state

private abbrev NormalHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedHilbert period
    hPeriod

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

local instance normalHilbertCompleteSpace :
    CompleteSpace (NormalHilbert period hPeriod) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCompleteSpace
    period hPeriod

local instance normalDualNormedAddCommGroup :
    NormedAddCommGroup (NormalHilbert period hPeriod →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance normalDualNormedSpace :
    NormedSpace Real (NormalHilbert period hPeriod →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

private theorem normalCovectorOfRieszRepresentative_contDiff
    (representative :
      FullChart period hPeriod configuration data analysis chartData →
        NormalHilbert period hPeriod)
    (representativeContDiff : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (NormalHilbert period hPeriod)
      inferInstance inferInstance ∞ representative) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (NormalHilbert period hPeriod →L[Real] Real)
      inferInstance inferInstance ∞
      (fun state => InnerProductSpace.toDual Real
        (NormalHilbert period hPeriod) (representative state)) := by
  exact @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (NormalHilbert period hPeriod)
    (NormalHilbert period hPeriod →L[Real] Real)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (InnerProductSpace.toDual Real (NormalHilbert period hPeriod))
    representative
    (@ContinuousLinearMap.contDiff Real
      (NormalHilbert period hPeriod)
      (NormalHilbert period hPeriod →L[Real] Real)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (NormalHilbert period hPeriod)).toContinuousLinearEquiv.toContinuousLinearMap)
    representativeContDiff

/-- Smooth continuous extensions of the authentic Robin and cross-block
normal covectors to the fixed paired-`L²` carrier. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D where
  robinCovector :
    FullChart period hPeriod configuration data analysis chartData →
      NormalHilbert period hPeriod →L[Real] Real
  robinRepresents : ∀ state test,
    robinCovector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
          period hPeriod test) =
      globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt period
        hPeriod configuration data analysis chartData
        (PhysicalPoint period hPeriod configuration data analysis chartData
          state) test
  robinContDiff : @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (NormalHilbert period hPeriod →L[Real] Real)
    inferInstance inferInstance ∞ robinCovector
  crossCovector :
    FullChart period hPeriod configuration data analysis chartData →
      NormalHilbert period hPeriod →L[Real] Real
  crossRepresents : ∀ state test,
    crossCovector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
          period hPeriod test) =
      globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt period
        hPeriod configuration data analysis chartData
        (PhysicalPoint period hPeriod configuration data analysis chartData
          state) test
  crossContDiff : @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (NormalHilbert period hPeriod →L[Real] Real)
    inferInstance inferInstance ∞ crossCovector

/-- Construct both normal regularity covectors from smooth fixed-carrier Riesz
representatives. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D.ofRieszRepresentatives
    (robinRepresentative crossRepresentative :
      FullChart period hPeriod configuration data analysis chartData →
        NormalHilbert period hPeriod)
    (robinPairing : ∀ state test,
      inner Real (robinRepresentative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
            period hPeriod test) =
        globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (PhysicalPoint period hPeriod configuration data analysis chartData
            state) test)
    (crossPairing : ∀ state test,
      inner Real (crossRepresentative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
            period hPeriod test) =
        globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (PhysicalPoint period hPeriod configuration data analysis chartData
            state) test)
    (robinContDiff : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (NormalHilbert period hPeriod)
      inferInstance inferInstance ∞ robinRepresentative)
    (crossContDiff : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (NormalHilbert period hPeriod)
      inferInstance inferInstance ∞ crossRepresentative) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
      period hPeriod configuration data analysis chartData where
  robinCovector := fun state => InnerProductSpace.toDual Real
    (NormalHilbert period hPeriod) (robinRepresentative state)
  robinRepresents := by
    intro state test
    change
      inner Real (robinRepresentative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
            period hPeriod test) = _
    exact robinPairing state test
  robinContDiff :=
    normalCovectorOfRieszRepresentative_contDiff period hPeriod configuration
      data analysis chartData robinRepresentative robinContDiff
  crossCovector := fun state => InnerProductSpace.toDual Real
    (NormalHilbert period hPeriod) (crossRepresentative state)
  crossRepresents := by
    intro state test
    change
      inner Real (crossRepresentative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding
            period hPeriod test) = _
    exact crossPairing state test
  crossContDiff :=
    normalCovectorOfRieszRepresentative_contDiff period hPeriod configuration
      data analysis chartData crossRepresentative crossContDiff

theorem normalRobinCrossRegularityData_robinCovector_unique
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.robinCovector = second.robinCovector := by
  funext state
  ext value
  have hFunctions :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding_denseRange
      period hPeriod).equalizer
        (first.robinCovector state).continuous
        (second.robinCovector state).continuous
        (by
          funext test
          exact (first.robinRepresents state test).trans
            (second.robinRepresents state test).symm)
  exact congrFun hFunctions value

theorem normalRobinCrossRegularityData_crossCovector_unique
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.crossCovector = second.crossCovector := by
  funext state
  ext value
  have hFunctions :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedDenseEmbedding_denseRange
      period hPeriod).equalizer
        (first.crossCovector state).continuous
        (second.crossCovector state).continuous
        (by
          funext test
          exact (first.crossRepresents state test).trans
            (second.crossRepresents state test).symm)
  exact congrFun hFunctions value

/-- Fixed-carrier Riesz representative of the authentic normal Robin
covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    NormalHilbert period hPeriod :=
  (InnerProductSpace.toDual Real (NormalHilbert period hPeriod)).symm
    (regularity.robinCovector state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : NormalHilbert period hPeriod) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative
          period hPeriod configuration data analysis chartData regularity state)
        test = regularity.robinCovector state test := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative
  exact InnerProductSpace.toDual_symm_apply

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (NormalHilbert period hPeriod)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative
        period hPeriod configuration data analysis chartData regularity) := by
  exact @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (NormalHilbert period hPeriod →L[Real] Real)
    (NormalHilbert period hPeriod)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (InnerProductSpace.toDual Real (NormalHilbert period hPeriod)).symm
    regularity.robinCovector
    (@ContinuousLinearMap.contDiff Real
      (NormalHilbert period hPeriod →L[Real] Real)
      (NormalHilbert period hPeriod)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (NormalHilbert period hPeriod)).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    regularity.robinContDiff

/-- Fixed-carrier Riesz representative of the authentic normal cross-block
covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    NormalHilbert period hPeriod :=
  (InnerProductSpace.toDual Real (NormalHilbert period hPeriod)).symm
    (regularity.crossCovector state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : NormalHilbert period hPeriod) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative
          period hPeriod configuration data analysis chartData regularity state)
        test = regularity.crossCovector state test := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative
  exact InnerProductSpace.toDual_symm_apply

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (NormalHilbert period hPeriod)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative
        period hPeriod configuration data analysis chartData regularity) := by
  exact @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (NormalHilbert period hPeriod →L[Real] Real)
    (NormalHilbert period hPeriod)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (InnerProductSpace.toDual Real (NormalHilbert period hPeriod)).symm
    regularity.crossCovector
    (@ContinuousLinearMap.contDiff Real
      (NormalHilbert period hPeriod →L[Real] Real)
      (NormalHilbert period hPeriod)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (NormalHilbert period hPeriod)).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    regularity.crossContDiff

/-- Gate 305: the normal Robin and cross covectors are unique and yield
smooth fixed-carrier Riesz representatives. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_normal_robin_cross_regularity_data_gate
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData) :
    (first.robinCovector = second.robinCovector ∧
      first.crossCovector = second.crossCovector) ∧
      (@ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (NormalHilbert period hPeriod)
        inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative
          period hPeriod configuration data analysis chartData first) ∧
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (NormalHilbert period hPeriod)
        inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative
          period hPeriod configuration data analysis chartData first)) :=
  ⟨⟨normalRobinCrossRegularityData_robinCovector_unique period hPeriod
        configuration data analysis chartData first second,
      normalRobinCrossRegularityData_crossCovector_unique period hPeriod
        configuration data analysis chartData first second⟩,
    ⟨globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative_contDiff
        period hPeriod configuration data analysis chartData first,
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative_contDiff
        period hPeriod configuration data analysis chartData first⟩⟩

end RegularityData
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
end JanusFormal
