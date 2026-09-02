import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCarrier4D

/-!
# Analytic remainder data for the Fourier-faithful SpinC coordinate

The spectral base covector is already continuous on the fixed ambient Hilbert
space. This file isolates the genuinely missing input: a globally smooth
continuous extension of the scalar cross-block remainder to the fixed carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D

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
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCarrier4D

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

local instance matterHilbertRealInnerProductSpaceSpinCRemainderData :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  { InnerProductSpace.complexToReal with
    toNormedSpace := inferInstance }

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

private abbrev SpinCHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedHilbert
    period hPeriod configuration data analysis chartData

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

local instance spinCHilbertCompleteSpace :
    CompleteSpace
      (SpinCHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCompleteSpace
    period hPeriod configuration data analysis chartData

/-- Minimal missing input for Fourier-faithful SpinC residual regularity. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D where
  covector :
    FullChart period hPeriod configuration data analysis chartData →
      SpinCHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real
  represents : ∀ state test,
    covector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
          period hPeriod configuration data analysis chartData test) =
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
        period hPeriod configuration data analysis chartData state).remainder test
  contDiff : @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (SpinCHilbert period hPeriod configuration data analysis chartData →L[Real]
      Real) inferInstance inferInstance ∞ covector

/-- Construct SpinC remainder regularity data from a smooth fixed-carrier
Riesz representative. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D.ofRieszRepresentative
    (representative :
      FullChart period hPeriod configuration data analysis chartData →
        SpinCHilbert period hPeriod configuration data analysis chartData)
    (representativePairing : ∀ state test,
      inner Real (representative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test) =
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
          period hPeriod configuration data analysis chartData state).remainder
            test)
    (representativeContDiff : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (SpinCHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞ representative) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
      period hPeriod configuration data analysis chartData where
  covector := fun state =>
    InnerProductSpace.toDual Real
      (SpinCHilbert period hPeriod configuration data analysis chartData)
      (representative state)
  represents := by
    intro state test
    change
      inner Real (representative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding
            period hPeriod configuration data analysis chartData test) = _
    exact representativePairing state test
  contDiff := by
    exact @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (SpinCHilbert period hPeriod configuration data analysis chartData)
      (SpinCHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (SpinCHilbert period hPeriod configuration data analysis chartData))
      representative
      (@ContinuousLinearMap.contDiff Real
        (SpinCHilbert period hPeriod configuration data analysis chartData)
        (SpinCHilbert period hPeriod configuration data analysis chartData →L[Real]
          Real)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (InnerProductSpace.toDual Real
          (SpinCHilbert period hPeriod configuration data analysis
            chartData)).toContinuousLinearEquiv.toContinuousLinearMap)
      representativeContDiff

theorem spinCFourierFaithfulRemainderRegularityData_covector_unique
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.covector = second.covector := by
  funext state
  ext value
  have hFunctions :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedDenseEmbedding_denseRange
      period hPeriod configuration data analysis chartData).equalizer
        (first.covector state).continuous (second.covector state).continuous
        (by
          funext test
          exact (first.represents state test).trans
            (second.represents state test).symm)
  exact congrFun hFunctions value

/-- Fixed-carrier Riesz representative of the SpinC cross-block remainder. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SpinCHilbert period hPeriod configuration data analysis chartData :=
  (InnerProductSpace.toDual Real
    (SpinCHilbert period hPeriod configuration data analysis chartData)).symm
      (regularity.covector state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : SpinCHilbert period hPeriod configuration data analysis chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
          period hPeriod configuration data analysis chartData regularity state)
        test = regularity.covector state test := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
  exact InnerProductSpace.toDual_symm_apply

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (SpinCHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
        period hPeriod configuration data analysis chartData regularity) := by
  exact @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (SpinCHilbert period hPeriod configuration data analysis chartData →L[Real]
      Real)
    (SpinCHilbert period hPeriod configuration data analysis chartData)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (InnerProductSpace.toDual Real
      (SpinCHilbert period hPeriod configuration data analysis chartData)).symm
    regularity.covector
    (@ContinuousLinearMap.contDiff Real
      (SpinCHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real)
      (SpinCHilbert period hPeriod configuration data analysis chartData)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (SpinCHilbert period hPeriod configuration data analysis chartData
          )).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    regularity.contDiff

/-- Gate 293: the missing SpinC remainder covector is unique and yields a
smooth fixed Riesz representative. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_spinC_fourier_faithful_remainder_regularity_data_gate
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.covector = second.covector ∧
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (SpinCHilbert period hPeriod configuration data analysis chartData)
        inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
          period hPeriod configuration data analysis chartData first) :=
  ⟨spinCFourierFaithfulRemainderRegularityData_covector_unique period hPeriod
      configuration data analysis chartData first second,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData first⟩

end RegularityData
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
end JanusFormal
