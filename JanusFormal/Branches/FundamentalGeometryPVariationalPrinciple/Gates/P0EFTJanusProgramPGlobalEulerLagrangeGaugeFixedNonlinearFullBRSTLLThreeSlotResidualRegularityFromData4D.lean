import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotRegularGraphRieszFormula4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingThreeRegularity4D

/-!
# Regularity of the three LL residual coordinates

The exact rank-one fixed-carrier formulas turn smooth remainder data into
global smoothness of the three authentic LL residual coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotResidualRegularityFromData4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 4000000
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLCommonFixedCarrier4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotBaseRegularity4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotRegularGraphRieszFormula4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeAndPhysicalGhostPotentialSpinCMetricNormalData4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

attribute [local instance 10001]
  llAuxMetricFixedNormedAddCommGroup
  llAuxMetricFixedInnerProductSpace
  llAuxMetricFixedNormedSpace
  llAuxMetricFixedModule
  llMeasureFixedNormedAddCommGroup
  llMeasureFixedInnerProductSpace
  llMeasureFixedNormedSpace
  llMeasureFixedModule
  llFieldFixedNormedAddCommGroup
  llFieldFixedInnerProductSpace
  llFieldFixedNormedSpace
  llFieldFixedModule
attribute [local instance 10002]
  llAuxMetricFixedSeminormedAddCommGroup
  llAuxMetricFixedAddCommGroup
  llAuxMetricFixedTopologicalSpace
  llMeasureFixedSeminormedAddCommGroup
  llMeasureFixedAddCommGroup
  llMeasureFixedTopologicalSpace
  llFieldFixedSeminormedAddCommGroup
  llFieldFixedAddCommGroup
  llFieldFixedTopologicalSpace
attribute [local instance 10003]
  llAuxMetricFixedPseudoMetricSpace
  llAuxMetricFixedUniformSpace
  llMeasureFixedPseudoMetricSpace
  llMeasureFixedUniformSpace
  llFieldFixedPseudoMetricSpace
  llFieldFixedUniformSpace

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

private abbrev LLCommonAmbient :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbient period
    hPeriod configuration data analysis

private abbrev LLGraphAmbient :=
  WithLp 2 (LLCommonAmbient period hPeriod configuration data analysis × Real)

private abbrev LLAuxMetricHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedHilbert period
    hPeriod configuration data analysis chartData

private abbrev LLMeasureHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedHilbert period
    hPeriod configuration data analysis chartData

private abbrev LLFieldHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedHilbert period hPeriod
    configuration data analysis chartData

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

@[implicit_reducible]
local instance (priority := 15000) llCommonAmbientNormedSpace :
    NormedSpace Real
      (LLCommonAmbient period hPeriod configuration data analysis) :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTLLCommonFixedAmbientInnerProductSpace
    period hPeriod configuration data analysis).toNormedSpace

private abbrev LLGraphRegularityContDiff
    (map : FullChart period hPeriod configuration data analysis chartData →
      LLGraphAmbient period hPeriod configuration data analysis) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (LLGraphAmbient period hPeriod configuration data analysis)
    inferInstance
    (WithLp.instProdNormedSpace 2 Real
      (LLCommonAmbient period hPeriod configuration data analysis) Real)
    ∞ map

private theorem rankOneRegularGraphRieszAmbientFormula_contDiff
    {Hilbert Ambient : Type*}
    [NormedAddCommGroup Hilbert] [NormedSpace Real Hilbert]
    [InnerProductSpace Real Hilbert]
    [NormedAddCommGroup Ambient] [NormedSpace Real Ambient]
    (inclusion : Hilbert → Ambient)
    (hInclusion :
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        Hilbert inferInstance inferInstance Ambient inferInstance inferInstance ∞
        inclusion)
    (base remainder :
      FullChart period hPeriod configuration data analysis chartData → Hilbert)
    (hBase : RegularityContDiff period hPeriod configuration data analysis
      chartData base)
    (hRemainder : RegularityContDiff period hPeriod configuration data analysis
      chartData remainder) :
    RegularityContDiff period hPeriod configuration data analysis chartData
      (fun state =>
        let total := base state + remainder state
        let scale := inner Real (remainder state) total /
          (1 + ‖remainder state‖ ^ 2)
        WithLp.toLp 2
          (inclusion (total - scale • remainder state), scale)) := by
  let total := fun state => base state + remainder state
  let numerator := fun state => inner Real (remainder state) (total state)
  let denominator := fun state => 1 + ‖remainder state‖ ^ 2
  let scale := fun state => numerator state / denominator state
  let carrierValue := fun state => total state - scale state • remainder state
  have hTotal : RegularityContDiff period hPeriod configuration data analysis
      chartData total :=
    @ContDiff.add Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      Hilbert inferInstance inferInstance ∞ base remainder hBase hRemainder
  have hNumerator : RegularityContDiff period hPeriod configuration data analysis
      chartData numerator :=
    @ContDiff.inner Real Hilbert inferInstance inferInstance inferInstance
      inferInstance
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      remainder total ∞ hRemainder hTotal
  have hNormSq : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state => ‖remainder state‖ ^ 2) :=
    @ContDiff.norm_sq Real Hilbert inferInstance inferInstance inferInstance
      inferInstance
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      remainder ∞ hRemainder
  have hOne : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun _ => (1 : Real)) :=
    @contDiff_const Real
      (FullChart period hPeriod configuration data analysis chartData) Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance ∞ (1 : Real)
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
      (fun state => ‖remainder state‖ ^ 2) hOne hNormSq
  have hDenominator_ne : ∀ state, denominator state ≠ 0 := by
    intro state
    dsimp only [denominator]
    positivity
  have hScale : RegularityContDiff period hPeriod configuration data analysis
      chartData scale :=
    @ContDiff.div Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      numerator denominator ∞ hNumerator hDenominator hDenominator_ne
  have hScaled : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state => scale state • remainder state) :=
    @ContDiff.smul Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      Hilbert inferInstance inferInstance ∞ Real inferInstance inferInstance
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
      Hilbert inferInstance inferInstance ∞ total _ hTotal hScaled
  have hCarrierAmbient : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state => inclusion (carrierValue state)) :=
    @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      Hilbert Ambient
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞ inclusion
      carrierValue hInclusion hCarrierValue
  have hPair : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state => (inclusion (carrierValue state), scale state)) :=
    @ContDiff.prodMk Real
      (FullChart period hPeriod configuration data analysis chartData)
      Ambient Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞ _ _
      hCarrierAmbient hScale
  have hFormula : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state =>
        WithLp.toLp 2 (inclusion (carrierValue state), scale state)) :=
    @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (Ambient × Real) (WithLp 2 (Ambient × Real))
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (WithLp.prodContinuousLinearEquiv 2 Real Ambient Real).symm.toContinuousLinearMap
      _
      (@ContinuousLinearMap.contDiff Real (Ambient × Real)
        (WithLp 2 (Ambient × Real))
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (WithLp.prodContinuousLinearEquiv 2 Real Ambient Real).symm.toContinuousLinearMap)
      hPair
  convert hFormula using 1

private theorem llAuxMetricFixedInclusion_contDiff :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (LLAuxMetricHilbert period hPeriod configuration data analysis chartData)
      (llAuxMetricFixedNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (llAuxMetricFixedNormedSpace period hPeriod configuration data analysis
        chartData)
      (LLCommonAmbient period hPeriod configuration data analysis)
      inferInstance inferInstance ∞
      (fun value =>
        globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedInclusionCLM
          period hPeriod configuration data analysis chartData value) := by
  exact @ContinuousLinearMap.contDiff Real
    (LLAuxMetricHilbert period hPeriod configuration data analysis chartData)
    (LLCommonAmbient period hPeriod configuration data analysis)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (llAuxMetricFixedNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (llAuxMetricFixedNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedInclusionCLM
      period hPeriod configuration data analysis chartData)

private theorem llMeasureFixedInclusion_contDiff :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (LLMeasureHilbert period hPeriod configuration data analysis chartData)
      (llMeasureFixedNormedAddCommGroup period hPeriod configuration data analysis
        chartData)
      (llMeasureFixedNormedSpace period hPeriod configuration data analysis
        chartData)
      (LLCommonAmbient period hPeriod configuration data analysis)
      inferInstance inferInstance ∞
      (fun value =>
        globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedInclusionCLM
          period hPeriod configuration data analysis chartData value) := by
  exact @ContinuousLinearMap.contDiff Real
    (LLMeasureHilbert period hPeriod configuration data analysis chartData)
    (LLCommonAmbient period hPeriod configuration data analysis)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (llMeasureFixedNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (llMeasureFixedNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedInclusionCLM period
      hPeriod configuration data analysis chartData)

private theorem llFieldFixedInclusion_contDiff :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (LLFieldHilbert period hPeriod configuration data analysis chartData)
      (llFieldFixedNormedAddCommGroup period hPeriod configuration data analysis
        chartData)
      (llFieldFixedNormedSpace period hPeriod configuration data analysis
        chartData)
      (LLCommonAmbient period hPeriod configuration data analysis)
      inferInstance inferInstance ∞
      (fun value =>
        globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedInclusionCLM
          period hPeriod configuration data analysis chartData value) := by
  exact @ContinuousLinearMap.contDiff Real
    (LLFieldHilbert period hPeriod configuration data analysis chartData)
    (LLCommonAmbient period hPeriod configuration data analysis)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (llFieldFixedNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (llFieldFixedNormedSpace period hPeriod configuration data analysis chartData)
    inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedInclusionCLM period
      hPeriod configuration data analysis chartData)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszAmbientFormula_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    LLGraphRegularityContDiff period hPeriod configuration data analysis chartData
      (fun state =>
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity state :
          LLGraphAmbient period hPeriod configuration data analysis)) := by
  convert rankOneRegularGraphRieszAmbientFormula_contDiff period hPeriod
    configuration data analysis chartData
    (fun value : LLAuxMetricHilbert period hPeriod configuration data analysis
        chartData =>
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedInclusionCLM
        period hPeriod configuration data analysis chartData value)
    (llAuxMetricFixedInclusion_contDiff period hPeriod configuration data analysis
      chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedBaseRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricFixedRemainderRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData regularity) using 1
  funext state
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszAmbientFormula_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    LLGraphRegularityContDiff period hPeriod configuration data analysis chartData
      (fun state =>
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity state :
          LLGraphAmbient period hPeriod configuration data analysis)) := by
  convert rankOneRegularGraphRieszAmbientFormula_contDiff period hPeriod
    configuration data analysis chartData
    (fun value : LLMeasureHilbert period hPeriod configuration data analysis
        chartData =>
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedInclusionCLM period
        hPeriod configuration data analysis chartData value)
    (llMeasureFixedInclusion_contDiff period hPeriod configuration data analysis
      chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedBaseRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureFixedRemainderRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData regularity) using 1
  funext state
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszAmbientFormula_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    LLGraphRegularityContDiff period hPeriod configuration data analysis chartData
      (fun state =>
        (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity state :
          LLGraphAmbient period hPeriod configuration data analysis)) := by
  convert rankOneRegularGraphRieszAmbientFormula_contDiff period hPeriod
    configuration data analysis chartData
    (fun value : LLFieldHilbert period hPeriod configuration data analysis
        chartData =>
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedInclusionCLM period
        hPeriod configuration data analysis chartData value)
    (llFieldFixedInclusion_contDiff period hPeriod configuration data analysis
      chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative
      period hPeriod configuration data analysis chartData regularity)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedBaseRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldFixedRemainderRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData regularity) using 1
  funext state
  rfl

theorem fixedNormedResidualLLAuxMetric_contDiff_of_remainderRegularityData
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    LLCoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualLLAuxMetric period hPeriod configuration data analysis
        chartData) := by
  have hPointwise :
      fixedNormedResidualLLAuxMetric period hPeriod configuration data analysis
          chartData =
        globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity := by
    funext state
    change
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 = _
    exact
      globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual_val_eq_regularFormula
        period hPeriod configuration data analysis chartData regularity state
  rw [hPointwise]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricRegularGraphRieszAmbientFormula_contDiff
      period hPeriod configuration data analysis chartData regularity

theorem fixedNormedResidualLLMeasure_contDiff_of_remainderRegularityData
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    LLCoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualLLMeasure period hPeriod configuration data analysis
        chartData) := by
  have hPointwise :
      fixedNormedResidualLLMeasure period hPeriod configuration data analysis
          chartData =
        globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity := by
    funext state
    change
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 = _
    exact
      globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual_val_eq_regularFormula
        period hPeriod configuration data analysis chartData regularity state
  rw [hPointwise]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureRegularGraphRieszAmbientFormula_contDiff
      period hPeriod configuration data analysis chartData regularity

theorem fixedNormedResidualLLField_contDiff_of_remainderRegularityData
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    LLCoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualLLField period hPeriod configuration data analysis
        chartData) := by
  have hPointwise :
      fixedNormedResidualLLField period hPeriod configuration data analysis
          chartData =
        globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity := by
    funext state
    change
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 = _
    exact
      globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual_val_eq_regularFormula
        period hPeriod configuration data analysis chartData regularity state
  rw [hPointwise]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldRegularGraphRieszAmbientFormula_contDiff
      period hPeriod configuration data analysis chartData regularity

theorem globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeCoordinateContDiff4D_of_llThreeSlotRemainderRegularityData
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeCoordinateContDiff4D
      period hPeriod configuration data analysis chartData :=
  { llAuxMetric :=
      fixedNormedResidualLLAuxMetric_contDiff_of_remainderRegularityData period
        hPeriod configuration data analysis chartData regularity
    llMeasure :=
      fixedNormedResidualLLMeasure_contDiff_of_remainderRegularityData period
        hPeriod configuration data analysis chartData regularity
    llField :=
      fixedNormedResidualLLField_contDiff_of_remainderRegularityData period
        hPeriod configuration data analysis chartData regularity }

/-- Gate 313: smooth fixed-carrier remainder data imply global smoothness of
the three authentic LL residual coordinates. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_ll_three_slot_residual_regularity_from_data_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTLLThreeSlotRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeCoordinateContDiff4D
      period hPeriod configuration data analysis chartData :=
  globalCandidateAGaugeFixedNonlinearFullBRSTFixedNormedResidualRemainingThreeCoordinateContDiff4D_of_llThreeSlotRemainderRegularityData
    period hPeriod configuration data analysis chartData regularity

end ResidualRegularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotResidualRegularityFromData4D
end JanusFormal
