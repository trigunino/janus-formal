import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszFormula4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

/-!
# Normal residual regularity from Robin/cross data

The exact two-covector fixed-carrier formula turns smooth Robin and cross
data into global smoothness of the authentic normal residual coordinate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalResidualRegularityFromData4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCarrier4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszFormula4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

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

private abbrev NormalAmbient :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedAmbient period
    hPeriod

private abbrev NormalHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedHilbert period
    hPeriod

private abbrev NormalInclusion :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedInclusionCLM
    period hPeriod

private abbrev NormalRobinBase :=
  WithLp 2 (NormalAmbient period hPeriod × Real)

private abbrev NormalResidual :=
  WithLp 2 (NormalRobinBase period hPeriod × Real)

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

local instance normalHilbertCompleteSpace :
    CompleteSpace (NormalHilbert period hPeriod) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCompleteSpace
    period hPeriod

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszAmbientFormula_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData) :
    RegularityContDiff period hPeriod configuration data analysis chartData
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity) := by
  letI sourceGroup : NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData
  letI sourceSpace : NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData
  let robin :
      FullChart period hPeriod configuration data analysis chartData →
        NormalHilbert period hPeriod :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative
      period hPeriod configuration data analysis chartData regularity
  let cross :
      FullChart period hPeriod configuration data analysis chartData →
        NormalHilbert period hPeriod :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative
      period hPeriod configuration data analysis chartData regularity
  let total := fun state => robin state + cross state
  let robinNormSq := fun state => ‖robin state‖ ^ 2
  let crossNormSq := fun state => ‖cross state‖ ^ 2
  let robinCross := fun state => inner Real (robin state) (cross state)
  let robinTotal := fun state => inner Real (robin state) (total state)
  let crossTotal := fun state => inner Real (cross state) (total state)
  let determinant := fun state =>
    (1 + robinNormSq state) * (1 + crossNormSq state) -
      robinCross state ^ 2
  let robinNumerator := fun state =>
    robinTotal state * (1 + crossNormSq state) -
      robinCross state * crossTotal state
  let crossNumerator := fun state =>
    (1 + robinNormSq state) * crossTotal state -
      robinCross state * robinTotal state
  let robinScale := fun state => robinNumerator state / determinant state
  let crossScale := fun state => crossNumerator state / determinant state
  let carrierValue := fun state =>
    total state - robinScale state • robin state -
      crossScale state • cross state
  have hRobin : RegularityContDiff period hPeriod configuration data analysis
      chartData robin :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedRobinRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData regularity
  have hCross : RegularityContDiff period hPeriod configuration data analysis
      chartData cross :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2FixedCrossRieszRepresentative_contDiff
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
      (NormalHilbert period hPeriod) inferInstance inferInstance ∞ robin cross
      hRobin hCross
  have hRobinNormSq : RegularityContDiff period hPeriod configuration data
      analysis chartData robinNormSq :=
    @ContDiff.norm_sq Real (NormalHilbert period hPeriod)
      inferInstance inferInstance inferInstance inferInstance
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) robin ∞ hRobin
  have hCrossNormSq : RegularityContDiff period hPeriod configuration data
      analysis chartData crossNormSq :=
    @ContDiff.norm_sq Real (NormalHilbert period hPeriod)
      inferInstance inferInstance inferInstance inferInstance
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) cross ∞ hCross
  have hRobinCross : RegularityContDiff period hPeriod configuration data
      analysis chartData robinCross :=
    @ContDiff.inner Real (NormalHilbert period hPeriod)
      inferInstance inferInstance inferInstance inferInstance
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) robin cross ∞ hRobin hCross
  have hRobinTotal : RegularityContDiff period hPeriod configuration data
      analysis chartData robinTotal :=
    @ContDiff.inner Real (NormalHilbert period hPeriod)
      inferInstance inferInstance inferInstance inferInstance
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) robin total ∞ hRobin hTotal
  have hCrossTotal : RegularityContDiff period hPeriod configuration data
      analysis chartData crossTotal :=
    @ContDiff.inner Real (NormalHilbert period hPeriod)
      inferInstance inferInstance inferInstance inferInstance
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) cross total ∞ hCross hTotal
  have hOne : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun _ => (1 : Real)) :=
    @contDiff_const Real
      (FullChart period hPeriod configuration data analysis chartData) Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) inferInstance inferInstance ∞ (1 : Real)
  have hOnePlusRobin : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state => 1 + robinNormSq state) :=
    @ContDiff.add Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) Real inferInstance inferInstance ∞ (fun _ => 1)
      robinNormSq hOne hRobinNormSq
  have hOnePlusCross : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state => 1 + crossNormSq state) :=
    @ContDiff.add Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) Real inferInstance inferInstance ∞ (fun _ => 1)
      crossNormSq hOne hCrossNormSq
  have hDeterminantProduct : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state =>
        (1 + robinNormSq state) * (1 + crossNormSq state)) :=
    @ContDiff.mul Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) ∞ Real inferInstance inferInstance _ _ hOnePlusRobin
      hOnePlusCross
  have hRobinCrossSq : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state => robinCross state ^ 2) :=
    @ContDiff.pow Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) ∞ Real inferInstance inferInstance robinCross hRobinCross 2
  have hDeterminant : RegularityContDiff period hPeriod configuration data
      analysis chartData determinant :=
    @ContDiff.sub Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) Real inferInstance inferInstance ∞ _ _ hDeterminantProduct
      hRobinCrossSq
  have hDeterminant_ne : ∀ state, determinant state ≠ 0 := by
    intro state
    apply ne_of_gt
    have hCS : inner Real (robin state) (cross state) ^ 2 ≤
        ‖robin state‖ ^ 2 * ‖cross state‖ ^ 2 := by
      simpa only [pow_two, real_inner_self_eq_norm_sq] using
        (real_inner_mul_inner_self_le (robin state) (cross state))
    have hBase : 0 < 1 + ‖robin state‖ ^ 2 + ‖cross state‖ ^ 2 := by
      positivity
    dsimp only [determinant, robinNormSq, crossNormSq, robinCross]
    calc
      (1 + ‖robin state‖ ^ 2) * (1 + ‖cross state‖ ^ 2) -
            inner Real (robin state) (cross state) ^ 2 =
          (1 + ‖robin state‖ ^ 2 + ‖cross state‖ ^ 2) +
            (‖robin state‖ ^ 2 * ‖cross state‖ ^ 2 -
              inner Real (robin state) (cross state) ^ 2) := by ring
      _ > 0 := add_pos_of_pos_of_nonneg hBase (sub_nonneg.mpr hCS)
  have hRobinNumerator : RegularityContDiff period hPeriod configuration data
      analysis chartData robinNumerator :=
    @ContDiff.sub Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) Real inferInstance inferInstance ∞ _ _
      (@ContDiff.mul Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData) ∞ Real inferInstance inferInstance _ _ hRobinTotal
        hOnePlusCross)
      (@ContDiff.mul Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData) ∞ Real inferInstance inferInstance _ _ hRobinCross
        hCrossTotal)
  have hCrossNumerator : RegularityContDiff period hPeriod configuration data
      analysis chartData crossNumerator :=
    @ContDiff.sub Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) Real inferInstance inferInstance ∞ _ _
      (@ContDiff.mul Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData) ∞ Real inferInstance inferInstance _ _ hOnePlusRobin
        hCrossTotal)
      (@ContDiff.mul Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData) ∞ Real inferInstance inferInstance _ _ hRobinCross
        hRobinTotal)
  have hRobinScale : RegularityContDiff period hPeriod configuration data
      analysis chartData robinScale :=
    @ContDiff.div Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) robinNumerator determinant ∞ hRobinNumerator hDeterminant
      hDeterminant_ne
  have hCrossScale : RegularityContDiff period hPeriod configuration data
      analysis chartData crossScale :=
    @ContDiff.div Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) crossNumerator determinant ∞ hCrossNumerator hDeterminant
      hDeterminant_ne
  have hRobinScaled : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state => robinScale state • robin state) :=
    @ContDiff.smul Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) (NormalHilbert period hPeriod) inferInstance inferInstance ∞
      Real inferInstance inferInstance inferInstance inferInstance inferInstance
      robinScale robin hRobinScale hRobin
  have hCrossScaled : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state => crossScale state • cross state) :=
    @ContDiff.smul Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) (NormalHilbert period hPeriod) inferInstance inferInstance ∞
      Real inferInstance inferInstance inferInstance inferInstance inferInstance
      crossScale cross hCrossScale hCross
  have hTotalMinusRobin : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state =>
        total state - robinScale state • robin state) :=
    @ContDiff.sub Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) (NormalHilbert period hPeriod) inferInstance inferInstance ∞
      total _ hTotal hRobinScaled
  have hCarrierValue : RegularityContDiff period hPeriod configuration data
      analysis chartData carrierValue :=
    @ContDiff.sub Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) (NormalHilbert period hPeriod) inferInstance inferInstance ∞
      _ _ hTotalMinusRobin hCrossScaled
  have hCarrierAmbient : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state =>
        ((carrierValue state : NormalHilbert period hPeriod) :
          NormalAmbient period hPeriod)) :=
    @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (NormalHilbert period hPeriod) (NormalAmbient period hPeriod)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) inferInstance inferInstance inferInstance inferInstance ∞
      (NormalInclusion period hPeriod) carrierValue
      (@ContinuousLinearMap.contDiff Real (NormalHilbert period hPeriod)
        (NormalAmbient period hPeriod)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (NormalInclusion period hPeriod)) hCarrierValue
  have hRobinPair : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state =>
        (((carrierValue state : NormalHilbert period hPeriod) :
          NormalAmbient period hPeriod), robinScale state)) :=
    @ContDiff.prodMk Real
      (FullChart period hPeriod configuration data analysis chartData)
      (NormalAmbient period hPeriod) Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) inferInstance inferInstance inferInstance inferInstance ∞ _ _
      hCarrierAmbient hRobinScale
  have hRobinLp : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state => WithLp.toLp 2
        (((carrierValue state : NormalHilbert period hPeriod) :
          NormalAmbient period hPeriod), robinScale state)) :=
    @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (NormalAmbient period hPeriod × Real) (NormalRobinBase period hPeriod)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) inferInstance inferInstance inferInstance inferInstance ∞
      (WithLp.prodContinuousLinearEquiv 2 Real
        (NormalAmbient period hPeriod) Real).symm.toContinuousLinearMap _
      (@ContinuousLinearMap.contDiff Real
        (NormalAmbient period hPeriod × Real) (NormalRobinBase period hPeriod)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (WithLp.prodContinuousLinearEquiv 2 Real
          (NormalAmbient period hPeriod) Real).symm.toContinuousLinearMap)
      hRobinPair
  have hOuterPair : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state =>
        (WithLp.toLp 2
          (((carrierValue state : NormalHilbert period hPeriod) :
          NormalAmbient period hPeriod), robinScale state),
          crossScale state)) :=
    @ContDiff.prodMk Real
      (FullChart period hPeriod configuration data analysis chartData)
      (NormalRobinBase period hPeriod) Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) inferInstance inferInstance inferInstance inferInstance ∞ _ _
      hRobinLp hCrossScale
  have hFormula : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state => WithLp.toLp 2
        (WithLp.toLp 2
          (((carrierValue state : NormalHilbert period hPeriod) :
          NormalAmbient period hPeriod), robinScale state),
          crossScale state)) :=
    @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (NormalRobinBase period hPeriod × Real) (NormalResidual period hPeriod)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData) inferInstance inferInstance inferInstance inferInstance ∞
      (WithLp.prodContinuousLinearEquiv 2 Real
        (NormalRobinBase period hPeriod) Real).symm.toContinuousLinearMap _
      (@ContinuousLinearMap.contDiff Real
        (NormalRobinBase period hPeriod × Real) (NormalResidual period hPeriod)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (WithLp.prodContinuousLinearEquiv 2 Real
          (NormalRobinBase period hPeriod) Real).symm.toContinuousLinearMap)
      hOuterPair
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (NormalResidual period hPeriod) inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszAmbientFormula
      period hPeriod configuration data analysis chartData regularity)
  convert hFormula using 1
  funext state
  rfl

theorem fixedNormedResidualNormal_contDiff_of_robinCrossRegularityData
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData) :
    CoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualNormal period hPeriod configuration data analysis
        chartData) := by
  have hPointwise :
      fixedNormedResidualNormal period hPeriod configuration data analysis
          chartData =
        globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity := by
    funext state
    change
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 = _
    exact
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual_val_eq_regularFormula
        period hPeriod configuration data analysis chartData regularity state
  rw [hPointwise]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalRegularGraphRieszAmbientFormula_contDiff
      period hPeriod configuration data analysis chartData regularity

/-- Gate 307: smooth Robin/cross data imply global smoothness of the
authentic normal residual coordinate. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_normal_residual_regularity_from_data_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalRobinCrossRegularityData4D
        period hPeriod configuration data analysis chartData) :
    CoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualNormal period hPeriod configuration data analysis
        chartData) :=
  fixedNormedResidualNormal_contDiff_of_robinCrossRegularityData period hPeriod
    configuration data analysis chartData regularity

end ResidualRegularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalResidualRegularityFromData4D
end JanusFormal
