import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszFormula4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

/-!
# Fourier-faithful SpinC residual regularity from remainder data

The exact rank-one fixed-carrier formula turns smooth cross-block remainder
data into global smoothness of the authentic SpinC residual coordinate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulResidualRegularityFromData4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulSpectralBaseRegularity4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszFormula4D
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

local instance matterHilbertRealInnerProductSpaceSpinCResidualRegularity :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  { InnerProductSpace.complexToReal with
    toNormedSpace := inferInstance }

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

private abbrev SpinCBase :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedAmbient

private abbrev SpinCHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedHilbert
    period hPeriod configuration data analysis chartData

private abbrev SpinCClosure :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedClosure
    period hPeriod configuration data analysis chartData

private abbrev SpinCResidual :=
  WithLp 2 (SpinCBase × Real)

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

local instance spinCHilbertCompleteSpace :
    CompleteSpace
      (SpinCHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCompleteSpace
    period hPeriod configuration data analysis chartData

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszAmbientFormula_contDiff
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
      (SpinCResidual) inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity) := by
  letI sourceGroup : NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData
  letI sourceSpace : NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData
  let base :
      FullChart period hPeriod configuration data analysis chartData →
        SpinCHilbert period hPeriod configuration data analysis chartData :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative
      period hPeriod configuration data analysis chartData
  let remainder :
      FullChart period hPeriod configuration data analysis chartData →
        SpinCHilbert period hPeriod configuration data analysis chartData :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative
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
        (SpinCHilbert period hPeriod configuration data analysis chartData)
        inferInstance inferInstance ∞ base :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData
  have hRemainder :
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (SpinCHilbert period hPeriod configuration data analysis chartData)
        inferInstance inferInstance ∞ remainder :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedRemainderRieszRepresentative_contDiff
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
      (SpinCHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞ base remainder hBase hRemainder
  have hNumerator : RegularityContDiff period hPeriod configuration data
      analysis chartData (fun state =>
      inner Real (remainder state) (total state)) :=
    @ContDiff.inner Real
      (SpinCHilbert period hPeriod configuration data analysis chartData)
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
      (SpinCHilbert period hPeriod configuration data analysis chartData)
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
      (SpinCHilbert period hPeriod configuration data analysis chartData)
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
      (SpinCHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞ total
      (fun state => scale state • remainder state) hTotal hScaled
  have hCarrier : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state =>
      ((carrierValue state :
          SpinCHilbert period hPeriod configuration data analysis chartData) :
        SpinCBase)) :=
    @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (SpinCHilbert period hPeriod configuration data analysis chartData)
      SpinCBase
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (SpinCClosure period hPeriod configuration data analysis chartData
        ).subtypeL carrierValue
      (@ContinuousLinearMap.contDiff Real
        (SpinCHilbert period hPeriod configuration data analysis chartData)
        SpinCBase
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (SpinCClosure period hPeriod configuration data analysis chartData
          ).subtypeL)
      hCarrierValue
  have hPair : RegularityContDiff period hPeriod configuration data analysis
      chartData (fun state =>
      (((carrierValue state :
          SpinCHilbert period hPeriod configuration data analysis chartData) :
        SpinCBase), scale state)) :=
    @ContDiff.prodMk Real
      (FullChart period hPeriod configuration data analysis chartData) SpinCBase
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
          SpinCHilbert period hPeriod configuration data analysis chartData) :
        SpinCBase), scale state)) :=
    @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (SpinCBase × Real) SpinCResidual
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (WithLp.prodContinuousLinearEquiv 2 Real SpinCBase Real
        ).symm.toContinuousLinearMap _
      (@ContinuousLinearMap.contDiff Real (SpinCBase × Real) SpinCResidual
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (WithLp.prodContinuousLinearEquiv 2 Real SpinCBase Real
          ).symm.toContinuousLinearMap)
      hPair
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (SpinCResidual) inferInstance inferInstance ∞
    (fun state =>
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity state)
  simpa only [
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszAmbientFormula,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularCarrierValue,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularRieszScale,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularTotalRepresentative,
    base, remainder, total, denominator, scale, carrierValue] using hFormula

theorem fixedNormedResidualSpinC_contDiff_of_remainderRegularityData
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    CoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualSpinC period hPeriod configuration data analysis
        chartData) := by
  have hPointwise :
      fixedNormedResidualSpinC period hPeriod configuration data analysis
          chartData =
        globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity := by
    funext state
    change
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 = _
    exact
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual_val_eq_regularFormula
        period hPeriod configuration data analysis chartData regularity state
  rw [hPointwise]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRegularGraphRieszAmbientFormula_contDiff
      period hPeriod configuration data analysis chartData regularity

/-- Gate 296: smooth cross-block remainder data imply global smoothness of the
authentic Fourier-faithful SpinC residual coordinate. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_spinC_fourier_faithful_residual_regularity_from_data_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D
        period hPeriod configuration data analysis chartData) :
    CoordinateContDiff period hPeriod configuration data analysis chartData
      (fixedNormedResidualSpinC period hPeriod configuration data analysis
        chartData) :=
  fixedNormedResidualSpinC_contDiff_of_remainderRegularityData period hPeriod
    configuration data analysis chartData regularity

end ResidualRegularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulResidualRegularityFromData4D
end JanusFormal
