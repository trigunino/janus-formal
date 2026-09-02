import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszFormula4D

/-!
# Potential residual regularity from fixed-carrier data

The explicit fixed-carrier formula turns smooth potential Euler data into
global smoothness of the authentic fixed-ambient potential residual.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialResidualRegularityFromData4D

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
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialFixedCarrier4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszFormula4D
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

private abbrev AbelianGraph :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAmbient period
    hPeriod configuration data

private abbrev PotentialClosure :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedClosure period
    hPeriod configuration data

private abbrev PotentialHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedHilbert period
    hPeriod configuration data

private abbrev PotentialResidual :=
  WithLp 2
    (GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAmbient period
      hPeriod configuration data × Real)

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

@[implicit_reducible]
local instance (priority := 10001) abelianGraphNormedAddCommGroup :
    NormedAddCommGroup (AbelianGraph period hPeriod configuration data) :=
  @Submodule.normedAddCommGroup Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)
    inferInstance inferInstance inferInstance
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data))

@[implicit_reducible]
local instance (priority := 10001) abelianGraphNormedSpace :
    NormedSpace Real (AbelianGraph period hPeriod configuration data) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 10002) abelianGraphAddCommGroup :
    AddCommGroup (AbelianGraph period hPeriod configuration data) :=
  (abelianGraphNormedAddCommGroup period hPeriod configuration data).toAddCommGroup

@[implicit_reducible]
local instance (priority := 10002) abelianGraphTopologicalSpace :
    TopologicalSpace (AbelianGraph period hPeriod configuration data) :=
  (abelianGraphNormedAddCommGroup period hPeriod configuration data
    ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
local instance (priority := 10001) abelianGraphModule :
    Module Real (AbelianGraph period hPeriod configuration data) :=
  (abelianGraphNormedSpace period hPeriod configuration data).toModule

local instance potentialHilbertCompleteSpace :
    CompleteSpace (PotentialHilbert period hPeriod configuration data) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCompleteSpace period
    hPeriod configuration data

/-- Fixed smooth map from a carrier Riesz representative to the ambient
potential residual formula. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCarrierRieszFormula
    (representative : PotentialHilbert period hPeriod configuration data) :
    PotentialResidual period hPeriod configuration data :=
  let scale := (1 + ‖representative‖ ^ 2)⁻¹
  WithLp.toLp 2
    (((scale • representative : PotentialHilbert period hPeriod configuration
        data) : AbelianGraph period hPeriod configuration data),
      scale * ‖representative‖ ^ 2)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCarrierRieszFormula_contDiff :
    ContDiff Real ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCarrierRieszFormula
        period hPeriod configuration data) := by
  let normSq := fun representative :
      PotentialHilbert period hPeriod configuration data =>
    ‖representative‖ ^ 2
  let denominator := fun representative :
      PotentialHilbert period hPeriod configuration data =>
    1 + normSq representative
  let scale := fun representative :
      PotentialHilbert period hPeriod configuration data =>
    (denominator representative)⁻¹
  have hNormSq : ContDiff Real ∞ normSq := contDiff_id.norm_sq Real
  have hDenominator : ContDiff Real ∞ denominator :=
    contDiff_const.add hNormSq
  have hScale : ContDiff Real ∞ scale := hDenominator.inv (fun representative => by
    dsimp only [denominator, normSq]
    positivity)
  have hScaled : ContDiff Real ∞ (fun representative =>
      scale representative • representative) := hScale.smul contDiff_id
  have hCarrier : ContDiff Real ∞ (fun representative =>
      ((scale representative • representative :
          PotentialHilbert period hPeriod configuration data) :
        AbelianGraph period hPeriod configuration data)) :=
    (PotentialClosure period hPeriod configuration data).subtypeL.contDiff.comp
      hScaled
  have hScalar : ContDiff Real ∞ (fun representative =>
      scale representative * normSq representative) := hScale.mul hNormSq
  have hPair : ContDiff Real ∞ (fun representative =>
      (((scale representative • representative :
          PotentialHilbert period hPeriod configuration data) :
        AbelianGraph period hPeriod configuration data),
        scale representative * normSq representative)) :=
    hCarrier.prodMk hScalar
  have hFormula : ContDiff Real ∞ (fun representative => WithLp.toLp 2
      (((scale representative • representative :
          PotentialHilbert period hPeriod configuration data) :
        AbelianGraph period hPeriod configuration data),
        scale representative * normSq representative)) :=
    (WithLp.prodContinuousLinearEquiv 2 Real
      (AbelianGraph period hPeriod configuration data) Real
      ).symm.toContinuousLinearMap.contDiff.comp hPair
  change ContDiff Real ∞ (fun representative =>
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCarrierRieszFormula
      period hPeriod configuration data representative)
  simpa only [
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCarrierRieszFormula,
    PotentialResidual, normSq, denominator, scale] using hFormula

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszAmbientFormula_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (PotentialResidual period hPeriod configuration data) inferInstance
      inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszAmbientFormula
        period hPeriod configuration data analysis chartData regularity) := by
  let representative :
      FullChart period hPeriod configuration data analysis chartData →
        PotentialHilbert period hPeriod configuration data :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative
      period hPeriod configuration data analysis chartData regularity
  have hRepresentative :
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (PotentialHilbert period hPeriod configuration data) inferInstance
        inferInstance ∞ representative :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData regularity
  have hComposition := @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (PotentialHilbert period hPeriod configuration data)
    (PotentialResidual period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCarrierRieszFormula
      period hPeriod configuration data)
    representative
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCarrierRieszFormula_contDiff
      period hPeriod configuration data)
    hRepresentative
  change @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (PotentialResidual period hPeriod configuration data) inferInstance
    inferInstance ∞
    (fun state =>
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedCarrierRieszFormula
        period hPeriod configuration data (representative state))
  exact hComposition

theorem fixedNormedResidualPotential_contDiff_of_eulerRegularityData
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData) :
    PotentialCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (fixedNormedResidualPotential period hPeriod configuration data analysis
        chartData) := by
  have hPointwise :
      fixedNormedResidualPotential period hPeriod configuration data analysis
          chartData =
        globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszAmbientFormula
          period hPeriod configuration data analysis chartData regularity := by
    funext state
    change
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
        period hPeriod configuration data analysis chartData state).1 = _
    exact
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual_val_eq_regularFormula
        period hPeriod configuration data analysis chartData regularity state
  rw [hPointwise]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialRegularGraphRieszAmbientFormula_contDiff
      period hPeriod configuration data analysis chartData regularity

/-- Gate 290: fixed-carrier Euler regularity implies global smoothness of the
authentic potential residual coordinate. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_potential_residual_regularity_from_data_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerRegularityData4D
        period hPeriod configuration data analysis chartData) :
    PotentialCoordinateContDiff period hPeriod configuration data analysis
      chartData
      (fixedNormedResidualPotential period hPeriod configuration data analysis
        chartData) :=
  fixedNormedResidualPotential_contDiff_of_eulerRegularityData period hPeriod
    configuration data analysis chartData regularity

end ResidualRegularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialResidualRegularityFromData4D
end JanusFormal
