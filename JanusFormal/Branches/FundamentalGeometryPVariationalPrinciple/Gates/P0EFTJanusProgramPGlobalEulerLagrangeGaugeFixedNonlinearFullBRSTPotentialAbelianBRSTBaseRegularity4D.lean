import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityFromData4D

/-!
# Canonical fixed-carrier regularity of the potential Abelian-BRST base

The Abelian gauge-fixing Hessian and the full-chart Abelian projection are
continuous linear maps. Restricting their covector to the fixed potential
carrier and applying Riesz therefore gives a canonical smooth representative.
This treats only the Abelian-BRST contribution; the Maxwell and physical
cross-block contributions remain separate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialAbelianBRSTBaseRegularity4D

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
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialFixedCarrier4D

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

section PotentialBase

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

private def restrictedPotentialAbelianBRSTRieszCLM
    (Subspace : Type*) [NormedAddCommGroup Subspace]
    [InnerProductSpace Real Subspace] [CompleteSpace Subspace]
    (inclusion : Subspace →L[Real]
      AbelianGraph period hPeriod configuration data) :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      Subspace :=
  ((InnerProductSpace.toDual Real Subspace).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((inclusion.precomp Real).comp
      ((globalPairedAbelianOffShellHessian period hPeriod
        (BaseMetric period hPeriod configuration data)).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData)))

/-- Riesz representative of the Abelian-BRST potential contribution on the
fixed potential carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      PotentialHilbert period hPeriod configuration data :=
  restrictedPotentialAbelianBRSTRieszCLM period hPeriod configuration data
    analysis chartData (PotentialHilbert period hPeriod configuration data)
    (PotentialClosure period hPeriod configuration data).subtypeL

def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PotentialHilbert period hPeriod configuration data :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszCLM
    period hPeriod configuration data analysis chartData state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : PotentialHilbert period hPeriod configuration data) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative
          period hPeriod configuration data analysis chartData state) test =
      globalPairedAbelianOffShellHessian period hPeriod
        (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData state)
        ((PotentialClosure period hPeriod configuration data).subtypeL test) := by
  change inner Real
      ((InnerProductSpace.toDual Real
        (PotentialHilbert period hPeriod configuration data)).symm
        (((PotentialClosure period hPeriod configuration data).subtypeL.precomp
          Real).comp
          ((globalPairedAbelianOffShellHessian period hPeriod
            (BaseMetric period hPeriod configuration data)).comp
            (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
              hPeriod configuration data analysis chartData)) state)) test = _
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative_dense_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (potential : Sector → SmoothAbelianGaugePotential period hPeriod) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative
          period hPeriod configuration data analysis chartData state)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
          period hPeriod configuration data potential) =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialAbelianBRSTCovector
        period hPeriod configuration data analysis chartData state potential := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative_pairing]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative_contDiff :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (PotentialHilbert period hPeriod configuration data)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative
        period hPeriod configuration data analysis chartData) := by
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (PotentialHilbert period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszCLM
      period hPeriod configuration data analysis chartData)

/-- Gate 315: the Abelian-BRST part of the potential Euler covector has a
canonical globally smooth fixed-carrier Riesz representative. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_potential_AbelianBRST_base_regularity_gate :
    @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (PotentialHilbert period hPeriod configuration data)
        inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative
          period hPeriod configuration data analysis chartData) ∧
      ∀ state potential,
        inner Real
            (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative
              period hPeriod configuration data analysis chartData state)
            (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedDenseEmbedding
              period hPeriod configuration data potential) =
          globalCandidateAGaugeFixedNonlinearFullBRSTPotentialAbelianBRSTCovector
            period hPeriod configuration data analysis chartData state potential :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialFixedAbelianBRSTRieszRepresentative_dense_pairing
      period hPeriod configuration data analysis chartData⟩

end PotentialBase
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialAbelianBRSTBaseRegularity4D
end JanusFormal
