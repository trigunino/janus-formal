import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

/-!
# Regularity of the Abelian ghost graph residual coordinate

The fixed Abelian ghost coordinate is the ambient inclusion of the Riesz
representative of a fixed-Hessian covector.  It is a bounded linear function
of the full-BRST chart state and hence globally smooth.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostResidualRegularity4D

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
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
  globalPairedAbelianOffShellGraphNormedAddCommGroupAbelianGhostResidual
  globalPairedAbelianOffShellGraphNormedSpaceAbelianGhostResidual
  globalPairedAbelianOffShellGraphAddCommGroupAbelianGhostResidual
  globalPairedAbelianOffShellGraphTopologicalSpaceAbelianGhostResidual
  globalPairedAbelianOffShellGraphModuleAbelianGhostResidual

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

section Regularity

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
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

private abbrev GhostGraph :=
  GlobalPairedAbelianPureGhostGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

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
  RegularityChartNormedSpace period hPeriod configuration data analysis chartData

private abbrev RegularityAbelianGraphNormedAddCommGroup :
    NormedAddCommGroup (AbelianGraph period hPeriod configuration data) :=
  globalPairedAbelianOffShellGraphNormedAddCommGroupAbelianGhostResidual period
    hPeriod (BaseMetric period hPeriod configuration data)

private abbrev RegularityAbelianGraphNormedSpace :
    NormedSpace Real (AbelianGraph period hPeriod configuration data) :=
  globalPairedAbelianOffShellGraphNormedSpaceAbelianGhostResidual period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance regularityGhostGraphCompleteSpace :
    CompleteSpace (GhostGraph period hPeriod configuration data) :=
  globalPairedAbelianPureGhostGraphCompleteSpace period hPeriod
    (BaseMetric period hPeriod configuration data)

private def realRieszInverseCLM
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] : (H →L[Real] Real) →L[Real] H :=
  (InnerProductSpace.toDual Real H).symm.toContinuousLinearEquiv.toContinuousLinearMap

def abelianGhostGraphCovectorCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      (GhostGraph period hPeriod configuration data →L[Real] Real) :=
  ((globalPairedAbelianPureGhostGraphSubmodule period hPeriod
      (BaseMetric period hPeriod configuration data)).subtypeL.precomp Real).comp
    ((globalPairedAbelianOffShellHessian period hPeriod
      (BaseMetric period hPeriod configuration data)).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData))

def abelianGhostGraphRieszResidualCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      GhostGraph period hPeriod configuration data :=
  (realRieszInverseCLM (GhostGraph period hPeriod configuration data)).comp
    (abelianGhostGraphCovectorCLM period hPeriod configuration data analysis
      chartData)

def abelianGhostFixedResidualCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      AbelianGraph period hPeriod configuration data :=
  (globalPairedAbelianPureGhostGraphSubmodule period hPeriod
    (BaseMetric period hPeriod configuration data)).subtypeL.comp
      (abelianGhostGraphRieszResidualCLM period hPeriod configuration data
        analysis chartData)

theorem fixedNormedResidualAbelianGhost_eq_clm
    (state : FullChart period hPeriod configuration data analysis chartData) :
    fixedNormedResidualAbelianGhost period hPeriod configuration data analysis
        chartData state =
      abelianGhostFixedResidualCLM period hPeriod configuration data analysis
        chartData state := by
  rfl

private abbrev AbelianGhostCoordinateContDiff
    (map : FullChart period hPeriod configuration data analysis chartData →
      AbelianGraph period hPeriod configuration data) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (AbelianGraph period hPeriod configuration data)
    (RegularityAbelianGraphNormedAddCommGroup period hPeriod configuration data)
    (RegularityAbelianGraphNormedSpace period hPeriod configuration data) ∞ map

theorem fixedNormedResidualAbelianGhost_contDiff :
    AbelianGhostCoordinateContDiff period hPeriod configuration data analysis
      chartData (fixedNormedResidualAbelianGhost period hPeriod configuration
        data analysis chartData) := by
  change AbelianGhostCoordinateContDiff period hPeriod configuration data
    analysis chartData (abelianGhostFixedResidualCLM period hPeriod
      configuration data analysis chartData)
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (AbelianGraph period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (RegularityAbelianGraphNormedAddCommGroup period hPeriod configuration data)
    (RegularityAbelianGraphNormedSpace period hPeriod configuration data) ∞
    (abelianGhostFixedResidualCLM period hPeriod configuration data analysis
      chartData)

/-- Gate 278: the Abelian ghost graph coordinate satisfies its `C∞`
obligation in the fourteen-coordinate reduction. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_abelian_ghost_residual_regularity_gate :
    AbelianGhostCoordinateContDiff period hPeriod configuration data analysis
      chartData (fixedNormedResidualAbelianGhost period hPeriod configuration
        data analysis chartData) :=
  fixedNormedResidualAbelianGhost_contDiff period hPeriod configuration data
    analysis chartData

end Regularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostResidualRegularity4D
end JanusFormal
