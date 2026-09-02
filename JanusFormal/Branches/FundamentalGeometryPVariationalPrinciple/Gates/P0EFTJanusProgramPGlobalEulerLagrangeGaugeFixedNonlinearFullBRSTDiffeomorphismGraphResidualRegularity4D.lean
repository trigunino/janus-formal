import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

/-!
# Regularity of the three diffeomorphism graph residual coordinates

The ghost, antighost and Nakanishi--Lautrup graph residuals are bounded linear
functions of the full-BRST chart state.  Their three fixed ambient coordinates
are therefore globally smooth.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGraphResidualRegularity4D

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
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedNormedResidualRegularityReduction4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
  pureGhostGraphNormedAddCommGroup
  pureGhostGraphPseudoMetricSpace
  pureGhostGraphUniformSpace
  pureGhostGraphSeminormedAddCommGroup
  pureGhostGraphAddCommGroup
  pureGhostGraphTopologicalSpace
  pureGhostGraphInnerProductSpace
  pureGhostGraphNormedSpace
  pureGhostGraphModule
  pureAntighostGraphNormedAddCommGroup
  pureAntighostGraphPseudoMetricSpace
  pureAntighostGraphUniformSpace
  pureAntighostGraphSeminormedAddCommGroup
  pureAntighostGraphAddCommGroup
  pureAntighostGraphTopologicalSpace
  pureAntighostGraphInnerProductSpace
  pureAntighostGraphNormedSpace
  pureAntighostGraphModule
  pureNakanishiGraphNormedAddCommGroup
  pureNakanishiGraphPseudoMetricSpace
  pureNakanishiGraphUniformSpace
  pureNakanishiGraphSeminormedAddCommGroup
  pureNakanishiGraphAddCommGroup
  pureNakanishiGraphTopologicalSpace
  pureNakanishiGraphInnerProductSpace
  pureNakanishiGraphNormedSpace
  pureNakanishiGraphModule

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

private abbrev DiagonalGraph :=
  GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

private abbrev GhostGraph :=
  GlobalDiffeomorphismPureGhostGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

private abbrev AntighostGraph :=
  GlobalDiffeomorphismPureAntighostGraphHilbert period hPeriod
    (BaseMetric period hPeriod configuration data)

private abbrev NakanishiGraph :=
  GlobalDiffeomorphismPureNakanishiLautrupGraphHilbert period hPeriod
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

@[implicit_reducible]
local instance (priority := 12000) regularityDiagonalGraphNormedAddCommGroup :
    NormedAddCommGroup
      (DiagonalGraph period hPeriod configuration data) :=
  diagonalGraphNormedAddCommGroupValue period hPeriod
    (BaseMetric period hPeriod configuration data)

@[implicit_reducible]
local instance (priority := 12000) regularityDiagonalGraphNormedSpace :
    NormedSpace Real (DiagonalGraph period hPeriod configuration data) :=
  diagonalGraphNormedSpace period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance regularityGhostGraphCompleteSpace :
    CompleteSpace (GhostGraph period hPeriod configuration data) :=
  globalDiffeomorphismPureGhostGraphCompleteSpace period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance regularityAntighostGraphCompleteSpace :
    CompleteSpace (AntighostGraph period hPeriod configuration data) :=
  globalDiffeomorphismPureAntighostGraphCompleteSpace period hPeriod
    (BaseMetric period hPeriod configuration data)

local instance regularityNakanishiGraphCompleteSpace :
    CompleteSpace (NakanishiGraph period hPeriod configuration data) :=
  globalDiffeomorphismPureNakanishiLautrupGraphCompleteSpace period hPeriod
    (BaseMetric period hPeriod configuration data)

private def realRieszInverseCLM
    (H : Type*) [group : NormedAddCommGroup H]
    [inner : InnerProductSpace Real H] [complete : CompleteSpace H] :
    (H →L[Real] Real) →L[Real] H :=
  (InnerProductSpace.toDual Real H).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The completed diagonal diffeomorphism point as a bounded linear map of
the full chart state. -/
def fullDiffeomorphismBRSTPointCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      DiagonalGraph period hPeriod configuration data :=
  (globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection period
    hPeriod configuration data analysis chartData).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
        hPeriod configuration data analysis chartData)

private def restrictedDiffeomorphismRieszResidualCLM
    (Subspace : Type*) [subspaceGroup : NormedAddCommGroup Subspace]
    [subspaceInner : InnerProductSpace Real Subspace]
    [subspaceComplete : CompleteSpace Subspace]
    (inclusion : Subspace →L[Real]
      DiagonalGraph period hPeriod configuration data) :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      Subspace :=
  (realRieszInverseCLM Subspace (group := subspaceGroup)
    (inner := subspaceInner) (complete := subspaceComplete)).comp
    ((inclusion.precomp Real).comp
        ((globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
          couplings (BaseMetric period hPeriod configuration data)).comp
            (fullDiffeomorphismBRSTPointCLM period hPeriod configuration data
              analysis chartData)))

def diffeomorphismGhostFixedResidualCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      DiagonalGraph period hPeriod configuration data :=
  (globalDiffeomorphismPureGhostGraphSubmodule period hPeriod
    (BaseMetric period hPeriod configuration data)).subtypeL.comp
      (restrictedDiffeomorphismRieszResidualCLM period hPeriod configuration
        data analysis chartData
        (Subspace := GhostGraph period hPeriod configuration data)
        (subspaceGroup := pureGhostGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data))
        (subspaceInner := pureGhostGraphInnerProductSpace period hPeriod
          (BaseMetric period hPeriod configuration data))
        (subspaceComplete := regularityGhostGraphCompleteSpace period hPeriod
          configuration data)
        (globalDiffeomorphismPureGhostGraphSubmodule period hPeriod
          (BaseMetric period hPeriod configuration data)).subtypeL)

def diffeomorphismAntighostFixedResidualCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      DiagonalGraph period hPeriod configuration data :=
  (globalDiffeomorphismPureAntighostGraphSubmodule period hPeriod
    (BaseMetric period hPeriod configuration data)).subtypeL.comp
      (restrictedDiffeomorphismRieszResidualCLM period hPeriod configuration
        data analysis chartData
        (Subspace := AntighostGraph period hPeriod configuration data)
        (subspaceGroup := pureAntighostGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data))
        (subspaceInner := pureAntighostGraphInnerProductSpace period hPeriod
          (BaseMetric period hPeriod configuration data))
        (subspaceComplete := regularityAntighostGraphCompleteSpace period
          hPeriod configuration data)
        (globalDiffeomorphismPureAntighostGraphSubmodule period hPeriod
          (BaseMetric period hPeriod configuration data)).subtypeL)

def diffeomorphismNakanishiLautrupFixedResidualCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      DiagonalGraph period hPeriod configuration data :=
  (globalDiffeomorphismPureNakanishiLautrupGraphSubmodule period hPeriod
    (BaseMetric period hPeriod configuration data)).subtypeL.comp
      (restrictedDiffeomorphismRieszResidualCLM period hPeriod configuration
        data analysis chartData
        (Subspace := NakanishiGraph period hPeriod configuration data)
        (subspaceGroup := pureNakanishiGraphNormedAddCommGroup period hPeriod
          (BaseMetric period hPeriod configuration data))
        (subspaceInner := pureNakanishiGraphInnerProductSpace period hPeriod
          (BaseMetric period hPeriod configuration data))
        (subspaceComplete := regularityNakanishiGraphCompleteSpace period
          hPeriod configuration data)
        (globalDiffeomorphismPureNakanishiLautrupGraphSubmodule period hPeriod
          (BaseMetric period hPeriod configuration data)).subtypeL)

theorem fixedNormedResidualDiffeomorphismGhost_eq_clm
    (state : FullChart period hPeriod configuration data analysis chartData) :
    fixedNormedResidualDiffeomorphismGhost period hPeriod configuration data
        analysis chartData state =
      diffeomorphismGhostFixedResidualCLM period hPeriod configuration data
        analysis chartData state := by
  rfl

theorem fixedNormedResidualDiffeomorphismAntighost_eq_clm
    (state : FullChart period hPeriod configuration data analysis chartData) :
    fixedNormedResidualDiffeomorphismAntighost period hPeriod configuration data
        analysis chartData state =
      diffeomorphismAntighostFixedResidualCLM period hPeriod configuration data
        analysis chartData state := by
  rfl

theorem fixedNormedResidualDiffeomorphismNakanishiLautrup_eq_clm
    (state : FullChart period hPeriod configuration data analysis chartData) :
    fixedNormedResidualDiffeomorphismNakanishiLautrup period hPeriod
        configuration data analysis chartData state =
      diffeomorphismNakanishiLautrupFixedResidualCLM period hPeriod configuration
        data analysis chartData state := by
  rfl

private abbrev DiffeomorphismCoordinateContDiff
    (map : FullChart period hPeriod configuration data analysis chartData →
      DiagonalGraph period hPeriod configuration data) : Prop :=
  @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (DiagonalGraph period hPeriod configuration data)
    (regularityDiagonalGraphNormedAddCommGroup period hPeriod configuration data)
    (regularityDiagonalGraphNormedSpace period hPeriod configuration data) ∞ map

theorem fixedNormedResidualDiffeomorphismGhost_contDiff :
    DiffeomorphismCoordinateContDiff period hPeriod configuration data analysis
      chartData (fixedNormedResidualDiffeomorphismGhost period hPeriod
        configuration data analysis chartData) := by
  change DiffeomorphismCoordinateContDiff period hPeriod configuration data
    analysis chartData (diffeomorphismGhostFixedResidualCLM period hPeriod
      configuration data analysis chartData)
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (DiagonalGraph period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (regularityDiagonalGraphNormedAddCommGroup period hPeriod configuration data)
    (regularityDiagonalGraphNormedSpace period hPeriod configuration data) ∞
    (diffeomorphismGhostFixedResidualCLM period hPeriod configuration data
      analysis chartData)

theorem fixedNormedResidualDiffeomorphismAntighost_contDiff :
    DiffeomorphismCoordinateContDiff period hPeriod configuration data analysis
      chartData (fixedNormedResidualDiffeomorphismAntighost period hPeriod
        configuration data analysis chartData) := by
  change DiffeomorphismCoordinateContDiff period hPeriod configuration data
    analysis chartData (diffeomorphismAntighostFixedResidualCLM period hPeriod
      configuration data analysis chartData)
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (DiagonalGraph period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (regularityDiagonalGraphNormedAddCommGroup period hPeriod configuration data)
    (regularityDiagonalGraphNormedSpace period hPeriod configuration data) ∞
    (diffeomorphismAntighostFixedResidualCLM period hPeriod configuration data
      analysis chartData)

theorem fixedNormedResidualDiffeomorphismNakanishiLautrup_contDiff :
    DiffeomorphismCoordinateContDiff period hPeriod configuration data analysis
      chartData (fixedNormedResidualDiffeomorphismNakanishiLautrup period hPeriod
        configuration data analysis chartData) := by
  change DiffeomorphismCoordinateContDiff period hPeriod configuration data
    analysis chartData
      (diffeomorphismNakanishiLautrupFixedResidualCLM period hPeriod
        configuration data analysis chartData)
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (DiagonalGraph period hPeriod configuration data)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (regularityDiagonalGraphNormedAddCommGroup period hPeriod configuration data)
    (regularityDiagonalGraphNormedSpace period hPeriod configuration data) ∞
    (diffeomorphismNakanishiLautrupFixedResidualCLM period hPeriod configuration
      data analysis chartData)

/-- Gate 277: the three diffeomorphism nonminimal graph coordinates satisfy
their `C∞` obligations in the fourteen-coordinate reduction. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_diffeomorphism_graph_residual_regularity_gate :
    DiffeomorphismCoordinateContDiff period hPeriod configuration data analysis
        chartData (fixedNormedResidualDiffeomorphismGhost period hPeriod
          configuration data analysis chartData) ∧
      DiffeomorphismCoordinateContDiff period hPeriod configuration data analysis
        chartData (fixedNormedResidualDiffeomorphismAntighost period hPeriod
          configuration data analysis chartData) ∧
      DiffeomorphismCoordinateContDiff period hPeriod configuration data analysis
        chartData (fixedNormedResidualDiffeomorphismNakanishiLautrup period
          hPeriod configuration data analysis chartData) :=
  ⟨fixedNormedResidualDiffeomorphismGhost_contDiff period hPeriod configuration
      data analysis chartData,
    fixedNormedResidualDiffeomorphismAntighost_contDiff period hPeriod
      configuration data analysis chartData,
    fixedNormedResidualDiffeomorphismNakanishiLautrup_contDiff period hPeriod
      configuration data analysis chartData⟩

end Regularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGraphResidualRegularity4D
end JanusFormal
