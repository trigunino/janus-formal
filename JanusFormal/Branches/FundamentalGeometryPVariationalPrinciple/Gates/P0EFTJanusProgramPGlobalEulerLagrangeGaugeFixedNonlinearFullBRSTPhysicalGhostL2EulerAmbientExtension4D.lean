import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D

/-!
# Canonical ambient L² extension of the physical-ghost Euler covector

A regular covector on the fixed closed carrier extends canonically to the full
paired `L²` space by precomposition with orthogonal projection.  The extension
still represents the authentic Euler covector and remains globally smooth.
Existence of the regularity data is not asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientExtension4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GhostMeasure :=
  intrinsicCanonicalThroatVolumeMeasure period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure (GhostMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

section AmbientExtension

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

private abbrev PhysicalGhostCarrier :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Carrier4D
    period hPeriod

private abbrev PhysicalGhostClosure :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D
    period hPeriod

private abbrev PhysicalGhostHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Hilbert4D
    period hPeriod

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

local instance physicalGhostHilbertCompleteSpace :
    CompleteSpace (PhysicalGhostHilbert period hPeriod) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2CompleteSpace4D
    period hPeriod

/-- Orthogonal projection from the full paired `L²` space to the fixed closed
physical-ghost carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2OrthogonalProjection :
    PhysicalGhostCarrier period hPeriod →L[Real]
      PhysicalGhostHilbert period hPeriod :=
  (PhysicalGhostClosure period hPeriod).orthogonalProjectionOnto

/-- Canonical extension of the regular Euler covector to the whole paired
`L²` space, chosen to vanish on the orthogonal complement. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientCovector
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PhysicalGhostCarrier period hPeriod →L[Real] Real :=
  (regularity.covector state).comp
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2OrthogonalProjection
      period hPeriod)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientCovector_represents
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (ghost : GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientCovector
        period hPeriod configuration data analysis chartData regularity state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap
          period hPeriod ghost) =
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
        period hPeriod configuration data analysis chartData state ghost := by
  change regularity.covector state
      ((PhysicalGhostClosure period hPeriod).orthogonalProjectionOnto
        ((globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
          period hPeriod ghost : PhysicalGhostHilbert period hPeriod) :
            PhysicalGhostCarrier period hPeriod)) = _
  rw [(PhysicalGhostClosure period hPeriod
    ).orthogonalProjectionOnto_mem_subspace_eq_self]
  exact regularity.represents state ghost

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientCovector_contDiff
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData) :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (PhysicalGhostCarrier period hPeriod →L[Real] Real)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientCovector
        period hPeriod configuration data analysis chartData regularity) := by
  let projection :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2OrthogonalProjection
      period hPeriod
  exact @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (PhysicalGhostHilbert period hPeriod →L[Real] Real)
    (PhysicalGhostCarrier period hPeriod →L[Real] Real)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (projection.precomp Real) regularity.covector
    (@ContinuousLinearMap.contDiff Real
      (PhysicalGhostHilbert period hPeriod →L[Real] Real)
      (PhysicalGhostCarrier period hPeriod →L[Real] Real)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      inferInstance inferInstance inferInstance inferInstance ∞
      (projection.precomp Real))
    regularity.contDiff

/-- Gate 282: the minimal regularity datum has a canonical globally smooth
ambient `L²` extension that still represents the true Euler covector. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_physicalGhost_l2_euler_ambient_extension_gate
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData) :
    (∀ state ghost,
        globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientCovector
            period hPeriod configuration data analysis chartData regularity state
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap
              period hPeriod ghost) =
          globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
            period hPeriod configuration data analysis chartData state ghost) ∧
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (PhysicalGhostCarrier period hPeriod →L[Real] Real)
        inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientCovector
          period hPeriod configuration data analysis chartData regularity) :=
  ⟨fun state ghost =>
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientCovector_represents
        period hPeriod configuration data analysis chartData regularity state
          ghost,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientCovector_contDiff
      period hPeriod configuration data analysis chartData regularity⟩

end AmbientExtension
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerAmbientExtension4D
end JanusFormal
