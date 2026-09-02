import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D

/-!
# Analytic regularity data for the physical full-BRST ghost

This file isolates the missing analytic input: a globally smooth family of
continuous Euler covectors on the fixed closed paired `L²` carrier.  Agreement
on the dense test embedding makes such a family unique.  Its Riesz
representatives are then globally smooth.  Existence is not asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2Closure4D

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

/-- Minimal non-tautological analytic input for the physical-ghost coordinate:
a smooth continuous covector family on the fixed closed `L²` carrier that
represents the authentic Euler covector on every original test. -/
structure GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D where
  covector :
    FullChart period hPeriod configuration data analysis chartData →
      PhysicalGhostHilbert period hPeriod →L[Real] Real
  represents : ∀ state ghost,
    covector state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
          period hPeriod ghost) =
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
        period hPeriod configuration data analysis chartData state ghost
  contDiff : @ContDiff Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (PhysicalGhostHilbert period hPeriod →L[Real] Real)
    inferInstance inferInstance ∞ covector

def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D_of_smoothRieszRepresentative
    (representative :
      FullChart period hPeriod configuration data analysis chartData →
        PhysicalGhostHilbert period hPeriod)
    (pairing : ∀ state ghost,
      inner Real (representative state)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding
            period hPeriod ghost) =
        globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
          period hPeriod configuration data analysis chartData state ghost)
    (representative_contDiff : @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
        chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (PhysicalGhostHilbert period hPeriod) inferInstance inferInstance ∞
      representative) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
      period hPeriod configuration data analysis chartData where
  covector := fun state =>
    InnerProductSpace.toDual Real (PhysicalGhostHilbert period hPeriod)
      (representative state)
  represents := by
    intro state ghost
    exact pairing state ghost
  contDiff := by
    exact @ContDiff.comp Real
      (FullChart period hPeriod configuration data analysis chartData)
      (PhysicalGhostHilbert period hPeriod)
      (PhysicalGhostHilbert period hPeriod →L[Real] Real)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
        chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (PhysicalGhostHilbert period hPeriod))
      representative
      (@ContinuousLinearMap.contDiff Real
        (PhysicalGhostHilbert period hPeriod)
        (PhysicalGhostHilbert period hPeriod →L[Real] Real)
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        inferInstance inferInstance inferInstance inferInstance ∞
        (InnerProductSpace.toDual Real
          (PhysicalGhostHilbert period hPeriod)).toContinuousLinearEquiv.toContinuousLinearMap)
      representative_contDiff

/-- The continuous extension is unique because the original test embedding is
dense. -/
theorem physicalGhostL2EulerRegularityData_covector_unique
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.covector = second.covector := by
  funext state
  ext value
  have hFunctions :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2DenseEmbedding_denseRange
      period hPeriod).equalizer
        (first.covector state).continuous (second.covector state).continuous
        (by
          funext ghost
          exact (first.represents state ghost).trans
            (second.represents state ghost).symm)
  exact congrFun hFunctions value

/-- Riesz representative of the regular Euler covector on the fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PhysicalGhostHilbert period hPeriod :=
  (InnerProductSpace.toDual Real
    (PhysicalGhostHilbert period hPeriod)).symm (regularity.covector state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative_pairing
    (regularity :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData)
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : PhysicalGhostHilbert period hPeriod) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
          period hPeriod configuration data analysis chartData regularity state)
        test =
      regularity.covector state test := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
  exact InnerProductSpace.toDual_symm_apply

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative_contDiff
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
      (PhysicalGhostHilbert period hPeriod) inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
        period hPeriod configuration data analysis chartData regularity) := by
  exact @ContDiff.comp Real
    (FullChart period hPeriod configuration data analysis chartData)
    (PhysicalGhostHilbert period hPeriod →L[Real] Real)
    (PhysicalGhostHilbert period hPeriod)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance inferInstance inferInstance ∞
    (InnerProductSpace.toDual Real
      (PhysicalGhostHilbert period hPeriod)).symm
    regularity.covector
    (@ContinuousLinearMap.contDiff Real
      (PhysicalGhostHilbert period hPeriod →L[Real] Real)
      (PhysicalGhostHilbert period hPeriod)
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      inferInstance inferInstance inferInstance inferInstance ∞
      (InnerProductSpace.toDual Real
        (PhysicalGhostHilbert period hPeriod)).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    regularity.contDiff

/-- Gate 281: any globally smooth continuous physical-ghost Euler extension on
the fixed carrier is unique and has a globally smooth Riesz representative. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_physicalGhost_l2_euler_regularity_data_gate
    (first second :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
        period hPeriod configuration data analysis chartData) :
    first.covector = second.covector ∧
      @ContDiff Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (PhysicalGhostHilbert period hPeriod) inferInstance inferInstance ∞
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative
          period hPeriod configuration data analysis chartData first) :=
  ⟨physicalGhostL2EulerRegularityData_covector_unique period hPeriod
      configuration data analysis chartData first second,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2RieszRepresentative_contDiff
      period hPeriod configuration data analysis chartData first⟩

end RegularityData
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerRegularityData4D
end JanusFormal
