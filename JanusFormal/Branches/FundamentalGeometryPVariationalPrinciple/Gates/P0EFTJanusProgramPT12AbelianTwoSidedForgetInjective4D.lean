import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFPClosable4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianTwoSidedSignedPairing4D

/-! Faithfulness of the two-sided graph readout from actual FP closability. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianTwoSidedForgetInjective4D
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D


local instance (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod metric

open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
set_option backward.isDefEq.respectTransparency false

open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D

open P0EFTJanusProgramPT12PairedFPClosable4D
open P0EFTJanusProgramPT12AbelianTwoSidedGhostGraph4D
open P0EFTJanusProgramPT12AbelianTwoSidedGhostRotation4D
open P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
open P0EFTJanusProgramPT12AbelianTwoSidedSignedPairing4D
open P0EFTJanusProgramPT12AbelianLorenzGraphShear4D

/-- The antighost and its actual FP image, read continuously from the strengthened graph. -/
def abelianTwoSidedAntighostFPFeatures
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    AbelianTwoSidedGraph period hPeriod metric →L[Real]
      (GlobalPairedGaugeLieL2 period hPeriod × GlobalPairedGaugeLieL2 period hPeriod) :=
  ((globalPairedAbelianOffShellAntighostProjection period hPeriod metric).comp
    (abelianTwoSidedForget period hPeriod metric)).prod
      ((WithLp.sndL 2 Real (GlobalPairedAbelianOffShellAmbient period hPeriod)
        (GlobalPairedGaugeLieL2 period hPeriod)).comp
        (abelianTwoSidedGraphSubmodule period hPeriod metric).subtypeL)

theorem abelianTwoSidedAntighostFPFeatures_mem_graph
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (vector : AbelianTwoSidedGraph period hPeriod metric) :
    abelianTwoSidedAntighostFPFeatures period hPeriod metric vector ∈
      CanonicalPairedFPGraph period hPeriod metric := by
  refine (abelianTwoSidedSmoothEmbedding_denseRange period hPeriod metric).induction_on
    (p := fun x => abelianTwoSidedAntighostFPFeatures period hPeriod metric x ∈
      CanonicalPairedFPGraph period hPeriod metric) vector ?_ ?_
  · exact (globalPairedGaugeLieL2LinearMap period hPeriod |>.prod
      (globalPairedAbelianFPL2LinearMap period hPeriod metric)).range.isClosed_topologicalClosure.preimage
        (abelianTwoSidedAntighostFPFeatures period hPeriod metric).continuous
  · intro state
    exact (globalPairedGaugeLieL2LinearMap period hPeriod |>.prod
      (globalPairedAbelianFPL2LinearMap period hPeriod metric)).range.le_topologicalClosure
        ⟨abelianAntighost period hPeriod state, rfl⟩

/-- FP closability removes every possible vertical extra coordinate. -/
theorem abelianTwoSidedForget_injective
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod) :
    Function.Injective (abelianTwoSidedForget period hPeriod (fun sector => (metric sector).metric)) := by
  intro first second hForget
  let features := abelianTwoSidedAntighostFPFeatures period hPeriod (fun sector => (metric sector).metric)
  let firstGraph : CanonicalPairedFPGraph period hPeriod (fun sector => (metric sector).metric) :=
    ⟨features first, abelianTwoSidedAntighostFPFeatures_mem_graph period hPeriod _ first⟩
  let secondGraph : CanonicalPairedFPGraph period hPeriod (fun sector => (metric sector).metric) :=
    ⟨features second, abelianTwoSidedAntighostFPFeatures_mem_graph period hPeriod _ second⟩
  have hInput : firstGraph.val.1 = secondGraph.val.1 :=
    congrArg (globalPairedAbelianOffShellAntighostProjection period hPeriod
      (fun sector => (metric sector).metric)) hForget
  have hGraph := canonicalPairedFPGraph_input_injective period hPeriod metric hInput
  have hOutput := congrArg (fun graph => graph.val.2) hGraph
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  exact Prod.ext (congrArg Subtype.val hForget) hOutput

/-- The continuous signed realization is now faithful as well as dense. -/
theorem abelianTwoSidedSignedRealization_injective
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod) :
    Function.Injective (abelianTwoSidedSignedRealization period hPeriod (fun sector => (metric sector).metric)) := by
  intro first second hEqual
  apply (abelianTwoSidedGhostRotation period hPeriod (fun sector => (metric sector).metric)).symm.injective
  apply abelianTwoSidedForget_injective period hPeriod metric
  exact (abelianLorenzGraphShear period hPeriod (fun sector => (metric sector).metric)).injective hEqual

end
end P0EFTJanusProgramPT12AbelianTwoSidedForgetInjective4D
end JanusFormal
