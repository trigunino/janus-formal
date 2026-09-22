import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D

/-! Minimal closure of the actual formal adjoint and its precise smooth-core criterion. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
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

open P0EFTJanusProgramPT12AbelianTwoSidedForgetInjective4D

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (data : GlobalCandidateAActionData period hPeriod configuration couplings
  NonNullFace NullFace)

open P0EFTJanusProgramPT12CandidateAAbelianFaithfulRealization4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D

open P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D
open P0EFTJanusProgramPT12ClosedFeatureAdjoint4D

open P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D

/-- The minimal closure of r FP(r⁻¹ ·), distinguished from the maximal Hilbert adjoint. -/
def candidateAFPFormalAdjointMinimal :
    GlobalPairedGaugeLieL2 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  closedFeatureOperator (globalPairedGaugeLieL2LinearMap period hPeriod)
    (pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data))

theorem candidateAFPFormalAdjoint_smooth_graph
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    (globalPairedGaugeLieL2LinearMap period hPeriod field,
      pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data) field) ∈
      (candidateAFPCanonicalMinimal period hPeriod data).adjoint.graph :=
  ((candidateAFPCanonicalMinimal period hPeriod data).adjoint.mem_graph_iff).mpr
    ⟨⟨_, candidateAFPCanonicalAdjoint_smooth_mem period hPeriod data field⟩, rfl,
      candidateAFPCanonicalAdjoint_smooth_apply period hPeriod data field⟩

theorem candidateAFPFormalAdjointGraph_input_injective :
    Function.Injective (fun graph : linearFeatureGraphClosure
      (globalPairedGaugeLieL2LinearMap period hPeriod)
      (pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data)) => graph.val.1) :=
  featureClosure_injective_of_closed_extension _ _ _
    (candidateAFPCanonicalAdjoint_isClosed period hPeriod data)
    (candidateAFPFormalAdjoint_smooth_graph period hPeriod data)

theorem candidateAFPFormalAdjointMinimal_isClosed :
    (candidateAFPFormalAdjointMinimal period hPeriod data).IsClosed :=
  closedFeatureOperator_isClosed _ _ (candidateAFPFormalAdjointGraph_input_injective period hPeriod data)

theorem candidateAFPFormalAdjointMinimal_dense_domain :
    Dense ((candidateAFPFormalAdjointMinimal period hPeriod data).domain :
      Set (GlobalPairedGaugeLieL2 period hPeriod)) :=
  closedFeatureOperator_dense_domain _ _ (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod)

theorem candidateAFPFormalAdjointMinimal_smooth_mem
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedGaugeLieL2LinearMap period hPeriod field ∈
      (candidateAFPFormalAdjointMinimal period hPeriod data).domain :=
  closedFeatureOperator_smooth_mem _ _ field

theorem candidateAFPFormalAdjointMinimal_smooth_apply
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    candidateAFPFormalAdjointMinimal period hPeriod data
      ⟨globalPairedGaugeLieL2LinearMap period hPeriod field,
        candidateAFPFormalAdjointMinimal_smooth_mem period hPeriod data field⟩ =
    pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data) field :=
  closedFeatureOperator_smooth_apply _ _ (candidateAFPFormalAdjointGraph_input_injective period hPeriod data) field

theorem candidateAFPFormalAdjointMinimal_le_adjoint :
    candidateAFPFormalAdjointMinimal period hPeriod data ≤
      (candidateAFPCanonicalMinimal period hPeriod data).adjoint :=
  closedFeatureOperator_minimal _ _ (candidateAFPFormalAdjointGraph_input_injective period hPeriod data) _
    (candidateAFPCanonicalAdjoint_isClosed period hPeriod data)
    (candidateAFPFormalAdjoint_smooth_graph period hPeriod data)

theorem candidateAFPFormalAdjointMinimal_hasCore :
    (candidateAFPFormalAdjointMinimal period hPeriod data).HasCore
      (globalPairedGaugeLieL2LinearMap period hPeriod).range :=
  closedFeatureOperator_hasCore _ _ (candidateAFPFormalAdjointGraph_input_injective period hPeriod data)

theorem candidateAFPCanonicalMinimal_hasCore :
    (candidateAFPCanonicalMinimal period hPeriod data).HasCore
      (globalPairedGaugeLieL2LinearMap period hPeriod).range :=
  closedFeatureOperator_hasCore _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)

/-- The missing approximation statement is exactly minimal/maximal equality. -/
theorem candidateAFPCanonicalAdjoint_hasCore_iff :
    (candidateAFPCanonicalMinimal period hPeriod data).adjoint.HasCore
      (globalPairedGaugeLieL2LinearMap period hPeriod).range ↔
    candidateAFPFormalAdjointMinimal period hPeriod data =
      (candidateAFPCanonicalMinimal period hPeriod data).adjoint :=
  smoothRange_hasCore_iff _ _ (candidateAFPFormalAdjointGraph_input_injective period hPeriod data) _
    (candidateAFPCanonicalAdjoint_isClosed period hPeriod data)
    (candidateAFPCanonicalAdjoint_smooth_mem period hPeriod data)
    (candidateAFPCanonicalAdjoint_smooth_apply period hPeriod data)

end
end P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
end JanusFormal
