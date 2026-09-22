import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureAdjoint4D

/-! Exact weak domain and smooth action of the actual FP Hilbert adjoint. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D
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

theorem candidateAFPCanonicalAdjoint_pairing
    (field test : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real (globalPairedAbelianFPL2LinearMap period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) field)
      (globalPairedGaugeLieL2LinearMap period hPeriod test) =
    inner Real (globalPairedGaugeLieL2LinearMap period hPeriod field)
      (pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data) test) :=
  (congrArg (fun metric =>
    inner Real (globalPairedAbelianFPL2LinearMap period hPeriod metric field)
      (globalPairedGaugeLieL2LinearMap period hPeriod test) =
    inner Real (globalPairedGaugeLieL2LinearMap period hPeriod field)
      (pairedFPCanonicalAdjointL2 period hPeriod metric test))
    (candidateARegularMetricBySector_metric period hPeriod data)).mp
      (pairedFPCanonicalAdjoint_pairing period hPeriod
        (candidateARegularMetricBySector period hPeriod data) field test)

/-- The maximal adjoint graph is characterized by genuine smooth FP tests. -/
theorem candidateAFPCanonicalAdjoint_graph_iff
    (input output : GlobalPairedGaugeLieL2 period hPeriod) :
    (input, output) ∈ (candidateAFPCanonicalMinimal period hPeriod data).adjoint.graph ↔
    ∀ test, inner Real (globalPairedAbelianFPL2LinearMap period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) test) input =
      inner Real (globalPairedGaugeLieL2LinearMap period hPeriod test) output :=
  closedFeatureAdjoint_graph_iff _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)
    (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod) input output

theorem candidateAFPCanonicalAdjoint_domain_iff
    (input : GlobalPairedGaugeLieL2 period hPeriod) :
    input ∈ (candidateAFPCanonicalMinimal period hPeriod data).adjoint.domain ↔
    ∃ output, ∀ test, inner Real (globalPairedAbelianFPL2LinearMap period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) test) input =
      inner Real (globalPairedGaugeLieL2LinearMap period hPeriod test) output :=
  closedFeatureAdjoint_domain_iff _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)
    (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod) input

theorem candidateAFPCanonicalAdjoint_smooth_mem
    (test : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedGaugeLieL2LinearMap period hPeriod test ∈
      (candidateAFPCanonicalMinimal period hPeriod data).adjoint.domain :=
  closedFeatureAdjoint_smooth_mem _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)
    (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod) _
    (candidateAFPCanonicalAdjoint_pairing period hPeriod data) test

theorem candidateAFPCanonicalAdjoint_smooth_apply
    (test : GlobalPairedGaugeLieSmooth period hPeriod) :
    (candidateAFPCanonicalMinimal period hPeriod data).adjoint
      ⟨globalPairedGaugeLieL2LinearMap period hPeriod test,
        candidateAFPCanonicalAdjoint_smooth_mem period hPeriod data test⟩ =
      pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data) test :=
  closedFeatureAdjoint_smooth_apply _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)
    (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod) _
    (candidateAFPCanonicalAdjoint_pairing period hPeriod data) test

theorem candidateAFPCanonicalAdjoint_dense_domain :
    Dense ((candidateAFPCanonicalMinimal period hPeriod data).adjoint.domain :
      Set (GlobalPairedGaugeLieL2 period hPeriod)) :=
  closedFeatureAdjoint_dense_domain _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)
    (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod) _
    (candidateAFPCanonicalAdjoint_pairing period hPeriod data)

theorem candidateAFPCanonicalAdjoint_isClosed :
    (candidateAFPCanonicalMinimal period hPeriod data).adjoint.IsClosed :=
  LinearPMap.adjoint_isClosed (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)

end
end P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D
end JanusFormal
