import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianFaithfulRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GraphClosureEstimate4D

/-! The actual Candidate-A FP as a minimal closed operator in canonical L2. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D
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

/-- Closure of the genuine smooth FP graph, using the actual two gravity metrics. -/
def candidateAFPCanonicalMinimal :
    GlobalPairedGaugeLieL2 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  closedFeatureOperator (globalPairedGaugeLieL2LinearMap period hPeriod)
    (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data))

theorem candidateAFPCanonicalMinimal_graph :
    (candidateAFPCanonicalMinimal period hPeriod data).graph =
      CanonicalPairedFPGraph period hPeriod (globalCandidateAMetricBySector period hPeriod data) :=
  closedFeatureOperator_graph _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)

theorem candidateAFPCanonicalMinimal_isClosed :
    (candidateAFPCanonicalMinimal period hPeriod data).IsClosed :=
  closedFeatureOperator_isClosed _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)

theorem candidateAFPCanonicalMinimal_dense_domain :
    Dense ((candidateAFPCanonicalMinimal period hPeriod data).domain :
      Set (GlobalPairedGaugeLieL2 period hPeriod)) :=
  closedFeatureOperator_dense_domain _ _ (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod)

theorem candidateAFPCanonicalMinimal_smooth_mem
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedGaugeLieL2LinearMap period hPeriod field ∈
      (candidateAFPCanonicalMinimal period hPeriod data).domain :=
  closedFeatureOperator_smooth_mem _ _ field

theorem candidateAFPCanonicalMinimal_smooth_apply
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    candidateAFPCanonicalMinimal period hPeriod data
      ⟨globalPairedGaugeLieL2LinearMap period hPeriod field,
        candidateAFPCanonicalMinimal_smooth_mem period hPeriod data field⟩ =
      globalPairedAbelianFPL2LinearMap period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) field :=
  closedFeatureOperator_smooth_apply _ _ (candidateAPairedFPGraph_input_injective period hPeriod data) field

/-- No smaller closed L2 extension can contain the actual smooth FP action. -/
theorem candidateAFPCanonicalMinimal_le_closed_extension
    (extension : GlobalPairedGaugeLieL2 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod)
    (hClosed : extension.IsClosed)
    (hExtends : ∀ field, (globalPairedGaugeLieL2LinearMap period hPeriod field,
      globalPairedAbelianFPL2LinearMap period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) field) ∈ extension.graph) :
    candidateAFPCanonicalMinimal period hPeriod data ≤ extension :=
  closedFeatureOperator_minimal _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)
    extension hClosed hExtends

/-- A smooth a priori estimate suffices for both analytic properties of the minimal actual FP.
The estimate remains an explicit obligation; no spectral or ellipticity hypothesis is inserted. -/
theorem candidateAFPCanonicalMinimal_finite_observation
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
    (observation : GlobalPairedGaugeLieL2 period hPeriod →L[Real] F) (C : NNReal)
    (hEstimate : ∀ field : GlobalPairedGaugeLieSmooth period hPeriod,
      ‖globalPairedGaugeLieL2LinearMap period hPeriod field‖ ≤ C *
        (‖globalPairedAbelianFPL2LinearMap period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) field‖ +
          ‖observation (globalPairedGaugeLieL2LinearMap period hPeriod field)‖)) :
    IsClosed (LinearMap.range (candidateAFPCanonicalMinimal period hPeriod data).toFun :
      Set (GlobalPairedGaugeLieL2 period hPeriod)) ∧
    FiniteDimensional Real (LinearMap.ker (candidateAFPCanonicalMinimal period hPeriod data).toFun) :=
  P0EFTJanusProgramPT12GraphClosureEstimate4D.closedFeatureOperator_finite_observation _ _
    (candidateAPairedFPGraph_input_injective period hPeriod data) observation C hEstimate

end
end P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D
end JanusFormal
