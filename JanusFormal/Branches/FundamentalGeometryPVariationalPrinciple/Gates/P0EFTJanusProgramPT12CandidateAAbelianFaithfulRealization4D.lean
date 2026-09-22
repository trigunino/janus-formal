import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianTwoSidedForgetInjective4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianTwoSidedSignedPairing4D

/-! Faithful signed abelian realization for the actual Candidate-A metrics. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianFaithfulRealization4D
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

/-- Regularity is already part of the actual gravity data in both sectors. -/
def candidateARegularMetricBySector :
    Sector → RegularGeneralLorentzMetric period hPeriod
  | .plus => data.plusGravity.metric
  | .minus => data.minusGravity.metric

theorem candidateARegularMetricBySector_metric :
    (fun sector => (candidateARegularMetricBySector period hPeriod data sector).metric) =
      globalCandidateAMetricBySector period hPeriod data := by
  funext sector
  cases sector <;> rfl

/-- The actual paired FP graph has no vertical ambiguity in canonical L². -/
theorem candidateAPairedFPGraph_input_injective :
    Function.Injective (fun graph : CanonicalPairedFPGraph period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) => graph.val.1) := by
  exact (congrArg (fun metric => Function.Injective
    (fun graph : CanonicalPairedFPGraph period hPeriod metric => graph.val.1))
      (candidateARegularMetricBySector_metric period hPeriod data)).mp
        (canonicalPairedFPGraph_input_injective period hPeriod
          (candidateARegularMetricBySector period hPeriod data))

/-- Forgetting the additional antighost FP coordinate loses no actual graph vector. -/
theorem candidateAAbelianTwoSidedForget_injective :
    Function.Injective (abelianTwoSidedForget period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)) := by
  exact (congrArg (fun metric => Function.Injective
    (abelianTwoSidedForget period hPeriod metric))
      (candidateARegularMetricBySector_metric period hPeriod data)).mp
        (abelianTwoSidedForget_injective period hPeriod
          (candidateARegularMetricBySector period hPeriod data))

/-- The signed realization is faithful for the actual Candidate-A action. -/
theorem candidateAAbelianSignedRealization_injective :
    Function.Injective (abelianTwoSidedSignedRealization period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)) := by
  exact (congrArg (fun metric => Function.Injective
    (abelianTwoSidedSignedRealization period hPeriod metric))
      (candidateARegularMetricBySector_metric period hPeriod data)).mp
        (abelianTwoSidedSignedRealization_injective period hPeriod
          (candidateARegularMetricBySector period hPeriod data))

end
end P0EFTJanusProgramPT12CandidateAAbelianFaithfulRealization4D
end JanusFormal
