import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D

/-! The self-adjoint L2 ghost block represents the actual smooth Hessian. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D
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
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D

open P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D
open P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D
open P0EFTJanusProgramPT12GhostRotationDefect4D

/-- Exact Hessian pairing on the genuine smooth ghost states of Candidate A. -/
theorem candidateAAbelianGhostOperator_smooth_hessian
    (a c b d : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real
      (candidateAAbelianGhostOperator period hPeriod data
        ⟨WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod a,
          globalPairedGaugeLieL2LinearMap period hPeriod c),
          candidateAAbelianGhostOperator_smooth_mem period hPeriod data a c⟩)
      (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod b,
        globalPairedGaugeLieL2LinearMap period hPeriod d)) =
    globalPairedAbelianOffShellHessian period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        (pureAbelianGhostPair period hPeriod a c))
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        (pureAbelianGhostPair period hPeriod b d)) := by
  rw [candidateAAbelianGhostOperator_smooth_apply, pureAbelianGhostPair_hessian]
  change inner Real (globalPairedAbelianFPL2LinearMap period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) c)
      (globalPairedGaugeLieL2LinearMap period hPeriod b) +
    inner Real (pairedFPCanonicalAdjointL2 period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) a)
      (globalPairedGaugeLieL2LinearMap period hPeriod d) = _
  have hAdj : inner Real (pairedFPCanonicalAdjointL2 period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) a)
      (globalPairedGaugeLieL2LinearMap period hPeriod d) =
    inner Real (globalPairedGaugeLieL2LinearMap period hPeriod a)
      (globalPairedAbelianFPL2LinearMap period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) d) :=
    (real_inner_comm _ _).trans
      ((candidateAFPCanonicalAdjoint_pairing period hPeriod data d a).symm.trans
        (real_inner_comm _ _))
  rw [hAdj, ghostCrossPairing, add_comm]

/-- Smooth ghost pairs form a dense test family in the canonical product L2. -/
theorem candidateAAbelianGhostSmooth_denseRange :
    DenseRange (fun pair : GlobalPairedGaugeLieSmooth period hPeriod × GlobalPairedGaugeLieSmooth period hPeriod =>
      WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod pair.1,
        globalPairedGaugeLieL2LinearMap period hPeriod pair.2)) := by
  have hDense := (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod).prodMap
    (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod)
  exact (WithLp.prodContinuousLinearEquiv 2 Real
    (GlobalPairedGaugeLieL2 period hPeriod) (GlobalPairedGaugeLieL2 period hPeriod)).symm.surjective.denseRange.comp
      hDense (WithLp.prodContinuousLinearEquiv 2 Real
        (GlobalPairedGaugeLieL2 period hPeriod) (GlobalPairedGaugeLieL2 period hPeriod)).symm.continuous

end
end P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D
end JanusFormal
