import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SymmetricCongruenceAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GhostL2Reconstruction4D

/-! Self-adjoint signed ghost coordinates on the exact transported L2 domain. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianSignedGhostL2Operator4D
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

open P0EFTJanusProgramPT12UnboundedCongruence4D
open P0EFTJanusProgramPT12SymmetricCongruenceAdjoint4D
open P0EFTJanusProgramPT12GhostL2Reconstruction4D

def candidateAAbelianSignedGhostOperator :
    CandidateAAbelianGhostL2 period hPeriod →ₗ.[Real] CandidateAAbelianGhostL2 period hPeriod :=
  unboundedCongruence (candidateAAbelianGhostOperator period hPeriod data)
    (ghostL2Reconstruction (GlobalPairedGaugeLieL2 period hPeriod))

theorem candidateAAbelianSignedGhostOperator_domain_iff
    (input : CandidateAAbelianGhostL2 period hPeriod) :
    input ∈ (candidateAAbelianSignedGhostOperator period hPeriod data).domain ↔
    (1 / 2 : Real) • (input.fst + input.snd) ∈
      (candidateAFPCanonicalMinimal period hPeriod data).adjoint.domain ∧
    (1 / 2 : Real) • (input.fst - input.snd) ∈
      (candidateAFPCanonicalMinimal period hPeriod data).domain :=
  (unboundedCongruence_domain_iff _ _ input).trans
    (candidateAAbelianGhostOperator_domain_iff period hPeriod data _)

theorem candidateAAbelianSignedGhostOperator_selfAdjoint :
    IsSelfAdjoint (candidateAAbelianSignedGhostOperator period hPeriod data) :=
  unboundedCongruence_selfAdjoint _ _ (ghostL2Reconstruction_symmetric _)
    (candidateAAbelianGhostOperator_selfAdjoint period hPeriod data)

theorem candidateAAbelianSignedGhostOperator_isClosed :
    (candidateAAbelianSignedGhostOperator period hPeriod data).IsClosed :=
  (candidateAAbelianSignedGhostOperator_selfAdjoint period hPeriod data).isClosed

theorem candidateAAbelianSignedGhostOperator_dense_domain :
    Dense ((candidateAAbelianSignedGhostOperator period hPeriod data).domain :
      Set (CandidateAAbelianGhostL2 period hPeriod)) :=
  unboundedCongruence_dense_domain _ _ (candidateAAbelianGhostOperator_dense_domain period hPeriod data)

theorem candidateAAbelianGhostReconstruction_smooth
    (first second : GlobalPairedGaugeLieSmooth period hPeriod) :
    ghostL2Reconstruction (GlobalPairedGaugeLieL2 period hPeriod)
      (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod first,
        globalPairedGaugeLieL2LinearMap period hPeriod second)) =
    WithLp.toLp 2
      (globalPairedGaugeLieL2LinearMap period hPeriod ((1 / 2 : Real) • (first + second)),
        globalPairedGaugeLieL2LinearMap period hPeriod ((1 / 2 : Real) • (first - second))) := by
  rw [ghostL2Reconstruction_apply]
  simp only [map_smul, map_add, map_sub]
  rfl

theorem candidateAAbelianSignedGhostOperator_smooth_mem
    (first second : GlobalPairedGaugeLieSmooth period hPeriod) :
    WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod first,
      globalPairedGaugeLieL2LinearMap period hPeriod second) ∈
      (candidateAAbelianSignedGhostOperator period hPeriod data).domain := by
  apply (unboundedCongruence_domain_iff _ _ _).mpr
  rw [candidateAAbelianGhostReconstruction_smooth]
  exact candidateAAbelianGhostOperator_smooth_mem period hPeriod data _ _

/-- Exact congruence pairing on the entire transported operator domain. -/
theorem candidateAAbelianSignedGhostOperator_pairing
    (input : (candidateAAbelianSignedGhostOperator period hPeriod data).domain)
    (test : CandidateAAbelianGhostL2 period hPeriod) :
    inner Real (candidateAAbelianSignedGhostOperator period hPeriod data input) test =
    inner Real (candidateAAbelianGhostOperator period hPeriod data
      ⟨ghostL2Reconstruction (GlobalPairedGaugeLieL2 period hPeriod) input.val,
        (unboundedCongruence_domain_iff _ _ _).mp input.property⟩)
      (ghostL2Reconstruction (GlobalPairedGaugeLieL2 period hPeriod) test) :=
  unboundedCongruence_pairing _ _ (ghostL2Reconstruction_symmetric _) input test

end
end P0EFTJanusProgramPT12CandidateAAbelianSignedGhostL2Operator4D
end JanusFormal
