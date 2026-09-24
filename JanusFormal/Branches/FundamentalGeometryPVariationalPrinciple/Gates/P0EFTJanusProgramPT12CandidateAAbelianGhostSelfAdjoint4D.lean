import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalFredholm4D

/-! The actual abelian ghost block on canonical L2, with its full adjoint domain. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D
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

/-- The two ghost slots carry the canonical product Hilbert norm. -/
abbrev CandidateAAbelianGhostL2 := WithLp 2
  (GlobalPairedGaugeLieL2 period hPeriod × GlobalPairedGaugeLieL2 period hPeriod)

/-- Output slots are FP(ghost) and FP†(antighost). -/
def candidateAAbelianGhostOperator :
    CandidateAAbelianGhostL2 period hPeriod →ₗ.[Real] CandidateAAbelianGhostL2 period hPeriod :=
  offDiagonalOperator (candidateAFPCanonicalMinimal period hPeriod data)
    (candidateAFPCanonicalMinimal period hPeriod data).adjoint

theorem candidateAAbelianGhostOperator_domain_iff
    (input : CandidateAAbelianGhostL2 period hPeriod) :
    input ∈ (candidateAAbelianGhostOperator period hPeriod data).domain ↔
    input.fst ∈ (candidateAFPCanonicalMinimal period hPeriod data).adjoint.domain ∧
    input.snd ∈ (candidateAFPCanonicalMinimal period hPeriod data).domain :=
  offDiagonalOperator_domain_iff _ _ input

theorem candidateAAbelianGhostOperator_selfAdjoint :
    IsSelfAdjoint (candidateAAbelianGhostOperator period hPeriod data) :=
  offDiagonalOperator_selfAdjoint _
    (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)
    (candidateAFPCanonicalAdjoint_dense_domain period hPeriod data)

theorem candidateAAbelianGhostOperator_isClosed :
    (candidateAAbelianGhostOperator period hPeriod data).IsClosed :=
  (candidateAAbelianGhostOperator_selfAdjoint period hPeriod data).isClosed

theorem candidateAAbelianGhostOperator_dense_domain :
    Dense ((candidateAAbelianGhostOperator period hPeriod data).domain :
      Set (CandidateAAbelianGhostL2 period hPeriod)) :=
  offDiagonalOperator_dense_domain _ _
    (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)
    (candidateAFPCanonicalAdjoint_dense_domain period hPeriod data)

theorem candidateAAbelianGhostOperator_smooth_mem
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod antighost,
      globalPairedGaugeLieL2LinearMap period hPeriod ghost) ∈
      (candidateAAbelianGhostOperator period hPeriod data).domain :=
  (candidateAAbelianGhostOperator_domain_iff period hPeriod data _).mpr
    ⟨candidateAFPCanonicalAdjoint_smooth_mem period hPeriod data antighost,
      candidateAFPCanonicalMinimal_smooth_mem period hPeriod data ghost⟩

theorem candidateAAbelianGhostOperator_smooth_apply
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    candidateAAbelianGhostOperator period hPeriod data
      ⟨WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod antighost,
        globalPairedGaugeLieL2LinearMap period hPeriod ghost),
        candidateAAbelianGhostOperator_smooth_mem period hPeriod data antighost ghost⟩ =
    WithLp.toLp 2
      (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data) ghost,
        pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data) antighost) := by
  change offDiagonalOperator (candidateAFPCanonicalMinimal period hPeriod data)
    (candidateAFPCanonicalMinimal period hPeriod data).adjoint _ = _
  rw [offDiagonalOperator_apply]
  exact congrArg (WithLp.toLp 2) (Prod.ext
    (candidateAFPCanonicalMinimal_smooth_apply period hPeriod data ghost)
    (candidateAFPCanonicalAdjoint_smooth_apply period hPeriod data antighost))

/-- The adjoint introduces no independent closed-range obligation. -/
theorem candidateAAbelianGhostOperator_range_isClosed_iff :
    IsClosed (LinearMap.range (candidateAAbelianGhostOperator period hPeriod data).toFun :
      Set (CandidateAAbelianGhostL2 period hPeriod)) ↔
    IsClosed (LinearMap.range (candidateAFPCanonicalMinimal period hPeriod data).toFun :
      Set (GlobalPairedGaugeLieL2 period hPeriod)) :=
  P0EFTJanusProgramPT12OffDiagonalFredholm4D.offDiagonalAdjoint_range_isClosed_iff _
    (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)
    (candidateAFPCanonicalAdjoint_dense_domain period hPeriod data)

/-- Exact remaining FP conditions, without identifying minimal and maximal domains. -/
theorem candidateAAbelianGhostOperator_fredholm_iff :
    let ghost := candidateAAbelianGhostOperator period hPeriod data
    let fp := candidateAFPCanonicalMinimal period hPeriod data
    (IsClosed (LinearMap.range ghost.toFun : Set (CandidateAAbelianGhostL2 period hPeriod)) ∧
      FiniteDimensional Real (LinearMap.ker ghost.toFun) ∧
      FiniteDimensional Real (CandidateAAbelianGhostL2 period hPeriod ⧸ LinearMap.range ghost.toFun)) ↔
    (IsClosed (LinearMap.range fp.toFun : Set (GlobalPairedGaugeLieL2 period hPeriod)) ∧
      FiniteDimensional Real (LinearMap.ker fp.toFun) ∧
      FiniteDimensional Real (LinearMap.ker fp.adjoint.toFun)) :=
  P0EFTJanusProgramPT12OffDiagonalFredholm4D.offDiagonalAdjoint_fredholm_iff _
    (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)
    (candidateAFPCanonicalAdjoint_dense_domain period hPeriod data)

end
end P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D
end JanusFormal
