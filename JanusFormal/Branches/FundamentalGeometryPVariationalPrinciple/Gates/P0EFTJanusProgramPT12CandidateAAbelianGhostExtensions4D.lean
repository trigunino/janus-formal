import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalExtensionPair4D

/-! Actual ghost extensions, their graph intersection and the exact uniqueness frontier. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianGhostExtensions4D
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

open P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
open P0EFTJanusProgramPT12OffDiagonalClosure4D
open P0EFTJanusProgramPT12OffDiagonalCore4D

open P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
open P0EFTJanusProgramPT12OffDiagonalExtensionPair4D

/-- The actual FP minimal graph lies in the maximal adjoint of its formal-adjoint closure. -/
theorem candidateAFPCanonicalMinimal_le_formalAdjointAdjoint :
    candidateAFPCanonicalMinimal period hPeriod data ≤
      (candidateAFPFormalAdjointMinimal period hPeriod data).adjoint :=
  closed_formal_pair_reverse _ _
    (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)
    (candidateAFPCanonicalAdjoint_dense_domain period hPeriod data)
    (candidateAFPFormalAdjointMinimal_dense_domain period hPeriod data)
    (candidateAFPFormalAdjointMinimal_le_adjoint period hPeriod data)

/-- The complementary extension puts the maximal domain in the ghost slot. -/
def candidateAAbelianGhostDualOperator :
    CandidateAAbelianGhostL2 period hPeriod →ₗ.[Real] CandidateAAbelianGhostL2 period hPeriod :=
  offDiagonalOperator (candidateAFPFormalAdjointMinimal period hPeriod data).adjoint
    (candidateAFPFormalAdjointMinimal period hPeriod data)

theorem candidateAAbelianGhostDualOperator_domain_iff
    (input : CandidateAAbelianGhostL2 period hPeriod) :
    input ∈ (candidateAAbelianGhostDualOperator period hPeriod data).domain ↔
      input.fst ∈ (candidateAFPFormalAdjointMinimal period hPeriod data).domain ∧
        input.snd ∈ (candidateAFPFormalAdjointMinimal period hPeriod data).adjoint.domain :=
  offDiagonalOperator_domain_iff _ _ input

theorem candidateAAbelianGhostDualOperator_selfAdjoint :
    IsSelfAdjoint (candidateAAbelianGhostDualOperator period hPeriod data) :=
  formalPair_dualBlock_selfAdjoint (candidateAFPCanonicalMinimal period hPeriod data) _
    (candidateAFPFormalAdjointMinimal_isClosed period hPeriod data)
    (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)
    (candidateAFPFormalAdjointMinimal_dense_domain period hPeriod data)
    (candidateAFPCanonicalMinimal_le_formalAdjointAdjoint period hPeriod data)

theorem candidateAAbelianGhostDualOperator_isClosed :
    (candidateAAbelianGhostDualOperator period hPeriod data).IsClosed :=
  (candidateAAbelianGhostDualOperator_selfAdjoint period hPeriod data).isClosed

theorem candidateAAbelianGhostDualOperator_dense_domain :
    Dense ((candidateAAbelianGhostDualOperator period hPeriod data).domain :
      Set (CandidateAAbelianGhostL2 period hPeriod)) :=
  (candidateAAbelianGhostDualOperator_selfAdjoint period hPeriod data).dense_domain

theorem candidateAAbelianGhostMinimal_le_dual :
    candidateAAbelianGhostMinimal period hPeriod data ≤ candidateAAbelianGhostDualOperator period hPeriod data :=
  (offDiagonalOperator_le_iff _ _ _ _).mpr
    ⟨candidateAFPCanonicalMinimal_le_formalAdjointAdjoint period hPeriod data, le_rfl⟩

/-- The two extensions have precisely the minimal graph in common. -/
theorem candidateAAbelianGhostExtensions_graph_intersection :
    (candidateAAbelianGhostMinimal period hPeriod data).graph =
      (candidateAAbelianGhostOperator period hPeriod data).graph ⊓
        (candidateAAbelianGhostDualOperator period hPeriod data).graph :=
  formalPair_graph_intersection _ _
    (candidateAFPFormalAdjointMinimal_le_adjoint period hPeriod data)
    (candidateAFPCanonicalMinimal_le_formalAdjointAdjoint period hPeriod data)

theorem candidateAAbelianGhostExtensions_eq_iff :
    candidateAAbelianGhostOperator period hPeriod data = candidateAAbelianGhostDualOperator period hPeriod data ↔
      candidateAFPFormalAdjointMinimal period hPeriod data = (candidateAFPCanonicalMinimal period hPeriod data).adjoint :=
  formalPair_extensions_eq_iff _ _
    (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)
    (candidateAFPCanonicalAdjoint_dense_domain period hPeriod data)

theorem candidateAAbelianGhostMinimal_selfAdjoint_iff :
    IsSelfAdjoint (candidateAAbelianGhostMinimal period hPeriod data) ↔
      candidateAFPFormalAdjointMinimal period hPeriod data = (candidateAFPCanonicalMinimal period hPeriod data).adjoint :=
  formalPair_minimal_selfAdjoint_iff _ _
    (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)
    (candidateAFPCanonicalAdjoint_dense_domain period hPeriod data)
    (candidateAFPFormalAdjointMinimal_dense_domain period hPeriod data)

/-- Smooth-core density is also the exact uniqueness condition among all self-adjoint extensions. -/
theorem candidateAAbelianGhost_unique_extension_iff_hasCore :
    (∀ extension : CandidateAAbelianGhostL2 period hPeriod →ₗ.[Real] CandidateAAbelianGhostL2 period hPeriod,
      IsSelfAdjoint extension → candidateAAbelianGhostMinimal period hPeriod data ≤ extension →
        extension = candidateAAbelianGhostOperator period hPeriod data) ↔
      (candidateAAbelianGhostOperator period hPeriod data).HasCore (candidateAAbelianGhostSmoothCore period hPeriod) :=
  (formalPair_unique_extension_iff _ _
    (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPFormalAdjointMinimal_isClosed period hPeriod data)
    (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)
    (candidateAFPFormalAdjointMinimal_dense_domain period hPeriod data)
    (candidateAFPCanonicalAdjoint_dense_domain period hPeriod data)
    (candidateAFPFormalAdjointMinimal_le_adjoint period hPeriod data)).trans
      (candidateAAbelianGhostOperator_hasCore_iff period hPeriod data).symm

end
end P0EFTJanusProgramPT12CandidateAAbelianGhostExtensions4D
end JanusFormal
