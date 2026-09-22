import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalCore4D

/-! Exact closure of the actual smooth ghost block and the remaining adjoint core equality. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
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

/-- Both slots range over genuine smooth paired gauge fields. -/
def candidateAAbelianGhostSmoothCore : Submodule Real (CandidateAAbelianGhostL2 period hPeriod) :=
  pairedCore (globalPairedGaugeLieL2LinearMap period hPeriod).range

/-- The minimal graph closure uses the minimal formal adjoint in the antighost slot. -/
def candidateAAbelianGhostMinimal :
    CandidateAAbelianGhostL2 period hPeriod →ₗ.[Real] CandidateAAbelianGhostL2 period hPeriod :=
  offDiagonalOperator (candidateAFPCanonicalMinimal period hPeriod data)
    (candidateAFPFormalAdjointMinimal period hPeriod data)

theorem candidateAAbelianGhostMinimal_isClosed :
    (candidateAAbelianGhostMinimal period hPeriod data).IsClosed :=
  offDiagonalOperator_isClosed _ _ (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPFormalAdjointMinimal_isClosed period hPeriod data)

theorem candidateAAbelianGhostMinimal_dense_domain :
    Dense ((candidateAAbelianGhostMinimal period hPeriod data).domain :
      Set (CandidateAAbelianGhostL2 period hPeriod)) :=
  offDiagonalOperator_dense_domain _ _ (candidateAFPCanonicalMinimal_dense_domain period hPeriod data)
    (candidateAFPFormalAdjointMinimal_dense_domain period hPeriod data)

theorem candidateAAbelianGhostMinimal_le_selfAdjoint :
    candidateAAbelianGhostMinimal period hPeriod data ≤ candidateAAbelianGhostOperator period hPeriod data := by
  apply LinearPMap.le_of_le_graph
  intro pair hPair
  have h := (offDiagonalOperator_mem_graph_iff _ _ _ _).mp hPair
  exact (offDiagonalOperator_mem_graph_iff _ _ _ _).mpr
    ⟨h.1, LinearPMap.le_graph_of_le (candidateAFPFormalAdjointMinimal_le_adjoint period hPeriod data) h.2⟩

theorem candidateAAbelianGhostMinimal_symmetric :
    (candidateAAbelianGhostMinimal period hPeriod data).IsFormalAdjoint
      (candidateAAbelianGhostMinimal period hPeriod data) := by
  have hLe := candidateAAbelianGhostMinimal_le_selfAdjoint period hPeriod data
  have hFormal := LinearPMap.adjoint_isFormalAdjoint
    (candidateAAbelianGhostOperator_dense_domain period hPeriod data)
  rw [LinearPMap.isSelfAdjoint_def.mp
    (candidateAAbelianGhostOperator_selfAdjoint period hPeriod data)] at hFormal
  intro first second
  let firstLift : (candidateAAbelianGhostOperator period hPeriod data).domain :=
    ⟨first.val, hLe.1 first.property⟩
  let secondLift : (candidateAAbelianGhostOperator period hPeriod data).domain :=
    ⟨second.val, hLe.1 second.property⟩
  have hFirst := hLe.2 (x := first) (y := firstLift) rfl
  have hSecond := hLe.2 (x := second) (y := secondLift) rfl
  exact (congrArg (fun value => inner Real value second.val) hFirst).trans
    ((hFormal firstLift secondLift).trans
      (congrArg (fun value => inner Real first.val value) hSecond.symm))

theorem candidateAAbelianGhostMinimal_hasCore :
    (candidateAAbelianGhostMinimal period hPeriod data).HasCore
      (candidateAAbelianGhostSmoothCore period hPeriod) := by
  apply (offDiagonalOperator_hasCore_iff _ _
    (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPFormalAdjointMinimal_isClosed period hPeriod data) _
    (candidateAFPCanonicalMinimal_hasCore period hPeriod data)
    (candidateAFPFormalAdjointMinimal_hasCore period hPeriod data).le_domain).mpr
  exact candidateAFPFormalAdjointMinimal_hasCore period hPeriod data

/-- The smooth block closure is computed, rather than identified with its extension by assumption. -/
theorem candidateAAbelianGhost_smoothClosure_eq_minimal :
    ((candidateAAbelianGhostOperator period hPeriod data).domRestrict
      (candidateAAbelianGhostSmoothCore period hPeriod)).closure =
      candidateAAbelianGhostMinimal period hPeriod data := by
  let first := candidateAFPCanonicalMinimal period hPeriod data
  let second := first.adjoint
  let core := (globalPairedGaugeLieL2LinearMap period hPeriod).range
  have hFirstRestrict : first.domRestrict core ≤ first := LinearPMap.domRestrict_le
  have hSecondRestrict : second.domRestrict core ≤ second := LinearPMap.domRestrict_le
  change ((offDiagonalOperator first second).domRestrict (pairedCore core)).closure = _
  rw [offDiagonalOperator_restriction, offDiagonalOperator_closure _ _
    ((candidateAFPCanonicalMinimal_isClosed period hPeriod data).isClosable.leIsClosable hFirstRestrict)
    ((candidateAFPCanonicalAdjoint_isClosed period hPeriod data).isClosable.leIsClosable hSecondRestrict)]
  exact congrArg₂ offDiagonalOperator
    (candidateAFPCanonicalMinimal_hasCore period hPeriod data).closure_eq
    (smoothRestriction_closure_eq _ _ (candidateAFPFormalAdjointGraph_input_injective period hPeriod data) _
      (candidateAFPCanonicalAdjoint_isClosed period hPeriod data)
      (candidateAFPCanonicalAdjoint_smooth_mem period hPeriod data)
      (candidateAFPCanonicalAdjoint_smooth_apply period hPeriod data))

/-- Exactly one analytic equality remains for the full smooth ghost core. -/
theorem candidateAAbelianGhostOperator_hasCore_iff :
    (candidateAAbelianGhostOperator period hPeriod data).HasCore
      (candidateAAbelianGhostSmoothCore period hPeriod) ↔
    candidateAFPFormalAdjointMinimal period hPeriod data =
      (candidateAFPCanonicalMinimal period hPeriod data).adjoint := by
  have hMem : (globalPairedGaugeLieL2LinearMap period hPeriod).range ≤
      (candidateAFPCanonicalMinimal period hPeriod data).adjoint.domain := by
    rintro _ ⟨field, rfl⟩
    exact candidateAFPCanonicalAdjoint_smooth_mem period hPeriod data field
  exact (offDiagonalOperator_hasCore_iff _ _
    (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPCanonicalAdjoint_isClosed period hPeriod data) _
    (candidateAFPCanonicalMinimal_hasCore period hPeriod data) hMem).trans
      (candidateAFPCanonicalAdjoint_hasCore_iff period hPeriod data)

end
end P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
end JanusFormal
