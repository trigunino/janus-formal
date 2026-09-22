import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BRSTSaddleProduct4D

/-! Full abelian BRST: graph Lorenz potential, canonical L2 auxiliary and ghosts. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianMixedOperator4D
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

open P0EFTJanusProgramPT12BRSTSaddleProduct4D
open P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D

local instance (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :=
  globalPairedAbelianLorenzGraphCompleteSpace period hPeriod metric

/-- Only the potential has the Lorenz graph norm; B and both ghosts have their L2 norm. -/
abbrev CandidateAAbelianMixedHilbert := WithLp 2
  (WithLp 2 (GlobalPairedAbelianLorenzGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data) × GlobalPairedGaugeLieL2 period hPeriod) ×
    CandidateAAbelianGhostL2 period hPeriod)

def candidateAAbelianMixedOperator :
    CandidateAAbelianMixedHilbert period hPeriod data →ₗ.[Real]
      CandidateAAbelianMixedHilbert period hPeriod data :=
  brstSaddleProduct
    (globalPairedAbelianLorenzFeatureProjection period hPeriod (globalCandidateAMetricBySector period hPeriod data))
    (candidateAAbelianGhostOperator period hPeriod data)

theorem candidateAAbelianMixedOperator_selfAdjoint :
    IsSelfAdjoint (candidateAAbelianMixedOperator period hPeriod data) :=
  brstSaddleProduct_selfAdjoint _ _ (candidateAAbelianGhostOperator_selfAdjoint period hPeriod data)

theorem candidateAAbelianMixedOperator_isClosed :
    (candidateAAbelianMixedOperator period hPeriod data).IsClosed :=
  (candidateAAbelianMixedOperator_selfAdjoint period hPeriod data).isClosed

theorem candidateAAbelianMixedOperator_dense_domain :
    Dense ((candidateAAbelianMixedOperator period hPeriod data).domain :
      Set (CandidateAAbelianMixedHilbert period hPeriod data)) :=
  (candidateAAbelianMixedOperator_selfAdjoint period hPeriod data).dense_domain

theorem candidateAAbelianMixedOperator_domain_iff
    (x : CandidateAAbelianMixedHilbert period hPeriod data) :
    x ∈ (candidateAAbelianMixedOperator period hPeriod data).domain ↔
      x.snd.fst ∈ (candidateAFPCanonicalMinimal period hPeriod data).adjoint.domain ∧
      x.snd.snd ∈ (candidateAFPCanonicalMinimal period hPeriod data).domain := by
  rw [candidateAAbelianMixedOperator, brstSaddleProduct_domain_iff,
    candidateAAbelianGhostOperator_domain_iff]

/-- Concrete realization of all four smooth fields, without changing the potential. -/
def candidateAAbelianMixedSmooth (state : GlobalPairedAbelianBRSTState period hPeriod) :
    CandidateAAbelianMixedHilbert period hPeriod data :=
  WithLp.toLp 2 (WithLp.toLp 2
    (globalPairedAbelianLorenzSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) state.potential,
     globalPairedGaugeLieL2LinearMap period hPeriod (fun s => (state.nonminimal s).nakanishiLautrup.field)),
    WithLp.toLp 2
      (globalPairedGaugeLieL2LinearMap period hPeriod (fun s => (state.nonminimal s).antighost.field),
       globalPairedGaugeLieL2LinearMap period hPeriod (fun s => (state.nonminimal s).ghost.field)))

theorem candidateAAbelianMixedSmooth_mem (state : GlobalPairedAbelianBRSTState period hPeriod) :
    candidateAAbelianMixedSmooth period hPeriod data state ∈
      (candidateAAbelianMixedOperator period hPeriod data).domain := by
  rw [candidateAAbelianMixedOperator, brstSaddleProduct_domain_iff]
  exact candidateAAbelianGhostOperator_smooth_mem period hPeriod data _ _

end
end P0EFTJanusProgramPT12CandidateAAbelianMixedOperator4D
end JanusFormal
