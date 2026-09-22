import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BRSTSaddleProduct4D

/-! Full abelian BRST: graph Lorenz potential, canonical L2 auxiliary and ghosts. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianMixedMinimal4D
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

open P0EFTJanusProgramPT12CandidateAAbelianMixedOperator4D

open P0EFTJanusProgramPT12CandidateAAbelianMixedSmooth4D
open P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
open P0EFTJanusProgramPT12ProductCore4D
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12ProductClosure4D
open P0EFTJanusProgramPT12ProductSelfAdjoint4D
open P0EFTJanusProgramPT12OffDiagonalCore4D

/-- The independent smooth potential and Nakanishi--Lautrup fields. -/
def candidateAAbelianNonminimalSmooth :
    (GlobalPairedAbelianPotentialSmooth period hPeriod × GlobalPairedGaugeLieSmooth period hPeriod) →ₗ[Real]
    WithLp 2 (GlobalPairedAbelianLorenzGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) × GlobalPairedGaugeLieL2 period hPeriod) :=
  (WithLp.prodContinuousLinearEquiv 2 Real _ _).symm.toLinearMap.comp
    ((globalPairedAbelianLorenzSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)).prodMap (globalPairedGaugeLieL2LinearMap period hPeriod))

theorem candidateAAbelianNonminimalSmooth_denseRange :
    DenseRange (candidateAAbelianNonminimalSmooth period hPeriod data) :=
  (WithLp.prodContinuousLinearEquiv 2 Real _ _).symm.surjective.denseRange.comp
    ((globalPairedAbelianLorenzSmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)).prodMap (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod))
    (WithLp.prodContinuousLinearEquiv 2 Real _ _).symm.continuous

theorem candidateAAbelianMixedSmooth_range :
    (candidateAAbelianMixedSmoothLinearMap period hPeriod data).range =
      productCore (candidateAAbelianNonminimalSmooth period hPeriod data).range
        (candidateAAbelianGhostSmoothCore period hPeriod) := by
  ext x
  constructor
  · rintro ⟨state, rfl⟩
    exact ⟨⟨(state.potential, fun s => (state.nonminimal s).nakanishiLautrup.field), rfl⟩,
      ⟨fun s => (state.nonminimal s).antighost.field, rfl⟩,
      ⟨fun s => (state.nonminimal s).ghost.field, rfl⟩⟩
  · rintro ⟨⟨p, hp⟩, ⟨a, ha⟩, ⟨c, hc⟩⟩
    refine ⟨⟨p.1, fun s => ⟨⟨c s⟩, ⟨a s⟩, ⟨p.2 s⟩⟩⟩, ?_⟩
    apply WithLp.ofLp_injective 2
    apply Prod.ext hp
    apply WithLp.ofLp_injective 2
    exact Prod.ext ha hc

/-- Minimal closed BRST: the antighost uses the minimal formal adjoint. -/
def candidateAAbelianMixedMinimal : CandidateAAbelianMixedHilbert period hPeriod data →ₗ.[Real]
    CandidateAAbelianMixedHilbert period hPeriod data :=
  brstSaddleProduct (globalPairedAbelianLorenzFeatureProjection period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)) (candidateAAbelianGhostMinimal period hPeriod data)

theorem candidateAAbelianMixedMinimal_isClosed : (candidateAAbelianMixedMinimal period hPeriod data).IsClosed :=
  productOperator_isClosed _ _
    (bounded_toPMap_selfAdjoint _ (nonminimalSaddle_symmetric _)).isClosed
    (candidateAAbelianGhostMinimal_isClosed period hPeriod data)

theorem candidateAAbelianMixedMinimal_hasCore : (candidateAAbelianMixedMinimal period hPeriod data).HasCore
    (candidateAAbelianMixedSmoothLinearMap period hPeriod data).range := by
  rw [candidateAAbelianMixedSmooth_range]
  exact productOperator_hasCore _ _
    (bounded_toPMap_selfAdjoint _ (nonminimalSaddle_symmetric _)).isClosed
    (candidateAAbelianGhostMinimal_isClosed period hPeriod data) _ _
    (bounded_range_hasCore _ (bounded_toPMap_selfAdjoint _ (nonminimalSaddle_symmetric _)).isClosed _
      (candidateAAbelianNonminimalSmooth_denseRange period hPeriod data))
    (candidateAAbelianGhostMinimal_hasCore period hPeriod data)

theorem candidateAAbelianMixedMinimal_le_selfAdjoint :
    candidateAAbelianMixedMinimal period hPeriod data ≤ candidateAAbelianMixedOperator period hPeriod data :=
  productOperator_mono _ _ _ _ le_rfl (candidateAAbelianGhostMinimal_le_selfAdjoint period hPeriod data)

/-- The actual smooth mixed BRST restriction has this computed graph closure. -/
theorem candidateAAbelianMixed_smoothClosure_eq_minimal :
    ((candidateAAbelianMixedOperator period hPeriod data).domRestrict
      (candidateAAbelianMixedSmoothLinearMap period hPeriod data).range).closure =
      candidateAAbelianMixedMinimal period hPeriod data := by
  rw [candidateAAbelianMixedSmooth_range]
  let L := globalPairedAbelianLorenzFeatureProjection period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
  let A := (nonminimalSaddle L).toPMap ⊤
  let S := (candidateAAbelianNonminimalSmooth period hPeriod data).range
  let G := candidateAAbelianGhostOperator period hPeriod data
  let T := candidateAAbelianGhostSmoothCore period hPeriod
  have hA : A.IsClosed := (bounded_toPMap_selfAdjoint _ (nonminimalSaddle_symmetric L)).isClosed
  have hG : G.IsClosed := (candidateAAbelianGhostOperator_selfAdjoint period hPeriod data).isClosed
  have hS : A.HasCore S := bounded_range_hasCore _ hA _
    (candidateAAbelianNonminimalSmooth_denseRange period hPeriod data)
  change ((productOperator A G).domRestrict (productCore S T)).closure = _
  rw [productOperator_restriction, productOperator_closure _ _
    (hA.isClosable.leIsClosable (show A.domRestrict S ≤ A from LinearPMap.domRestrict_le))
    (hG.isClosable.leIsClosable (show G.domRestrict T ≤ G from LinearPMap.domRestrict_le)),
    hS.closure_eq]
  change productOperator A ((candidateAAbelianGhostOperator period hPeriod data).domRestrict
    (candidateAAbelianGhostSmoothCore period hPeriod)).closure = _
  rw [
    candidateAAbelianGhost_smoothClosure_eq_minimal]
  rfl

end
end P0EFTJanusProgramPT12CandidateAAbelianMixedMinimal4D
end JanusFormal
