import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianMixedOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BRSTSaddleProduct4D

/-! Full abelian BRST: graph Lorenz potential, canonical L2 auxiliary and ghosts. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianMixedSmooth4D
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

def candidateAAbelianMixedSmoothLinearMap :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real] CandidateAAbelianMixedHilbert period hPeriod data where
  toFun := candidateAAbelianMixedSmooth period hPeriod data
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((globalPairedAbelianLorenzSmoothEmbedding period hPeriod _).map_add _ _)
        ((globalPairedGaugeLieL2LinearMap period hPeriod).map_add _ _)
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((globalPairedGaugeLieL2LinearMap period hPeriod).map_add _ _)
        ((globalPairedGaugeLieL2LinearMap period hPeriod).map_add _ _)
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((globalPairedAbelianLorenzSmoothEmbedding period hPeriod _).map_smul r _)
        ((globalPairedGaugeLieL2LinearMap period hPeriod).map_smul r _)
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((globalPairedGaugeLieL2LinearMap period hPeriod).map_smul r _)
        ((globalPairedGaugeLieL2LinearMap period hPeriod).map_smul r _)

theorem candidateAAbelianMixedSmooth_injective :
    Function.Injective (candidateAAbelianMixedSmooth period hPeriod data) := by
  intro first second h
  have hP := globalPairedAbelianLorenzSmoothEmbedding_injective period hPeriod _
    (congrArg (fun x : CandidateAAbelianMixedHilbert period hPeriod data => x.fst.fst) h)
  have hB := globalPairedGaugeLieL2LinearMap_injective period hPeriod
    (congrArg (fun x : CandidateAAbelianMixedHilbert period hPeriod data => x.fst.snd) h)
  have hA := globalPairedGaugeLieL2LinearMap_injective period hPeriod
    (congrArg (fun x : CandidateAAbelianMixedHilbert period hPeriod data => x.snd.fst) h)
  have hC := globalPairedGaugeLieL2LinearMap_injective period hPeriod
    (congrArg (fun x : CandidateAAbelianMixedHilbert period hPeriod data => x.snd.snd) h)
  apply GlobalPairedAbelianBRSTState.ext hP
  funext s
  exact GlobalAbelianNonminimalFields.ext
    (GlobalAbelianGhostField.ext (congrFun hC s))
    (GlobalAbelianAntighostField.ext (congrFun hA s))
    (GlobalAbelianNakanishiLautrupField.ext (congrFun hB s))

private theorem dense_withLp_pair {X Y P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [NormedAddCommGroup Q] [NormedSpace Real Q]
    {f : X → P} {g : Y → Q} (hf : DenseRange f) (hg : DenseRange g) :
    DenseRange (fun pair : X × Y => WithLp.toLp 2 (f pair.1, g pair.2)) :=
  (WithLp.prodContinuousLinearEquiv 2 Real P Q).symm.surjective.denseRange.comp
    (hf.prodMap hg) (WithLp.prodContinuousLinearEquiv 2 Real P Q).symm.continuous

/-- Density is in the mixed Hilbert norm; no operator-core claim is made. -/
theorem candidateAAbelianMixedSmooth_denseRange :
    DenseRange (candidateAAbelianMixedSmooth period hPeriod data) := by
  have h := dense_withLp_pair
    (dense_withLp_pair (globalPairedAbelianLorenzSmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data))
      (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod))
    (candidateAAbelianGhostSmooth_denseRange period hPeriod)
  refine Dense.mono ?_ h
  rintro _ ⟨p, rfl⟩
  exact ⟨⟨p.1.1, fun s => ⟨⟨p.2.2 s⟩, ⟨p.2.1 s⟩, ⟨p.1.2 s⟩⟩⟩, rfl⟩

end
end P0EFTJanusProgramPT12CandidateAAbelianMixedSmooth4D
end JanusFormal
