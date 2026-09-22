import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostExtensions4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D

/-! Both actual self-adjoint extensions agree with the same smooth ghost Hessian. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianGhostExtensionPairing4D
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
open P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
open P0EFTJanusProgramPT12CandidateAAbelianGhostExtensions4D
open P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D

/-- The extensions agree on the entire minimal domain, not only on smooth fields. -/
theorem candidateAAbelianGhostExtensions_apply_on_minimal
    (input : (candidateAAbelianGhostMinimal period hPeriod data).domain) :
    candidateAAbelianGhostOperator period hPeriod data
      ⟨input.val, (candidateAAbelianGhostMinimal_le_selfAdjoint period hPeriod data).1 input.property⟩ =
    candidateAAbelianGhostDualOperator period hPeriod data
      ⟨input.val, (candidateAAbelianGhostMinimal_le_dual period hPeriod data).1 input.property⟩ := by
  have hFirst := (candidateAAbelianGhostMinimal_le_selfAdjoint period hPeriod data).2
    (x := input) (y := ⟨input.val, (candidateAAbelianGhostMinimal_le_selfAdjoint period hPeriod data).1 input.property⟩) rfl
  have hSecond := (candidateAAbelianGhostMinimal_le_dual period hPeriod data).2
    (x := input) (y := ⟨input.val, (candidateAAbelianGhostMinimal_le_dual period hPeriod data).1 input.property⟩) rfl
  exact hFirst.symm.trans hSecond

theorem candidateAAbelianGhostMinimal_smooth_mem
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod antighost,
      globalPairedGaugeLieL2LinearMap period hPeriod ghost) ∈
      (candidateAAbelianGhostMinimal period hPeriod data).domain :=
  (offDiagonalOperator_domain_iff _ _ _).mpr
    ⟨candidateAFPFormalAdjointMinimal_smooth_mem period hPeriod data antighost,
      candidateAFPCanonicalMinimal_smooth_mem period hPeriod data ghost⟩

theorem candidateAAbelianGhostDualOperator_smooth_mem
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod antighost,
      globalPairedGaugeLieL2LinearMap period hPeriod ghost) ∈
      (candidateAAbelianGhostDualOperator period hPeriod data).domain :=
  (candidateAAbelianGhostMinimal_le_dual period hPeriod data).1
    (candidateAAbelianGhostMinimal_smooth_mem period hPeriod data antighost ghost)

theorem candidateAAbelianGhostDualOperator_smooth_apply_eq_original
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    candidateAAbelianGhostDualOperator period hPeriod data
      ⟨WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod antighost,
        globalPairedGaugeLieL2LinearMap period hPeriod ghost),
        candidateAAbelianGhostDualOperator_smooth_mem period hPeriod data antighost ghost⟩ =
    candidateAAbelianGhostOperator period hPeriod data
      ⟨WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod antighost,
        globalPairedGaugeLieL2LinearMap period hPeriod ghost),
        candidateAAbelianGhostOperator_smooth_mem period hPeriod data antighost ghost⟩ :=
  (candidateAAbelianGhostExtensions_apply_on_minimal period hPeriod data
    ⟨_, candidateAAbelianGhostMinimal_smooth_mem period hPeriod data antighost ghost⟩).symm

/-- Both self-adjoint extensions reproduce the unchanged actual ghost Hessian. -/
theorem candidateAAbelianGhostDualOperator_smooth_hessian
    (a c b d : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real
      (candidateAAbelianGhostDualOperator period hPeriod data
        ⟨WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod a,
          globalPairedGaugeLieL2LinearMap period hPeriod c),
          candidateAAbelianGhostDualOperator_smooth_mem period hPeriod data a c⟩)
      (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod b,
        globalPairedGaugeLieL2LinearMap period hPeriod d)) =
    globalPairedAbelianOffShellHessian period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        (pureAbelianGhostPair period hPeriod a c))
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        (pureAbelianGhostPair period hPeriod b d)) := by
  rw [candidateAAbelianGhostDualOperator_smooth_apply_eq_original]
  exact candidateAAbelianGhostOperator_smooth_hessian period hPeriod data a c b d

/-- If the smooth core fails, the complementary extension is a concrete distinct witness. -/
theorem candidateAAbelianGhostDualOperator_ne_of_not_hasCore
    (hNotCore : ¬ (candidateAAbelianGhostOperator period hPeriod data).HasCore
      (candidateAAbelianGhostSmoothCore period hPeriod)) :
    candidateAAbelianGhostDualOperator period hPeriod data ≠ candidateAAbelianGhostOperator period hPeriod data := by
  intro hEqual
  exact hNotCore ((candidateAAbelianGhostOperator_hasCore_iff period hPeriod data).mpr
    ((candidateAAbelianGhostExtensions_eq_iff period hPeriod data).mp hEqual.symm))

end
end P0EFTJanusProgramPT12CandidateAAbelianGhostExtensionPairing4D
end JanusFormal
