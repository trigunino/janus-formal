import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianSignedGhostL2Operator4D

/-! The signed self-adjoint L2 operator has the actual reconstructed ghost Hessian. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAAbelianSignedGhostL2Pairing4D
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

open P0EFTJanusProgramPT12CandidateAAbelianSignedGhostL2Operator4D
open P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D

/-- Exact agreement with the pre-existing smooth signed ghost reconstruction. -/
theorem candidateAAbelianSignedGhostOperator_smooth_hessian
    (u v x y : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real (candidateAAbelianSignedGhostOperator period hPeriod data
      ⟨WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod u,
        globalPairedGaugeLieL2LinearMap period hPeriod v),
        candidateAAbelianSignedGhostOperator_smooth_mem period hPeriod data u v⟩)
      (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod x,
        globalPairedGaugeLieL2LinearMap period hPeriod y)) =
    globalPairedAbelianOffShellHessian period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        (pureAbelianGhostPair period hPeriod ((1 / 2 : Real) • (u + v)) ((1 / 2 : Real) • (u - v))))
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        (pureAbelianGhostPair period hPeriod ((1 / 2 : Real) • (x + y)) ((1 / 2 : Real) • (x - y)))) := by
  let signedInput : (candidateAAbelianSignedGhostOperator period hPeriod data).domain :=
    ⟨WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod u,
      globalPairedGaugeLieL2LinearMap period hPeriod v),
      candidateAAbelianSignedGhostOperator_smooth_mem period hPeriod data u v⟩
  let originalInput : (candidateAAbelianGhostOperator period hPeriod data).domain :=
    ⟨ghostL2Reconstruction (GlobalPairedGaugeLieL2 period hPeriod) signedInput.val,
      (unboundedCongruence_domain_iff _ _ _).mp signedInput.property⟩
  let smoothInput : (candidateAAbelianGhostOperator period hPeriod data).domain :=
    ⟨WithLp.toLp 2
      (globalPairedGaugeLieL2LinearMap period hPeriod ((1 / 2 : Real) • (u + v)),
        globalPairedGaugeLieL2LinearMap period hPeriod ((1 / 2 : Real) • (u - v))),
      candidateAAbelianGhostOperator_smooth_mem period hPeriod data _ _⟩
  have hInput : originalInput = smoothInput :=
    Subtype.ext (candidateAAbelianGhostReconstruction_smooth period hPeriod u v)
  have hPair := candidateAAbelianSignedGhostOperator_pairing period hPeriod data signedInput
    (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod x,
      globalPairedGaugeLieL2LinearMap period hPeriod y))
  exact hPair.trans ((congrArg₂ (inner Real)
    (congrArg (candidateAAbelianGhostOperator period hPeriod data) hInput)
    (candidateAAbelianGhostReconstruction_smooth period hPeriod x y)).trans
      (candidateAAbelianGhostOperator_smooth_hessian period hPeriod data _ _ _ _))

/-- Signed diagonal terms and the genuine FP cross defects, with the exact factors. -/
theorem candidateAAbelianSignedGhostOperator_smooth_pairing
    (u v x y : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real (candidateAAbelianSignedGhostOperator period hPeriod data
      ⟨WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod u,
        globalPairedGaugeLieL2LinearMap period hPeriod v),
        candidateAAbelianSignedGhostOperator_smooth_mem period hPeriod data u v⟩)
      (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod x,
        globalPairedGaugeLieL2LinearMap period hPeriod y)) =
    (fpSymmetricPairing (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data)) u x -
     fpSymmetricPairing (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data)) v y) / 2 +
    (fpPairingDefect (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data)) u y +
     fpPairingDefect (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data)) x v) / 4 := by
  rw [candidateAAbelianSignedGhostOperator_smooth_hessian,
    pureAbelianGhostPair_hessian, ghostCrossPairing_signed_coordinates]

end
end P0EFTJanusProgramPT12CandidateAAbelianSignedGhostL2Pairing4D
end JanusFormal
