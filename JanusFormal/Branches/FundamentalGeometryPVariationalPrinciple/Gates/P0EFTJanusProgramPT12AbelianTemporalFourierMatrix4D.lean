import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianTemporalFourierCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D

/-! Faithful finite temporal Fourier packets in the actual paired abelian ghost domain. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianTemporalFourierMatrix4D
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
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D

variable [hPeriodPos : Fact (0 < period)]

open P0EFTJanusProgramPT12AbelianTemporalFourierCore4D

/-- A sector, temporal frequency, and real/imaginary Lie component. -/
abbrev TemporalGhostMode := Sector × Int × Fin 2

def temporalModeCoefficients (mode : TemporalGhostMode) : PairedTemporalCoefficients := by
  classical
  exact Pi.single mode.1 (Finsupp.single mode.2.1 (if mode.2.2 = 0 then 1 else Complex.I))

variable {ι : Type*} [Fintype ι]

def temporalPacket (modes : ι → TemporalGhostMode) (amplitudes : ι → Real) :
    PairedTemporalCoefficients :=
  ∑ i, amplitudes i • temporalModeCoefficients (modes i)

/-- The actual variable-metric FP map, without a diagonal-symbol assumption. -/
def temporalFP : PairedTemporalCoefficients →ₗ[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  (globalPairedAbelianFPL2LinearMap period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)).comp (pairedTemporalGhost period hPeriod)

/-- First index is the input mode; second index is the test mode. -/
def temporalFPMatrix (modes : ι → TemporalGhostMode) (i j : ι) : Real :=
  inner Real (temporalFP period hPeriod data (temporalModeCoefficients (modes i)))
    (pairedTemporalGhostL2 period hPeriod (temporalModeCoefficients (modes j)))

private theorem finite_packet_pairing
    {D E : Type*} [AddCommGroup D] [Module Real D]
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    (L R : D →ₗ[Real] E) (v : ι → D) (a b : ι → Real) :
    inner Real (L (∑ i, a i • v i)) (R (∑ j, b j • v j)) =
      ∑ i, ∑ j, a i * b j * inner Real (L (v i)) (R (v j)) := by
  simp only [map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  ring

theorem temporalFPMatrix_pairing (modes : ι → TemporalGhostMode) (a b : ι → Real) :
    inner Real (temporalFP period hPeriod data (temporalPacket modes a))
      (pairedTemporalGhostL2 period hPeriod (temporalPacket modes b)) =
      ∑ i, ∑ j, a i * b j * temporalFPMatrix period hPeriod data modes i j :=
  finite_packet_pairing _ _ _ a b

/-- The adjoint block is reconstructed by transposing the actual FP pairing. -/
theorem temporalGhostInput_pairing
    (antighost ghost testAnti testGhost : PairedTemporalCoefficients) :
    inner Real
      (candidateAAbelianGhostOperator period hPeriod data
        ⟨temporalGhostInput period hPeriod antighost ghost,
          temporalGhostInput_mem_domain period hPeriod data antighost ghost⟩)
      (temporalGhostInput period hPeriod testAnti testGhost) =
    inner Real (temporalFP period hPeriod data ghost) (pairedTemporalGhostL2 period hPeriod testAnti) +
      inner Real (temporalFP period hPeriod data testGhost) (pairedTemporalGhostL2 period hPeriod antighost) := by
  have hApply : candidateAAbelianGhostOperator period hPeriod data
      ⟨temporalGhostInput period hPeriod antighost ghost,
        temporalGhostInput_mem_domain period hPeriod data antighost ghost⟩ =
      WithLp.toLp 2
        (globalPairedAbelianFPL2LinearMap period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) (pairedTemporalGhost period hPeriod ghost),
        pairedFPCanonicalAdjointL2 period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) (pairedTemporalGhost period hPeriod antighost)) :=
    candidateAAbelianGhostOperator_smooth_apply period hPeriod data _ _
  rw [hApply]
  change inner Real (globalPairedAbelianFPL2LinearMap period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) (pairedTemporalGhost period hPeriod ghost))
      (pairedTemporalGhostL2 period hPeriod testAnti) +
    inner Real (pairedFPCanonicalAdjointL2 period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) (pairedTemporalGhost period hPeriod antighost))
      (pairedTemporalGhostL2 period hPeriod testGhost) = _
  congr 1
  rw [real_inner_comm]
  exact (candidateAFPCanonicalAdjoint_pairing period hPeriod data
    (pairedTemporalGhost period hPeriod testGhost) (pairedTemporalGhost period hPeriod antighost)).symm

theorem temporalGhostInput_matrix_pairing (modes : ι → TemporalGhostMode)
    (antighost ghost testAnti testGhost : ι → Real) :
    inner Real
      (candidateAAbelianGhostOperator period hPeriod data
        ⟨temporalGhostInput period hPeriod (temporalPacket modes antighost) (temporalPacket modes ghost),
          temporalGhostInput_mem_domain period hPeriod data _ _⟩)
      (temporalGhostInput period hPeriod (temporalPacket modes testAnti) (temporalPacket modes testGhost)) =
      (∑ i, ∑ j, ghost i * testAnti j * temporalFPMatrix period hPeriod data modes i j) +
      (∑ i, ∑ j, testGhost i * antighost j * temporalFPMatrix period hPeriod data modes i j) := by
  rw [temporalGhostInput_pairing, temporalFPMatrix_pairing, temporalFPMatrix_pairing]

end
end P0EFTJanusProgramPT12AbelianTemporalFourierMatrix4D
end JanusFormal
