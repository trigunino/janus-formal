import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D

/-! Faithful finite temporal Fourier packets in the actual paired abelian ghost domain. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianTemporalFourierCore4D
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

abbrev PairedTemporalCoefficients := Sector → FiniteTemporalFourierCoefficients

def pairedTemporalGhost : PairedTemporalCoefficients →ₗ[Real] GlobalPairedGaugeLieSmooth period hPeriod where
  toFun coefficients sector := finiteTemporalFourierGaugeGhostLinearMap period (coefficients sector)
  map_add' first second := by
    funext sector
    exact map_add (finiteTemporalFourierGaugeGhostLinearMap period) _ _
  map_smul' scalar coefficients := by
    funext sector
    exact map_smul (finiteTemporalFourierGaugeGhostLinearMap period) _ _

theorem pairedTemporalGhost_injective : Function.Injective (pairedTemporalGhost period hPeriod) := by
  intro first second hEqual
  funext sector
  apply finiteTemporalFourierGaugeGhostLinearMap_injective period
  exact congrArg (fun field : GlobalPairedGaugeLieSmooth period hPeriod => field sector) hEqual

def pairedTemporalGhostL2 : PairedTemporalCoefficients →ₗ[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  (globalPairedGaugeLieL2LinearMap period hPeriod).comp (pairedTemporalGhost period hPeriod)

theorem pairedTemporalGhostL2_injective : Function.Injective (pairedTemporalGhostL2 period hPeriod) :=
  (globalPairedGaugeLieL2LinearMap_injective period hPeriod).comp (pairedTemporalGhost_injective period hPeriod)

def temporalGhostInput (antighost ghost : PairedTemporalCoefficients) : CandidateAAbelianGhostL2 period hPeriod :=
  WithLp.toLp 2 (pairedTemporalGhostL2 period hPeriod antighost,
    pairedTemporalGhostL2 period hPeriod ghost)

theorem temporalGhostInput_mem_domain (antighost ghost : PairedTemporalCoefficients) :
    temporalGhostInput period hPeriod antighost ghost ∈
      (candidateAAbelianGhostOperator period hPeriod data).domain :=
  candidateAAbelianGhostOperator_smooth_mem period hPeriod data
    (pairedTemporalGhost period hPeriod antighost) (pairedTemporalGhost period hPeriod ghost)

theorem temporalGhostInput_actual_graph (antighost ghost : PairedTemporalCoefficients) :
    (temporalGhostInput period hPeriod antighost ghost,
      WithLp.toLp 2
        (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data)
          (pairedTemporalGhost period hPeriod ghost),
        pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data)
          (pairedTemporalGhost period hPeriod antighost))) ∈
      (candidateAAbelianGhostOperator period hPeriod data).graph :=
  (LinearPMap.mem_graph_iff _).mpr
    ⟨⟨temporalGhostInput period hPeriod antighost ghost,
      temporalGhostInput_mem_domain period hPeriod data antighost ghost⟩, rfl,
      candidateAAbelianGhostOperator_smooth_apply period hPeriod data
        (pairedTemporalGhost period hPeriod antighost) (pairedTemporalGhost period hPeriod ghost)⟩

end
end P0EFTJanusProgramPT12AbelianTemporalFourierCore4D
end JanusFormal
