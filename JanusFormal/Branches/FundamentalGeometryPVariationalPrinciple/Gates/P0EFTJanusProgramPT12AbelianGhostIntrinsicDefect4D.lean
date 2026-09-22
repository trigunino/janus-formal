import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianFaddeevPopovScalarBridge4D

/-! The actual intrinsic ghost signed-coordinate mixing equals a scalar skew integral. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D
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

open scoped BigOperators
open P0EFTJanusProgramPT12GhostRotationDefect4D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovScalarBridge4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D

/-- The four real components of the paired U(1)^2 scalar defect. -/
def intrinsicPairedFPSkewIntegral (first second : GlobalPairedGaugeLieSmooth period hPeriod) : Real :=
  ∑ index : GlobalPairedAbelianLorenzCoordinateIndex,
    ∫ point, canonicalPhysicalScalarEulerSkewDensity period hPeriod 0
      (ghostComponent period hPeriod (first index.1) index.2)
      (ghostComponent period hPeriod (second index.1) index.2) point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

theorem intrinsicPairedFPDefect_eq_skewIntegral
    (first second : GlobalPairedGaugeLieSmooth period hPeriod) :
    fpPairingDefect (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod)) first second =
      intrinsicPairedFPSkewIntegral period hPeriod first second := by
  simp only [fpPairingDefect, PiLp.inner_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _
  exact intrinsicAbelianFaddeevPopov_component_pairingDefect_eq_integral
    period hPeriod (first index.1) (second index.1) index.2

def pureAbelianGhostPair (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod where
  potential := 0
  nonminimal := fun sector => ⟨⟨ghost sector⟩, ⟨antighost sector⟩, ⟨0⟩⟩

theorem pureAbelianGhostPair_hessian
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (a c b d : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedAbelianOffShellHessian period hPeriod metric
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        (pureAbelianGhostPair period hPeriod a c))
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        (pureAbelianGhostPair period hPeriod b d)) =
      ghostCrossPairing (globalPairedGaugeLieL2LinearMap period hPeriod)
        (globalPairedAbelianFPL2LinearMap period hPeriod metric) a c b d := by
  simp only [globalPairedAbelianOffShellHessian_apply,
    globalPairedAbelianOffShellBProjection_smooth, globalPairedAbelianOffShellLorenzProjection_smooth,
    globalPairedAbelianOffShellAntighostProjection_smooth, globalPairedAbelianOffShellFPProjection_smooth,
    pureAbelianGhostPair, map_zero, inner_zero_left, inner_zero_right,
    add_zero]
  change 0 - inner Real (globalPairedGaugeLieL2LinearMap period hPeriod 0)
    (globalPairedGaugeLieL2LinearMap period hPeriod 0) + _ + _ = _
  rw [map_zero, inner_zero_left, sub_zero, zero_add]
  rfl

/-- Actual plus/minus cross tests measure the geometric defect, not a presumed zero. -/
theorem intrinsicGhostRotation_mixed_hessian
    (first second : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedAbelianOffShellHessian period hPeriod
      (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (pureAbelianGhostPair period hPeriod ((1 / 2 : Real) • first) ((1 / 2 : Real) • first)))
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (pureAbelianGhostPair period hPeriod ((1 / 2 : Real) • second) (-(1 / 2 : Real) • second))) =
      intrinsicPairedFPSkewIntegral period hPeriod first second / 4 := by
  rw [pureAbelianGhostPair_hessian, ghostCrossPairing_mixed_signed,
    intrinsicPairedFPDefect_eq_skewIntegral]

/-- Exact scalar criterion needed before discarding the signed ghost cross block. -/
theorem intrinsicPairedFP_symmetric_iff_skewIntegral_zero
    (first second : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real (globalPairedAbelianFPL2LinearMap period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) first)
      (globalPairedGaugeLieL2LinearMap period hPeriod second) =
    inner Real (globalPairedGaugeLieL2LinearMap period hPeriod first)
      (globalPairedAbelianFPL2LinearMap period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) second) ↔
      intrinsicPairedFPSkewIntegral period hPeriod first second = 0 := by
  rw [← intrinsicPairedFPDefect_eq_skewIntegral, fpPairingDefect, sub_eq_zero]

end
end P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D
end JanusFormal
