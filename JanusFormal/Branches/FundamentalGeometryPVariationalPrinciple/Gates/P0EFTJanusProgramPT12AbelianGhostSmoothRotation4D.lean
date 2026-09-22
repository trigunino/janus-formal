import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GhostRotationDefect4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianLorenzGraphShear4D

/-! Invertible ghost sum/difference coordinates on the authentic smooth core.
No extension to the asymmetric completed off-shell graph is claimed. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
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

open P0EFTJanusProgramPT12GhostRotationDefect4D

abbrev abelianGhost (state : GlobalPairedAbelianBRSTState period hPeriod) :
    GlobalPairedGaugeLieSmooth period hPeriod := fun sector => (state.nonminimal sector).ghost.field

abbrev abelianAntighost (state : GlobalPairedAbelianBRSTState period hPeriod) :
    GlobalPairedGaugeLieSmooth period hPeriod := fun sector => (state.nonminimal sector).antighost.field

/-- Slots (antighost, ghost) become (antighost + ghost, antighost - ghost). -/
def abelianGhostSignedState (state : GlobalPairedAbelianBRSTState period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod where
  potential := state.potential
  nonminimal := fun sector =>
    { ghost := ⟨abelianAntighost period hPeriod state sector - abelianGhost period hPeriod state sector⟩
      antighost := ⟨abelianAntighost period hPeriod state sector + abelianGhost period hPeriod state sector⟩
      nakanishiLautrup := (state.nonminimal sector).nakanishiLautrup }

def abelianGhostSignedReconstruct (state : GlobalPairedAbelianBRSTState period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod where
  potential := state.potential
  nonminimal := fun sector =>
    { ghost := ⟨(1 / 2 : Real) • (abelianAntighost period hPeriod state sector -
          abelianGhost period hPeriod state sector)⟩
      antighost := ⟨(1 / 2 : Real) • (abelianAntighost period hPeriod state sector +
          abelianGhost period hPeriod state sector)⟩
      nakanishiLautrup := (state.nonminimal sector).nakanishiLautrup }

theorem abelianGhostSignedReconstruct_state (state : GlobalPairedAbelianBRSTState period hPeriod) :
    abelianGhostSignedReconstruct period hPeriod (abelianGhostSignedState period hPeriod state) = state := by
  apply GlobalPairedAbelianBRSTState.ext
  · rfl
  · funext sector
    apply GlobalAbelianNonminimalFields.ext
    · apply GlobalAbelianGhostField.ext
      change (1 / 2 : Real) • ((_ + _) - (_ - _)) = _
      module
    · apply GlobalAbelianAntighostField.ext
      change (1 / 2 : Real) • ((_ + _) + (_ - _)) = _
      module
    · rfl

theorem abelianGhostSignedState_reconstruct (state : GlobalPairedAbelianBRSTState period hPeriod) :
    abelianGhostSignedState period hPeriod (abelianGhostSignedReconstruct period hPeriod state) = state := by
  apply GlobalPairedAbelianBRSTState.ext
  · rfl
  · funext sector
    apply GlobalAbelianNonminimalFields.ext
    · apply GlobalAbelianGhostField.ext
      change (1 / 2 : Real) • (_ + _) - (1 / 2 : Real) • (_ - _) = _
      module
    · apply GlobalAbelianAntighostField.ext
      change (1 / 2 : Real) • (_ + _) + (1 / 2 : Real) • (_ - _) = _
      module
    · rfl

def abelianGhostSignedEquiv : GlobalPairedAbelianBRSTState period hPeriod ≃ₗ[Real]
    GlobalPairedAbelianBRSTState period hPeriod where
  toFun := abelianGhostSignedState period hPeriod
  invFun := abelianGhostSignedReconstruct period hPeriod
  left_inv := abelianGhostSignedReconstruct_state period hPeriod
  right_inv := abelianGhostSignedState_reconstruct period hPeriod
  map_add' first second := by
    apply GlobalPairedAbelianBRSTState.ext
    · rfl
    · funext sector
      apply GlobalAbelianNonminimalFields.ext
      · apply GlobalAbelianGhostField.ext
        change (abelianAntighost period hPeriod first sector + abelianAntighost period hPeriod second sector) - (abelianGhost period hPeriod first sector + abelianGhost period hPeriod second sector) = (abelianAntighost period hPeriod first sector - abelianGhost period hPeriod first sector) + (abelianAntighost period hPeriod second sector - abelianGhost period hPeriod second sector)
        abel
      · apply GlobalAbelianAntighostField.ext
        change (abelianAntighost period hPeriod first sector + abelianAntighost period hPeriod second sector) + (abelianGhost period hPeriod first sector + abelianGhost period hPeriod second sector) = (abelianAntighost period hPeriod first sector + abelianGhost period hPeriod first sector) + (abelianAntighost period hPeriod second sector + abelianGhost period hPeriod second sector)
        abel
      · rfl
  map_smul' scalar state := by
    apply GlobalPairedAbelianBRSTState.ext
    · rfl
    · funext sector
      apply GlobalAbelianNonminimalFields.ext
      · apply GlobalAbelianGhostField.ext
        exact (smul_sub scalar _ _).symm
      · apply GlobalAbelianAntighostField.ext
        exact (smul_add scalar _ _).symm
      · rfl

def abelianGhostPairing (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod) : Real :=
  ghostCrossPairing (globalPairedGaugeLieL2LinearMap period hPeriod)
    (globalPairedAbelianFPL2LinearMap period hPeriod metric)
    (abelianAntighost period hPeriod first) (abelianGhost period hPeriod first)
    (abelianAntighost period hPeriod second) (abelianGhost period hPeriod second)

/-- Unconditional signed-coordinate formula, including both mixed defects. -/
theorem abelianGhostPairing_signed_reconstruct
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    abelianGhostPairing period hPeriod metric
      (abelianGhostSignedReconstruct period hPeriod first)
      (abelianGhostSignedReconstruct period hPeriod second) =
    (fpSymmetricPairing (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod metric)
      (abelianAntighost period hPeriod first) (abelianAntighost period hPeriod second) -
    fpSymmetricPairing (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod metric)
      (abelianGhost period hPeriod first) (abelianGhost period hPeriod second)) / 2 +
    (fpPairingDefect (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod metric)
      (abelianAntighost period hPeriod first) (abelianGhost period hPeriod second) +
    fpPairingDefect (globalPairedGaugeLieL2LinearMap period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod metric)
      (abelianAntighost period hPeriod second) (abelianGhost period hPeriod first)) / 4 :=
  ghostCrossPairing_signed_coordinates _ _ _ _ _ _

/-- The potential and auxiliary terms of the original Hessian are unchanged. -/
theorem abelianOffShellHessian_signed_reconstruct
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianOffShellHessian period hPeriod metric
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        (abelianGhostSignedReconstruct period hPeriod first))
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        (abelianGhostSignedReconstruct period hPeriod second)) =
    globalPairedAbelianOffShellHessian period hPeriod metric
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric first)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric second) -
    abelianGhostPairing period hPeriod metric first second +
    abelianGhostPairing period hPeriod metric
      (abelianGhostSignedReconstruct period hPeriod first)
      (abelianGhostSignedReconstruct period hPeriod second) := by
  simp only [globalPairedAbelianOffShellHessian_apply,
    globalPairedAbelianOffShellBProjection_smooth, globalPairedAbelianOffShellLorenzProjection_smooth,
    globalPairedAbelianOffShellAntighostProjection_smooth, globalPairedAbelianOffShellFPProjection_smooth]
  unfold abelianGhostPairing ghostCrossPairing
  dsimp only [abelianGhostSignedReconstruct, abelianGhost, abelianAntighost]
  ring

end
end P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
end JanusFormal
