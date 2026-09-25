import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Recovery4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameDiffeomorphismC2Core4D

/-! Faithful normalized ghost L² and finite-frame recovery, without a regular metric. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeGhostL2Core4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D P0EFTJanusProgramPT12SmoothMatrixL24D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local notation "frame" => finiteSmoothTangentFrame period hPeriod
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod
local notation "Ghost" => CInfinityDiffeomorphismGhost period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "Ambient" => GlobalDiffeomorphismVectorL2 period hPeriod
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

def frameFreeGhostL2Space : Submodule Real Ambient :=
  (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).range.topologicalClosure

abbrev FrameFreeGhostL2 := frameFreeGhostL2Space period hPeriod metric
local notation "Core" => FrameFreeGhostL2 period hPeriod metric
instance frameFreeGhostL2_complete : CompleteSpace Core := Submodule.topologicalClosure.completeSpace _

def frameFreeGhostL2Smooth : Ghost →ₗ[Real] Core :=
  (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).codRestrict
    (frameFreeGhostL2Space period hPeriod metric) (fun ghost => Submodule.le_topologicalClosure _ ⟨ghost, rfl⟩)

theorem frameFreeGhostL2Smooth_injective : Function.Injective (frameFreeGhostL2Smooth period hPeriod metric) := by
  intro first second h
  exact globalNormalizedVectorFrameL2LinearMap_injective period hPeriod metric (congrArg Subtype.val h)

theorem frameFreeGhostL2Smooth_denseRange : DenseRange (frameFreeGhostL2Smooth period hPeriod metric) := by
  rw [DenseRange, Subtype.dense_iff]
  have hRange : Subtype.val '' Set.range (frameFreeGhostL2Smooth period hPeriod metric) =
      ((globalNormalizedVectorFrameL2LinearMap period hPeriod metric).range : Set Ambient) := by
    ext value
    constructor
    · rintro ⟨_, ⟨ghost, rfl⟩, rfl⟩; exact ⟨ghost, rfl⟩
    · rintro ⟨ghost, rfl⟩
      exact ⟨frameFreeGhostL2Smooth period hPeriod metric ghost, ⟨ghost, rfl⟩, rfl⟩
  change closure ((globalNormalizedVectorFrameL2LinearMap period hPeriod metric).range : Set Ambient) ⊆ _
  exact (congrArg closure hRange).symm.subset

def frameFreeGhostRecoveryMatrix (row column : N) : Scalar :=
  canonicalScalarMul period hPeriod (inverseSmoothMetricRatio period hPeriod metric)
    (generalMetricFiniteFrameCoefficient period hPeriod frame metric (frameTangentField period hPeriod frame column) row)

theorem frameFreeGhostRecoveryMatrix_smooth (ghost : Ghost) (row : N) :
    (∑ column : N, canonicalScalarMul period hPeriod (frameFreeGhostRecoveryMatrix period hPeriod metric row column)
      (globalNormalizedVectorCoordinate period hPeriod metric ghost column)) =
      generalMetricFiniteFrameCoefficient period hPeriod frame metric ghost row := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [canonicalScalar_sum_apply]
  let dual := generalMetricFiniteFrameCoefficientAt period hPeriod frame metric point row
  have hPair := globalFiniteTangentPairingFactorizationPublic period hPeriod point dual (ghost point)
  have hRatio := (globalMetricVolumeRatio_pos period hPeriod metric point).ne'
  have hWeight := (globalFiniteTangentWeightSquareSum_pos period hPeriod point).ne'
  change (∑ column : N, ((globalMetricVolumeRatio period hPeriod metric point)⁻¹ *
    dual ((frame).vectorAt point column)) * globalNormalizedVectorCoordinate period hPeriod metric ghost column point) =
      dual (ghost point)
  simp only [globalNormalizedVectorCoordinate_apply, globalGeneralMetricDeDonderPairingNormalization]
  calc
    _ = ((globalMetricVolumeRatio period hPeriod metric point)⁻¹ *
        (globalMetricVolumeRatio period hPeriod metric point / globalFiniteTangentWeightSquareSum period hPeriod point)) *
        (globalFiniteTangentWeightSquareSum period hPeriod point * dual (ghost point)) := by
      rw [← hPair, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro column _
      ring
    _ = dual (ghost point) := by field_simp

/-- Each reconstructed coefficient is a bounded readout of the original physical ghost. -/
def frameFreeGhostCoordinate (row : N) : Core →L[Real] H :=
  ((PiLp.proj 2 (fun _ : N => H) row).comp
    (canonicalSmoothMatrixL2 period hPeriod (frameFreeGhostRecoveryMatrix period hPeriod metric))).comp
      (frameFreeGhostL2Space period hPeriod metric).subtypeL

theorem frameFreeGhostCoordinate_smooth (ghost : Ghost) (row : N) :
    frameFreeGhostCoordinate period hPeriod metric row (frameFreeGhostL2Smooth period hPeriod metric ghost) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod (generalMetricFiniteFrameCoefficient period hPeriod frame metric ghost row) :=
  (canonicalSmoothMatrixL2_smooth period hPeriod (frameFreeGhostRecoveryMatrix period hPeriod metric)
    (globalNormalizedVectorCoordinate period hPeriod metric ghost) row).trans
      (congrArg (smoothToCanonicalPhysicalBulkL2 period hPeriod)
        (frameFreeGhostRecoveryMatrix_smooth period hPeriod metric ghost row))

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeGhostL2Core4D
