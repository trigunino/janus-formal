import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FPVolumeH1Bound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D

/-! Paired actual FP correction on the dense ten-flow H¹ ghost core. -/
namespace JanusFormal.P0EFTJanusProgramPT12PairedFPH1Correction4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12CanonicalDirectionalH1L24D
open P0EFTJanusProgramPT12FPVolumeH1Bound4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

abbrev PairedFPH1 := PiLp 2 fun _ : GlobalPairedAbelianLorenzCoordinateIndex =>
  CanonicalTenFlowScalarH1 period hPeriod

def pairedGhostH1 : GlobalPairedGaugeLieSmooth period hPeriod →ₗ[Real] PairedFPH1 period hPeriod where
  toFun field := WithLp.toLp 2 fun index =>
    smoothToH1GraphLinearMap period hPeriod Real (canonicalTenFlowFrame period hPeriod)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (ghostComponent period hPeriod (field index.1) index.2)
  map_add' first second := by
    apply PiLp.ext
    intro index
    change (smoothToH1GraphLinearMap period hPeriod Real _ _)
      (ghostComponent period hPeriod (first index.1 + second index.1) index.2) = _
    rw [ghostComponent_add, map_add]
    rfl
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    have hComponent : ghostComponent period hPeriod (scalar • field index.1) index.2 =
        scalar • ghostComponent period hPeriod (field index.1) index.2 := by
      apply SmoothQuotientField.ext period hPeriod Real
      intro point
      exact (EuclideanSpace.proj index.2).map_smul scalar _
    change (smoothToH1GraphLinearMap period hPeriod Real _ _)
      (ghostComponent period hPeriod (scalar • field index.1) index.2) = _
    rw [hComponent, map_smul]
    rfl

theorem pairedGhostH1_denseRange : DenseRange (pairedGhostH1 period hPeriod) := by
  let coords := PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalPairedAbelianLorenzCoordinateIndex => CanonicalTenFlowScalarH1 period hPeriod)
  let synth := fun fields : GlobalPairedAbelianLorenzCoordinateIndex →
      SmoothQuotientField period hPeriod Real =>
    WithLp.toLp 2 fun i => smoothToH1GraphLinearMap period hPeriod Real
      (canonicalTenFlowFrame period hPeriod) (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) (fields i)
  have hCoordinates : DenseRange (coords ∘ synth) :=
    DenseRange.piMap fun _ => smoothToH1Graph_denseRange period hPeriod Real _ _
  have hBack := coords.symm.surjective.denseRange.comp hCoordinates coords.symm.continuous
  have hDense : DenseRange synth := by simpa [coords, Function.comp_def] using hBack
  apply hDense.mono
  rintro _ ⟨fields, rfl⟩
  refine ⟨globalPairedGaugeLieSmoothOfComponents period hPeriod fields, ?_⟩
  apply PiLp.ext
  intro index
  change (smoothToH1GraphLinearMap period hPeriod Real _ _)
    (ghostComponent period hPeriod
      (globalPairedGaugeLieSmoothOfComponents period hPeriod fields index.1) index.2) = _
  rw [ghostComponent_globalPairedGaugeLieSmoothOfComponents]

def pairedH1ToL2 : PairedFPH1 period hPeriod →L[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  (PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalPairedAbelianLorenzCoordinateIndex => CanonicalPhysicalBulkL2 period hPeriod)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun index =>
        (h1GraphToL2 period hPeriod Real (canonicalTenFlowFrame period hPeriod)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).comp
            (PiLp.proj 2 (fun _ : GlobalPairedAbelianLorenzCoordinateIndex =>
              CanonicalTenFlowScalarH1 period hPeriod) index))

theorem pairedH1ToL2_smooth (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    pairedH1ToL2 period hPeriod (pairedGhostH1 period hPeriod field) =
      globalPairedGaugeLieL2LinearMap period hPeriod field := by
  apply PiLp.ext
  intro index
  exact h1GraphToL2_agrees_on_smooth period hPeriod Real _ _ _

def pairedFPVolumeCorrection (metric : Sector → RegularGeneralLorentzMetric period hPeriod) :
    PairedFPH1 period hPeriod →L[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  (PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalPairedAbelianLorenzCoordinateIndex => CanonicalPhysicalBulkL2 period hPeriod)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun index =>
        (fpVolumeCorrectionH1ToL2 period hPeriod (metric index.1)).comp
          (PiLp.proj 2 (fun _ : GlobalPairedAbelianLorenzCoordinateIndex =>
            CanonicalTenFlowScalarH1 period hPeriod) index))

theorem pairedFPVolumeCorrection_smooth
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    pairedFPCanonicalAdjointL2 period hPeriod (fun sector => (metric sector).metric) field =
      globalPairedAbelianFPL2LinearMap period hPeriod (fun sector => (metric sector).metric) field +
        pairedFPVolumeCorrection period hPeriod metric (pairedGhostH1 period hPeriod field) := by
  have hDifference :
      pairedFPCanonicalAdjointL2 period hPeriod (fun sector => (metric sector).metric) field -
      globalPairedAbelianFPL2LinearMap period hPeriod (fun sector => (metric sector).metric) field =
        pairedFPVolumeCorrection period hPeriod metric (pairedGhostH1 period hPeriod field) := by
    apply PiLp.ext
    intro index
    exact (fpVolumeCorrectionH1ToL2_actual period hPeriod (metric index.1) (field index.1) index.2).symm
  exact (sub_eq_iff_eq_add.mp hDifference).trans (add_comm _ _)

end
end JanusFormal.P0EFTJanusProgramPT12PairedFPH1Correction4D
