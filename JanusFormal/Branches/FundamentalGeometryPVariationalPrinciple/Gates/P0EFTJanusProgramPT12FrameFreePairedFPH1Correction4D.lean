import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFPH1Correction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFPVolumeH1Bound4D

/-! Paired FP correction on H¹ for smooth Lorentz metrics without a global tangent basis. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreePairedFPH1Correction4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12CanonicalDirectionalH1L24D
open P0EFTJanusProgramPT12PairedFPH1Correction4D
open P0EFTJanusProgramPT12FrameFreeFPVolumeH1Bound4D

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

def frameFreePairedFPVolumeCorrection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    PairedFPH1 period hPeriod →L[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  (PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalPairedAbelianLorenzCoordinateIndex => CanonicalPhysicalBulkL2 period hPeriod)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun index =>
        (frameFreeFPVolumeCorrectionH1ToL2 period hPeriod (metric index.1)).comp
          (PiLp.proj 2 (fun _ : GlobalPairedAbelianLorenzCoordinateIndex =>
            CanonicalTenFlowScalarH1 period hPeriod) index))

theorem frameFreePairedFPVolumeCorrection_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    pairedFPCanonicalAdjointL2 period hPeriod metric field =
      globalPairedAbelianFPL2LinearMap period hPeriod metric field +
        frameFreePairedFPVolumeCorrection period hPeriod metric (pairedGhostH1 period hPeriod field) := by
  have hDifference :
      pairedFPCanonicalAdjointL2 period hPeriod metric field -
      globalPairedAbelianFPL2LinearMap period hPeriod metric field =
        frameFreePairedFPVolumeCorrection period hPeriod metric (pairedGhostH1 period hPeriod field) := by
    apply PiLp.ext
    intro index
    exact (frameFreeFPVolumeCorrectionH1ToL2_actual period hPeriod
      (metric index.1) (field index.1) index.2).symm
  exact (sub_eq_iff_eq_add.mp hDifference).trans (add_comm _ _)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreePairedFPH1Correction4D
