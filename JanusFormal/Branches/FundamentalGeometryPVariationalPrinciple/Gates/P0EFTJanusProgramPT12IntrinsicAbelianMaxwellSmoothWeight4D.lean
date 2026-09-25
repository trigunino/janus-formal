import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SmoothMatrixL24D

/-! Smooth coefficients for the exact native Maxwell Hessian at the intrinsic background. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellSmoothWeight4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2MaxwellCurvature4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusFiniteFrameMetricContraction4D
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "Scalar" => P0EFTJanusMappingTorusSmoothFieldDescent4D.SmoothQuotientField period hPeriod Real
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod
local notation "μ" => intrinsicCanonicalLorentzVolumeMeasure period hPeriod

private theorem inverse_zero (row column : N) :
    finiteFrameInverseMetricC0Coefficient period hPeriod frame base row column 0 =
    smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (finiteFrameInverseMetricCoefficient period hPeriod frame base base row column) := by
  simpa only [map_zero] using finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame base
    0 base (by simp) (by simpa only [map_zero] using
      zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame base) row column

def intrinsicAbelianMaxwellWeight (first second raisedFirst raisedSecond : N) : Scalar :=
  canonicalScalarMul period hPeriod (globalSmoothMetricVolumeRatio period hPeriod base)
    ((-(1 / 4 : Real)) • canonicalScalarMul period hPeriod
      (finiteFrameInverseMetricCoefficient period hPeriod frame base base first raisedFirst)
      (finiteFrameInverseMetricCoefficient period hPeriod frame base base second raisedSecond))

theorem intrinsicAbelianMaxwellWeight_continuous (first second raisedFirst raisedSecond : N) :
    smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (intrinsicAbelianMaxwellWeight period hPeriod first second raisedFirst raisedSecond) =
    finiteFrameCanonicalVolumeC0 period hPeriod frame base 0 *
      ((-(1 / 4 : Real)) •
        (finiteFrameInverseMetricC0Coefficient period hPeriod frame base first raisedFirst 0 *
          finiteFrameInverseMetricC0Coefficient period hPeriod frame base second raisedSecond 0)) := by
  rw [finiteFrameCanonicalVolumeC0_zero, inverse_zero, inverse_zero]
  apply ContinuousMap.ext
  intro point
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellSmoothWeight4D
