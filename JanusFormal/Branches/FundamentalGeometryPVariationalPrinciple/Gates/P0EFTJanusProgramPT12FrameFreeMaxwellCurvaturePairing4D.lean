import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MaxwellCurvature4D

/-! Weak Cartan curvature identity on a finite redundant smooth frame. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeMaxwellCurvaturePairing4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusProgramPT12FrameFreeDivergenceStokes4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "μ" => intrinsicCanonicalLorentzVolumeMeasure period hPeriod
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D
open P0EFTJanusFiniteFrameC2MaxwellCurvature4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D

variable (frame : SmoothD8Frame period hPeriod)
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

/-- The curvature is determined weakly by the undifferentiated potential. -/
theorem frameFreeMaxwellCurvature_pairing
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin frame.count) (test : Scalar) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame potential component first second))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (finiteFramePotentialCoefficient period hPeriod frame potential component second))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFrameDerivativeAdjoint period hPeriod metric frame first test)) -
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (finiteFramePotentialCoefficient period hPeriod frame potential component first))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFrameDerivativeAdjoint period hPeriod metric frame second test)) -
    ∑ upper : Fin frame.count,
      inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (finiteFramePotentialCoefficient period hPeriod frame potential component upper))
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (canonicalScalarMul period hPeriod
            (finiteFrameStructureCoefficient period hPeriod frame metric first second upper) test)) := by
  rw [finiteFrameSmoothGaugeCurvatureCoefficient,
    finiteFrameBracketPotentialCoefficient_eq_sum period hPeriod frame metric]
  simp only [map_sub, map_sum, inner_sub_left, sum_inner]
  change inner Real (canonicalFrameDerivativeL2 period hPeriod frame first _) _ -
    inner Real (canonicalFrameDerivativeL2 period hPeriod frame second _) _ - _ = _
  rw [frameFreeFrameDerivativeAdjoint_pairing period hPeriod metric,
    frameFreeFrameDerivativeAdjoint_pairing period hPeriod metric]
  congr 1
  apply Finset.sum_congr rfl
  intro upper _
  exact canonicalScalarMul_pairing period hPeriod
    (finiteFrameStructureCoefficient period hPeriod frame metric first second upper) _ test

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeMaxwellCurvaturePairing4D
