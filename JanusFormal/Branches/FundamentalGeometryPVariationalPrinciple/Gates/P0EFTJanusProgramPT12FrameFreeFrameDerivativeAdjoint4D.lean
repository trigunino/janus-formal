import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDivergenceStokes4D

/-! Canonical-volume adjoints for every finite smooth generating family,
using only an inhabited smooth Lorentz metric and the ten-flow Stokes theorem. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
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
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
variable (frame : SmoothD8Frame period hPeriod)

def frameFreeFrameDerivativeAdjoint (index : Fin frame.count) (test : Scalar) : Scalar :=
  -frameFreeTenFlowDivergence period hPeriod metric
    (smoothScalarSMulTangentField period hPeriod test (frameTangentField period hPeriod frame index))

theorem frameFreeFrameDerivativeAdjoint_integral (index : Fin frame.count) (field test : Scalar) :
    (∫ point, canonicalFrameDerivativeSmooth period hPeriod frame index field point * test point ∂μ) =
      ∫ point, field point * frameFreeFrameDerivativeAdjoint period hPeriod metric frame index test point ∂μ := by
  let vector := smoothScalarSMulTangentField period hPeriod test (frameTangentField period hPeriod frame index)
  have hDerivative : (fun point => mvfderiv coverModelWithCorners field.toFun point (vector point)) =
      (fun point => canonicalFrameDerivativeSmooth period hPeriod frame index field point * test point) := by
    funext point
    change mvfderiv coverModelWithCorners field.toFun point (test point • frame.vectorAt point index) = _
    rw [map_smul]
    exact mul_comm _ _
  have hStokes := frameFreeTenFlowDivergence_weak_stokes period hPeriod metric vector field
  rw [hDerivative] at hStokes
  calc
    _ = -(∫ point, field point * frameFreeTenFlowDivergence period hPeriod metric vector point ∂μ) := by
      linarith only [hStokes]
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with point
      change -(field point * _) = field point * (-_)
      ring

theorem frameFreeFrameDerivativeAdjoint_pairing (index : Fin frame.count) (field test : Scalar) :
    inner Real (canonicalFrameDerivativeL2 period hPeriod frame index field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFrameDerivativeAdjoint period hPeriod metric frame index test)) := by
  change inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
    (canonicalFrameDerivativeSmooth period hPeriod frame index field)) _ = _
  rw [canonicalScalarL2_inner, canonicalScalarL2_inner]
  exact frameFreeFrameDerivativeAdjoint_integral period hPeriod metric frame index field test

def frameFreeFirstOrderColumnAdjoint (first second : Fin frame.count)
    (zeroth firstWeight secondWeight test : Scalar) : Scalar :=
  canonicalScalarMul period hPeriod zeroth test +
    frameFreeFrameDerivativeAdjoint period hPeriod metric frame first
      (canonicalScalarMul period hPeriod firstWeight test) +
    frameFreeFrameDerivativeAdjoint period hPeriod metric frame second
      (canonicalScalarMul period hPeriod secondWeight test)

theorem frameFreeFirstOrderColumn_pairing (first second : Fin frame.count)
    (zeroth firstWeight secondWeight field test : Scalar) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (canonicalFirstOrderColumn period hPeriod frame first second zeroth firstWeight secondWeight field))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeFirstOrderColumnAdjoint period hPeriod metric frame first second zeroth firstWeight secondWeight test)) := by
  simp only [canonicalFirstOrderColumn, frameFreeFirstOrderColumnAdjoint,
    LinearMap.add_apply, LinearMap.comp_apply, map_add, inner_add_left, inner_add_right]
  apply congrArg₂ (fun left right : Real => left + right)
  · apply congrArg₂ (fun left right : Real => left + right)
    · exact canonicalScalarMul_pairing period hPeriod zeroth field test
    · exact (canonicalScalarMul_pairing period hPeriod firstWeight
        (canonicalFrameDerivativeSmooth period hPeriod frame first field) test).trans
        (frameFreeFrameDerivativeAdjoint_pairing period hPeriod metric frame first field
          (canonicalScalarMul period hPeriod firstWeight test))
  · exact (canonicalScalarMul_pairing period hPeriod secondWeight
      (canonicalFrameDerivativeSmooth period hPeriod frame second field) test).trans
      (frameFreeFrameDerivativeAdjoint_pairing period hPeriod metric frame second field
        (canonicalScalarMul period hPeriod secondWeight test))

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
