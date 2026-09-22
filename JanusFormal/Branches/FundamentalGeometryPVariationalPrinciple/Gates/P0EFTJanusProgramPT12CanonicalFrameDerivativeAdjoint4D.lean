import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Concrete canonical-volume formal adjoints for every derivative of a smooth
finite generating frame. The integration-by-parts identity is proved by Stokes. -/
namespace JanusFormal.P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

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

def frameTangentField (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count) :
    SmoothTangentField period hPeriod where
  toFun point := frame.vectorAt point index
  contMDiff_toFun := frame.contMDiff_vector index

def canonicalFrameDerivativeSmooth (frame : SmoothD8Frame period hPeriod)
    (index : Fin frame.count) :
    SmoothQuotientField period hPeriod Real →ₗ[Real] SmoothQuotientField period hPeriod Real where
  toFun field := frameDerivativeComponentField period hPeriod frame field index
  map_add' first second := frameDerivativeComponentField_add period hPeriod frame first second index
  map_smul' scalar field := frameDerivativeComponentField_smul period hPeriod frame scalar field index

def canonicalFrameDerivativeAdjoint (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (test : SmoothQuotientField period hPeriod Real) : SmoothQuotientField period hPeriod Real :=
  -canonicalTenFlowDivergence period hPeriod metric
    (smoothScalarSMulTangentField period hPeriod test (frameTangentField period hPeriod frame index))

theorem canonicalFrameDerivativeAdjoint_integral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (field test : SmoothQuotientField period hPeriod Real) :
    (∫ point, canonicalFrameDerivativeSmooth period hPeriod frame index field point * test point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
    ∫ point, field point * canonicalFrameDerivativeAdjoint period hPeriod metric frame index test point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  let vector := smoothScalarSMulTangentField period hPeriod test
    (frameTangentField period hPeriod frame index)
  have hDerivative : (fun point => mvfderiv coverModelWithCorners field.toFun point (vector point)) =
      (fun point => test point * canonicalFrameDerivativeSmooth period hPeriod frame index field point) := by
    funext point
    change mvfderiv coverModelWithCorners field.toFun point
      (test point • frame.vectorAt point index) = _
    rw [map_smul]
    rfl
  have hStokes := canonicalTenFlowDivergence_weak_stokes period hPeriod metric vector field
  rw [hDerivative] at hStokes
  calc
    _ = ∫ point, test point * canonicalFrameDerivativeSmooth period hPeriod frame index field point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact mul_comm _ _
    _ = -(∫ point, field point * canonicalTenFlowDivergence period hPeriod metric vector point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by linarith only [hStokes]
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with point
      change -(field point * _) = field point * (-_)
      ring

theorem canonicalScalarL2_inner
    (first second : SmoothQuotientField period hPeriod Real) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod second) =
      ∫ point, first point * second point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [smoothFieldToL2_ae period hPeriod Real (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) first,
     smoothFieldToL2_ae period hPeriod Real (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) second]
    with point hFirst hSecond
  change inner Real
    ((smoothFieldToL2 period hPeriod Real (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) first :
      EffectiveQuotient period hPeriod → Real) point)
    ((smoothFieldToL2 period hPeriod Real (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) second :
      EffectiveQuotient period hPeriod → Real) point) = _
  rw [hFirst, hSecond]
  exact Real.inner_apply _ _

def canonicalFrameDerivativeL2 (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count) :
    SmoothQuotientField period hPeriod Real →ₗ[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
    (canonicalFrameDerivativeSmooth period hPeriod frame index)

theorem canonicalFrameDerivativeAdjoint_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (field test : SmoothQuotientField period hPeriod Real) :
    inner Real (canonicalFrameDerivativeL2 period hPeriod frame index field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (canonicalFrameDerivativeAdjoint period hPeriod metric frame index test)) := by
  change inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
    (canonicalFrameDerivativeSmooth period hPeriod frame index field)) _ = _
  rw [canonicalScalarL2_inner, canonicalScalarL2_inner]
  exact canonicalFrameDerivativeAdjoint_integral period hPeriod metric frame index field test

end
end JanusFormal.P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
