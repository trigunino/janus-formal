import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalFrameDerivativeClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDivergenceStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Concrete canonical-volume formal adjoints for every derivative of a smooth
finite generating frame. The integration-by-parts identity is proved by Stokes. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeFrameDerivativeClosed4D
set_option autoImplicit false


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

open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusProgramPT12FrameFreeDivergenceStokes4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeClosed4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

def frameFreeCanonicalFrameDerivativeAdjoint 
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (test : SmoothQuotientField period hPeriod Real) : SmoothQuotientField period hPeriod Real :=
  -frameFreeTenFlowDivergence period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    (smoothScalarSMulTangentField period hPeriod test (frameTangentField period hPeriod frame index))

theorem frameFreeCanonicalFrameDerivativeAdjoint_integral
    
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (field test : SmoothQuotientField period hPeriod Real) :
    (∫ point, canonicalFrameDerivativeSmooth period hPeriod frame index field point * test point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
    ∫ point, field point * frameFreeCanonicalFrameDerivativeAdjoint period hPeriod frame index test point
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
  have hStokes := frameFreeTenFlowDivergence_weak_stokes period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod) vector field
  rw [hDerivative] at hStokes
  calc
    _ = ∫ point, test point * canonicalFrameDerivativeSmooth period hPeriod frame index field point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact mul_comm _ _
    _ = -(∫ point, field point * frameFreeTenFlowDivergence period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod) vector point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by linarith only [hStokes]
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with point
      change -(field point * _) = field point * (-_)
      ring

theorem frameFreeCanonicalFrameDerivativeAdjoint_pairing
    
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (field test : SmoothQuotientField period hPeriod Real) :
    inner Real (canonicalFrameDerivativeL2 period hPeriod frame index field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (frameFreeCanonicalFrameDerivativeAdjoint period hPeriod frame index test)) := by
  change inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
    (canonicalFrameDerivativeSmooth period hPeriod frame index field)) _ = _
  rw [canonicalScalarL2_inner, canonicalScalarL2_inner]
  exact frameFreeCanonicalFrameDerivativeAdjoint_integral period hPeriod frame index field test

/-- No regular metric is needed for the closability of a genuine smooth derivative. -/
theorem frameFreeCanonicalFrameDerivativeGraph_input_injective
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count) :
    Function.Injective (fun graph : linearFeatureGraphClosure
      (smoothToCanonicalPhysicalBulkL2 period hPeriod)
      (canonicalFrameDerivativeL2 period hPeriod frame index) => graph.val.1) :=
  linearFeatureGraphClosure_fst_injective _ _
    (fun test => smoothToCanonicalPhysicalBulkL2 period hPeriod
      (frameFreeCanonicalFrameDerivativeAdjoint period hPeriod frame index test))
    (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod)
    (frameFreeCanonicalFrameDerivativeAdjoint_pairing period hPeriod frame index)

theorem frameFreeCanonicalFrameDerivativeMinimal_isClosed
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count) :
    (canonicalFrameDerivativeMinimal period hPeriod frame index).IsClosed :=
  closedFeatureOperator_isClosed _ _
    (frameFreeCanonicalFrameDerivativeGraph_input_injective period hPeriod frame index)

theorem frameFreeCanonicalFrameDerivativeMinimal_smooth_apply
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalFrameDerivativeMinimal period hPeriod frame index
      ⟨smoothToCanonicalPhysicalBulkL2 period hPeriod field,
        canonicalFrameDerivativeMinimal_smooth_mem period hPeriod frame index field⟩ =
      canonicalFrameDerivativeL2 period hPeriod frame index field :=
  closedFeatureOperator_smooth_apply _ _
    (frameFreeCanonicalFrameDerivativeGraph_input_injective period hPeriod frame index) field

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeFrameDerivativeClosed4D
