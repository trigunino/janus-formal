import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D

/-! Minimal closed canonical L² realizations of the actual frame derivatives. -/
namespace JanusFormal.P0EFTJanusProgramPT12CanonicalFrameDerivativeClosed4D
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

open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D

/-- Stokes and unconditional smooth density exclude every vertical graph vector. -/
theorem canonicalFrameDerivativeGraph_input_injective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count) :
    Function.Injective (fun graph : linearFeatureGraphClosure
      (smoothToCanonicalPhysicalBulkL2 period hPeriod)
      (canonicalFrameDerivativeL2 period hPeriod frame index) => graph.val.1) :=
  linearFeatureGraphClosure_fst_injective _ _
    (fun test => smoothToCanonicalPhysicalBulkL2 period hPeriod
      (canonicalFrameDerivativeAdjoint period hPeriod metric frame index test))
    (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod)
    (canonicalFrameDerivativeAdjoint_pairing period hPeriod metric frame index)

def canonicalFrameDerivativeMinimal (frame : SmoothD8Frame period hPeriod)
    (index : Fin frame.count) :
    CanonicalPhysicalBulkL2 period hPeriod →ₗ.[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  closedFeatureOperator (smoothToCanonicalPhysicalBulkL2 period hPeriod)
    (canonicalFrameDerivativeL2 period hPeriod frame index)

theorem canonicalFrameDerivativeMinimal_isClosed
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count) :
    (canonicalFrameDerivativeMinimal period hPeriod frame index).IsClosed :=
  closedFeatureOperator_isClosed _ _
    (canonicalFrameDerivativeGraph_input_injective period hPeriod metric frame index)

theorem canonicalFrameDerivativeMinimal_denseDomain
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count) :
    Dense ((canonicalFrameDerivativeMinimal period hPeriod frame index).domain :
      Set (CanonicalPhysicalBulkL2 period hPeriod)) :=
  closedFeatureOperator_dense_domain _ _ (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod)

theorem canonicalFrameDerivativeMinimal_hasCore
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count) :
    (canonicalFrameDerivativeMinimal period hPeriod frame index).HasCore
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).range :=
  closedFeatureOperator_hasCore _ _
    (canonicalFrameDerivativeGraph_input_injective period hPeriod metric frame index)

theorem canonicalFrameDerivativeMinimal_smooth_mem
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (field : SmoothQuotientField period hPeriod Real) :
    smoothToCanonicalPhysicalBulkL2 period hPeriod field ∈
      (canonicalFrameDerivativeMinimal period hPeriod frame index).domain :=
  closedFeatureOperator_smooth_mem _ _ field

theorem canonicalFrameDerivativeMinimal_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalFrameDerivativeMinimal period hPeriod frame index
      ⟨smoothToCanonicalPhysicalBulkL2 period hPeriod field,
        canonicalFrameDerivativeMinimal_smooth_mem period hPeriod frame index field⟩ =
      canonicalFrameDerivativeL2 period hPeriod frame index field :=
  closedFeatureOperator_smooth_apply _ _
    (canonicalFrameDerivativeGraph_input_injective period hPeriod metric frame index) field

end
end JanusFormal.P0EFTJanusProgramPT12CanonicalFrameDerivativeClosed4D
