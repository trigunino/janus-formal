import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBoundaryBulkCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostRadical4D

/-! The genuine shared smooth antighost in the compatible boundary/bulk core.
The insertion and its faithfulness require no equation on kinetic weights. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryDiffeomorphismAntighostCore4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostRadical4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
open P0EFTJanusProgramPT12IntrinsicBoundaryBulkCore4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (Throat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Throat period hPeriod) := borel _
local instance : BorelSpace (Throat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert := InnerProductSpace.complexToReal
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "C3" => FrameFreeBoundaryC3Core period hPeriod frame base
variable (couplings : GlobalCandidateAActionCouplings)
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local notation "Core" => IntrinsicBoundaryBulkCore period hPeriod couplings
local instance bulkNormedAddCommGroup : NormedAddCommGroup Bulk := inferInstance
local instance : AddZeroClass Bulk :=
  (bulkNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings
local instance : NormedSpace Real (Bulk × (C3 × C3)) :=
  ambientNormedSpace period hPeriod couplings

private theorem zeroBoundary_compatible (point : Bulk)
    (hMetric : intrinsicBulkMetricPairProjection period hPeriod couplings point = 0) :
    (point, (0 : C3 × C3)) ∈ intrinsicBoundaryBulkCompatibleSubmodule period hPeriod couplings := by
  change intrinsicBulkMetricPairProjection period hPeriod couplings point -
    ((frameFreeBoundaryC3CoreToC2 period hPeriod frame base).prodMap
      (frameFreeBoundaryC3CoreToC2 period hPeriod frame base)) 0 = 0
  exact sub_eq_zero.mpr (hMetric.trans
    ((frameFreeBoundaryC3CoreToC2 period hPeriod frame base).prodMap
      (frameFreeBoundaryC3CoreToC2 period hPeriod frame base)).map_zero.symm)

private theorem smoothAntighost_metricProjection_zero
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    intrinsicBulkMetricPairProjection period hPeriod couplings
      (intrinsicBulkSmoothAntighostInsertion period hPeriod couplings antighost) = 0 := by
  change (smoothToGeneralMetricRelativeC2Core period hPeriod frame base 0,
    smoothToGeneralMetricRelativeC2Core period hPeriod frame base 0) = 0
  simp only [(smoothToGeneralMetricRelativeC2Core period hPeriod frame base).map_zero]
  rfl

def intrinsicBoundarySmoothAntighostInsertion
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) : Core :=
  (⟨(intrinsicBulkSmoothAntighostInsertion period hPeriod couplings antighost, 0),
    zeroBoundary_compatible period hPeriod couplings _
      (smoothAntighost_metricProjection_zero period hPeriod couplings antighost)⟩, 0)

theorem intrinsicBoundarySmoothAntighostInsertion_bulk
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    intrinsicBoundaryBulkProjection period hPeriod couplings
      (intrinsicBoundarySmoothAntighostInsertion period hPeriod couplings antighost) =
    intrinsicBulkSmoothAntighostInsertion period hPeriod couplings antighost := rfl

theorem intrinsicBoundarySmoothAntighostInsertion_plusJoint
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    intrinsicBoundaryBulkPlusJoint period hPeriod couplings
      (intrinsicBoundarySmoothAntighostInsertion period hPeriod couplings antighost) = 0 := rfl

theorem intrinsicBoundarySmoothAntighostInsertion_minusJoint
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    intrinsicBoundaryBulkMinusJoint period hPeriod couplings
      (intrinsicBoundarySmoothAntighostInsertion period hPeriod couplings antighost) = 0 := rfl

theorem intrinsicBoundarySmoothAntighostInsertion_injective :
    Function.Injective (intrinsicBoundarySmoothAntighostInsertion period hPeriod couplings) := by
  intro first second hEqual
  exact intrinsicBulkSmoothAntighostInsertion_injective period hPeriod couplings
    (congrArg (intrinsicBoundaryBulkProjection period hPeriod couplings) hEqual)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryDiffeomorphismAntighostCore4D
