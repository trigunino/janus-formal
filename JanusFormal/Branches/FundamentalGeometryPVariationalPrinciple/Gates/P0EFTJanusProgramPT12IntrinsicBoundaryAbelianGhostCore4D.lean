import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBoundaryBulkCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianGhostPairing4D

/-! Faithful smooth Abelian ghost pairs in the compatible bulk/boundary core.
Both C³ metric variations and the shared boundary displacement are zero. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryAbelianGhostCore4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameMetricContraction4D P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothAbelianBRSTCore4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianGhostPairing4D
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

private theorem smoothGhost_metricProjection_zero
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    intrinsicBulkMetricPairProjection period hPeriod couplings
      (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
        (pureAbelianGhostPair period hPeriod antighost ghost)) = 0 :=
  (intrinsicBulkMetricPairProjection_apply period hPeriod couplings _).trans
    (intrinsicBulkSmoothAbelianBRSTInsertion_metric period hPeriod couplings
      (pureAbelianGhostPair period hPeriod antighost ghost))

def intrinsicBoundarySmoothAbelianGhostInsertion
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) : Core :=
  (⟨(intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
      (pureAbelianGhostPair period hPeriod antighost ghost), 0),
    zeroBoundary_compatible period hPeriod couplings _
      (smoothGhost_metricProjection_zero period hPeriod couplings antighost ghost)⟩, 0)

theorem intrinsicBoundarySmoothAbelianGhostInsertion_bulk
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    intrinsicBoundaryBulkProjection period hPeriod couplings
      (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) =
    intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
      (pureAbelianGhostPair period hPeriod antighost ghost) := rfl

theorem intrinsicBoundarySmoothAbelianGhostInsertion_plusJoint
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    intrinsicBoundaryBulkPlusJoint period hPeriod couplings
      (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) = 0 := rfl

theorem intrinsicBoundarySmoothAbelianGhostInsertion_minusJoint
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    intrinsicBoundaryBulkMinusJoint period hPeriod couplings
      (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) = 0 := rfl

theorem intrinsicBoundarySmoothAbelianGhostInsertion_injective :
    Function.Injective (fun pair : GlobalPairedGaugeLieSmooth period hPeriod × GlobalPairedGaugeLieSmooth period hPeriod =>
      intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings pair.1 pair.2) := by
  intro first second hEqual
  exact intrinsicBulkSmoothGhostPair_injective period hPeriod couplings
    (congrArg (intrinsicBoundaryBulkProjection period hPeriod couplings) hEqual)

private theorem smoothPotentialCoefficients_zero :
    finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame 0 = 0 := by
  funext component index
  have hCoefficient : finiteFramePotentialCoefficient period hPeriod frame 0 component index = 0 := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    rfl
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod _ = 0
  rw [hCoefficient]
  exact (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod).map_zero

/-- The smooth pair lies in the already constructed completed nonminimal sector. -/
theorem intrinsicBulkSmoothGhostPair_mem_nonminimal
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    ∃ fields : IntrinsicBulkAbelianNonminimalCore period hPeriod,
      intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
        (pureAbelianGhostPair period hPeriod antighost ghost) =
      intrinsicBulkAbelianNonminimalInsertion period hPeriod couplings fields := by
  let point := intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
    (pureAbelianGhostPair period hPeriod antighost ghost)
  refine ⟨(point.1.1.2.1.1.2, point.1.1.2.1.2.2), ?_⟩
  have hPlus : point.1.1.2.1.1.1 = 0 := smoothPotentialCoefficients_zero period hPeriod
  have hMinus : point.1.1.2.1.2.1 = 0 := smoothPotentialCoefficients_zero period hPeriod
  have hFields : point.1.1.2.1 =
      ((0, point.1.1.2.1.1.2), (0, point.1.1.2.1.2.2)) :=
    Prod.ext (Prod.ext hPlus (Eq.refl point.1.1.2.1.1.2))
      (Prod.ext hMinus (Eq.refl point.1.1.2.1.2.2))
  exact Prod.ext (Prod.ext (Prod.ext
    (intrinsicBulkSmoothAbelianBRSTInsertion_metric period hPeriod couplings
      (pureAbelianGhostPair period hPeriod antighost ghost))
    (Prod.ext hFields rfl)) rfl) rfl

open P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D

private theorem pairedAbelian_metricProjection_zero
    (fields : IntrinsicBulkPairedAbelianCore period hPeriod) :
    intrinsicBulkMetricPairProjection period hPeriod couplings
      (intrinsicBulkPairedAbelianInsertion period hPeriod couplings fields) = 0 := rfl

/-- Both complete Abelian packets in the genuine compatible bulk/boundary core. -/
def intrinsicBoundaryPairedAbelianInsertion
    (fields : IntrinsicBulkPairedAbelianCore period hPeriod) : Core :=
  (⟨(intrinsicBulkPairedAbelianInsertion period hPeriod couplings fields, 0),
    zeroBoundary_compatible period hPeriod couplings _
      (pairedAbelian_metricProjection_zero period hPeriod couplings fields)⟩, 0)

theorem intrinsicBoundaryPairedAbelianInsertion_bulk
    (fields : IntrinsicBulkPairedAbelianCore period hPeriod) :
    intrinsicBoundaryBulkProjection period hPeriod couplings
      (intrinsicBoundaryPairedAbelianInsertion period hPeriod couplings fields) =
    intrinsicBulkPairedAbelianInsertion period hPeriod couplings fields := rfl

theorem intrinsicBoundaryPairedAbelianInsertion_plusJoint
    (fields : IntrinsicBulkPairedAbelianCore period hPeriod) :
    intrinsicBoundaryBulkPlusJoint period hPeriod couplings
      (intrinsicBoundaryPairedAbelianInsertion period hPeriod couplings fields) = 0 := rfl

theorem intrinsicBoundaryPairedAbelianInsertion_minusJoint
    (fields : IntrinsicBulkPairedAbelianCore period hPeriod) :
    intrinsicBoundaryBulkMinusJoint period hPeriod couplings
      (intrinsicBoundaryPairedAbelianInsertion period hPeriod couplings fields) = 0 := rfl

theorem intrinsicBoundaryPairedAbelianInsertion_injective :
    Function.Injective (intrinsicBoundaryPairedAbelianInsertion period hPeriod couplings) := by
  intro first second hEqual
  exact congrArg (fun input : Core =>
    (intrinsicBoundaryBulkProjection period hPeriod couplings input).1.1.2.1) hEqual

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryAbelianGhostCore4D
