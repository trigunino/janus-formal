import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkDiffeomorphismGraphPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismStrongClosed4D

/-! Physical closed diagonal BRST realization at the actual intrinsic bulk background. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicDiffeomorphismBRSTStrongPhysical4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothBRSTCore4D P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismBilinearFamily4D
open P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

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
open P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismL2Core4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismStrongSmooth4D
open P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismStrongClosed4D
open P0EFTJanusProgramPT12IntrinsicBulkDiffeomorphismGraphPairing4D
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "metrics" => fun _ : Sector => metric
local notation "State" => GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFullL2Core4D
local notation "Mono" => FrameFreeDiffeomorphismFullL2 period hPeriod metric
local instance monoGroup : NormedAddCommGroup Mono := inferInstance
local instance : SeminormedAddCommGroup Mono := (monoGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Mono := inferInstance
local instance : InnerProductSpace Real Mono := inferInstance
local notation "Pair" => WithLp 2 (Mono × Mono)
local instance pairGroup : NormedAddCommGroup Pair := inferInstance
local instance : SeminormedAddCommGroup Pair := (pairGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Pair := inferInstance
local instance : InnerProductSpace Real Pair := inferInstance
abbrev IntrinsicDiffeomorphismPhysicalL2 := FrameFreeDiagonalDiffeomorphismL2 period hPeriod metrics
local notation "Core" => IntrinsicDiffeomorphismPhysicalL2 period hPeriod
local instance coreGroup : NormedAddCommGroup Core := inferInstance
local instance : SeminormedAddCommGroup Core := (coreGroup period hPeriod).toSeminormedAddCommGroup
local instance coreNormedSpace : NormedSpace Real Core :=
  Submodule.normedSpace (frameFreeDiagonalDiffeomorphismL2Space period hPeriod metrics)
local instance coreModule : Module Real Core := (coreNormedSpace period hPeriod).toModule
local instance : SMul Real Core := (coreModule period hPeriod).toSMul
local instance : InnerProductSpace Real Core := Submodule.innerProductSpace (𝕜 := Real) _
local instance coreTopology : IsTopologicalAddGroup Core := SeminormedAddCommGroup.toIsTopologicalAddGroup
local instance : ContinuousAdd Core := (coreTopology period hPeriod).toContinuousAdd
local instance : ContinuousConstSMul Real Core where
  continuous_const_smul scalar := (lipschitzWith_smul (β := Core) scalar).continuous
local notation "inc" => frameFreeDiagonalDiffeomorphismL2Smooth period hPeriod metrics
variable (couplings : GlobalCandidateAActionCouplings)
local instance : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings

def intrinsicDiffeomorphismBRSTStrongSmooth : State →ₗ[Real] Core :=
  frameFreeDiagonalDiffeomorphismStrongSmooth period hPeriod metrics couplings

def intrinsicDiffeomorphismBRSTStrongMinimal : Core →ₗ.[Real] Core :=
  frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metrics couplings

/-- Exact native bulk BRST pairing, retaining both metric columns and the shared triplet. -/
theorem intrinsicDiffeomorphismBRSTStrongSmooth_pairing (first second : State) :
    inner Real (intrinsicDiffeomorphismBRSTStrongSmooth period hPeriod couplings first) (inc second) =
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings first)
      (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings second) :=
  (frameFreeDiagonalDiffeomorphismStrongSmooth_pairing period hPeriod metrics couplings first second).trans
    (intrinsicBulkBRSTHessian_smoothDiffeomorphism_eq_offShellGraph period hPeriod couplings first second).symm

theorem intrinsicDiffeomorphismBRSTStrongMinimal_isClosed :
    (intrinsicDiffeomorphismBRSTStrongMinimal period hPeriod couplings).IsClosed :=
  frameFreeDiagonalDiffeomorphismStrongMinimal_isClosed period hPeriod metrics couplings

theorem intrinsicDiffeomorphismBRSTStrongMinimal_dense_domain :
    Dense ((intrinsicDiffeomorphismBRSTStrongMinimal period hPeriod couplings).domain : Set Core) :=
  frameFreeDiagonalDiffeomorphismStrongMinimal_dense_domain period hPeriod metrics couplings

theorem intrinsicDiffeomorphismBRSTStrongMinimal_hasCore :
    (intrinsicDiffeomorphismBRSTStrongMinimal period hPeriod couplings).HasCore (inc).range :=
  frameFreeDiagonalDiffeomorphismStrongMinimal_hasCore period hPeriod metrics couplings

theorem intrinsicDiffeomorphismBRSTStrongMinimal_symmetric :
    (intrinsicDiffeomorphismBRSTStrongMinimal period hPeriod couplings).IsFormalAdjoint
      (intrinsicDiffeomorphismBRSTStrongMinimal period hPeriod couplings) :=
  frameFreeDiagonalDiffeomorphismStrongMinimal_symmetric period hPeriod metrics couplings

theorem intrinsicDiffeomorphismBRSTStrongMinimal_pairing (first second : State) :
    inner Real (intrinsicDiffeomorphismBRSTStrongMinimal period hPeriod couplings
      ⟨inc first, frameFreeDiagonalDiffeomorphismStrongMinimal_smooth_mem period hPeriod metrics couplings first⟩)
      (inc second) =
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings first)
      (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings second) :=
  (frameFreeDiagonalDiffeomorphismStrongMinimal_pairing period hPeriod metrics couplings first second).trans
    (intrinsicBulkBRSTHessian_smoothDiffeomorphism_eq_offShellGraph period hPeriod couplings first second).symm

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicDiffeomorphismBRSTStrongPhysical4D
