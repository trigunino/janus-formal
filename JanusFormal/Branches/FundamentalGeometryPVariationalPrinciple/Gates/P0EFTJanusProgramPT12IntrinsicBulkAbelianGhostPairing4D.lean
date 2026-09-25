import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeAbelianGhostSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianGraphPairing4D

/-! The actual self-adjoint L² ghost block represents the native bulk BRST
Hessian on faithful paired smooth ghost states, with the native positive FP sign. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianGhostPairing4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D
open P0EFTJanusProgramPT12FrameFreeAbelianGhostSelfAdjoint4D
open P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D P0EFTJanusProgramPT12GhostRotationDefect4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothAbelianBRSTCore4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianGraphPairing4D
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

def frameFreeAbelianGhostSmoothDomain (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    (frameFreeAbelianGhostOperator period hPeriod metric).domain :=
  ⟨WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod antighost,
      globalPairedGaugeLieL2LinearMap period hPeriod ghost),
    LinearPMap.mem_domain_of_mem_graph
      (frameFreeAbelianGhostOperator_smooth_graph period hPeriod metric antighost ghost)⟩

theorem frameFreeAbelianGhostOperator_smooth_apply
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    frameFreeAbelianGhostOperator period hPeriod metric
        (frameFreeAbelianGhostSmoothDomain period hPeriod metric antighost ghost) =
      WithLp.toLp 2 (globalPairedAbelianFPL2LinearMap period hPeriod metric ghost,
        pairedFPCanonicalAdjointL2 period hPeriod metric antighost) :=
  (frameFreeAbelianGhostOperator period hPeriod metric).mem_graph_snd_inj
    ((frameFreeAbelianGhostOperator period hPeriod metric).mem_graph
      (frameFreeAbelianGhostSmoothDomain period hPeriod metric antighost ghost))
    (frameFreeAbelianGhostOperator_smooth_graph period hPeriod metric antighost ghost) rfl

theorem frameFreeAbelianGhostOperator_smooth_hessian
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (a c b d : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real (frameFreeAbelianGhostOperator period hPeriod metric
        (frameFreeAbelianGhostSmoothDomain period hPeriod metric a c))
      (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod b,
        globalPairedGaugeLieL2LinearMap period hPeriod d)) =
    globalPairedAbelianOffShellHessian period hPeriod metric
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric (pureAbelianGhostPair period hPeriod a c))
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric (pureAbelianGhostPair period hPeriod b d)) := by
  rw [frameFreeAbelianGhostOperator_smooth_apply, pureAbelianGhostPair_hessian]
  change inner Real (globalPairedAbelianFPL2LinearMap period hPeriod metric c)
      (globalPairedGaugeLieL2LinearMap period hPeriod b) +
    inner Real (pairedFPCanonicalAdjointL2 period hPeriod metric a)
      (globalPairedGaugeLieL2LinearMap period hPeriod d) = _
  have hAdj : inner Real (pairedFPCanonicalAdjointL2 period hPeriod metric a)
      (globalPairedGaugeLieL2LinearMap period hPeriod d) =
    inner Real (globalPairedGaugeLieL2LinearMap period hPeriod a)
      (globalPairedAbelianFPL2LinearMap period hPeriod metric d) :=
    (real_inner_comm _ _).trans
      ((frameFreePairedFPCanonicalAdjoint_pairing period hPeriod metric d a).symm.trans
        (real_inner_comm _ _))
  rw [hAdj, ghostCrossPairing, add_comm]

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
variable (couplings : GlobalCandidateAActionCouplings)
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local instance : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings

theorem intrinsicBulkSmoothGhostPair_injective :
    Function.Injective (fun pair : GlobalPairedGaugeLieSmooth period hPeriod × GlobalPairedGaugeLieSmooth period hPeriod =>
      intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
        (pureAbelianGhostPair period hPeriod pair.1 pair.2)) := by
  intro first second hEqual
  have hState := intrinsicBulkSmoothAbelianBRSTInsertion_injective period hPeriod couplings hEqual
  apply Prod.ext
  · funext sector
    exact congrArg (fun state : GlobalPairedAbelianBRSTState period hPeriod =>
      (state.nonminimal sector).antighost.field) hState
  · funext sector
    exact congrArg (fun state : GlobalPairedAbelianBRSTState period hPeriod =>
      (state.nonminimal sector).ghost.field) hState

theorem intrinsicBulkBRSTHessian_ghost_eq_L2_pairing
    (a c b d : GlobalPairedGaugeLieSmooth period hPeriod) :
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings (pureAbelianGhostPair period hPeriod a c))
      (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings (pureAbelianGhostPair period hPeriod b d)) =
    inner Real (frameFreeAbelianGhostOperator period hPeriod (fun _ => base)
        (frameFreeAbelianGhostSmoothDomain period hPeriod (fun _ => base) a c))
      (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod b,
        globalPairedGaugeLieL2LinearMap period hPeriod d)) :=
  (intrinsicBulkBRSTHessian_smoothAbelian_eq_offShellGraph period hPeriod couplings
    (pureAbelianGhostPair period hPeriod a c) (pureAbelianGhostPair period hPeriod b d)).trans
      (frameFreeAbelianGhostOperator_smooth_hessian period hPeriod (fun _ => base) a c b d).symm

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianGhostPairing4D
