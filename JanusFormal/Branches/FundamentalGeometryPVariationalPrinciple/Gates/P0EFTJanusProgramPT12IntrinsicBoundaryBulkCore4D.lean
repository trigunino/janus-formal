import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryC3Faithful4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D

/-! A closed compatibility core for the actual bulk and both boundary metrics,
with one shared normal displacement. C³ data introduce no independent metric
values: forgetting their extra regularity is injective. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryBulkCore4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Faithful4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusReciprocalBimetricPotential
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
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "C2" => GeneralMetricRelativeC2Core period hPeriod frame metric
local notation "C3" => FrameFreeBoundaryC3Core period hPeriod frame metric
local notation "Normal" => NormalBoundaryC2JetCore period hPeriod
local instance : NormedAddCommGroup C2 := (generalMetricRelativeC2CoreSubmodule period hPeriod frame metric).normedAddCommGroup
local instance : NormedSpace Real C2 := Submodule.normedSpace (generalMetricRelativeC2CoreSubmodule period hPeriod frame metric)
local instance : CompleteSpace C2 := generalMetricRelativeC2CoreCompleteSpace period hPeriod frame metric
local instance : CompactSpace (CutThroatBoundary period hPeriod) :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : NormedAddCommGroup Normal := (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real Normal := Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
local instance : CompleteSpace Normal := normalBoundaryC2JetCoreCompleteSpace period hPeriod
variable (couplings : GlobalCandidateAActionCouplings)
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local instance bulkNormedAddCommGroup : NormedAddCommGroup Bulk := inferInstance
local instance bulkNormedSpace : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings
local instance : AddZeroClass Bulk :=
  (bulkNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : CompleteSpace Bulk := by
  letI : CompleteSpace (P0EFTJanusFiniteFramePairedC2PhysicalAction4D.FiniteFramePairedC2PhysicalCore
      period hPeriod (intrinsicBulkGeometry period hPeriod) frame) := inferInstance
  letI : CompleteSpace (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod couplings.matterMassSquared) := inferInstance
  letI : CompleteSpace (C(Throat period hPeriod, LLFieldFiber) ×
      C(Throat period hPeriod, Fin (canonicalDivergenceFreeLLFrame period hPeriod).count → LLFieldFiber)) :=
    CompleteSpace.prod
  letI : CompleteSpace (C(Throat period hPeriod, Real) ×
      (C(Throat period hPeriod, LLFieldFiber) ×
        C(Throat period hPeriod, Fin (canonicalDivergenceFreeLLFrame period hPeriod).count → LLFieldFiber))) :=
    CompleteSpace.prod
  letI : CompleteSpace (GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)) := CompleteSpace.prod
  letI : CompleteSpace (GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)) := CompleteSpace.prod
  unfold IntrinsicBulkCore
    P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D.FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore
  infer_instance

local instance ambientNormedSpace : NormedSpace Real (Bulk × (C3 × C3)) :=
  letI : NormedSpace Real (C3 × C3) := Prod.normedSpace
  Prod.normedSpace
local instance ambientModule : Module Real (Bulk × (C3 × C3)) :=
  (ambientNormedSpace period hPeriod couplings).toModule
local instance ambientMulAction : MulAction Real (Bulk × (C3 × C3)) :=
  (ambientModule period hPeriod couplings).toDistribMulAction.toMulAction
local instance : SMul Real (Bulk × (C3 × C3)) :=
  (ambientMulAction period hPeriod couplings).toSMul
local instance : IsScalarTower Real Real (Bulk × (C3 × C3)) := ⟨mul_smul⟩

def intrinsicBulkMetricPairProjection : Bulk →L[Real] C2 × C2 :=
  (ContinuousLinearMap.fst Real _ _).comp
    ((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _))

@[simp] theorem intrinsicBulkMetricPairProjection_apply (point : Bulk) :
    intrinsicBulkMetricPairProjection period hPeriod couplings point = point.1.1.1 := rfl

def intrinsicBoundaryBulkMetricMismatch : Bulk × (C3 × C3) →L[Real] C2 × C2 :=
  (intrinsicBulkMetricPairProjection period hPeriod couplings).comp (ContinuousLinearMap.fst Real _ _) -
    ((frameFreeBoundaryC3CoreToC2 period hPeriod frame metric).prodMap
      (frameFreeBoundaryC3CoreToC2 period hPeriod frame metric)).comp (ContinuousLinearMap.snd Real _ _)

def intrinsicBoundaryBulkCompatibleSubmodule : Submodule Real (Bulk × (C3 × C3)) :=
  (intrinsicBoundaryBulkMetricMismatch period hPeriod couplings).ker

instance intrinsicBoundaryBulkCompatible_isClosed :
    IsClosed (intrinsicBoundaryBulkCompatibleSubmodule period hPeriod couplings : Set (Bulk × (C3 × C3))) :=
  (intrinsicBoundaryBulkMetricMismatch period hPeriod couplings).isClosed_ker

abbrev IntrinsicBoundaryBulkCore := intrinsicBoundaryBulkCompatibleSubmodule period hPeriod couplings × Normal
local notation "Core" => IntrinsicBoundaryBulkCore period hPeriod couplings
instance intrinsicBoundaryBulkCoreNormedAddCommGroup : NormedAddCommGroup Core := inferInstance
instance intrinsicBoundaryBulkCoreNormedSpace : NormedSpace Real Core :=
  letI : NormedSpace Real (intrinsicBoundaryBulkCompatibleSubmodule period hPeriod couplings) :=
    Submodule.normedSpace (intrinsicBoundaryBulkCompatibleSubmodule period hPeriod couplings)
  Prod.normedSpace
instance intrinsicBoundaryBulkCoreCompleteSpace : CompleteSpace Core := inferInstance
local instance : AddZeroClass Core :=
  (intrinsicBoundaryBulkCoreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : AddCommGroup Core :=
  (intrinsicBoundaryBulkCoreNormedAddCommGroup period hPeriod couplings).toAddCommGroup
local instance : Module Real Core :=
  (intrinsicBoundaryBulkCoreNormedSpace period hPeriod couplings).toModule
local instance coreDualNormedAddCommGroup : NormedAddCommGroup (Core →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance coreDualNormedSpace : NormedSpace Real (Core →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace
local instance : AddCommGroup (Core →L[Real] Real) :=
  (coreDualNormedAddCommGroup period hPeriod couplings).toAddCommGroup
local instance : Module Real (Core →L[Real] Real) :=
  (coreDualNormedSpace period hPeriod couplings).toModule

private def compatibleProjection : Core →L[Real] Bulk × (C3 × C3) :=
  (intrinsicBoundaryBulkCompatibleSubmodule period hPeriod couplings).subtypeL.comp
    (ContinuousLinearMap.fst Real _ _)

def intrinsicBoundaryBulkProjection : Core →L[Real] Bulk :=
  (ContinuousLinearMap.fst Real _ _).comp (compatibleProjection period hPeriod couplings)

def intrinsicBoundaryBulkC3Projection : Core →L[Real] C3 × C3 :=
  (ContinuousLinearMap.snd Real _ _).comp (compatibleProjection period hPeriod couplings)

def intrinsicBoundaryBulkNormalProjection : Core →L[Real] Normal := ContinuousLinearMap.snd Real _ _

theorem intrinsicBoundaryBulk_metrics_compatible (point : Core) :
    intrinsicBulkMetricPairProjection period hPeriod couplings
      (intrinsicBoundaryBulkProjection period hPeriod couplings point) =
    ((frameFreeBoundaryC3CoreToC2 period hPeriod frame metric)
        (intrinsicBoundaryBulkC3Projection period hPeriod couplings point).1,
      (frameFreeBoundaryC3CoreToC2 period hPeriod frame metric)
        (intrinsicBoundaryBulkC3Projection period hPeriod couplings point).2) :=
  sub_eq_zero.mp point.1.property

def intrinsicBoundaryBulkFaithfulProjection : Core →L[Real] Bulk × Normal :=
  (intrinsicBoundaryBulkProjection period hPeriod couplings).prod
    (intrinsicBoundaryBulkNormalProjection period hPeriod couplings)

theorem intrinsicBoundaryBulkFaithfulProjection_injective :
    Function.Injective (intrinsicBoundaryBulkFaithfulProjection period hPeriod couplings) := by
  intro first second hEqual
  have hBulk := congrArg Prod.fst hEqual
  change first.1.val.1 = second.1.val.1 at hBulk
  have hNormal := congrArg Prod.snd hEqual
  have hMetrics := (intrinsicBoundaryBulk_metrics_compatible period hPeriod couplings first).symm.trans
    ((congrArg (intrinsicBulkMetricPairProjection period hPeriod couplings) hBulk).trans
      (intrinsicBoundaryBulk_metrics_compatible period hPeriod couplings second))
  apply Prod.ext
  · apply Subtype.ext
    refine Prod.ext hBulk ?_
    apply Prod.ext
    · exact frameFreeBoundaryC3CanonicalToC2_injective period hPeriod metric
        (congrArg (Prod.fst : C2 × C2 → C2) hMetrics)
    · exact frameFreeBoundaryC3CanonicalToC2_injective period hPeriod metric
        (congrArg (Prod.snd : C2 × C2 → C2) hMetrics)
  · exact hNormal

def intrinsicBoundaryBulkPlusJoint : Core →L[Real] FrameFreeBoundaryJointCore period hPeriod frame metric :=
  ((ContinuousLinearMap.fst Real _ _).comp
    (intrinsicBoundaryBulkC3Projection period hPeriod couplings)).prod
      (intrinsicBoundaryBulkNormalProjection period hPeriod couplings)

def intrinsicBoundaryBulkMinusJoint : Core →L[Real] FrameFreeBoundaryJointCore period hPeriod frame metric :=
  ((ContinuousLinearMap.snd Real _ _).comp
    (intrinsicBoundaryBulkC3Projection period hPeriod couplings)).prod
      (intrinsicBoundaryBulkNormalProjection period hPeriod couplings)

def intrinsicBoundaryBulkDomain : Set Core :=
  intrinsicBoundaryBulkProjection period hPeriod couplings ⁻¹' intrinsicBulkDomain period hPeriod couplings

theorem intrinsicBoundaryBulkDomain_isOpen : IsOpen (intrinsicBoundaryBulkDomain period hPeriod couplings) :=
  (intrinsicBulkDomain_isOpen period hPeriod couplings).preimage
    (intrinsicBoundaryBulkProjection period hPeriod couplings).continuous

theorem intrinsicBoundaryBulkDomain_zero_mem : (0 : Core) ∈ intrinsicBoundaryBulkDomain period hPeriod couplings := by
  change intrinsicBoundaryBulkProjection period hPeriod couplings 0 ∈ intrinsicBulkDomain period hPeriod couplings
  rw [(intrinsicBoundaryBulkProjection period hPeriod couplings).map_zero]
  exact intrinsicBulkDomain_zero_mem period hPeriod couplings

def intrinsicBoundaryBulkAction (interactionScale : Real) (coefficients : PotentialCoefficients) (point : Core) : Real :=
  intrinsicBulkAction period hPeriod couplings interactionScale coefficients
    (intrinsicBoundaryBulkProjection period hPeriod couplings point)

theorem intrinsicBoundaryBulkAction_contDiffAt_zero (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffAt Real 2 (intrinsicBoundaryBulkAction period hPeriod couplings interactionScale coefficients) 0 := by
  have hBulk : ContDiffAt Real 2 (intrinsicBulkAction period hPeriod couplings interactionScale coefficients)
      (intrinsicBoundaryBulkProjection period hPeriod couplings 0) := by
    simpa only [(intrinsicBoundaryBulkProjection period hPeriod couplings).map_zero] using
      intrinsicBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients
  exact hBulk.comp 0 (intrinsicBoundaryBulkProjection period hPeriod couplings).contDiff.contDiffAt

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryBulkCore4D
