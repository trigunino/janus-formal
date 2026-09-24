import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostInfiniteKernel4D
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Group.Quotient

/-! Bilinear reduction by the closed image of genuine smooth ghosts. Only the
bulk Hessian descends here; no action, BRST, or Fredholm descent is asserted. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkSmoothGhostQuotient4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostInfiniteKernel4D
open P0EFTJanusReciprocalBimetricPotential
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

private theorem symmetry_of_surjective {Source Target : Type*}
    (projection : Source → Target) (hSurjective : Function.Surjective projection)
    (pairing : Target → Target → Real)
    (hSymmetry : ∀ first second, pairing (projection first) (projection second) =
      pairing (projection second) (projection first)) (first second : Target) :
    pairing first second = pairing second first := by
  obtain ⟨first, rfl⟩ := hSurjective first
  obtain ⟨second, rfl⟩ := hSurjective second
  exact hSymmetry first second

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
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local instance coreNormedAddCommGroup : NormedAddCommGroup Core := inferInstance
local instance coreNormedSpace : NormedSpace Real Core :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local instance coreModule : Module Real Core :=
  (coreNormedSpace period hPeriod couplings).toModule
local instance coreMulAction : MulAction Real Core :=
  (coreModule period hPeriod couplings).toDistribMulAction.toMulAction
local instance : SMul Real Core := (coreMulAction period hPeriod couplings).toSMul
local instance : AddZeroClass Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance coreTopologicalAddGroup : IsTopologicalAddGroup Core :=
  @SeminormedAddCommGroup.toIsTopologicalAddGroup Core
    (coreNormedAddCommGroup period hPeriod couplings).toSeminormedAddCommGroup
local instance : ContinuousAdd Core :=
  (coreTopologicalAddGroup period hPeriod couplings).toContinuousAdd
local instance : IsBoundedSMul Real Core :=
  IsBoundedSMul.of_norm_smul_le (NormedSpace.norm_smul_le (𝕜 := Real) (E := Core))
local instance : ContinuousSMul Real Core := IsBoundedSMul.continuousSMul
local instance : ContinuousConstSMul Real Core := ContinuousSMul.continuousConstSMul

def intrinsicBulkSmoothGhostRadical : Submodule Real Core :=
  (LinearMap.range (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings)).topologicalClosure
local notation "R" => intrinsicBulkSmoothGhostRadical period hPeriod couplings

instance intrinsicBulkSmoothGhostRadical_isClosed : IsClosed (R : Set Core) :=
  (LinearMap.range (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings)).isClosed_topologicalClosure

theorem intrinsicBulkSmoothGhostRadical_smooth_mem
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings ghost ∈ R :=
  (LinearMap.range (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings)).le_topologicalClosure
    ⟨ghost, rfl⟩

theorem intrinsicBulkSmoothGhostRadical_minimal (subspace : Submodule Real Core)
    (hClosed : IsClosed (subspace : Set Core))
    (hGhost : ∀ ghost : GlobalDiffeomorphismGhostField period hPeriod,
      intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings ghost ∈ subspace) :
    R ≤ subspace := by
  apply (LinearMap.range (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings)).topologicalClosure_minimal
    (fun _ ⟨ghost, hGhostEq⟩ => hGhostEq ▸ hGhost ghost) hClosed

abbrev IntrinsicBulkSmoothGhostQuotient := Core ⧸ R
local notation "Reduced" => IntrinsicBulkSmoothGhostQuotient period hPeriod couplings
local instance : IsScalarTower Real Real Core := ⟨mul_smul⟩
local instance reducedNormedAddCommGroup : NormedAddCommGroup Reduced :=
  Submodule.Quotient.normedAddCommGroup (R)
local instance reducedNormedSpace : NormedSpace Real Reduced :=
  Submodule.Quotient.normedSpace (R) Real
local instance reducedModule : Module Real Reduced :=
  (reducedNormedSpace period hPeriod couplings).toModule
local instance reducedMulAction : MulAction Real Reduced :=
  (reducedModule period hPeriod couplings).toDistribMulAction.toMulAction
local instance : SMul Real Reduced := (reducedMulAction period hPeriod couplings).toSMul

def intrinsicBulkSmoothGhostQuotientMap : Core →L[Real] Reduced := (R).mkQL

theorem intrinsicBulkSmoothGhostQuotientMap_smooth_ghost_zero
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    intrinsicBulkSmoothGhostQuotientMap period hPeriod couplings
      (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings ghost) = 0 :=
  (Submodule.Quotient.mk_eq_zero (R)).mpr
    (intrinsicBulkSmoothGhostRadical_smooth_mem period hPeriod couplings ghost)

variable (interactionScale : Real) (coefficients : PotentialCoefficients)
variable (hWeights : candidateAPlusEinsteinKineticWeight couplings +
  candidateAMinusEinsteinKineticWeight couplings = 0)
local notation "H" => intrinsicBulkHessian period hPeriod couplings interactionScale coefficients

include hWeights in
theorem intrinsicBulkSmoothGhostRadical_le_ker : R ≤ (H).ker := by
  apply (LinearMap.range (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings)).topologicalClosure_minimal
    ?_ (H).isClosed_ker
  rintro _ ⟨ghost, rfl⟩
  exact intrinsicBulkHessian_smoothDiagonalGhost_zero period hPeriod couplings
    interactionScale coefficients hWeights ghost

include hWeights in
theorem intrinsicBulkHessian_radical_left_zero (radical test : Core) (hRadical : radical ∈ R) :
    H radical test = 0 :=
  congrArg (fun functional : Core →L[Real] Real => functional test)
    (intrinsicBulkSmoothGhostRadical_le_ker period hPeriod couplings
      interactionScale coefficients hWeights hRadical)

include hWeights in
theorem intrinsicBulkHessian_radical_right_zero (test radical : Core) (hRadical : radical ∈ R) :
    H test radical = 0 :=
  (intrinsicBulkHessian_symmetric period hPeriod couplings interactionScale coefficients test radical).trans
    (intrinsicBulkHessian_radical_left_zero period hPeriod couplings
      interactionScale coefficients hWeights radical test hRadical)

private def intrinsicBulkGhostLeftQuotientHessian : Reduced →L[Real] Core →L[Real] Real :=
  (R).liftQL H (intrinsicBulkSmoothGhostRadical_le_ker period hPeriod couplings
    interactionScale coefficients hWeights)

private theorem intrinsicBulkGhostLeftQuotientHessian_flip_ker :
    R ≤ (intrinsicBulkGhostLeftQuotientHessian period hPeriod couplings
      interactionScale coefficients hWeights).flip.ker := by
  intro radical hRadical
  apply ContinuousLinearMap.ext
  intro reduced
  obtain ⟨test, rfl⟩ := (R).mkQ_surjective reduced
  exact intrinsicBulkHessian_radical_right_zero period hPeriod couplings
    interactionScale coefficients hWeights test radical hRadical

/-- The actual continuous bilinear Hessian induced on the closed ghost quotient. -/
def intrinsicBulkSmoothGhostQuotientHessian : Reduced →L[Real] Reduced →L[Real] Real :=
  ((R).liftQL (intrinsicBulkGhostLeftQuotientHessian period hPeriod couplings
      interactionScale coefficients hWeights).flip
    (intrinsicBulkGhostLeftQuotientHessian_flip_ker period hPeriod couplings
      interactionScale coefficients hWeights)).flip

@[simp] theorem intrinsicBulkSmoothGhostQuotientHessian_mk (first second : Core) :
    intrinsicBulkSmoothGhostQuotientHessian period hPeriod couplings interactionScale coefficients hWeights
      (intrinsicBulkSmoothGhostQuotientMap period hPeriod couplings first)
      (intrinsicBulkSmoothGhostQuotientMap period hPeriod couplings second) = H first second := rfl

theorem intrinsicBulkSmoothGhostQuotientHessian_symmetric (first second : Reduced) :
    intrinsicBulkSmoothGhostQuotientHessian period hPeriod couplings interactionScale coefficients hWeights first second =
      intrinsicBulkSmoothGhostQuotientHessian period hPeriod couplings interactionScale coefficients hWeights second first := by
  apply symmetry_of_surjective
    (intrinsicBulkSmoothGhostQuotientMap period hPeriod couplings) (R).mkQ_surjective
    (fun left right => intrinsicBulkSmoothGhostQuotientHessian period hPeriod couplings
      interactionScale coefficients hWeights left right) ?_ first second
  intro left right
  exact (intrinsicBulkSmoothGhostQuotientHessian_mk period hPeriod couplings
    interactionScale coefficients hWeights left right).trans
    ((intrinsicBulkHessian_symmetric period hPeriod couplings interactionScale coefficients left right).trans
      (intrinsicBulkSmoothGhostQuotientHessian_mk period hPeriod couplings
        interactionScale coefficients hWeights right left).symm)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkSmoothGhostQuotient4D
