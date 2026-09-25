import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAntighostHessian4D
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Group.Quotient

/-! The exact closed C² antighost subspace and the induced full bulk Hessian.
Closedness follows from its bounded coordinate retraction. Under opposite
Einstein weights this subspace lies in the Hessian radical; it is not claimed
to exhaust that radical. No action or BRST descent is asserted here. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAntighostQuotient4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkAntighostHessian4D
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
local notation "Ghost" => FiniteFrameDiffeomorphismC2Core period hPeriod (finiteSmoothTangentFrame period hPeriod)
local instance : NormedAddCommGroup Ghost := inferInstance
local instance : NormedSpace Real Ghost := inferInstance

variable (couplings : GlobalCandidateAActionCouplings)
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local instance coreNormedAddCommGroup : NormedAddCommGroup Core := inferInstance
local instance coreNormedSpace : NormedSpace Real Core :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local instance coreModule : Module Real Core := (coreNormedSpace period hPeriod couplings).toModule
local instance coreMulAction : MulAction Real Core :=
  (coreModule period hPeriod couplings).toDistribMulAction.toMulAction
local instance : SMul Real Core := (coreMulAction period hPeriod couplings).toSMul
local instance : AddZeroClass Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance coreTopologicalAddGroup : IsTopologicalAddGroup Core :=
  @SeminormedAddCommGroup.toIsTopologicalAddGroup Core
    (coreNormedAddCommGroup period hPeriod couplings).toSeminormedAddCommGroup
local instance : ContinuousAdd Core := (coreTopologicalAddGroup period hPeriod couplings).toContinuousAdd
local instance : IsBoundedSMul Real Core :=
  IsBoundedSMul.of_norm_smul_le (NormedSpace.norm_smul_le (𝕜 := Real) (E := Core))
local instance : ContinuousSMul Real Core := IsBoundedSMul.continuousSMul
local instance : ContinuousConstSMul Real Core := ContinuousSMul.continuousConstSMul

/-- The actual antighost coordinate of the full bulk core. -/
def intrinsicBulkAntighostReadout : Core →L[Real] Ghost where
  toFun input := input.1.1.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_fst.comp (continuous_snd.comp (continuous_snd.comp
    (continuous_snd.comp (continuous_fst.comp continuous_fst))))

@[simp] theorem intrinsicBulkAntighostReadout_apply (input : Core) :
    intrinsicBulkAntighostReadout period hPeriod couplings input = input.1.1.2.2.2.1 := rfl

@[simp] theorem intrinsicBulkAntighostReadout_insertion (antighost : Ghost) :
    intrinsicBulkAntighostReadout period hPeriod couplings
      (intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings antighost) = antighost := rfl

theorem intrinsicBulkAntighostReadout_comp_insertion :
    (intrinsicBulkAntighostReadout period hPeriod couplings).comp
      (intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings) =
        ContinuousLinearMap.id Real Ghost := by
  apply ContinuousLinearMap.ext
  intro antighost
  rfl

/-- The closed antighost coordinate subspace; no density completion is used. -/
def intrinsicBulkAntighostRadical : Submodule Real Core :=
  (ContinuousLinearMap.id Real Core -
    (intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings).comp
      (intrinsicBulkAntighostReadout period hPeriod couplings)).ker
local notation "R" => intrinsicBulkAntighostRadical period hPeriod couplings

instance intrinsicBulkAntighostRadical_isClosed : IsClosed (R : Set Core) :=
  (ContinuousLinearMap.id Real Core -
    (intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings).comp
      (intrinsicBulkAntighostReadout period hPeriod couplings)).isClosed_ker

theorem intrinsicBulkAntighostRadical_mem_iff (input : Core) :
    input ∈ R ↔ ∃ antighost : Ghost,
      input = intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings antighost := by
  change input - intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings
    (intrinsicBulkAntighostReadout period hPeriod couplings input) = 0 ↔ _
  constructor
  · intro hInput
    exact ⟨intrinsicBulkAntighostReadout period hPeriod couplings input, sub_eq_zero.mp hInput⟩
  · rintro ⟨antighost, rfl⟩
    exact sub_self _

theorem intrinsicBulkAntighostRadical_eq_range :
    R = LinearMap.range
      (intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings).toLinearMap := by
  apply Submodule.ext
  intro input
  exact (intrinsicBulkAntighostRadical_mem_iff period hPeriod couplings input).trans
    (exists_congr fun _ => eq_comm)

theorem intrinsicBulkAntighostRadical_insertion_mem (antighost : Ghost) :
    intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings antighost ∈ R :=
  (intrinsicBulkAntighostRadical_mem_iff period hPeriod couplings _).mpr ⟨antighost, rfl⟩

abbrev IntrinsicBulkAntighostQuotient := Core ⧸ R
local notation "Reduced" => IntrinsicBulkAntighostQuotient period hPeriod couplings
local instance : IsScalarTower Real Real Core := ⟨mul_smul⟩
local instance reducedNormedAddCommGroup : NormedAddCommGroup Reduced :=
  Submodule.Quotient.normedAddCommGroup (R)
local instance reducedNormedSpace : NormedSpace Real Reduced := Submodule.Quotient.normedSpace (R) Real
local instance reducedModule : Module Real Reduced := (reducedNormedSpace period hPeriod couplings).toModule
local instance reducedMulAction : MulAction Real Reduced :=
  (reducedModule period hPeriod couplings).toDistribMulAction.toMulAction
local instance : SMul Real Reduced := (reducedMulAction period hPeriod couplings).toSMul

def intrinsicBulkAntighostQuotientMap : Core →L[Real] Reduced := (R).mkQL

@[simp] theorem intrinsicBulkAntighostQuotientMap_insertion (antighost : Ghost) :
    intrinsicBulkAntighostQuotientMap period hPeriod couplings
      (intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings antighost) = 0 :=
  (Submodule.Quotient.mk_eq_zero (R)).mpr
    (intrinsicBulkAntighostRadical_insertion_mem period hPeriod couplings antighost)

variable (interactionScale : Real) (coefficients : PotentialCoefficients)
variable (hWeights : candidateAPlusEinsteinKineticWeight couplings +
  candidateAMinusEinsteinKineticWeight couplings = 0)
local notation "H" => intrinsicBulkHessian period hPeriod couplings interactionScale coefficients

include hWeights in
theorem intrinsicBulkAntighostRadical_le_ker : R ≤ (H).ker := by
  intro input hInput
  obtain ⟨antighost, rfl⟩ := (intrinsicBulkAntighostRadical_mem_iff period hPeriod couplings input).mp hInput
  apply ContinuousLinearMap.ext
  intro test
  exact intrinsicBulkHessian_antighost_column_zero period hPeriod couplings
    interactionScale coefficients hWeights antighost test

include hWeights in
theorem intrinsicBulkHessian_antighostRadical_left_zero (radical test : Core) (hRadical : radical ∈ R) :
    H radical test = 0 :=
  congrArg (fun functional : Core →L[Real] Real => functional test)
    (intrinsicBulkAntighostRadical_le_ker period hPeriod couplings
      interactionScale coefficients hWeights hRadical)

include hWeights in
theorem intrinsicBulkHessian_antighostRadical_right_zero (test radical : Core) (hRadical : radical ∈ R) :
    H test radical = 0 :=
  (intrinsicBulkHessian_symmetric period hPeriod couplings interactionScale coefficients test radical).trans
    (intrinsicBulkHessian_antighostRadical_left_zero period hPeriod couplings
      interactionScale coefficients hWeights radical test hRadical)

private def intrinsicBulkAntighostLeftQuotientHessian : Reduced →L[Real] Core →L[Real] Real :=
  (R).liftQL H (intrinsicBulkAntighostRadical_le_ker period hPeriod couplings
    interactionScale coefficients hWeights)

private theorem intrinsicBulkAntighostLeftQuotientHessian_flip_ker :
    R ≤ (intrinsicBulkAntighostLeftQuotientHessian period hPeriod couplings
      interactionScale coefficients hWeights).flip.ker := by
  intro radical hRadical
  apply ContinuousLinearMap.ext
  intro reduced
  obtain ⟨test, rfl⟩ := (R).mkQ_surjective reduced
  exact intrinsicBulkHessian_antighostRadical_right_zero period hPeriod couplings
    interactionScale coefficients hWeights test radical hRadical

/-- The full continuous bilinear bulk Hessian on the exact antighost quotient. -/
def intrinsicBulkAntighostQuotientHessian : Reduced →L[Real] Reduced →L[Real] Real :=
  ((R).liftQL (intrinsicBulkAntighostLeftQuotientHessian period hPeriod couplings
      interactionScale coefficients hWeights).flip
    (intrinsicBulkAntighostLeftQuotientHessian_flip_ker period hPeriod couplings
      interactionScale coefficients hWeights)).flip

@[simp] theorem intrinsicBulkAntighostQuotientHessian_mk (first second : Core) :
    intrinsicBulkAntighostQuotientHessian period hPeriod couplings interactionScale coefficients hWeights
      (intrinsicBulkAntighostQuotientMap period hPeriod couplings first)
      (intrinsicBulkAntighostQuotientMap period hPeriod couplings second) = H first second := rfl

theorem intrinsicBulkAntighostQuotientHessian_symmetric (first second : Reduced) :
    intrinsicBulkAntighostQuotientHessian period hPeriod couplings interactionScale coefficients hWeights first second =
      intrinsicBulkAntighostQuotientHessian period hPeriod couplings interactionScale coefficients hWeights second first := by
  apply symmetry_of_surjective
    (intrinsicBulkAntighostQuotientMap period hPeriod couplings) (R).mkQ_surjective
    (fun left right => intrinsicBulkAntighostQuotientHessian period hPeriod couplings
      interactionScale coefficients hWeights left right) ?_ first second
  intro left right
  exact (intrinsicBulkAntighostQuotientHessian_mk period hPeriod couplings
    interactionScale coefficients hWeights left right).trans
    ((intrinsicBulkHessian_symmetric period hPeriod couplings interactionScale coefficients left right).trans
      (intrinsicBulkAntighostQuotientHessian_mk period hPeriod couplings
        interactionScale coefficients hWeights right left).symm)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAntighostQuotient4D
