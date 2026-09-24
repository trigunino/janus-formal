import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianBARestriction4D

/-! The actual mixed B--potential Hessian column, obtained by differentiating the action restriction. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianBAHessian4D
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianLorenz4D P0EFTJanusProgramPT12IntrinsicBulkAbelianBARestriction4D
open P0EFTJanusReciprocalBimetricPotential
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

private theorem affine_comp_hasFDerivAt_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (f : E → Real) (j : F →L[Real] E) (point : E)
    (hf : DifferentiableAt Real f point) :
    HasFDerivAt (fun current : F => f (point + j current))
      ((fderiv Real f point).comp j) 0 := by
  have hInput : HasFDerivAt (fun current : F => point + j current) j 0 := by
    simpa only [Pi.add_def, zero_add] using
      (hasFDerivAt_const point (0 : F)).add j.hasFDerivAt
  have hOuter : HasFDerivAt f (fderiv Real f point) (point + j 0) := by
    simpa only [j.map_zero, add_zero] using hf.hasFDerivAt
  exact hOuter.comp (f := fun current : F => point + j current) (0 : F) hInput

private theorem clm_pullback_eval_hasFDerivAt_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (g : E → E →L[Real] Real) (g' : E →L[Real] E →L[Real] Real)
    (j : F →L[Real] E) (value : E) (hg : HasFDerivAt g g' 0) :
    HasFDerivAt (fun current : F => g (j current) value)
      ((g'.flip value).comp j) 0 := by
  have hOuter : HasFDerivAt g g' (j 0) := by
    simpa only [j.map_zero] using hg
  have hApply := (hOuter.comp (f := j) (0 : F) j.hasFDerivAt).clm_apply
    (hasFDerivAt_const value (0 : F))
  apply hApply.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  change g (j 0) 0 + g' (j direction) value = g' (j direction) value
  rw [(g (j 0)).map_zero, zero_add]

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
variable (couplings : GlobalCandidateAActionCouplings)
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local notation "ACore" => IntrinsicBulkAbelianACore period hPeriod
local notation "BCore" => IntrinsicBulkAbelianBCore period hPeriod
local instance coreNormedAddCommGroup : NormedAddCommGroup Core := inferInstance
local instance aCoreNormedAddCommGroup : NormedAddCommGroup ACore := inferInstance
local instance bCoreNormedAddCommGroup : NormedAddCommGroup BCore := inferInstance
local instance : AddZeroClass Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : AddZeroClass ACore :=
  (aCoreNormedAddCommGroup period hPeriod).toAddCommGroup.toAddZeroClass
local instance : AddZeroClass BCore :=
  (bCoreNormedAddCommGroup period hPeriod).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local instance : NormedSpace Real ACore := inferInstance
local instance : NormedSpace Real BCore := inferInstance
local instance aToCoreNormedAddCommGroup : NormedAddCommGroup (ACore →L[Real] Core) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance bToCoreNormedAddCommGroup : NormedAddCommGroup (BCore →L[Real] Core) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : AddZeroClass (ACore →L[Real] Core) :=
  (aToCoreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : AddZeroClass (BCore →L[Real] Core) :=
  (bToCoreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local notation "jA" => intrinsicBulkAbelianAInsertion period hPeriod couplings
local notation "jB" => intrinsicBulkAbelianBInsertion period hPeriod couplings
variable (interactionScale : Real) (coefficients : PotentialCoefficients)
local notation "action" => intrinsicBulkAction period hPeriod couplings interactionScale coefficients
local notation "euler" => intrinsicBulkEuler period hPeriod couplings interactionScale coefficients
local notation "hessian" => intrinsicBulkHessian period hPeriod couplings interactionScale coefficients

private theorem abelianQuadratic_hasFDerivAt_zero (constant : Real)
    (linear : BCore →L[Real] Real) :
    HasFDerivAt (fun field : BCore => constant + linear field -
      (1 / 2 : Real) * intrinsicBulkAbelianBPairing period hPeriod field field) linear 0 := by
  have hDiagonal := ((intrinsicBulkAbelianBPairing period hPeriod).hasFDerivAt (x := (0 : BCore))).clm_apply
    (hasFDerivAt_id (𝕜 := Real) (0 : BCore))
  have hDerivative := ((hasFDerivAt_const constant (0 : BCore)).add linear.hasFDerivAt).sub
      (hDiagonal.const_mul (1 / 2 : Real))
  apply hDerivative.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  change 0 + linear direction -
      (1 / 2 : Real) * (intrinsicBulkAbelianBPairing period hPeriod 0 direction +
        intrinsicBulkAbelianBPairing period hPeriod direction 0) = linear direction
  simp only [(intrinsicBulkAbelianBPairing period hPeriod).map_zero,
    (intrinsicBulkAbelianBPairing period hPeriod direction).map_zero,
    zero_apply, zero_add, mul_zero, sub_zero]

theorem intrinsicBulkAction_abelianBA_hasFDerivAt_B_zero (potential : ACore) :
    HasFDerivAt (fun field : BCore => action (jA potential + jB field))
      ((intrinsicBulkAbelianBAPairing period hPeriod).flip potential) 0 := by
  have hRestriction : (fun field : BCore => action (jA potential + jB field)) =
      (fun field => action (jA potential) + intrinsicBulkAbelianBAPairing period hPeriod field potential -
        (1 / 2 : Real) * intrinsicBulkAbelianBPairing period hPeriod field field) :=
    funext (intrinsicBulkAction_abelianBA_restriction period hPeriod couplings interactionScale coefficients potential)
  rw [hRestriction]
  exact abelianQuadratic_hasFDerivAt_zero period hPeriod (action (jA potential))
    ((intrinsicBulkAbelianBAPairing period hPeriod).flip potential)

private theorem action_along_B_hasFDerivAt (potential : ACore)
    (hDifferentiable : DifferentiableAt Real action (jA potential)) :
    HasFDerivAt (fun current : BCore => action (jA potential + jB current))
      ((euler (jA potential)).comp jB) 0 := by
  exact affine_comp_hasFDerivAt_zero action jB (jA potential) hDifferentiable

private theorem euler_B_at_A (potential : ACore) (field : BCore)
    (hDifferentiable : DifferentiableAt Real action (jA potential)) :
    euler (jA potential) (jB field) = intrinsicBulkAbelianBAPairing period hPeriod field potential := by
  have hEqual := (action_along_B_hasFDerivAt period hPeriod couplings
    interactionScale coefficients potential hDifferentiable).unique
    (intrinsicBulkAction_abelianBA_hasFDerivAt_B_zero period hPeriod couplings interactionScale coefficients potential)
  exact congrArg (fun derivative : BCore →L[Real] Real => derivative field) hEqual

private theorem action_differentiable_near_A_zero :
    ∀ᶠ current in 𝓝 (0 : ACore), DifferentiableAt Real action (jA current) := by
  have h := ((intrinsicBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients).eventually
    (by norm_num)).mono (fun point hPoint => hPoint.differentiableAt (by norm_num))
  have hTend : Tendsto jA (𝓝 (0 : ACore)) (𝓝 (0 : Core)) :=
    by simpa only [(jA).map_zero] using (jA).continuous.tendsto (0 : ACore)
  exact hTend.eventually h

private theorem euler_B_along_A_hasFDerivAt (field : BCore) :
    HasFDerivAt (fun current : ACore => euler (jA current) (jB field))
      (((hessian).flip (jB field)).comp jA) 0 := by
  exact clm_pullback_eval_hasFDerivAt_zero euler hessian jA (jB field)
    (intrinsicBulkEuler_hasFDerivAt_zero period hPeriod couplings interactionScale coefficients)

theorem intrinsicBulkHessian_abelianB_abelianA (field : BCore) (potential : ACore) :
    hessian (jB field) (jA potential) = intrinsicBulkAbelianBAPairing period hPeriod field potential := by
  have hAgreement : (fun current : ACore => euler (jA current) (jB field)) =ᶠ[𝓝 (0 : ACore)]
      (fun current => intrinsicBulkAbelianBAPairing period hPeriod field current) := by
    filter_upwards [action_differentiable_near_A_zero period hPeriod couplings
      interactionScale coefficients] with current hCurrent
    exact euler_B_at_A period hPeriod couplings interactionScale coefficients current field hCurrent
  have hApply := euler_B_along_A_hasFDerivAt period hPeriod couplings
    interactionScale coefficients field
  have hEqual := (hApply.congr_of_eventuallyEq hAgreement.symm).unique
    (intrinsicBulkAbelianBAPairing period hPeriod field).hasFDerivAt
  have hValue : hessian (jA potential) (jB field) =
      intrinsicBulkAbelianBAPairing period hPeriod field potential :=
    congrArg (fun derivative : ACore →L[Real] Real => derivative potential) hEqual
  calc
    hessian (jB field) (jA potential) = hessian (jA potential) (jB field) :=
      intrinsicBulkHessian_symmetric period hPeriod couplings interactionScale coefficients _ _
    _ = intrinsicBulkAbelianBAPairing period hPeriod field potential := hValue

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianBAHessian4D
