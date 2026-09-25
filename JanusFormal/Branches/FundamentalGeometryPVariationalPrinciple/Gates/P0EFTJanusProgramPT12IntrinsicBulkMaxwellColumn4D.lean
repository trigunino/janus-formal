import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkMaxwellRestriction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BilinearSecondJetFreeze4D

/-! The actual physical bulk Maxwell column against every C² bulk test.
The pairing retains the native curvature, density and two Maxwell couplings. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkMaxwellColumn4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusProgramPT12AffineHessianPullback4D
open P0EFTJanusProgramPT12BilinearSecondJetFreeze4D

section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
local instance : NormedAddCommGroup (E →L[Real] Real) := inferInstance
local instance : NormedSpace Real (E →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (E →L[Real] E →L[Real] Real) := inferInstance
local instance : NormedSpace Real (E →L[Real] E →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] F →L[Real] Real) := inferInstance

private theorem quadratic_restriction_hessian
    (f : E → Real) (j : F →L[Real] E) (B : F →L[Real] F →L[Real] Real) (c : Real)
    (hf : ContDiffAt Real 2 f 0) (hRestriction : ∀ x, f (j x) = c + B x x) (first second : F) :
    fderiv Real (fderiv Real f) 0 (j first) (j second) = B first second + B second first := by
  have hPull : fderiv Real (fderiv Real (fun x : F => f (j x))) 0 first second =
      fderiv Real (fderiv Real f) 0 (j first) (j second) := by
    simpa only [one_mul, zero_add] using scaledAffineHessian f 0 j 1 hf first second
  have hAction : (fun x : F => f (j x)) = (fun x : F => c + B x x) := funext hRestriction
  have hGradient : fderiv Real (fun x : F => c + B x x) = fderiv Real (fun x : F => B x x) :=
    funext fun x => fderiv_const_add (𝕜 := Real) (f := fun y : F => B y y) (x := x) c
  rw [hAction, hGradient] at hPull
  exact hPull.symm.trans (bilinearCoefficient_second_fderiv_zero
    (fun _ : F => B) (ContinuousLinearMap.id Real F) (ContinuousLinearMap.id Real F)
    (show ContDiffAt Real 2 (fun _ : F => B) 0 from contDiffAt_const) first second)

private theorem reflection_hessian_column
    (f : E → Real) (R : E →L[Real] E) (j : F →L[Real] E) (p : E →L[Real] F)
    (hf : ContDiffAt Real 2 f 0) (hEven : ∀ x, f (R x) = f x)
    (hReflection : ∀ x, R x = x - (2 : Real) • j (p x))
    (hInsertion : ∀ a, R (j a) = -j a) (a : F) (test : E) :
    fderiv Real (fderiv Real f) 0 (j a) test =
      fderiv Real (fderiv Real f) 0 (j a) (j (p test)) := by
  have hPull : fderiv Real (fderiv Real (fun x : E => f (R x))) 0 (j a) test =
      fderiv Real (fderiv Real f) 0 (R (j a)) (R test) := by
    simpa only [one_mul, zero_add] using scaledAffineHessian f 0 R 1 hf (j a) test
  have hAction : (fun x : E => f (R x)) = f := funext hEven
  rw [hAction, hInsertion, hReflection] at hPull
  simp only [map_neg, neg_apply, map_sub, map_smul, smul_eq_mul] at hPull
  linarith
end Calculus

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalProjection4D P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianLorenz4D P0EFTJanusProgramPT12IntrinsicBulkAbelianBARestriction4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12IntrinsicBulkMaxwellRestriction4D
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
variable (couplings : GlobalCandidateAActionCouplings)
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local notation "ACore" => IntrinsicBulkAbelianACore period hPeriod
local instance coreNormedAddCommGroup : NormedAddCommGroup Core := inferInstance
local instance : AddZeroClass Core := (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real Core :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local instance : NormedAddCommGroup ACore := inferInstance
local instance : NormedSpace Real ACore := inferInstance
local instance : NormedAddCommGroup (Core →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Core →L[Real] Real) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Core →L[Real] Core →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Core →L[Real] Core →L[Real] Real) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (ACore →L[Real] Real) := inferInstance
local instance : NormedSpace Real (ACore →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (ACore →L[Real] ACore →L[Real] Real) := inferInstance
local instance : NormedSpace Real (ACore →L[Real] ACore →L[Real] Real) := inferInstance
variable (interactionScale : Real) (coefficients : PotentialCoefficients)

theorem intrinsicBulkPhysicalHessian_potential_potential
    (first second : IntrinsicBulkAbelianACore period hPeriod) :
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings first)
      (intrinsicBulkAbelianAInsertion period hPeriod couplings second) =
        intrinsicBulkMaxwellPairing period hPeriod couplings first second +
          intrinsicBulkMaxwellPairing period hPeriod couplings second first :=
  quadratic_restriction_hessian
    (intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkAbelianAInsertion period hPeriod couplings)
    (intrinsicBulkMaxwellPairing period hPeriod couplings)
    (intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients 0)
    (intrinsicBulkPhysicalAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPhysicalAction_potential_restriction period hPeriod couplings interactionScale coefficients)
    first second

theorem intrinsicBulkPhysicalHessian_potential_column
    (potential : IntrinsicBulkAbelianACore period hPeriod) (test : IntrinsicBulkCore period hPeriod couplings) :
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings potential) test =
        intrinsicBulkMaxwellPairing period hPeriod couplings potential
          (intrinsicBulkAbelianPotentialReadout period hPeriod couplings test) +
        intrinsicBulkMaxwellPairing period hPeriod couplings
          (intrinsicBulkAbelianPotentialReadout period hPeriod couplings test) potential :=
  (reflection_hessian_column
    (intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPotentialReflection period hPeriod couplings)
    (intrinsicBulkAbelianAInsertion period hPeriod couplings)
    (intrinsicBulkAbelianPotentialReadout period hPeriod couplings)
    (intrinsicBulkPhysicalAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPhysicalAction_potential_reflection period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPotentialReflection_sub period hPeriod couplings)
    (intrinsicBulkPotentialReflection_insert period hPeriod couplings) potential test).trans
      (intrinsicBulkPhysicalHessian_potential_potential period hPeriod couplings interactionScale coefficients
        potential (intrinsicBulkAbelianPotentialReadout period hPeriod couplings test))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkMaxwellColumn4D
