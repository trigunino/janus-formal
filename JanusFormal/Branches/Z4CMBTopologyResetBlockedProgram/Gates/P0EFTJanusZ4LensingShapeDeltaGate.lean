import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4LensedRemappingResponseGate

namespace JanusFormal
namespace P0EFTJanusZ4LensingShapeDeltaGate

set_option autoImplicit false

structure LensingShapeDeltaGate where
  kernelSourceLevelDelta : Prop
  directClPatch : Prop
  rawNativeLOSUsedForPlanck : Prop
  lambdaZeroIdentityPassed : Prop
  unlensedPrimaryUnchanged : Prop
  phiphiConventionChecked : Prop
  phiphiContinuityPassed : Prop
  lensedRemappingContinuityPassed : Prop
  shapeComponentPresent : Prop
  observationallyUsefulShape : Prop
  gatePassed : Prop
  nonzeroZ4PlanckEligible : Prop

def stableShapeDelta (g : LensingShapeDeltaGate) : Prop :=
  g.kernelSourceLevelDelta /\
  Not g.directClPatch /\
  Not g.rawNativeLOSUsedForPlanck /\
  g.lambdaZeroIdentityPassed /\
  g.unlensedPrimaryUnchanged /\
  g.phiphiConventionChecked /\
  g.phiphiContinuityPassed /\
  g.lensedRemappingContinuityPassed /\
  g.shapeComponentPresent /\
  g.observationallyUsefulShape

theorem stable_shape_delta_implies_gate
    (g : LensingShapeDeltaGate)
    (hPolicy : stableShapeDelta g -> g.gatePassed)
    (h : stableShapeDelta g) :
    g.gatePassed := by
  exact hPolicy h

theorem shape_delta_not_planck_eligible_without_eligibility_gate
    (g : LensingShapeDeltaGate)
    (hNoEligibility : Not g.nonzeroZ4PlanckEligible) :
    Not g.nonzeroZ4PlanckEligible := by
  exact hNoEligibility

end P0EFTJanusZ4LensingShapeDeltaGate
end JanusFormal
