import JanusFormal.P0EFTJanusZ4LensingShapeDeltaGate

namespace JanusFormal
namespace P0EFTJanusZ4NonzeroPlanckEligibilityGate

set_option autoImplicit false

structure NonzeroPlanckEligibilityGate where
  cambGRSafeBaselineRoundtripPassed : Prop
  nativeToyLOSUsed : Prop
  nativeToyLOSPlanckForbidden : Prop
  lambdaZeroIdentityPassed : Prop
  taggedWeylLensingShapeDeltaEnabled : Prop
  forbiddenNonLensingDeltasOff : Prop
  unlensedPrimaryUnchanged : Prop
  phiphiConventionChecked : Prop
  smallLambdaContinuityPassed : Prop
  shapeFractionHealthy : Prop
  shapeSmoothnessPassed : Prop
  z4PlanckPassed : Prop
  nonzeroZ4OfficialLikelihoodAllowed : Prop

def eligibleForLikelihoodTrial (g : NonzeroPlanckEligibilityGate) : Prop :=
  g.cambGRSafeBaselineRoundtripPassed /\
  Not g.nativeToyLOSUsed /\
  g.nativeToyLOSPlanckForbidden /\
  g.lambdaZeroIdentityPassed /\
  g.taggedWeylLensingShapeDeltaEnabled /\
  g.forbiddenNonLensingDeltasOff /\
  g.unlensedPrimaryUnchanged /\
  g.phiphiConventionChecked /\
  g.smallLambdaContinuityPassed /\
  g.shapeFractionHealthy /\
  g.shapeSmoothnessPassed

theorem eligibility_implies_likelihood_allowed
    (g : NonzeroPlanckEligibilityGate)
    (hPolicy : eligibleForLikelihoodTrial g -> g.nonzeroZ4OfficialLikelihoodAllowed)
    (h : eligibleForLikelihoodTrial g) :
    g.nonzeroZ4OfficialLikelihoodAllowed := by
  exact hPolicy h

theorem likelihood_allowed_does_not_imply_planck_passed
    (g : NonzeroPlanckEligibilityGate)
    (hNoVerdict : Not g.z4PlanckPassed) :
    Not g.z4PlanckPassed := by
  exact hNoVerdict

end P0EFTJanusZ4NonzeroPlanckEligibilityGate
end JanusFormal
