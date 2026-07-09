import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4ControlledDeviationGate

namespace JanusFormal
namespace P0EFTJanusZ4WeylLensingDeltaGate

set_option autoImplicit false

structure WeylLensingDeltaGate where
  deltaChannelIsWeylLensingKernel : Prop
  rawNativeLOSUsedForPlanck : Prop
  lambdaZeroIdentityPassed : Prop
  unlensedPrimaryUnchanged : Prop
  phiphiConventionChecked : Prop
  smallLambdaContinuityPassed : Prop
  internalLensingResponseGatePassed : Prop
  nonzeroZ4PlanckAllowed : Prop
  officialPlanckAllowed : Prop

def pureWeylLensingDelta (g : WeylLensingDeltaGate) : Prop :=
  g.deltaChannelIsWeylLensingKernel /\
  Not g.rawNativeLOSUsedForPlanck /\
  g.lambdaZeroIdentityPassed /\
  g.unlensedPrimaryUnchanged /\
  g.phiphiConventionChecked /\
  g.smallLambdaContinuityPassed

theorem pure_lensing_delta_internal_gate
    (g : WeylLensingDeltaGate)
    (hPolicy : pureWeylLensingDelta g -> g.internalLensingResponseGatePassed)
    (h : pureWeylLensingDelta g) :
    g.internalLensingResponseGatePassed := by
  exact hPolicy h

theorem nonzero_lensing_delta_not_planck_allowed_without_eligibility_gate
    (g : WeylLensingDeltaGate)
    (hPolicy : g.officialPlanckAllowed -> g.nonzeroZ4PlanckAllowed)
    (hNoEligibility : Not g.nonzeroZ4PlanckAllowed) :
    Not g.officialPlanckAllowed := by
  intro h
  exact hNoEligibility (hPolicy h)

end P0EFTJanusZ4WeylLensingDeltaGate
end JanusFormal
