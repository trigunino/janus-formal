import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4WeylLensingDeltaGate

namespace JanusFormal
namespace P0EFTJanusZ4LensedRemappingResponseGate

set_option autoImplicit false

structure LensedRemappingResponseGate where
  cambGRUnlensedInputUsed : Prop
  weylLensingPhiPhiDeltaUsed : Prop
  rawNativeLOSUsedForPlanck : Prop
  unlensedPrimaryUnchanged : Prop
  lambdaZeroIdentityPassed : Prop
  lensedTTResponseContinuous : Prop
  lensedTEResponseContinuous : Prop
  lensedEEResponseContinuous : Prop
  remappingResponseGatePassed : Prop
  nonzeroZ4PlanckAllowed : Prop
  officialPlanckAllowed : Prop

def stablePureLensingRemapping (g : LensedRemappingResponseGate) : Prop :=
  g.cambGRUnlensedInputUsed /\
  g.weylLensingPhiPhiDeltaUsed /\
  Not g.rawNativeLOSUsedForPlanck /\
  g.unlensedPrimaryUnchanged /\
  g.lambdaZeroIdentityPassed /\
  g.lensedTTResponseContinuous /\
  g.lensedTEResponseContinuous /\
  g.lensedEEResponseContinuous

theorem stable_remapping_implies_internal_gate
    (g : LensedRemappingResponseGate)
    (hPolicy : stablePureLensingRemapping g -> g.remappingResponseGatePassed)
    (h : stablePureLensingRemapping g) :
    g.remappingResponseGatePassed := by
  exact hPolicy h

theorem remapping_gate_alone_does_not_enable_planck
    (g : LensedRemappingResponseGate)
    (hPolicy : g.officialPlanckAllowed -> g.nonzeroZ4PlanckAllowed)
    (hNoEligibility : Not g.nonzeroZ4PlanckAllowed) :
    Not g.officialPlanckAllowed := by
  intro h
  exact hNoEligibility (hPolicy h)

end P0EFTJanusZ4LensedRemappingResponseGate
end JanusFormal
