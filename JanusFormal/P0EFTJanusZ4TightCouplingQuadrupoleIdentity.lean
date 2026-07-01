import JanusFormal.P0EFTJanusZ4AcousticPolarizationPhaseKernel
import JanusFormal.P0EFTJanusZ4PhotonBaryonHierarchyTarget

namespace JanusFormal
namespace P0EFTJanusZ4TightCouplingQuadrupoleIdentity

set_option autoImplicit false

structure TightCouplingQuadrupoleIdentity where
  quadrupoleEquationDeclared : Prop
  tightCouplingLimitDeclared : Prop
  monopoleLeakageRemoved : Prop
  potentialLeakageRemoved : Prop
  z4FreeLeakageRemoved : Prop
  eModeFeedbackRemoved : Prop
  theta2EqualsKVbOverTauDotDerived : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def quadrupoleIdentityReady (q : TightCouplingQuadrupoleIdentity) : Prop :=
  q.quadrupoleEquationDeclared /\
  q.tightCouplingLimitDeclared /\
  q.monopoleLeakageRemoved /\
  q.potentialLeakageRemoved /\
  q.z4FreeLeakageRemoved /\
  q.eModeFeedbackRemoved /\
  q.theta2EqualsKVbOverTauDotDerived

theorem quadrupole_identity_feeds_phase_kernel
    (q : TightCouplingQuadrupoleIdentity)
    (k : P0EFTJanusZ4AcousticPolarizationPhaseKernel.AcousticPolarizationPhaseKernel)
    (hq : quadrupoleIdentityReady q)
    (hk : P0EFTJanusZ4AcousticPolarizationPhaseKernel.phaseKernelScaffoldReady k)
    (hTransport : q.theta2EqualsKVbOverTauDotDerived -> k.tightCouplingQuadrupoleIdentityDerived) :
    P0EFTJanusZ4AcousticPolarizationPhaseKernel.phaseKernelPhysicalReady k := by
  exact And.intro hk (hTransport hq.right.right.right.right.right.right)

theorem quadrupole_identity_keeps_solver_frozen
    (q : TightCouplingQuadrupoleIdentity)
    (_h : quadrupoleIdentityReady q)
    (hFrozen : Not q.solverNumericsModified) :
    Not q.solverNumericsModified := by
  exact hFrozen

theorem quadrupole_identity_does_not_claim_planck
    (q : TightCouplingQuadrupoleIdentity)
    (_h : quadrupoleIdentityReady q)
    (hNoClaim : Not q.planckValidationClaimed) :
    Not q.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4TightCouplingQuadrupoleIdentity
end JanusFormal
