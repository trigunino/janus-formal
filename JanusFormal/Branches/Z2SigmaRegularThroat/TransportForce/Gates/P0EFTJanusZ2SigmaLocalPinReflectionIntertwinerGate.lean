namespace JanusFormal
namespace P0EFTJanusZ2SigmaLocalPinReflectionIntertwinerGate

set_option autoImplicit false

structure LocalPinReflectionIntertwinerGate where
  pinReflectionFromUnitNormalDeclared : Prop
  z2NormalReversalImported : Prop
  cliffordIntertwiningLocalDeclared : Prop
  diracAdjointLocalCompatibilityDeclared : Prop
  globalSpinorLiftNotClaimed : Prop
  observationalFitForbidden : Prop
  sigmaUnitFrameReady : Prop
  localPinReflectionUZ2Declared : Prop
  normalGammaIntertwiningReady : Prop
  tangentGammaIntertwiningReady : Prop
  diracAdjointLocalCompatibilityReady : Prop
  localCliffordIntertwinerReady : Prop
  globalResolvedTunnelSpinorLiftReady : Prop
  physicalSpinorEquivarianceDerived : Prop

def localPinReflectionIntertwinerReady
    (g : LocalPinReflectionIntertwinerGate) : Prop :=
  g.pinReflectionFromUnitNormalDeclared /\
  g.z2NormalReversalImported /\
  g.cliffordIntertwiningLocalDeclared /\
  g.diracAdjointLocalCompatibilityDeclared /\
  g.globalSpinorLiftNotClaimed /\
  g.observationalFitForbidden /\
  g.sigmaUnitFrameReady /\
  g.localPinReflectionUZ2Declared /\
  g.normalGammaIntertwiningReady /\
  g.tangentGammaIntertwiningReady /\
  g.diracAdjointLocalCompatibilityReady /\
  g.localCliffordIntertwinerReady

theorem local_intertwiner_does_not_claim_global_lift
    (g : LocalPinReflectionIntertwinerGate)
    (_h : localPinReflectionIntertwinerReady g) :
    g.globalSpinorLiftNotClaimed := by
  exact _h.2.2.2.2.1

theorem local_intertwiner_still_needs_physical_equivariance
    (g : LocalPinReflectionIntertwinerGate)
    (_h : localPinReflectionIntertwinerReady g)
    (hMissing : Not g.physicalSpinorEquivarianceDerived) :
    Not g.physicalSpinorEquivarianceDerived := by
  exact hMissing

end P0EFTJanusZ2SigmaLocalPinReflectionIntertwinerGate
end JanusFormal
