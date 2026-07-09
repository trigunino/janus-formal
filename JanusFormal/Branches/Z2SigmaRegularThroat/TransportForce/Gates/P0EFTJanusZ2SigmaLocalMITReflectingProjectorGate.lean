namespace JanusFormal
namespace P0EFTJanusZ2SigmaLocalMITReflectingProjectorGate

set_option autoImplicit false

structure LocalMITReflectingProjectorGate where
  localUnitNormalFrameImported : Prop
  normalCliffordActionDeclared : Prop
  mitReflectingProjectorDeclared : Prop
  projectorPhaseFixed : Prop
  observationalFitForbidden : Prop
  sigmaUnitNormalFrameReady : Prop
  z2NormalReversalReady : Prop
  unitNormalCliffordActionReady : Prop
  projectionIdempotentReady : Prop
  projectionSelfAdjointReady : Prop
  normalCurrentZeroAlgebraIdentityReady : Prop
  boundarySpinorSatisfiesProjectorDerived : Prop

def localMITReflectingProjectorReady
    (g : LocalMITReflectingProjectorGate) : Prop :=
  g.localUnitNormalFrameImported /\
  g.normalCliffordActionDeclared /\
  g.mitReflectingProjectorDeclared /\
  g.projectorPhaseFixed /\
  g.observationalFitForbidden /\
  g.sigmaUnitNormalFrameReady /\
  g.z2NormalReversalReady /\
  g.unitNormalCliffordActionReady /\
  g.projectionIdempotentReady /\
  g.projectionSelfAdjointReady /\
  g.normalCurrentZeroAlgebraIdentityReady

theorem local_projector_does_not_supply_physical_boundary_condition
    (g : LocalMITReflectingProjectorGate)
    (_h : localMITReflectingProjectorReady g)
    (hMissing : Not g.boundarySpinorSatisfiesProjectorDerived) :
    Not g.boundarySpinorSatisfiesProjectorDerived := by
  exact hMissing

theorem local_projector_supplies_clifford_and_algebra
    (g : LocalMITReflectingProjectorGate)
    (h : localMITReflectingProjectorReady g) :
    g.unitNormalCliffordActionReady /\
      g.projectionIdempotentReady /\
      g.projectionSelfAdjointReady /\
      g.normalCurrentZeroAlgebraIdentityReady := by
  exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

end P0EFTJanusZ2SigmaLocalMITReflectingProjectorGate
end JanusFormal
