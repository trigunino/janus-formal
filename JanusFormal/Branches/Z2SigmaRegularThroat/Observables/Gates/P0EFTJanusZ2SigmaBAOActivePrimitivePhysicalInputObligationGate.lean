namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOActivePrimitivePhysicalInputObligationGate

set_option autoImplicit false

structure BAOActivePrimitivePhysicalInputObligationGate where
  activeCoreZ2TunnelSigma : Prop
  scaleFreeOmegaKInputsValid : Prop
  flrwComponentInputsValid : Prop
  earlyPlasmaInputsValid : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4Forbidden : Prop
  observationalH0FitForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  mockActiveInputsForbidden : Prop
  eZ2SigmaObligationTracked : Prop
  omegaKZ2SigmaObligationTracked : Prop
  csOverCZ2SigmaObligationTracked : Prop
  gammaDragOverH0Z2SigmaObligationTracked : Prop
  scaleFreePrimitivePhysicsReady : Prop
  desiDR2BAOChi2Allowed : Prop
  gatePassed : Prop

def activePhysicalInputsReady
    (g : BAOActivePrimitivePhysicalInputObligationGate) : Prop :=
  g.scaleFreeOmegaKInputsValid /\
  g.flrwComponentInputsValid /\
  g.earlyPlasmaInputsValid

def primitiveObligationsTracked
    (g : BAOActivePrimitivePhysicalInputObligationGate) : Prop :=
  g.eZ2SigmaObligationTracked /\
  g.omegaKZ2SigmaObligationTracked /\
  g.csOverCZ2SigmaObligationTracked /\
  g.gammaDragOverH0Z2SigmaObligationTracked

def noLegacyInputs
    (g : BAOActivePrimitivePhysicalInputObligationGate) : Prop :=
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4Forbidden /\
  g.observationalH0FitForbidden /\
  g.phenomenologicalHolstBAOScanForbidden /\
  g.mockActiveInputsForbidden

theorem chi2_allowed_requires_active_physical_inputs
    (g : BAOActivePrimitivePhysicalInputObligationGate)
    (hAllowed : g.desiDR2BAOChi2Allowed)
    (hImplies : g.desiDR2BAOChi2Allowed -> activePhysicalInputsReady g) :
    activePhysicalInputsReady g := by
  exact hImplies hAllowed

theorem primitive_physics_ready_requires_tracked_obligations
    (g : BAOActivePrimitivePhysicalInputObligationGate)
    (hReady : g.scaleFreePrimitivePhysicsReady)
    (hImplies : g.scaleFreePrimitivePhysicsReady -> primitiveObligationsTracked g) :
    primitiveObligationsTracked g := by
  exact hImplies hReady

theorem policy_keeps_legacy_inputs_forbidden
    (g : BAOActivePrimitivePhysicalInputObligationGate)
    (hPolicy : noLegacyInputs g) :
    g.compressedPlanckLCDMForbidden /\
    g.archivedZ4Forbidden /\
    g.observationalH0FitForbidden /\
    g.phenomenologicalHolstBAOScanForbidden /\
    g.mockActiveInputsForbidden := by
  exact hPolicy

end P0EFTJanusZ2SigmaBAOActivePrimitivePhysicalInputObligationGate
end JanusFormal
