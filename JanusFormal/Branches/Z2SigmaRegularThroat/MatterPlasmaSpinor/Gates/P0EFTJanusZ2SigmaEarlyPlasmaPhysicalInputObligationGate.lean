namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaPhysicalInputObligationGate

set_option autoImplicit false

structure EarlyPlasmaPhysicalInputObligationGate where
  activeCoreZ2TunnelSigma : Prop
  codataConstantsValid : Prop
  modelNormalizationValid : Prop
  baryonPhotonNormalizationValid : Prop
  ionizationThomsonNormalizationValid : Prop
  rhoBaryonBuilderReady : Prop
  rhoPhotonBuilderReady : Prop
  csOverCBuilderReady : Prop
  gammaDragBuilderReady : Prop
  requiresBackgroundH0ForGammaOverH0 : Prop
  requiresActiveEForZdSolver : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4Used : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  mockInputsUsed : Prop
  gatePassed : Prop

def activeEarlyPlasmaInputsReady
    (g : EarlyPlasmaPhysicalInputObligationGate) : Prop :=
  g.baryonPhotonNormalizationValid /\
  g.ionizationThomsonNormalizationValid

def earlyPlasmaUpstreamInputsAvailable
    (g : EarlyPlasmaPhysicalInputObligationGate) : Prop :=
  g.codataConstantsValid /\ g.modelNormalizationValid

def earlyPlasmaBuildersReady
    (g : EarlyPlasmaPhysicalInputObligationGate) : Prop :=
  g.rhoBaryonBuilderReady /\
  g.rhoPhotonBuilderReady /\
  g.csOverCBuilderReady /\
  g.gammaDragBuilderReady

def noLegacyEarlyPlasmaInputs
    (g : EarlyPlasmaPhysicalInputObligationGate) : Prop :=
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4Used /\
  Not g.phenomenologicalHolstBAOScanUsed /\
  Not g.mockInputsUsed

theorem gate_requires_active_early_plasma_inputs
    (g : EarlyPlasmaPhysicalInputObligationGate)
    (hGate : g.gatePassed)
    (hImplies : g.gatePassed -> activeEarlyPlasmaInputsReady g) :
    activeEarlyPlasmaInputsReady g := by
  exact hImplies hGate

theorem active_inputs_transport_to_builders
    (g : EarlyPlasmaPhysicalInputObligationGate)
    (hInputs : activeEarlyPlasmaInputsReady g)
    (hImplies : activeEarlyPlasmaInputsReady g -> earlyPlasmaBuildersReady g) :
    earlyPlasmaBuildersReady g := by
  exact hImplies hInputs

theorem policy_forbids_legacy_early_plasma_inputs
    (g : EarlyPlasmaPhysicalInputObligationGate)
    (hPolicy : noLegacyEarlyPlasmaInputs g) :
    Not g.compressedPlanckLCDMRdUsed /\
    Not g.archivedZ4Used /\
    Not g.phenomenologicalHolstBAOScanUsed /\
    Not g.mockInputsUsed := by
  exact hPolicy

end P0EFTJanusZ2SigmaEarlyPlasmaPhysicalInputObligationGate
end JanusFormal
