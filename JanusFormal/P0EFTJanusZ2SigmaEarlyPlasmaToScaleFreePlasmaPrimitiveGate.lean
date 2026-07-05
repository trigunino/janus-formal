namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaToScaleFreePlasmaPrimitiveGate

set_option autoImplicit false

structure EarlyPlasmaToScaleFreePlasmaPrimitiveGate where
  activeCoreZ2TunnelSigma : Prop
  earlyPlasmaManifestAvailable : Prop
  activeH0ManifestAvailable : Prop
  plasmaPrimitiveWritten : Prop
  plasmaPrimitiveValid : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  earlyPlasmaManifestFrontierDeclared : Prop
  activeH0NormalizationFrontierDeclared : Prop
  activeH0ManifestFrontierDeclared : Prop
  activeH0WriterFrontierDeclared : Prop
  nearestPlasmaPrimitiveFrontierDeclared : Prop
  nearestPlasmaPrimitiveFrontierDiagnosticOnly : Prop
  gatePassed : Prop

def plasmaPrimitiveClosed
    (g : EarlyPlasmaToScaleFreePlasmaPrimitiveGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.earlyPlasmaManifestAvailable /\
  g.activeH0ManifestAvailable /\
  g.plasmaPrimitiveWritten /\
  g.plasmaPrimitiveValid /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.earlyPlasmaManifestFrontierDeclared /\
  g.activeH0NormalizationFrontierDeclared /\
  g.activeH0ManifestFrontierDeclared /\
  g.activeH0WriterFrontierDeclared /\
  g.nearestPlasmaPrimitiveFrontierDeclared /\
  g.nearestPlasmaPrimitiveFrontierDiagnosticOnly /\
  g.gatePassed

theorem closed_plasma_primitive_forbids_compressed_inputs
    (g : EarlyPlasmaToScaleFreePlasmaPrimitiveGate)
    (hClosed : plasmaPrimitiveClosed g) :
    Not g.compressedPlanckLCDMUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  exact ⟨hClosed.2.2.2.2.2.1, hClosed.2.2.2.2.2.2.1, hClosed.2.2.2.2.2.2.2.1⟩

theorem diagnostic_plasma_primitive_frontier_does_not_close_primitive
    (g : EarlyPlasmaToScaleFreePlasmaPrimitiveGate)
    (_hDiag : g.nearestPlasmaPrimitiveFrontierDiagnosticOnly)
    (hMissingEarly : Not g.earlyPlasmaManifestAvailable) :
    Not (g.nearestPlasmaPrimitiveFrontierDiagnosticOnly /\
      plasmaPrimitiveClosed g) := by
  intro h
  exact hMissingEarly h.2.2.1

end P0EFTJanusZ2SigmaEarlyPlasmaToScaleFreePlasmaPrimitiveGate
end JanusFormal
