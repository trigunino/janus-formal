namespace JanusFormal
namespace P0EFTJanusZ2SigmaEarlyPlasmaToScaleFreePlasmaPrimitiveNormalizationInputGate

set_option autoImplicit false

structure EarlyPlasmaToScaleFreePlasmaPrimitiveNormalizationInputGate where
  activeCoreZ2TunnelSigma : Prop
  earlyPlasmaAvailable : Prop
  activeH0Available : Prop
  normalizationInputWritten : Prop
  downstreamPlasmaWriterPassed : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def normalizationInputClosed
    (g : EarlyPlasmaToScaleFreePlasmaPrimitiveNormalizationInputGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.earlyPlasmaAvailable /\
  g.activeH0Available /\
  g.normalizationInputWritten /\
  g.downstreamPlasmaWriterPassed /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.gatePassed

theorem closed_forbids_planck_z4_and_h0_fit
    (g : EarlyPlasmaToScaleFreePlasmaPrimitiveNormalizationInputGate)
    (hClosed : normalizationInputClosed g) :
    Not g.compressedPlanckLCDMUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, _, hNoPlanck, hNoZ4, hNoH0, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaEarlyPlasmaToScaleFreePlasmaPrimitiveNormalizationInputGate
end JanusFormal
