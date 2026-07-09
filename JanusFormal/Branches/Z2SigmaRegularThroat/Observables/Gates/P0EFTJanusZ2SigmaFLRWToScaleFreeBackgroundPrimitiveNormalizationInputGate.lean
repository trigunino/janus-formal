namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWToScaleFreeBackgroundPrimitiveNormalizationInputGate

set_option autoImplicit false

structure FLRWToScaleFreeBackgroundPrimitiveNormalizationInputGate where
  activeCoreZ2TunnelSigma : Prop
  flrwComponentsAvailable : Prop
  scaleFreeOmegaKAvailable : Prop
  normalizationInputWritten : Prop
  downstreamBackgroundWriterPassed : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def normalizationInputClosed
    (g : FLRWToScaleFreeBackgroundPrimitiveNormalizationInputGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.flrwComponentsAvailable /\
  g.scaleFreeOmegaKAvailable /\
  g.normalizationInputWritten /\
  g.downstreamBackgroundWriterPassed /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.gatePassed

theorem closed_forbids_planck_z4_and_h0_fit
    (g : FLRWToScaleFreeBackgroundPrimitiveNormalizationInputGate)
    (hClosed : normalizationInputClosed g) :
    Not g.compressedPlanckLCDMUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, _, hNoPlanck, hNoZ4, hNoH0, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaFLRWToScaleFreeBackgroundPrimitiveNormalizationInputGate
end JanusFormal
