namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWToScaleFreeBackgroundPrimitiveGate

set_option autoImplicit false

structure FLRWToScaleFreeBackgroundPrimitiveGate where
  activeCoreZ2TunnelSigma : Prop
  flrwComponentManifestAvailable : Prop
  scaleFreeOmegaKManifestAvailable : Prop
  backgroundPrimitiveWritten : Prop
  backgroundPrimitiveValid : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def backgroundPrimitiveClosed
    (g : FLRWToScaleFreeBackgroundPrimitiveGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.flrwComponentManifestAvailable /\
  g.scaleFreeOmegaKManifestAvailable /\
  g.backgroundPrimitiveWritten /\
  g.backgroundPrimitiveValid /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.gatePassed

theorem closed_background_primitive_forbids_compressed_inputs
    (g : FLRWToScaleFreeBackgroundPrimitiveGate)
    (hClosed : backgroundPrimitiveClosed g) :
    Not g.compressedPlanckLCDMUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, _, hNoPlanck, hNoZ4, hNoH0, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaFLRWToScaleFreeBackgroundPrimitiveGate
end JanusFormal
