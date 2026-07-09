namespace JanusFormal
namespace P0EFTJanusZ2SigmaScaleFreePlasmaPrimitiveInputWriterGate

set_option autoImplicit false

structure ScaleFreePlasmaPrimitiveInputWriterGate where
  activeCoreZ2TunnelSigma : Prop
  inputManifestAvailable : Prop
  plasmaPrimitiveWritten : Prop
  plasmaPrimitiveValid : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def scaleFreePlasmaPrimitiveWriterClosed
    (g : ScaleFreePlasmaPrimitiveInputWriterGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.inputManifestAvailable /\
  g.plasmaPrimitiveWritten /\
  g.plasmaPrimitiveValid /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.gatePassed

theorem scale_free_plasma_writer_forbids_planck_z4_and_h0_fit
    (g : ScaleFreePlasmaPrimitiveInputWriterGate)
    (hClosed : scaleFreePlasmaPrimitiveWriterClosed g) :
    Not g.compressedPlanckLCDMRdUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, hNoPlanck, hNoZ4, hNoH0, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaScaleFreePlasmaPrimitiveInputWriterGate
end JanusFormal
