namespace JanusFormal
namespace P0EFTJanusZ2SigmaScaleFreeBackgroundPrimitiveInputWriterGate

set_option autoImplicit false

structure ScaleFreeBackgroundPrimitiveInputWriterGate where
  activeCoreZ2TunnelSigma : Prop
  inputManifestAvailable : Prop
  backgroundPrimitiveWritten : Prop
  backgroundPrimitiveValid : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def scaleFreeBackgroundPrimitiveWriterClosed
    (g : ScaleFreeBackgroundPrimitiveInputWriterGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.inputManifestAvailable /\
  g.backgroundPrimitiveWritten /\
  g.backgroundPrimitiveValid /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.gatePassed

theorem scale_free_background_writer_forbids_planck_z4_and_h0_fit
    (g : ScaleFreeBackgroundPrimitiveInputWriterGate)
    (hClosed : scaleFreeBackgroundPrimitiveWriterClosed g) :
    Not g.compressedPlanckLCDMRdUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, hNoPlanck, hNoZ4, hNoH0, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaScaleFreeBackgroundPrimitiveInputWriterGate
end JanusFormal
