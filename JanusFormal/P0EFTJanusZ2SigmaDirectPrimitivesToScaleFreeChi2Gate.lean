namespace JanusFormal
namespace P0EFTJanusZ2SigmaDirectPrimitivesToScaleFreeChi2Gate

set_option autoImplicit false

structure DirectPrimitivesToScaleFreeChi2Gate where
  activeCoreZ2TunnelSigma : Prop
  backgroundPrimitiveWriterPassed : Prop
  plasmaPrimitiveWriterPassed : Prop
  primitiveInputsAssemblerPassed : Prop
  baoChi2Evaluated : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def directPrimitiveChi2Closed
    (g : DirectPrimitivesToScaleFreeChi2Gate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.backgroundPrimitiveWriterPassed /\
  g.plasmaPrimitiveWriterPassed /\
  g.primitiveInputsAssemblerPassed /\
  g.baoChi2Evaluated /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.gatePassed

theorem direct_primitive_chi2_forbids_planck_z4_and_h0_fit
    (g : DirectPrimitivesToScaleFreeChi2Gate)
    (hClosed : directPrimitiveChi2Closed g) :
    Not g.compressedPlanckLCDMUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, _, hNoPlanck, hNoZ4, hNoH0, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaDirectPrimitivesToScaleFreeChi2Gate
end JanusFormal
