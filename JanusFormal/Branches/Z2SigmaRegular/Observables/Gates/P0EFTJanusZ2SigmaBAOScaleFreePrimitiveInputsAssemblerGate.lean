namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOScaleFreePrimitiveInputsAssemblerGate

set_option autoImplicit false

structure BAOScaleFreePrimitiveInputsAssemblerGate where
  activeCoreZ2TunnelSigma : Prop
  backgroundPrimitiveManifestAvailable : Prop
  plasmaPrimitiveManifestAvailable : Prop
  primitiveManifestWritten : Prop
  primitiveManifestValid : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def primitiveInputsAssemblerClosed
    (g : BAOScaleFreePrimitiveInputsAssemblerGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.backgroundPrimitiveManifestAvailable /\
  g.plasmaPrimitiveManifestAvailable /\
  g.primitiveManifestWritten /\
  g.primitiveManifestValid /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.gatePassed

theorem primitive_inputs_assembler_forbids_compressed_inputs
    (g : BAOScaleFreePrimitiveInputsAssemblerGate)
    (hClosed : primitiveInputsAssemblerClosed g) :
    Not g.compressedPlanckLCDMUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, _, hNoPlanck, hNoZ4, hNoH0, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaBAOScaleFreePrimitiveInputsAssemblerGate
end JanusFormal
