namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOSplitPrimitivesToScaleFreeChi2Gate

set_option autoImplicit false

structure BAOSplitPrimitivesToScaleFreeChi2Gate where
  activeCoreZ2TunnelSigma : Prop
  primitiveInputsAssemblerPassed : Prop
  primitiveChi2Passed : Prop
  baoChi2Evaluated : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def splitPrimitivesChi2Closed
    (g : BAOSplitPrimitivesToScaleFreeChi2Gate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.primitiveInputsAssemblerPassed /\
  g.primitiveChi2Passed /\
  g.baoChi2Evaluated /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.gatePassed

theorem split_primitives_chi2_forbids_compressed_inputs
    (g : BAOSplitPrimitivesToScaleFreeChi2Gate)
    (hClosed : splitPrimitivesChi2Closed g) :
    Not g.compressedPlanckLCDMUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, hNoPlanck, hNoZ4, hNoH0, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaBAOSplitPrimitivesToScaleFreeChi2Gate
end JanusFormal
