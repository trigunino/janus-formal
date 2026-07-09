namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOScaleFreePrimitiveChi2Gate

set_option autoImplicit false

structure BAOScaleFreePrimitiveChi2Gate where
  activeCoreZ2TunnelSigma : Prop
  primitiveInputManifestAvailable : Prop
  scaleFreeBAOInputManifestWritten : Prop
  activeScaleFreeBAOInputValid : Prop
  scaleFreeBAOEvaluation : Prop
  baoChi2Evaluated : Prop
  gammaDragOverH0Available : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def primitiveScaleFreeChi2Closed
    (g : BAOScaleFreePrimitiveChi2Gate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.primitiveInputManifestAvailable /\
  g.scaleFreeBAOInputManifestWritten /\
  g.activeScaleFreeBAOInputValid /\
  g.scaleFreeBAOEvaluation /\
  g.baoChi2Evaluated /\
  g.gammaDragOverH0Available /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  g.gatePassed

theorem primitive_scale_free_chi2_forbids_compressed_inputs
    (g : BAOScaleFreePrimitiveChi2Gate)
    (hClosed : primitiveScaleFreeChi2Closed g) :
    Not g.compressedPlanckLCDMUsed /\ Not g.archivedZ4Used /\ Not g.observationalH0FitUsed := by
  rcases hClosed with
    ⟨_, _, _, _, _, _, _, hNoPlanck, hNoZ4, hNoH0, _⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaBAOScaleFreePrimitiveChi2Gate
end JanusFormal
