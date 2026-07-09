namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOComponentToScaleFreePrimitiveChi2Gate

set_option autoImplicit false

structure BAOComponentToScaleFreePrimitiveChi2Gate where
  activeCoreZ2TunnelSigma : Prop
  componentManifestAvailable : Prop
  splitPrimitivesWritten : Prop
  canonicalPrimitiveManifestWritten : Prop
  scaleFreeBAOInputsWritten : Prop
  desiDR2Chi2Evaluated : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def primitiveChainReady
    (g : BAOComponentToScaleFreePrimitiveChi2Gate) : Prop :=
  g.splitPrimitivesWritten /\
  g.canonicalPrimitiveManifestWritten /\
  g.scaleFreeBAOInputsWritten

def activeObservationPolicyClosed
    (g : BAOComponentToScaleFreePrimitiveChi2Gate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed

theorem gate_requires_component_manifest
    (g : BAOComponentToScaleFreePrimitiveChi2Gate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.componentManifestAvailable) :
    g.componentManifestAvailable := by
  exact hImplies _hGate

theorem chi2_requires_primitive_chain
    (g : BAOComponentToScaleFreePrimitiveChi2Gate)
    (_hChi2 : g.desiDR2Chi2Evaluated)
    (hImplies : g.desiDR2Chi2Evaluated -> primitiveChainReady g) :
    primitiveChainReady g := by
  exact hImplies _hChi2

theorem policy_forbids_legacy_inputs
    (g : BAOComponentToScaleFreePrimitiveChi2Gate)
    (hClosed : activeObservationPolicyClosed g) :
    Not g.compressedPlanckLCDMUsed /\
    Not g.archivedZ4Used /\
    Not g.observationalH0FitUsed := by
  rcases hClosed with ⟨_, hNoPlanck, hNoZ4, hNoH0⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaBAOComponentToScaleFreePrimitiveChi2Gate
end JanusFormal
