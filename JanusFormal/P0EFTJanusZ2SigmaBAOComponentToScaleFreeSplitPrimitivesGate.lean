namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOComponentToScaleFreeSplitPrimitivesGate

set_option autoImplicit false

structure BAOComponentToScaleFreeSplitPrimitivesGate where
  activeCoreZ2TunnelSigma : Prop
  componentManifestAvailable : Prop
  componentManifestActiveDerived : Prop
  backgroundPrimitiveWritten : Prop
  plasmaPrimitiveWritten : Prop
  backgroundPrimitiveValid : Prop
  plasmaPrimitiveValid : Prop
  splitPrimitiveGridsAligned : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  gatePassed : Prop

def splitPrimitivesReady
    (g : BAOComponentToScaleFreeSplitPrimitivesGate) : Prop :=
  g.backgroundPrimitiveWritten /\
  g.plasmaPrimitiveWritten /\
  g.backgroundPrimitiveValid /\
  g.plasmaPrimitiveValid /\
  g.splitPrimitiveGridsAligned

def activePolicyClosed
    (g : BAOComponentToScaleFreeSplitPrimitivesGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.componentManifestActiveDerived /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed

theorem gate_requires_component_manifest
    (g : BAOComponentToScaleFreeSplitPrimitivesGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.componentManifestAvailable) :
    g.componentManifestAvailable := by
  exact hImplies _hGate

theorem component_manifest_transports_split_primitives
    (g : BAOComponentToScaleFreeSplitPrimitivesGate)
    (_hComponent : g.componentManifestAvailable)
    (hImplies : g.componentManifestAvailable -> splitPrimitivesReady g) :
    splitPrimitivesReady g := by
  exact hImplies _hComponent

theorem active_policy_forbids_legacy_inputs
    (g : BAOComponentToScaleFreeSplitPrimitivesGate)
    (hClosed : activePolicyClosed g) :
    Not g.compressedPlanckLCDMUsed /\
    Not g.archivedZ4Used /\
    Not g.observationalH0FitUsed := by
  rcases hClosed with ⟨_, _, hNoPlanck, hNoZ4, hNoH0⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0⟩

end P0EFTJanusZ2SigmaBAOComponentToScaleFreeSplitPrimitivesGate
end JanusFormal
