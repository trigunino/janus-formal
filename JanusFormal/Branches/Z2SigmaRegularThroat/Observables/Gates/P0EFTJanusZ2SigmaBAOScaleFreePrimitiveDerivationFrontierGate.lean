namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOScaleFreePrimitiveDerivationFrontierGate

set_option autoImplicit false

structure BAOScaleFreePrimitiveDerivationFrontierGate where
  activeCoreZ2TunnelSigma : Prop
  bibliographyChecked : Prop
  standardDistanceDefinitionsAvailable : Prop
  standardSoundHorizonContextAvailable : Prop
  localZ2SigmaDerivationRequired : Prop
  eZ2SigmaDerived : Prop
  omegaKZ2SigmaDerived : Prop
  csOverCZ2SigmaDerived : Prop
  gammaDragOverH0Z2SigmaDerived : Prop
  backgroundPrimitiveManifestValid : Prop
  plasmaPrimitiveManifestValid : Prop
  splitPrimitiveGridsAligned : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  gatePassed : Prop

def primitiveDerivationsClosed
    (g : BAOScaleFreePrimitiveDerivationFrontierGate) : Prop :=
  g.eZ2SigmaDerived /\
  g.omegaKZ2SigmaDerived /\
  g.csOverCZ2SigmaDerived /\
  g.gammaDragOverH0Z2SigmaDerived

def splitPrimitiveManifestsClosed
    (g : BAOScaleFreePrimitiveDerivationFrontierGate) : Prop :=
  g.backgroundPrimitiveManifestValid /\
  g.plasmaPrimitiveManifestValid /\
  g.splitPrimitiveGridsAligned

def frontierPolicyClosed
    (g : BAOScaleFreePrimitiveDerivationFrontierGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.bibliographyChecked /\
  g.standardDistanceDefinitionsAvailable /\
  g.standardSoundHorizonContextAvailable /\
  g.localZ2SigmaDerivationRequired /\
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  Not g.phenomenologicalHolstBAOScanUsed

theorem gate_requires_split_primitive_manifests
    (g : BAOScaleFreePrimitiveDerivationFrontierGate)
    (hGate : g.gatePassed)
    (hImplies : g.gatePassed -> splitPrimitiveManifestsClosed g) :
    splitPrimitiveManifestsClosed g := by
  exact hImplies hGate

theorem split_manifests_transport_primitive_derivations
    (g : BAOScaleFreePrimitiveDerivationFrontierGate)
    (hSplit : splitPrimitiveManifestsClosed g)
    (hImplies : splitPrimitiveManifestsClosed g -> primitiveDerivationsClosed g) :
    primitiveDerivationsClosed g := by
  exact hImplies hSplit

theorem frontier_policy_forbids_legacy_inputs
    (g : BAOScaleFreePrimitiveDerivationFrontierGate)
    (hClosed : frontierPolicyClosed g) :
    Not g.compressedPlanckLCDMUsed /\
    Not g.archivedZ4Used /\
    Not g.observationalH0FitUsed /\
    Not g.phenomenologicalHolstBAOScanUsed := by
  rcases hClosed with ⟨_, _, _, _, _, hNoPlanck, hNoZ4, hNoH0, hNoScan⟩
  exact ⟨hNoPlanck, hNoZ4, hNoH0, hNoScan⟩

end P0EFTJanusZ2SigmaBAOScaleFreePrimitiveDerivationFrontierGate
end JanusFormal
