namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOScaleFreeMinimalContractGate

set_option autoImplicit false

structure BAOScaleFreeMinimalContractGate where
  activeCoreZ2TunnelSigma : Prop
  bibliographyChecked : Prop
  standardDistanceDefinitionsAvailable : Prop
  standardSoundHorizonContextAvailable : Prop
  localZ2SigmaDerivationRequired : Prop
  componentManifestValid : Prop
  eZ2SigmaPrimitiveDerived : Prop
  csOverCPrimitiveDerived : Prop
  gammaDragOverH0PrimitiveDerived : Prop
  omegaKPrimitiveDerived : Prop
  observationalH0FitUsed : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4ReuseUsed : Prop
  phenomenologicalHolstBAOScanUsed : Prop
  gatePassed : Prop

def primitiveContractReady
    (g : BAOScaleFreeMinimalContractGate) : Prop :=
  g.eZ2SigmaPrimitiveDerived /\
  g.csOverCPrimitiveDerived /\
  g.gammaDragOverH0PrimitiveDerived /\
  g.omegaKPrimitiveDerived

def contractPolicyClosed
    (g : BAOScaleFreeMinimalContractGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.bibliographyChecked /\
  g.standardDistanceDefinitionsAvailable /\
  g.standardSoundHorizonContextAvailable /\
  g.localZ2SigmaDerivationRequired /\
  Not g.observationalH0FitUsed /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4ReuseUsed /\
  Not g.phenomenologicalHolstBAOScanUsed

theorem valid_component_manifest_supplies_primitive_contract
    (g : BAOScaleFreeMinimalContractGate)
    (_hValid : g.componentManifestValid)
    (hImplies : g.componentManifestValid -> primitiveContractReady g) :
    primitiveContractReady g := by
  exact hImplies _hValid

theorem primitive_contract_required_for_gate
    (g : BAOScaleFreeMinimalContractGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> primitiveContractReady g) :
    primitiveContractReady g := by
  exact hImplies _hGate

theorem contract_policy_forbids_compressed_inputs
    (g : BAOScaleFreeMinimalContractGate)
    (hClosed : contractPolicyClosed g) :
    Not g.observationalH0FitUsed /\
    Not g.compressedPlanckLCDMRdUsed /\
    Not g.archivedZ4ReuseUsed /\
    Not g.phenomenologicalHolstBAOScanUsed := by
  rcases hClosed with ⟨_, _, _, _, _, hNoH0, hNoPlanck, hNoZ4, hNoScan⟩
  exact ⟨hNoH0, hNoPlanck, hNoZ4, hNoScan⟩

end P0EFTJanusZ2SigmaBAOScaleFreeMinimalContractGate
end JanusFormal
