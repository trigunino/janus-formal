namespace JanusFormal
namespace P0EFTJanusZ2GlobalActionOnshellAlphaSelectorGate

set_option autoImplicit false

structure GlobalActionOnshellAlphaSelectorGate where
  publishedActionAnchorAvailable : Prop
  exactAlphaFamilyAvailable : Prop
  minisuperspaceLagrangianWritten : Prop
  onShellSOrVAlphaDerived : Prop
  finiteBoundaryPrescriptionForNoncompactOrbit : Prop
  stationarityOrMinimumSelectorDerived : Prop

def alphaSelectorReady (g : GlobalActionOnshellAlphaSelectorGate) : Prop :=
  g.publishedActionAnchorAvailable /\
  g.exactAlphaFamilyAvailable /\
  g.minisuperspaceLagrangianWritten /\
  g.onShellSOrVAlphaDerived /\
  g.finiteBoundaryPrescriptionForNoncompactOrbit /\
  g.stationarityOrMinimumSelectorDerived

theorem no_onshell_functional_blocks_global_action_selector
    (g : GlobalActionOnshellAlphaSelectorGate)
    (hMissing : Not g.onShellSOrVAlphaDerived) :
    Not (alphaSelectorReady g) := by
  intro h
  exact hMissing h.2.2.2.1

theorem no_finite_boundary_blocks_global_action_selector
    (g : GlobalActionOnshellAlphaSelectorGate)
    (hMissing : Not g.finiteBoundaryPrescriptionForNoncompactOrbit) :
    Not (alphaSelectorReady g) := by
  intro h
  exact hMissing h.2.2.2.2.1

end P0EFTJanusZ2GlobalActionOnshellAlphaSelectorGate
end JanusFormal
