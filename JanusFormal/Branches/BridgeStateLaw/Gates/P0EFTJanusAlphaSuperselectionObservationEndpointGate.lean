namespace JanusFormal
namespace P0EFTJanusAlphaSuperselectionObservationEndpointGate

set_option autoImplicit false

structure AlphaObservationEndpointGate where
  alphaSectorProgramDeclared : Prop
  supernovaDataAvailable : Prop
  baoDataAvailable : Prop
  snOnlyShapeAllowed : Prop
  absoluteScaleSelectionReady : Prop
  noFitClaimForbidden : Prop

def endpointReadyForFullSectorSelection (g : AlphaObservationEndpointGate) : Prop :=
  g.alphaSectorProgramDeclared /\
  g.supernovaDataAvailable /\
  g.baoDataAvailable /\
  g.absoluteScaleSelectionReady /\
  g.noFitClaimForbidden

theorem sn_without_bao_is_not_full_sector_selection
    (g : AlphaObservationEndpointGate)
    (_hSN : g.supernovaDataAvailable)
    (hNoBAO : Not g.baoDataAvailable) :
    Not (endpointReadyForFullSectorSelection g) := by
  intro h
  exact hNoBAO h.right.right.left

end P0EFTJanusAlphaSuperselectionObservationEndpointGate
end JanusFormal
