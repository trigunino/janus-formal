namespace JanusFormal
namespace P0EFTJanusZ2AlphaSolutionSearchGate

set_option autoImplicit false

structure AlphaSolutionSearchGate where
  pureTopologyRouteTested : Prop
  boundaryChargeRouteTested : Prop
  souriauRouteTested : Prop
  fluxQuantizationRouteTested : Prop
  casimirRouteTested : Prop
  stateSectorRouteAvailable : Prop
  pureTopologyFixesDimensionfulAlpha : Prop
  claimsFullNoFit : Prop

def honestAlphaResolution (g : AlphaSolutionSearchGate) : Prop :=
  g.pureTopologyRouteTested /\
  g.boundaryChargeRouteTested /\
  g.souriauRouteTested /\
  g.fluxQuantizationRouteTested /\
  g.casimirRouteTested /\
  g.stateSectorRouteAvailable /\
  Not g.pureTopologyFixesDimensionfulAlpha /\
  Not g.claimsFullNoFit

theorem topology_fix_claim_blocks_resolution
    (g : AlphaSolutionSearchGate)
    (hBad : g.pureTopologyFixesDimensionfulAlpha) :
    Not (honestAlphaResolution g) := by
  intro h
  exact h.right.right.right.right.right.right.left hBad

theorem full_no_fit_claim_blocks_state_resolution
    (g : AlphaSolutionSearchGate)
    (hBad : g.claimsFullNoFit) :
    Not (honestAlphaResolution g) := by
  intro h
  exact h.right.right.right.right.right.right.right hBad

end P0EFTJanusZ2AlphaSolutionSearchGate
end JanusFormal
