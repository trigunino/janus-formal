import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusMicrocanonicalBoundaryStateLawAttemptGate

namespace JanusFormal
namespace P0EFTJanusEntropyToRulerResolutionMapGate

set_option autoImplicit false

structure EntropyToRulerResolutionMapGate where
  BoundaryEntropyEqualsLog1001 : Prop
  AminEqualsExpMinusEntropy : Prop
  ZmaxEquals1000 : Prop
  PhotonBaryonDragUsesBoundaryResolution : Prop
  NativeSoundHorizonExecutable : Prop

def EntropyRulerMapClosed
    (g : EntropyToRulerResolutionMapGate) : Prop :=
  g.BoundaryEntropyEqualsLog1001 /\
  g.AminEqualsExpMinusEntropy /\
  g.ZmaxEquals1000 /\
  g.PhotonBaryonDragUsesBoundaryResolution /\
  g.NativeSoundHorizonExecutable

def EntropyRulerMapFrontier
    (g : EntropyToRulerResolutionMapGate) : Prop :=
  g.BoundaryEntropyEqualsLog1001 /\
  g.AminEqualsExpMinusEntropy /\
  g.ZmaxEquals1000 /\
  Not g.PhotonBaryonDragUsesBoundaryResolution /\
  Not g.NativeSoundHorizonExecutable

theorem entropy_resolution_still_needs_drag_coupling
    (g : EntropyToRulerResolutionMapGate)
    (hFrontier : EntropyRulerMapFrontier g) :
    Not (EntropyRulerMapClosed g) := by
  intro h
  exact hFrontier.2.2.2.1 h.2.2.2.1

end P0EFTJanusEntropyToRulerResolutionMapGate
end JanusFormal
