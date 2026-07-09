namespace JanusFormal
namespace P0EFTJanusZ2AlphaStateSectorClosureReadinessGate

set_option autoImplicit false

structure AlphaStateSectorClosureReadinessGate where
  nonzeroKKSDensityDerived : Prop
  torsionfulOrNullThetaDerived : Prop
  matterGaugeBoundaryPhaseSpaceDerived : Prop
  minisuperspaceVAlphaDerived : Prop

def anyClosureRouteReady (g : AlphaStateSectorClosureReadinessGate) : Prop :=
  g.nonzeroKKSDensityDerived \/
  g.torsionfulOrNullThetaDerived \/
  g.matterGaugeBoundaryPhaseSpaceDerived \/
  g.minisuperspaceVAlphaDerived

def closureBlocked (g : AlphaStateSectorClosureReadinessGate) : Prop :=
  Not (anyClosureRouteReady g)

theorem closure_blocked_when_all_routes_absent
    (g : AlphaStateSectorClosureReadinessGate)
    (hKKS : Not g.nonzeroKKSDensityDerived)
    (hTheta : Not g.torsionfulOrNullThetaDerived)
    (hMatter : Not g.matterGaugeBoundaryPhaseSpaceDerived)
    (hV : Not g.minisuperspaceVAlphaDerived) :
    closureBlocked g := by
  intro h
  exact h.elim hKKS (fun h => h.elim hTheta (fun h => h.elim hMatter hV))

theorem any_closure_route_blocks_closure_blocked
    (g : AlphaStateSectorClosureReadinessGate)
    (h : anyClosureRouteReady g) :
    Not (closureBlocked g) := by
  intro hBlocked
  exact hBlocked h

end P0EFTJanusZ2AlphaStateSectorClosureReadinessGate
end JanusFormal
