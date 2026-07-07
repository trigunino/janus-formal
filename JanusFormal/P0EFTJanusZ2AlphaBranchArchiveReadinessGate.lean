namespace JanusFormal
namespace P0EFTJanusZ2AlphaBranchArchiveReadinessGate

set_option autoImplicit false

structure AlphaBranchArchiveReadinessGate where
  nonzeroKKSDensityDerived : Prop
  torsionfulOrNullThetaDerived : Prop
  matterGaugeBoundaryPhaseSpaceDerived : Prop
  minisuperspaceVAlphaDerived : Prop

def anyReopenRouteReady (g : AlphaBranchArchiveReadinessGate) : Prop :=
  g.nonzeroKKSDensityDerived \/
  g.torsionfulOrNullThetaDerived \/
  g.matterGaugeBoundaryPhaseSpaceDerived \/
  g.minisuperspaceVAlphaDerived

def archiveRecommended (g : AlphaBranchArchiveReadinessGate) : Prop :=
  Not (anyReopenRouteReady g)

theorem archive_when_all_reopen_routes_absent
    (g : AlphaBranchArchiveReadinessGate)
    (hKKS : Not g.nonzeroKKSDensityDerived)
    (hTheta : Not g.torsionfulOrNullThetaDerived)
    (hMatter : Not g.matterGaugeBoundaryPhaseSpaceDerived)
    (hV : Not g.minisuperspaceVAlphaDerived) :
    archiveRecommended g := by
  intro h
  rcases h with h | h | h | h
  · exact hKKS h
  · exact hTheta h
  · exact hMatter h
  · exact hV h

theorem any_reopen_route_blocks_archive
    (g : AlphaBranchArchiveReadinessGate)
    (h : anyReopenRouteReady g) :
    Not (archiveRecommended g) := by
  intro hArchive
  exact hArchive h

end P0EFTJanusZ2AlphaBranchArchiveReadinessGate
end JanusFormal
