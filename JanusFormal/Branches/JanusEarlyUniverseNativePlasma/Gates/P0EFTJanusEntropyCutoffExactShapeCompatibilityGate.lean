import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusEntropyCutoffDragReadinessAuditGate

namespace JanusFormal
namespace P0EFTJanusEntropyCutoffExactShapeCompatibilityGate

set_option autoImplicit false

structure EntropyCutoffExactShapeCompatibilityGate where
  EntropyCutoffRequiresQ0NearMinusOneOver2000 : Prop
  PublishedLateSNQ0NearMinus0087 : Prop
  SameExactCoshBranchCompatible : Prop
  EarlyLateMatchingSurfaceDerived : Prop

def EntropyCutoffSameShapeClosed
    (g : EntropyCutoffExactShapeCompatibilityGate) : Prop :=
  g.EntropyCutoffRequiresQ0NearMinusOneOver2000 /\
  g.PublishedLateSNQ0NearMinus0087 /\
  g.SameExactCoshBranchCompatible

def EntropyCutoffEarlyBranchFrontier
    (g : EntropyCutoffExactShapeCompatibilityGate) : Prop :=
  g.EntropyCutoffRequiresQ0NearMinusOneOver2000 /\
  g.PublishedLateSNQ0NearMinus0087 /\
  Not g.SameExactCoshBranchCompatible /\
  Not g.EarlyLateMatchingSurfaceDerived

theorem entropy_cutoff_needs_separate_early_branch
    (g : EntropyCutoffExactShapeCompatibilityGate)
    (hFrontier : EntropyCutoffEarlyBranchFrontier g) :
    Not (EntropyCutoffSameShapeClosed g) := by
  intro h
  exact hFrontier.2.2.1 h.2.2

end P0EFTJanusEntropyCutoffExactShapeCompatibilityGate
end JanusFormal
