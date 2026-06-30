import JanusFormal.P0EFTBoundaryCartanGHYConversion

namespace JanusFormal
namespace P0EFTBoundaryIdentityObstruction

set_option autoImplicit false

structure IdentityChannelObstruction where
  qTNonzero : Prop
  radionJumpNonzero : Prop
  standardSurfaceSourcesOnly : Prop
  identityResidueNonzero : Prop
  pureGeometricClosureAvailable : Prop

structure EFTIdentityCounterterm where
  scalarBoundaryCountertermAdded : Prop
  exactCountertermCancelsIdentityResidue : Prop
  countertermDerivedFromJanusInvariant : Prop
  algebraicClosureRestored : Prop

def standardSourcesNoGo (o : IdentityChannelObstruction) : Prop :=
  o.qTNonzero /\
  o.radionJumpNonzero /\
  o.standardSurfaceSourcesOnly /\
  o.identityResidueNonzero /\
  Not o.pureGeometricClosureAvailable

def eftBranchClosesOnlyIfAccepted (e : EFTIdentityCounterterm) : Prop :=
  e.scalarBoundaryCountertermAdded /\
  e.exactCountertermCancelsIdentityResidue /\
  e.algebraicClosureRestored

theorem identity_channel_obstruction_for_standard_sources
    (o : IdentityChannelObstruction)
    (hQT : o.qTNonzero)
    (hJump : o.radionJumpNonzero)
    (hStd : o.standardSurfaceSourcesOnly)
    (hResidue : o.identityResidueNonzero)
    (hNoPure : Not o.pureGeometricClosureAvailable) :
    standardSourcesNoGo o := by
  exact And.intro hQT
    (And.intro hJump
      (And.intro hStd
        (And.intro hResidue hNoPure)))

theorem eft_counterterm_restores_only_algebraic_closure
    (e : EFTIdentityCounterterm)
    (hAdded : e.scalarBoundaryCountertermAdded)
    (hExact : e.exactCountertermCancelsIdentityResidue)
    (hClosure : e.algebraicClosureRestored) :
    eftBranchClosesOnlyIfAccepted e := by
  exact And.intro hAdded (And.intro hExact hClosure)

theorem underived_eft_counterterm_is_not_pure_geometric_closure
    (e : EFTIdentityCounterterm)
    (hUnderived : Not e.countertermDerivedFromJanusInvariant) :
    Not (e.countertermDerivedFromJanusInvariant /\ eftBranchClosesOnlyIfAccepted e) := by
  intro h
  exact hUnderived h.left

end P0EFTBoundaryIdentityObstruction
end JanusFormal
