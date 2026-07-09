namespace JanusFormal
namespace P0EFTJanusAlphaBridgeStateLawCrediblePistesTerminalGate

set_option autoImplicit false

structure CrediblePistesTerminalGate where
  compositeRouteAudited : Prop
  superselectionRouteAudited : Prop
  paperReferenceRouteAudited : Prop
  noDirectAlphaFit : Prop
  noInventedBoundaryLaw : Prop
  explicitBoundaryStateLawDerived : Prop
  alphaAsSuperselectionAllowed : Prop
  paperGapReportAllowed : Prop

def terminalButNotNoFit (g : CrediblePistesTerminalGate) : Prop :=
  g.compositeRouteAudited /\
  g.superselectionRouteAudited /\
  g.paperReferenceRouteAudited /\
  g.noDirectAlphaFit /\
  g.noInventedBoundaryLaw /\
  Not g.explicitBoundaryStateLawDerived /\
  g.alphaAsSuperselectionAllowed /\
  g.paperGapReportAllowed

theorem no_fit_requires_explicit_boundary_state_law
    (g : CrediblePistesTerminalGate)
    (h : terminalButNotNoFit g) :
    Not g.explicitBoundaryStateLawDerived := by
  exact h.right.right.right.right.right.left

end P0EFTJanusAlphaBridgeStateLawCrediblePistesTerminalGate
end JanusFormal
