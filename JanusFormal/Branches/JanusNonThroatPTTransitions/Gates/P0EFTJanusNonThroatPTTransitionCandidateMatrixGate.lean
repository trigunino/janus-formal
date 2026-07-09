namespace JanusFormal
namespace P0EFTJanusNonThroatPTTransitionCandidateMatrixGate

set_option autoImplicit false

structure NonThroatPTTransitionCandidateMatrixGate where
  ConformalPTBoundaryCandidateDeclared : Prop
  CrosscapPTTransitionCandidateDeclared : Prop
  NullPTBoundaryCandidateDeclared : Prop
  AllAvoidSigmaRadius : Prop
  ConformalPTBoundaryRecommendedFirst : Prop
  ConformalMatchingLawDerived : Prop

def NonThroatPTTransitionClosed
    (g : NonThroatPTTransitionCandidateMatrixGate) : Prop :=
  g.ConformalPTBoundaryCandidateDeclared /\
  g.AllAvoidSigmaRadius /\
  g.ConformalPTBoundaryRecommendedFirst /\
  g.ConformalMatchingLawDerived

def NonThroatPTTransitionFrontier
    (g : NonThroatPTTransitionCandidateMatrixGate) : Prop :=
  g.ConformalPTBoundaryCandidateDeclared /\
  g.CrosscapPTTransitionCandidateDeclared /\
  g.NullPTBoundaryCandidateDeclared /\
  g.AllAvoidSigmaRadius /\
  g.ConformalPTBoundaryRecommendedFirst /\
  Not g.ConformalMatchingLawDerived

theorem non_throat_matrix_selects_but_does_not_close_conformal
    (g : NonThroatPTTransitionCandidateMatrixGate)
    (hFrontier : NonThroatPTTransitionFrontier g) :
    Not (NonThroatPTTransitionClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.2 h.2.2.2

end P0EFTJanusNonThroatPTTransitionCandidateMatrixGate
end JanusFormal
