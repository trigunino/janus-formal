namespace JanusFormal
namespace P0EFTJanusExoticPTTransitionConfigurationMatrixGate

set_option autoImplicit false

structure ExoticPTTransitionConfigurationMatrixGate where
  WeylCuspPTBoundaryCandidateDeclared : Prop
  MobiusNormalBandCandidateDeclared : Prop
  CrosscapPTTransitionCandidateDeclared : Prop
  LensSpacePTQuotientCandidateDeclared : Prop
  BranchedCoverPTTransitionCandidateDeclared : Prop
  WeylCuspRecommendedFirst : Prop
  WeylClockFlowDerived : Prop

def ExoticPTTransitionMatrixClosed
    (g : ExoticPTTransitionConfigurationMatrixGate) : Prop :=
  g.WeylCuspPTBoundaryCandidateDeclared /\
  g.WeylCuspRecommendedFirst /\
  g.WeylClockFlowDerived

def ExoticPTTransitionMatrixFrontier
    (g : ExoticPTTransitionConfigurationMatrixGate) : Prop :=
  g.WeylCuspPTBoundaryCandidateDeclared /\
  g.MobiusNormalBandCandidateDeclared /\
  g.CrosscapPTTransitionCandidateDeclared /\
  g.LensSpacePTQuotientCandidateDeclared /\
  g.BranchedCoverPTTransitionCandidateDeclared /\
  g.WeylCuspRecommendedFirst /\
  Not g.WeylClockFlowDerived

theorem exotic_matrix_selects_weyl_cusp_but_needs_clock
    (g : ExoticPTTransitionConfigurationMatrixGate)
    (hFrontier : ExoticPTTransitionMatrixFrontier g) :
    Not (ExoticPTTransitionMatrixClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.2.2 h.2.2

end P0EFTJanusExoticPTTransitionConfigurationMatrixGate
end JanusFormal
