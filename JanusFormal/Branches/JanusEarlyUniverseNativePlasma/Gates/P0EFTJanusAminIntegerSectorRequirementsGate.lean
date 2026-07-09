namespace JanusFormal
namespace P0EFTJanusAminIntegerSectorRequirementsGate

set_option autoImplicit false

structure AminIntegerSectorRequirementsGate where
  aminEqualsOneOverNAnsatzDeclared : Prop
  requiredNComputed : Prop
  projectiveCoverTwoFailsLargeN : Prop
  targetIntegerCircularIfChosenFromBAO : Prop
  boundaryHilbertDimensionNeedsStateLaw : Prop
  fluxAreaQuantizationNeedsUnit : Prop
  largeNMustEnterPhotonRulerDynamics : Prop
  compatibleWithTwoFoldCoverRequired : Prop

def aminIntegerSectorReady
    (g : AminIntegerSectorRequirementsGate) : Prop :=
  g.aminEqualsOneOverNAnsatzDeclared /\
  g.requiredNComputed /\
  g.projectiveCoverTwoFailsLargeN /\
  g.targetIntegerCircularIfChosenFromBAO /\
  g.boundaryHilbertDimensionNeedsStateLaw /\
  g.fluxAreaQuantizationNeedsUnit /\
  g.largeNMustEnterPhotonRulerDynamics /\
  g.compatibleWithTwoFoldCoverRequired

theorem large_N_requires_new_boundary_state_or_flux_law
    (g : AminIntegerSectorRequirementsGate)
    (hReady : aminIntegerSectorReady g) :
    g.boundaryHilbertDimensionNeedsStateLaw /\ g.fluxAreaQuantizationNeedsUnit := by
  exact And.intro hReady.2.2.2.2.1 hReady.2.2.2.2.2.1

end P0EFTJanusAminIntegerSectorRequirementsGate
end JanusFormal
