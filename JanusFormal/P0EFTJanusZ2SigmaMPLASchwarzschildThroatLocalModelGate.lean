namespace JanusFormal
namespace P0EFTJanusZ2SigmaMPLASchwarzschildThroatLocalModelGate

set_option autoImplicit false

structure MPLASchwarzschildThroatLocalModelGate where
  activeCoreZ2Sigma : Prop
  arealRadiusFormulaDeclared : Prop
  rhoReflectionDeclared : Prop
  minimalThroatReady : Prop
  rSigmaOverRsEqualsOne : Prop
  z2OrientationReversalReady : Prop
  massInversionReferenceSupported : Prop
  negativeThermodynamicDensityPostulated : Prop
  absoluteRSigmaSolutionReady : Prop
  countertermCoefficientsDerived : Prop
  eCountertermDerived : Prop

def mplaLocalThroatReady
    (g : MPLASchwarzschildThroatLocalModelGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.arealRadiusFormulaDeclared /\
  g.rhoReflectionDeclared /\
  g.minimalThroatReady /\
  g.rSigmaOverRsEqualsOne /\
  g.z2OrientationReversalReady /\
  g.massInversionReferenceSupported /\
  Not g.negativeThermodynamicDensityPostulated

theorem local_mpla_throat_does_not_fix_absolute_radius
    (g : MPLASchwarzschildThroatLocalModelGate)
    (_hLocal : mplaLocalThroatReady g)
    (hMissing : Not g.absoluteRSigmaSolutionReady) :
    Not g.absoluteRSigmaSolutionReady := by
  exact hMissing

theorem local_mpla_throat_does_not_close_counterterm
    (g : MPLASchwarzschildThroatLocalModelGate)
    (_hLocal : mplaLocalThroatReady g)
    (hMissingCoeffs : Not g.countertermCoefficientsDerived)
    (hCountertermNeedsCoeffs : g.eCountertermDerived -> g.countertermCoefficientsDerived) :
    Not g.eCountertermDerived := by
  intro hE
  exact hMissingCoeffs (hCountertermNeedsCoeffs hE)

end P0EFTJanusZ2SigmaMPLASchwarzschildThroatLocalModelGate
end JanusFormal
