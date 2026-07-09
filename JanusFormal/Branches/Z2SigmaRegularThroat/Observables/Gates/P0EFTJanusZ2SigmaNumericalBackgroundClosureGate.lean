import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaBackgroundEquationDerivationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaNumericalBackgroundClosureGate

set_option autoImplicit false

structure Z2SigmaNumericalBackgroundClosureGate where
  backgroundEquationsDerived : Prop
  rhoEffZ2SigmaOfAReady : Prop
  pEffZ2SigmaOfAReady : Prop
  curvatureKDeclared : Prop
  kappaNormalizationDeclared : Prop
  integrationDomainDeclared : Prop
  observationalParameterFitForbidden : Prop
  legacyLCDMBackgroundReuseForbidden : Prop
  archivedZ4BackgroundReuseForbidden : Prop
  numericalHZ2SigmaReady : Prop
  numericalOmegaMZ2SigmaReady : Prop

def numericalBackgroundPrerequisites
    (g : Z2SigmaNumericalBackgroundClosureGate) : Prop :=
  g.backgroundEquationsDerived /\
  g.rhoEffZ2SigmaOfAReady /\
  g.pEffZ2SigmaOfAReady /\
  g.curvatureKDeclared /\
  g.kappaNormalizationDeclared /\
  g.integrationDomainDeclared /\
  g.observationalParameterFitForbidden /\
  g.legacyLCDMBackgroundReuseForbidden /\
  g.archivedZ4BackgroundReuseForbidden

theorem numerical_h_requires_background_functions
    (g : Z2SigmaNumericalBackgroundClosureGate)
    (hReady : g.numericalHZ2SigmaReady)
    (hImplies : g.numericalHZ2SigmaReady -> numericalBackgroundPrerequisites g) :
    numericalBackgroundPrerequisites g := by
  exact hImplies hReady

theorem numerical_omega_m_requires_h
    (g : Z2SigmaNumericalBackgroundClosureGate)
    (hOmega : g.numericalOmegaMZ2SigmaReady)
    (hImplies : g.numericalOmegaMZ2SigmaReady -> g.numericalHZ2SigmaReady) :
    g.numericalHZ2SigmaReady := by
  exact hImplies hOmega

end P0EFTJanusZ2SigmaNumericalBackgroundClosureGate
end JanusFormal
