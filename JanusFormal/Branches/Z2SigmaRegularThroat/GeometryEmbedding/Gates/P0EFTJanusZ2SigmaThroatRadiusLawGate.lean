import JanusFormal.Branches.Z2SigmaRegularThroat.Topology.Gates.P0EFTJanusProjectiveTunnelInterface

namespace JanusFormal
namespace P0EFTJanusZ2SigmaThroatRadiusLawGate

set_option autoImplicit false

structure ThroatRadiusLawGate where
  janusTunnelBibliographyChecked : Prop
  thinShellFRWWormholeBibliographyChecked : Prop
  throatRadiusVariableDeclared : Prop
  candidateComovingThroatAnsatzDeclared : Prop
  activeNoFitDerivationRequired : Prop
  observationalFitForRadiusForbidden : Prop
  janusActionOrTopologyDerivesRadiusLaw : Prop
  rSigmaOfAReady : Prop
  rSigmaLawPredictionReady : Prop

def throatRadiusLawProblemDeclared
    (g : ThroatRadiusLawGate) : Prop :=
  g.janusTunnelBibliographyChecked /\
  g.thinShellFRWWormholeBibliographyChecked /\
  g.throatRadiusVariableDeclared /\
  g.candidateComovingThroatAnsatzDeclared /\
  g.activeNoFitDerivationRequired /\
  g.observationalFitForRadiusForbidden

def throatRadiusLawClosureReady
    (g : ThroatRadiusLawGate) : Prop :=
  throatRadiusLawProblemDeclared g /\
  g.janusActionOrTopologyDerivesRadiusLaw /\
  g.rSigmaOfAReady /\
  g.rSigmaLawPredictionReady

theorem throat_radius_prediction_requires_janus_derivation
    (g : ThroatRadiusLawGate)
    (hReady : throatRadiusLawClosureReady g) :
    g.janusActionOrTopologyDerivesRadiusLaw := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaThroatRadiusLawGate
end JanusFormal
