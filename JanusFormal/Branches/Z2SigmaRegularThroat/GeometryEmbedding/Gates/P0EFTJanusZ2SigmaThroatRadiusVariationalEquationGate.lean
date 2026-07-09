import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusSigmaBoundaryActionSupportGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusLawGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate

set_option autoImplicit false

structure ThroatRadiusVariationalEquationGate where
  throatRadiusBibliographyChecked : Prop
  topologyOnlyUnderdeterminesRadiusLaw : Prop
  sigmaBoundaryActionAvailable : Prop
  radialEmbeddingVariableDeclared : Prop
  radialEulerLagrangeEquationDeclared : Prop
  candidateComovingLawDiagnosticOnly : Prop
  observationalFitForbidden : Prop
  radialEulerLagrangeOperatorReady : Prop
  rSigmaEquationReady : Prop
  rSigmaEquationSolved : Prop
  rSigmaOfAReady : Prop

def throatRadiusVariationalProblemDeclared
    (g : ThroatRadiusVariationalEquationGate) : Prop :=
  g.throatRadiusBibliographyChecked /\
  g.topologyOnlyUnderdeterminesRadiusLaw /\
  g.sigmaBoundaryActionAvailable /\
  g.radialEmbeddingVariableDeclared /\
  g.radialEulerLagrangeEquationDeclared /\
  g.candidateComovingLawDiagnosticOnly /\
  g.observationalFitForbidden

def throatRadiusVariationalEquationReady
    (g : ThroatRadiusVariationalEquationGate) : Prop :=
  throatRadiusVariationalProblemDeclared g /\
  g.radialEulerLagrangeOperatorReady /\
  g.rSigmaEquationReady

def throatRadiusVariationalClosureReady
    (g : ThroatRadiusVariationalEquationGate) : Prop :=
  throatRadiusVariationalEquationReady g /\
  g.rSigmaEquationSolved /\
  g.rSigmaOfAReady

theorem solved_radius_requires_variational_equation
    (g : ThroatRadiusVariationalEquationGate)
    (hReady : throatRadiusVariationalClosureReady g) :
    g.rSigmaEquationReady := by
  exact hReady.1.2.2

theorem topology_only_is_not_radius_law
    (g : ThroatRadiusVariationalEquationGate)
    (hDeclared : throatRadiusVariationalProblemDeclared g) :
    g.topologyOnlyUnderdeterminesRadiusLaw := by
  exact hDeclared.2.1

end P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate
end JanusFormal
