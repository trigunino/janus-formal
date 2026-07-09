import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaEmbeddingGaugeEquationGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaEmbeddingGaugePolicyGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusLawGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTunnelEmbeddingConstraintCountGate

set_option autoImplicit false

structure TunnelEmbeddingConstraintCountGate where
  activeEmbeddingProblemDeclared : Prop
  embeddingUnknownFunctionsDeclared : Prop
  inducedMetricMatchingConstraintsDeclared : Prop
  z2EquivarianceConstraintsDeclared : Prop
  regularThroatConstraintDeclared : Prop
  throatRadiusVariationalEquationDeclared : Prop
  throatRadiusBlockExpansionDeclared : Prop
  embeddingGaugePolicyDeclared : Prop
  embeddingGaugeEquationsDeclared : Prop
  independentConstraintCountSufficient : Prop
  throatRadiusLawDerived : Prop
  embeddingGaugeFixed : Prop
  xPlusMinusOfADetermined : Prop

def embeddingConstraintLedgerDeclared
    (g : TunnelEmbeddingConstraintCountGate) : Prop :=
  g.activeEmbeddingProblemDeclared /\
  g.embeddingUnknownFunctionsDeclared /\
  g.inducedMetricMatchingConstraintsDeclared /\
  g.z2EquivarianceConstraintsDeclared /\
  g.regularThroatConstraintDeclared /\
  g.throatRadiusVariationalEquationDeclared /\
  g.throatRadiusBlockExpansionDeclared /\
  g.embeddingGaugePolicyDeclared /\
  g.embeddingGaugeEquationsDeclared

def embeddingConstraintClosureReady
    (g : TunnelEmbeddingConstraintCountGate) : Prop :=
  embeddingConstraintLedgerDeclared g /\
  g.independentConstraintCountSufficient /\
  g.throatRadiusLawDerived /\
  g.embeddingGaugeFixed /\
  g.xPlusMinusOfADetermined

theorem xpm_determined_requires_throat_radius_law
    (g : TunnelEmbeddingConstraintCountGate)
    (hReady : embeddingConstraintClosureReady g) :
    g.throatRadiusLawDerived := by
  exact hReady.2.2.1

end P0EFTJanusZ2SigmaTunnelEmbeddingConstraintCountGate
end JanusFormal
