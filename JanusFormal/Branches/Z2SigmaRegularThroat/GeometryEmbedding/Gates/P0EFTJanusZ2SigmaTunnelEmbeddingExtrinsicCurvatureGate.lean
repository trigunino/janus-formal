import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate
import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaTunnelJunctionConditionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate

set_option autoImplicit false

structure TunnelEmbeddingExtrinsicCurvatureGate where
  thinShellEmbeddingBibliographyChecked : Prop
  sigmaEmbeddingsDeclared : Prop
  tangentFramesDeclared : Prop
  unitNormalsDeclared : Prop
  inducedMetricMatchingDeclared : Prop
  extrinsicCurvatureDefinitionReady : Prop
  z2NormalOrientationApplied : Prop
  deltaKsFromKPlusMinusReady : Prop
  deltaKtauFromKPlusMinusReady : Prop
  tunnelEmbeddingFunctionsOfAReady : Prop
  deltaKsOfAReady : Prop
  deltaKtauOfAReady : Prop

def extrinsicCurvatureStructuralClosure
    (g : TunnelEmbeddingExtrinsicCurvatureGate) : Prop :=
  g.thinShellEmbeddingBibliographyChecked /\
  g.sigmaEmbeddingsDeclared /\
  g.tangentFramesDeclared /\
  g.unitNormalsDeclared /\
  g.inducedMetricMatchingDeclared /\
  g.extrinsicCurvatureDefinitionReady /\
  g.z2NormalOrientationApplied /\
  g.deltaKsFromKPlusMinusReady /\
  g.deltaKtauFromKPlusMinusReady

def extrinsicCurvatureScaleFactorClosure
    (g : TunnelEmbeddingExtrinsicCurvatureGate) : Prop :=
  extrinsicCurvatureStructuralClosure g /\
  g.tunnelEmbeddingFunctionsOfAReady /\
  g.deltaKsOfAReady /\
  g.deltaKtauOfAReady

theorem deltaK_of_a_requires_tunnel_embedding_functions
    (g : TunnelEmbeddingExtrinsicCurvatureGate)
    (hReady : extrinsicCurvatureScaleFactorClosure g) :
    g.tunnelEmbeddingFunctionsOfAReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate
end JanusFormal
