import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaRSigmaSolutionToEmbeddingCurvatureBranchGate

set_option autoImplicit false

structure RSigmaSolutionToEmbeddingCurvatureBranchGate where
  bridgeDeclared : Prop
  throatRadiusSolutionCertificateReady : Prop
  matterFluxBlockReduced : Prop
  countertermBlockReduced : Prop
  rSigmaOfAReady : Prop
  xPlusMinusOfAReady : Prop
  embeddingUnblockedByRadiusSolution : Prop
  activeCurvatureBranchReady : Prop
  embeddingManifestWritable : Prop
  curvatureBranchManifestWritable : Prop
  h0NormalizationManifestWritable : Prop
  curvatureRadiusNormalizationManifestWritable : Prop
  embeddingManifestWritten : Prop
  curvatureBranchManifestWritten : Prop
  h0NormalizationManifestWritten : Prop
  curvatureRadiusNormalizationManifestWritten : Prop
  gatePassed : Prop

def bridgeReady
    (g : RSigmaSolutionToEmbeddingCurvatureBranchGate) : Prop :=
  g.bridgeDeclared /\
  g.throatRadiusSolutionCertificateReady /\
  g.matterFluxBlockReduced /\
  g.countertermBlockReduced /\
  g.rSigmaOfAReady /\
  g.xPlusMinusOfAReady /\
  g.embeddingUnblockedByRadiusSolution /\
  g.activeCurvatureBranchReady /\
  g.embeddingManifestWritable /\
  g.curvatureBranchManifestWritable /\
  g.h0NormalizationManifestWritable /\
  g.curvatureRadiusNormalizationManifestWritable /\
  g.embeddingManifestWritten /\
  g.curvatureBranchManifestWritten /\
  g.h0NormalizationManifestWritten /\
  g.curvatureRadiusNormalizationManifestWritten

theorem bridge_requires_radial_blocks_reduced
    (g : RSigmaSolutionToEmbeddingCurvatureBranchGate)
    (h : bridgeReady g) :
    g.matterFluxBlockReduced /\ g.countertermBlockReduced := by
  exact And.intro h.2.2.1 h.2.2.2.1

theorem bridge_requires_rsigma_and_embedding
    (g : RSigmaSolutionToEmbeddingCurvatureBranchGate)
    (h : bridgeReady g) :
    g.rSigmaOfAReady /\ g.xPlusMinusOfAReady := by
  exact And.intro h.2.2.2.2.1 h.2.2.2.2.2.1

theorem bridge_requires_embedding_unblocked_by_radius_solution
    (g : RSigmaSolutionToEmbeddingCurvatureBranchGate)
    (h : bridgeReady g) :
    g.embeddingUnblockedByRadiusSolution := by
  exact h.2.2.2.2.2.2.1

theorem bridge_writes_embedding_and_curvature_manifests
    (g : RSigmaSolutionToEmbeddingCurvatureBranchGate)
    (h : bridgeReady g) :
    g.embeddingManifestWritten /\ g.curvatureBranchManifestWritten := by
  exact And.intro h.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bridge_writes_dimensional_background_normalizations
    (g : RSigmaSolutionToEmbeddingCurvatureBranchGate)
    (h : bridgeReady g) :
    g.h0NormalizationManifestWritten /\
      g.curvatureRadiusNormalizationManifestWritten := by
  exact And.intro h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end P0EFTJanusZ2SigmaRSigmaSolutionToEmbeddingCurvatureBranchGate
end JanusFormal
