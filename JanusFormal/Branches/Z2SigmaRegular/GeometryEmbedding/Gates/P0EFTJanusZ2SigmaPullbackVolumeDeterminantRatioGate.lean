import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate
import JanusFormal.Branches.Z2SigmaRegular.TransportForce.Gates.P0EFTJanusZ2SigmaBridgeDeterminantFactorAuditGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaOrientedPullbackVariationCommutationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaPullbackVolumeDeterminantRatioGate

set_option autoImplicit false

structure PullbackVolumeDeterminantRatioGate where
  activeEmbeddingReadinessGateImported : Prop
  bridgeDeterminantFactorAuditGateImported : Prop
  orientedPullbackCommutationGateImported : Prop
  plusVolumeFormDeclared : Prop
  minusVolumeFormDeclared : Prop
  z2PullbackVolumeMapDeclared : Prop
  jacobianDensityChannelDeclared : Prop
  orientationSignFixed : Prop
  noFittedVolumeCoefficient : Prop
  activeEmbeddingReady : Prop
  plusMinusMetricDeterminantsAvailable : Prop
  pullbackVolumeRatioDerived : Prop
  bPlusFromPullbackVolume : Prop
  bMinusFromInversePullbackVolume : Prop
  reciprocalIdentityDerived : Prop
  feedsBridgeDeterminantAudit : Prop

def pullbackVolumeRatioTemplateReady
    (g : PullbackVolumeDeterminantRatioGate) : Prop :=
  g.activeEmbeddingReadinessGateImported /\
  g.bridgeDeterminantFactorAuditGateImported /\
  g.orientedPullbackCommutationGateImported /\
  g.plusVolumeFormDeclared /\
  g.minusVolumeFormDeclared /\
  g.z2PullbackVolumeMapDeclared /\
  g.jacobianDensityChannelDeclared /\
  g.orientationSignFixed /\
  g.noFittedVolumeCoefficient

def pullbackVolumeRatioDerivedReady
    (g : PullbackVolumeDeterminantRatioGate) : Prop :=
  pullbackVolumeRatioTemplateReady g /\
  g.activeEmbeddingReady /\
  g.plusMinusMetricDeterminantsAvailable /\
  g.pullbackVolumeRatioDerived /\
  g.bPlusFromPullbackVolume /\
  g.bMinusFromInversePullbackVolume /\
  g.reciprocalIdentityDerived /\
  g.feedsBridgeDeterminantAudit

theorem pullback_volume_derivation_feeds_b_factors
    (g : PullbackVolumeDeterminantRatioGate)
    (hReady : pullbackVolumeRatioDerivedReady g) :
    g.bPlusFromPullbackVolume /\
      g.bMinusFromInversePullbackVolume /\
      g.reciprocalIdentityDerived := by
  exact And.intro hReady.right.right.right.right.left
    (And.intro hReady.right.right.right.right.right.left
      hReady.right.right.right.right.right.right.left)

theorem missing_active_embedding_blocks_volume_ratio
    (g : PullbackVolumeDeterminantRatioGate)
    (hMissing : Not g.activeEmbeddingReady) :
    Not (pullbackVolumeRatioDerivedReady g) := by
  intro hReady
  exact hMissing hReady.right.left

theorem pullback_volume_derivation_feeds_determinant_audit
    (g : PullbackVolumeDeterminantRatioGate)
    (hReady : pullbackVolumeRatioDerivedReady g) :
    g.feedsBridgeDeterminantAudit := by
  exact hReady.right.right.right.right.right.right.right

end P0EFTJanusZ2SigmaPullbackVolumeDeterminantRatioGate
end JanusFormal
