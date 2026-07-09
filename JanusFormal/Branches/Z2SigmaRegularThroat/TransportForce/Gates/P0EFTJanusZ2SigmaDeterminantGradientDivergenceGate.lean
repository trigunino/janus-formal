import JanusFormal.Branches.Z2SigmaRegularThroat.TransportForce.Gates.P0EFTJanusZ2SigmaBridgeDeterminantFactorAuditGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaPullbackVolumeDeterminantRatioGate
import JanusFormal.Branches.Z2SigmaRegularThroat.TransportForce.Gates.P0EFTJanusZ2SigmaTransportCompatibilitySourceEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaDeterminantGradientDivergenceGate

set_option autoImplicit false

structure DeterminantGradientDivergenceGate where
  bridgeDeterminantAuditGateImported : Prop
  pullbackVolumeRatioGateImported : Prop
  transportCompatibilitySourceEquationGateImported : Prop
  bPlusCovariantGradientDeclared : Prop
  bMinusCovariantGradientDeclared : Prop
  plusProductRuleDeclared : Prop
  minusProductRuleDeclared : Prop
  gradientsKeptOutsideK : Prop
  gradientsKeptOutsideQcross : Prop
  noDeterminantGradientAbsorption : Prop
  bPlusFromPullbackVolumeReady : Prop
  bMinusFromPullbackVolumeReady : Prop
  plusDivergenceSplitDerived : Prop
  minusDivergenceSplitDerived : Prop
  feedsPlusCompatibilityEquation : Prop
  feedsMinusCompatibilityEquation : Prop

def determinantGradientTemplateReady
    (g : DeterminantGradientDivergenceGate) : Prop :=
  g.bridgeDeterminantAuditGateImported /\
  g.pullbackVolumeRatioGateImported /\
  g.transportCompatibilitySourceEquationGateImported /\
  g.bPlusCovariantGradientDeclared /\
  g.bMinusCovariantGradientDeclared /\
  g.plusProductRuleDeclared /\
  g.minusProductRuleDeclared /\
  g.gradientsKeptOutsideK /\
  g.gradientsKeptOutsideQcross /\
  g.noDeterminantGradientAbsorption

def determinantGradientDivergenceReady
    (g : DeterminantGradientDivergenceGate) : Prop :=
  determinantGradientTemplateReady g /\
  g.bPlusFromPullbackVolumeReady /\
  g.bMinusFromPullbackVolumeReady /\
  g.plusDivergenceSplitDerived /\
  g.minusDivergenceSplitDerived /\
  g.feedsPlusCompatibilityEquation /\
  g.feedsMinusCompatibilityEquation

theorem determinant_gradient_splits_both_cross_divergences
    (g : DeterminantGradientDivergenceGate)
    (hReady : determinantGradientDivergenceReady g) :
    g.plusDivergenceSplitDerived /\ g.minusDivergenceSplitDerived := by
  exact And.intro hReady.right.right.right.left
    hReady.right.right.right.right.left

theorem determinant_gradient_feeds_transport_compatibility_equations
    (g : DeterminantGradientDivergenceGate)
    (hReady : determinantGradientDivergenceReady g) :
    g.feedsPlusCompatibilityEquation /\ g.feedsMinusCompatibilityEquation := by
  exact And.intro hReady.right.right.right.right.right.left
    hReady.right.right.right.right.right.right

theorem missing_bplus_pullback_blocks_plus_divergence_split
    (g : DeterminantGradientDivergenceGate)
    (hMissing : Not g.bPlusFromPullbackVolumeReady) :
    Not (determinantGradientDivergenceReady g) := by
  intro hReady
  exact hMissing hReady.right.left

theorem determinant_gradient_not_absorbed_into_k_or_qcross
    (g : DeterminantGradientDivergenceGate)
    (hTemplate : determinantGradientTemplateReady g) :
    g.gradientsKeptOutsideK /\ g.gradientsKeptOutsideQcross /\
      g.noDeterminantGradientAbsorption := by
  exact And.intro hTemplate.right.right.right.right.right.right.right.left
    (And.intro hTemplate.right.right.right.right.right.right.right.right.left
      hTemplate.right.right.right.right.right.right.right.right.right)

end P0EFTJanusZ2SigmaDeterminantGradientDivergenceGate
end JanusFormal
