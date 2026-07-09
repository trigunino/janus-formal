import JanusFormal.Branches.Z2SigmaRegular.GlobalBimetricAlpha.Gates.P0EFTJanusZ2SigmaCountertermAlphaResZ2AntiInvarianceObligationGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaSmoothEmbeddedThroatGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaPointCollapseLimitGate

set_option autoImplicit false

structure SigmaPointCollapseLimitGate where
  alphaResAntiInvarianceGateImported : Prop
  smoothEmbeddedThroatGateImported : Prop
  pointCollapseRouteDeclared : Prop
  singularLimitNotSmoothSigmaDeclared : Prop
  noActivePipelineReplacement : Prop
  noFittedCountertermCoefficient : Prop
  volumeCollapseRateDeclared : Prop
  alphaResGrowthBoundDeclared : Prop
  distributionalDefectControlDeclared : Prop
  z2LimitCompatibilityDeclared : Prop
  integratedAlphaResVanishes : Prop
  lCtBypassReady : Prop
  sigmaPointCollapseLimitGatePassed : Prop

def pointCollapseLimitLedgerDeclared
    (g : SigmaPointCollapseLimitGate) : Prop :=
  g.alphaResAntiInvarianceGateImported /\
  g.smoothEmbeddedThroatGateImported /\
  g.pointCollapseRouteDeclared /\
  g.singularLimitNotSmoothSigmaDeclared /\
  g.noActivePipelineReplacement /\
  g.noFittedCountertermCoefficient

def pointCollapseLimitReady
    (g : SigmaPointCollapseLimitGate) : Prop :=
  pointCollapseLimitLedgerDeclared g /\
  g.volumeCollapseRateDeclared /\
  g.alphaResGrowthBoundDeclared /\
  g.distributionalDefectControlDeclared /\
  g.z2LimitCompatibilityDeclared /\
  g.integratedAlphaResVanishes /\
  g.lCtBypassReady /\
  g.sigmaPointCollapseLimitGatePassed

theorem point_collapse_limit_requires_integrated_residual_vanishing
    (g : SigmaPointCollapseLimitGate)
    (hReady : pointCollapseLimitReady g) :
    g.integratedAlphaResVanishes := by
  exact hReady.right.right.right.right.right.left

theorem point_collapse_limit_requires_lct_bypass_certificate
    (g : SigmaPointCollapseLimitGate)
    (hReady : pointCollapseLimitReady g) :
    g.lCtBypassReady := by
  exact hReady.right.right.right.right.right.right.left

theorem missing_growth_bound_blocks_point_collapse_route
    (g : SigmaPointCollapseLimitGate)
    (hMissing : Not g.alphaResGrowthBoundDeclared) :
    Not (pointCollapseLimitReady g) := by
  intro hReady
  exact hMissing hReady.right.right.left

theorem missing_integrated_limit_blocks_lct_bypass
    (g : SigmaPointCollapseLimitGate)
    (hMissing : Not g.integratedAlphaResVanishes) :
    Not (pointCollapseLimitReady g) := by
  intro hReady
  exact hMissing (point_collapse_limit_requires_integrated_residual_vanishing g hReady)

end P0EFTJanusZ2SigmaPointCollapseLimitGate
end JanusFormal
